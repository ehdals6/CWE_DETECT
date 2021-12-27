open Core_kernel
open Bap.Std
open Bap_primus.Std
include Self()

let check_name = "Dongmin Check"
let sexps atoms = Sexp.List (List.map ~f:(fun x -> Sexp.Atom x) atoms)
let results r op = Sexp.List [op; Primus.sexp_of_value r]

let sexp_of_binop ((op,x,y),r) = results r @@ sexps [
    Bil.string_of_binop op;
    Primus.Value.to_string x;
    Primus.Value.to_string y;
  ]

let dongmin, print_dongmin =
  Primus.Observation.provide ~inspect:sexp_of_binop "cwe190"


module Notify (Machine : Primus.Machine.S) = struct
  open Machine.Syntax

  let size32: int =   0x7FFFFFFF
  let size64: int64 = 0x7FFFFFFFFFFFFFFFL
  let except_flag = ref 0

  let on_read (x,y) = 
	if Var.to_string x = "RBP" || Var.to_string x = "brk" then 
	  let _ = except_flag := 1 in
	  Machine.return ()
	else 
	  let _ = except_flag := 0 in
	  Machine.return ()

  let on_binop ((op,x,y),r) = 
	if op = Bil.PLUS || op = Bil.TIMES then
	  let str = Sexplib0.Sexp.to_string (Primus.Value.sexp_of_t r) in
	  let index = Option.value_exn (String.index str ':') in 
	  let data_type = String.sub str index 3 in
	  let data_value = String.sub str 0 index in
	  if data_type = ":32" then
		if Primus.Value.(>) x r then
		  Machine.Observation.make print_dongmin ((op,x,y),r)
		else if int_of_string (data_value) > size32 then
		  Machine.Observation.make print_dongmin ((op,x,y),r)
		else Machine.return ()
	  else if data_type = ":64" && !except_flag = 0 then
                if Primus.Value.(>) x r then
                  Machine.Observation.make print_dongmin ((op,x,y),r)
                else if Int64.of_string (data_value) > size64 then
                  Machine.Observation.make print_dongmin ((op,x,y),r)
                else Machine.return ()
	  else Machine.return ()
	else Machine.return ()
  let init () = Machine.sequence Primus.Interpreter.[
	binop >>> on_binop;
	read >>> on_read;
  ]
end

let () = Config.when_ready (fun {get=(!!)} ->
    Primus.Machine.add_component (module Notify) [@warning "-D"];
    Primus.Components.register_generic "TEST" (module Notify)
      ~internal:true
      ~package:"bap"
)

 
