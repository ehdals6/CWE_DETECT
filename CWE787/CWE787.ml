open Core_kernel
open Bap.Std
open Graphlib.Std
open Format
open Bap_main
open Printf

include Self()

let temp_int : int ref = ref 0;;
let temp_sub : Sub.t Option.t ref = ref None;;
let temp_bool_blk : bool ref = ref true;;
let temp_String : string ref = ref "";;

let return : Bil.exp Option.t ref = ref None;;
let new_track : Bil.exp Option.t ref = ref None;;
let backtrack_pos : Def.t Option.t ref = ref None;;
let track_flag : bool ref = ref false;;

let rec parse exp = 
  let temp : Bil.exp = exp in
  match temp with
  | Load (exp1,exp2,endian,size) -> Option.some exp2
  | Store (exp1,exp2,exp3,endian,size) -> Option.some exp2
  | Cast (cast,int,exp) -> parse exp
  | BinOp (binop,exp1,exp2) -> Option.some temp
  | Var var -> Option.some temp
  | _ -> None

let parse_store exp =
  let temp : Bil.exp = exp in
  match temp with
  | Store (exp1,exp2,exp3,endian,size) -> parse exp3
  | _ -> None 

let parse_store2 exp =
  let temp : Bil.exp = exp in
  match temp with
  | Store (exp1,exp2,exp3,endian,size) -> parse exp2
  | _ -> None 

let rec parse_load exp =
  let temp : Bil.exp = exp in
  match temp with
  | Load (exp1,exp2,endian,size) -> parse exp2
  | Cast (cast,int,exp) -> parse_load exp
  | _ -> None 

let rec parse_binop exp =
  let temp : Bil.exp = exp in
  match temp with
  | BinOp (binop,exp1,exp2) -> 
    (match binop with 
    | PLUS | MINUS | TIMES -> Option.some temp
    | _ -> None )
  | Cast (cast,int,exp) -> parse_binop exp
  | Store (exp1,exp2,exp3,endian,size) -> parse_binop exp3
  | _ -> None


let backtrack_blk blk exp pos =
  let def_t = Term.enum def_t blk in 
  Seq.iter def_t ~f:(fun def ->
    let rhs = Def.rhs def in
    print_endline(Exp.to_string rhs)
  )

let rec backtrack_sub sub exp pos =
  let exp : Bil.exp = exp in
  let _ = printf "---BACKTRACK [%a]--- \n" Exp.ppo exp in
  let blk_t = Term.enum blk_t sub in
  let _ = Seq.iter blk_t ~f:(fun blk ->
    let def_t = Term.enum def_t blk in
    Seq.iter def_t ~f:(fun def ->
      let rhs = Def.rhs def in
      let lhs = Def.lhs def in
      match exp with
      | BinOp (binop,exp1,exp2) -> 
        if parse_store2 rhs = Option.some exp && Tid.(>) (Term.tid pos) (Term.tid def)then
          let _ = new_track := parse_store rhs in
          let _ = print_string(Def.to_string(def)) in
          backtrack_pos := Option.some def
        else if Tid.(=) (Term.tid pos) (Term.tid def) && Option.is_some !backtrack_pos then
          let temp = !backtrack_pos in
          let _ = backtrack_pos := None in
          if Option.is_some(parse_binop(Def.rhs(Option.value_exn temp))) then
            let _ = return := parse_binop(Def.rhs(Option.value_exn temp)) in
            printf "Binary Operation: %a" Def.ppo (Option.value_exn temp)
          else if Option.is_some !new_track then
            return := backtrack_sub sub (Option.value_exn !new_track) (Option.value_exn temp)

      | Var var ->
        if Exp.to_string exp = Var.name lhs && Tid.(>) (Term.tid pos) (Term.tid def)  then
          let _ = new_track := parse rhs in
          let _ = print_string(Def.to_string(def)) in
          backtrack_pos := Option.some def
        else if Tid.(=) (Term.tid pos) (Term.tid def) && Option.is_some !backtrack_pos then
          let temp = !backtrack_pos in
          let _ = backtrack_pos := None in
          if Option.is_some(parse_binop(Def.rhs(Option.value_exn temp))) then
            let _ = return := parse_binop(Def.rhs(Option.value_exn temp)) in
            printf "Binary Operation: %a" Def.ppo (Option.value_exn temp)
          else if Option.is_some !new_track then
            return := backtrack_sub sub (Option.value_exn !new_track) (Option.value_exn temp)

      | Int word -> ()
      | _ -> ()

    ) (*def*)
  ) in (*blk*)
  !return

let analyze_sub sub = 
  let blk_t = Term.enum blk_t sub in
  Seq.iter blk_t ~f:(fun blk ->
    let def_t = Term.enum def_t blk in
    Seq.iter def_t ~f:(fun def ->
      let rhs = Def.rhs def in
      let store = parse_store2 rhs in
      if Option.is_some store && Exp.to_string(Option.value_exn store) <> "RSP" then
        let _ = printf "\nWRITE SIGNATURE: [%a]\n" Exp.ppo rhs in
        if backtrack_sub sub (Option.value_exn store) def <> None then
		  let _ = return := None in
          printf "Out-of-bounds Write: %a" Def.ppo def
    ) (*def*)
  ) (*blk*)

(*
	return type is string
	return the call target name
*)
let get_call_target_name blks : string = 
  let _ = temp_String:="" in
  let _ = Seq.iter blks ~f:(fun blk ->
  let jmp_e = Term.enum jmp_t blk in
  let _ = Seq.find jmp_e ~f:(fun jmp ->
  let kind = Jmp.kind jmp in
  match kind with
  | Goto _ | Int _ | Ret _ -> false
  | Call dst -> 
    (match Call.target dst with
	| Indirect _ -> false
	| Direct tid -> 
	  let dst_str = Tid.name tid in
	  let len = String.length dst_str -1 in
	  let strip_str = String.sub dst_str 1 len in
	  let _ = print_endline("\n"^strip_str^"\n") in 
	  temp_String := strip_str;
	true
	)
  ) in ()
)in	!temp_String


(*
	return type is Bil.exp Option.t
	but actually return the Exp2 in Store instruction
*)
let get_second_exp exps : Bil.exp Option.t = 
	let exp : Bil.exp = exps in
	match exp with
	| Store (exp1, exp2, exp3,endian, size) ->
		Option.some exp2
	| _ -> None

(*find the input function and only return such subroutine*)
let find_by_name prog name = 
	Term.enum sub_t prog |> Seq.find ~f:(fun sub ->
		String.equal (Sub.name sub) name)

(*
	check if the defs satisfy the jmptable pattern
	return type: bool
*)
let check_def defs flag : bool = 
	let def : Def.t = defs in
	let rhs = Def.rhs def in
	let lhs = Def.lhs def in
	match flag with
	| "RBP" -> 
		if Exp.to_string(rhs) = flag then
			let _ = print_endline("#1 = RSP true") in
			true
		else
			false
	| "RSP - 8" ->
		if Var.name(lhs)="RSP" && Exp.to_string(rhs) = flag then
			let _ = print_endline("RBP = RSP - 9 true") in
			true
		else
			false
	| "RSP" ->
		if Var.name(lhs)="mem" && Exp.to_string(Option.value_exn (get_second_exp rhs))= flag then 
			let _ = print_endline("mem:= mem with [RSP] true") in
			true
		else
			false
	| "end" ->
		if Var.name(lhs) = "RBP" && Exp.to_string(rhs) = "RSP" then
			let _ = print_endline("RBP = RSP true") in
			true
		else
			false
	| _ -> false


(* 	if
	1.#434724 := RBP
	2.RSP := RSP - 8
	3.mem := mem with [RSP, el]:u64 <- #434724
	4.RBP := RSP
	ok jmptable
	any case doesn`t match or there have more instructions return false
	return tye: bool
	temp_bool_blks free.
*)
let check_blk_pattern blks : bool = 
	let _ = temp_bool_blk:= true in
	let _ = Seq.iter blks ~f:(fun blk ->
		let def_e = Term.enum def_t blk in
		let _ = temp_int := 0 in
		Seq.iter def_e ~f:(fun def ->
			if !temp_int = 0 then
				begin
					temp_int := !temp_int + 1;
					temp_bool_blk := !temp_bool_blk && (check_def def "RBP");
				end
			else if !temp_int = 1 && !temp_bool_blk then
				begin
					temp_int := !temp_int + 1;
					temp_bool_blk := !temp_bool_blk && (check_def def "RSP - 8");
				end
			else if !temp_int = 2 && !temp_bool_blk then
				begin
					temp_int := !temp_int + 1;
					temp_bool_blk := !temp_bool_blk && (check_def def "RSP");
				end
			else if !temp_int = 3 && !temp_bool_blk then 
				begin
					temp_int := !temp_int + 1;
					temp_bool_blk := !temp_bool_blk && (check_def def "end");
				end
			else 
				temp_bool_blk := !temp_bool_blk && false
		)
	) in !temp_bool_blk


(* 
	return type: Sub.t Option.t
	return the [None] or [Subroutine]
*)
let check_sub_jmpt subs : string Option.t = 
	let sub : Sub.t = subs in
	let blk = Term.enum blk_t sub in
	let len = Seq.length blk in
	if len = 1 then
		begin
		print_endline("only 1 blk start to check jmptable case");
		let res = check_blk_pattern blk	in
		(if res then
			let _ = print_endline("find jmptable pattern") in
			Option.some (get_call_target_name blk)
		else
			let _ = print_endline("Not jmptable, Other case") in
			None)
		end
	else
		begin
		print_endline("more than 1 blk "^(string_of_int len));
		None
		end 

(*
	case 1: jump table then find real [subroutine]
	case 2: real subroutine then get the [new sub] and then we start to analyze [subroutine]
	return type: union()
*)
let rec detect_fun fname proj = 
	let prog = Project.program proj in
	let subs = find_by_name prog fname in
	match subs with
	| None -> print_endline("No such sub")
	| Some sub ->
		let _ = print_endline("Find sub"^(Sub.name sub)) in
		let check_jmptable = check_sub_jmpt sub in
		match check_jmptable with
		| None -> 
			let _ = print_endline("Start to analyze sub") in
			let _ = analyze_sub sub in ()
		| Some realsub_name ->
			detect_fun realsub_name proj


let main fun_name proj = 
	let _ = detect_fun fun_name proj in
	print_endline("finish search")



module Cmdline = struct
	open Config
	let fun_name = param string "fun_name" ~doc:"Name of the detect function name"

	let () = when_ready (fun {get=(!!)} ->
		Project.register_pass' (main !!fun_name ))

	let () = manpage [
		`S "DESCRIPTION";
		`P
			"Checks whether if there is a vulnerability"
	]
end