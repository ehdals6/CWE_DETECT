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

let parent_def : Def.t Option.t ref = ref None;;
let parent_exp : Bil.exp Option.t ref = ref None;;
let trace_rhs_rhs : Bil.exp Option.t ref = ref None;;




let rax_address : Bil.exp Option.t ref = ref None;;
let rdi_address : Bil.exp Option.t ref = ref None;;
let r15_address : Bil.exp Option.t ref = ref None;;
let rbx_address : Bil.exp Option.t ref = ref None;;
let r12_address : Bil.exp Option.t ref = ref None;;
let dangling_address : Bil.exp Option.t ref = ref None;;


let free_flag = ref 0;;
let sub_count = ref 0;;


let collect_exp_value = Exp.fold ~init:[] (object
  inherit [exp list] Exp.visitor
  method! enter_exp a b = a::b
    end);;


(*
	RDI := mem[RBP - 0x10, el]:u64
	RDI := RAX
	mem := mem with [RBP - 0x24, el]:u32 <- low:32[RAX]
	RSP := RSP - 8
	mem := mem with [RSP, el]:u64 <- 0x100000EDF
	call @_free with return %00000100
*)


let analyze_sub subs fname= 
	let sub : Sub.t = subs in
	Term.enum blk_t sub |> Seq.iter ~f:(fun blk ->
		let def_t = Term.enum def_t blk in
		let _= Seq.iter def_t ~f:(fun def ->
			let lhs = Def.lhs def in
			let rhs = Def.rhs def in
			match Var.name(lhs) with
			| "RAX" -> 
				let list = collect_exp_value rhs in
				let exp = List.nth list 2 in 
				if Option.is_some exp then
					rax_address := exp
			| "RBX" -> 
				let list = collect_exp_value rhs in
				let exp = List.nth list 2 in 
				if Option.is_some exp then
					rbx_address := exp
			| "R15" -> 
				let list = collect_exp_value rhs in
				let exp = List.nth list 2 in 
				if Option.is_some exp then
					r15_address := exp
			| "R12" -> 
				let list = collect_exp_value rhs in
				let exp = List.nth list 2 in 
				if Option.is_some exp then
					r12_address := exp
			| "RDI" -> 
				(match rhs with 
				| Var var ->
					let exp_value = Exp.to_string(rhs) in 
					if exp_value = "RAX" then
						rdi_address := !rax_address
					else if exp_value ="RBX" then
						rdi_address := !rbx_address
					else if exp_value ="R15" then
						rdi_address := !r15_address
					else if exp_value = "R12" then
						rdi_address := !r12_address
					else
						print_endline("unknown RDI right hand")
				| Load (exp1,exp2,endian,size) -> 
					let exp = Option.some exp2 in 
					if Option.is_some exp then
						rdi_address := exp
					else
						print_endline("RDI None")
				| _ -> print_endline("")
				)
				
			| "mem" -> 
				if !free_flag = 1 then
					let list = collect_exp_value rhs in
					let exp0 = List.nth list 0 in
					let exp3 = List.nth list 3 in
					if !rdi_address = exp3 && Exp.to_string(Option.value_exn exp0) = "0" then
						let _ = print_endline("Saved Pointer Free") in
						free_flag := 0
					else
						let _ = print_endline("Find Dangling Pointer in function: ") in
						let _ = print_endline(Sub.name sub) in
						free_flag := 0
			| _ ->
				if !free_flag = 1 then
					let _ = print_endline("Find Dangling Pointer in function: "^(Sub.name sub)) in
					free_flag := 0
				else 
					free_flag := 0
				) in 
		let jmp_t = Term.enum jmp_t blk in
		Seq.iter jmp_t ~f:(fun jmp ->
			let kind = Jmp.kind jmp in
			match kind with 
			| Call dst -> let call_dst = Call.target dst in 
				if Label.to_string(call_dst) = "@_kfree_addr" || Label.to_string(call_dst) = "@free" || Label.to_string(call_dst) = "@_rtfree_common" ||Label.to_string(call_dst) =  "@_m_freethen" then
					let _ = print_endline("find free function call start to check null"^ (Jmp.to_string jmp)) in
					free_flag := 1
			| _ -> free_flag := 0
		)
	
	)


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

let print_all_def sub = 
	Term.enum blk_t sub |> Seq.iter ~f:(fun blk ->
		Term.enum def_t blk |> Seq.iter ~f:(fun def ->
			print_endline(Def.to_string def)
		)
	)


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
	| Some sub ->
		let _ = print_endline("Find sub"^(Sub.name sub)) in
		let check_jmptable = check_sub_jmpt sub in
		(match check_jmptable with
		| Some realsub_name ->
			detect_fun realsub_name proj
		| _ -> 
			let _ = print_endline("Start to analyze sub") in
			let _ = analyze_sub sub fname in 
			()
		)
	| _ -> print_endline("No such sub")

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