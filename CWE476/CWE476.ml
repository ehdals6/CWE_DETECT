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
let temp_bool : bool ref = ref true;;
let temp_bool_t : bool ref = ref true;;

let parent_exp : Bil.exp Option.t ref = ref None;;
let trace_rhs_rhs : Bil.exp Option.t ref = ref None;;

let rdx_val : Bil.exp Option.t ref = ref None;;
let new_track : Bil.exp Option.t ref = ref None;;
let max_val : int ref = ref 0;;
let min_val : int ref = ref 0;;
let int32_max : int ref = ref 2147483647;;
let int32_min : int ref = ref (-2147483648);;
let enter_name : string ref = ref "";;

let real_sub_name : string ref = ref "";;

let trace_reg : Bil.exp Option.t ref = ref None;;
let trace_reg_pos : Def.t Option.t ref = ref None;;
let trace_reg_long : Bil.exp Option.t ref = ref None;;
let trace_mem_exp : int ref = ref 0;;
let trace_terminate : bool ref = ref false;;
let diif_flag :bool ref = ref false;;

let trace_rhs : Bil.exp Option.t ref = ref None;;
let trace_rhs_rhs : Bil.exp Option.t ref = ref None;;
let trace_sub : Sub.t Option.t ref = ref None;;
let backtrack_pos : Def.t Option.t ref = ref None;;
let new_track : Bil.exp Option.t ref = ref None;;
let track_temp_int : int ref = ref 0;;
let trace_blk_pos : Blk.t Option.t ref = ref None;;
let parent_exp : Bil.exp Option.t ref = ref None;;
let parent_pos : Def.t Option.t ref = ref None;;
let temp_bool_parent : bool ref = ref true;;
let if_lhs : Bil.var Option.t ref = ref None;;
let if_flag_int : int ref = ref 0;;
let if_reg : Bil.exp Option.t ref = ref None;;
let if_def : Def.t Option.t ref = ref None;;
let if_retn_reg : Bil.exp Option.t ref = ref None;;
let if_varient : Bil.exp Option.t ref = ref None;;
let if_temp : Bil.exp Option.t ref = ref None;;
let temp_index : int ref = ref 0;;



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


let rec parse exp = 
	let temp : Bil.exp = exp in
	match temp with
	| Load (exp1,exp2,endian,size) -> Option.some exp2
	| Store (exp1,exp2,exp3,endian,size) -> Option.some exp2
	| Cast (cast,int,exp) -> parse exp
	| BinOp (binop,exp1,exp2) -> Option.some exp1 
	| UnOp (unop,exp)-> None
	| Var var -> Option.some temp
	| Int word -> Option.some temp
	| Concat (exp1,exp2) -> Option.some exp1
	| _ -> None



let rec trace_reg_from_exp exp = 
	let temp : Bil.exp = exp in
	match temp with
	| Load (exp1,exp2,endian,size) -> trace_reg_from_exp exp2
	| Store (exp1,exp2,exp3,endian,size) -> 
		if Exp.to_string exp3 = "RAX" then
			let _ = printf "find some RAX from function call, we consider RAx may be zero\n"in
			None
		else
			trace_reg_from_exp exp3
	| Cast (cast,int,exp1) -> trace_reg_from_exp exp1
	| Var var -> Option.some temp
	| BinOp (binop,exp1,exp2) -> Option.some exp1
	| Int word -> Option.some temp
	| _ -> None




let check_rhs_store rhs name : bool =
	let temp : Bil.exp = rhs in
	match temp with
	| Store (exp1,exp2,exp3,endian,size) ->
		if Exp.to_string(exp2) = name then
			begin
				printf "find the mem with instruction [ %a ]" Exp.ppo exp2;
				printf "in %a \n" Exp.ppo temp;
				trace_rhs_rhs:= Option.some exp3;
				true
			end
		else
			false
	| _ -> false


let rec trace_exp_value sub exp pos regflag =
	let _ = temp_bool:= false in
	let _ = trace_rhs := None in
	let _ = backtrack_pos := None in 
	let _ = printf "---------[%a]:\n BACKTRACK: Data flow analyzing----------\n" Exp.ppo exp in
	let _ = track_temp_int:= -9999 in
	match regflag with 
	| true ->
		
		let _ = temp_int:= 0 in
		let blk_e = Term.enum blk_t sub in
		Seq.iter blk_e ~f:(fun blk ->
			let def_e = Term.enum def_t blk in
			Seq.iter def_e ~f:(fun def ->
				
				let rhs = Def.rhs def in
				let lhs = Def.lhs def in
				if (check_rhs_store rhs (Exp.to_string(exp))) && Tid.(>) (Term.tid pos) (Term.tid def) then 
					let _ = temp_int:= !temp_int + 1 in
					let _ = trace_rhs := !trace_rhs_rhs in 
					let _ = backtrack_pos := Option.some def in
					printf "Exist store mem with [%a]\n" Def.ppo def
				else if Exp.to_string(exp) = Var.name lhs && Tid.(>) (Term.tid pos) (Term.tid def) then 
					let _ = temp_int:= !temp_int + 1 in
					let _ = trace_rhs := Option.some rhs in 
					let _ = backtrack_pos := Option.some def in
					printf "Exist %a = ****** \n" Def.ppo def
				else if Tid.(=) (Term.tid pos) (Term.tid def) then 
					let _ = printf "Back to instruction\n" in
					if !temp_int = 0 then
						begin
							print_endline("Register value is zero\n");
							track_temp_int:= 0
						end
					else
						begin
							track_temp_int:= trace_exp_value sub (Option.value_exn !trace_rhs) (Option.value_exn !backtrack_pos) false;
							printf "Found value is %d\n" !track_temp_int
						end
						
				else
					()
				)(*def*)
		); (*blk*)
		!track_temp_int
	| false->
		
		let temp : Bil.exp = exp in
		match temp with 
		| Load (exp1,exp2,endian,size) -> 
			if Exp.to_string(exp1) = "RBP" then
					begin
						printf "LOAD RBP case \n";
						printf "exp1 is %a\n" Exp.ppo exp1;
						printf "exp2 is %a\n" Exp.ppo exp2;
						trace_exp_value sub temp pos true
					end
				else
					begin
						printf "LOAD No RBP case \n";
						printf "exp1 is %a\n" Exp.ppo exp1;
						printf "exp2 is %a\n" Exp.ppo exp2;
						trace_exp_value sub exp2 pos false
					end
		| Store (exp1,exp2,exp3,endian,size) -> 
			let _ = printf "Gointo Store " in
			trace_exp_value sub exp3 pos false
		| Int word -> int_of_string(Exp.to_string temp)
		| Var var -> trace_exp_value sub temp pos true
		| Cast (cast,int,exp0) -> trace_exp_value sub exp0 pos regflag
		| BinOp (binop,exp1,exp2) -> (match binop with
			| PLUS -> 
				printf "PLUS case \n";
				if Exp.to_string(exp1) = "RBP" then
					begin
						printf "PLUS RBP case \n";
						printf "exp1 is %a\n" Exp.ppo exp1;
						printf "exp2 is %a\n" Exp.ppo exp2;
						(trace_exp_value sub temp pos true)
					end
				else
					begin
						printf "PLUS No RBP case \n";
						printf "exp1 is %a\n" Exp.ppo exp1;
						printf "exp2 is %a\n" Exp.ppo exp2;
						(trace_exp_value sub exp2 pos false) + (trace_exp_value sub exp1 pos false)	
					end
					
			| MINUS -> printf "MINUS case \n";
				(trace_exp_value sub exp1 pos false) - (trace_exp_value sub exp2 pos false)
			| _ -> 0)
		| _ -> 0
	

let check_target_exception exp : bool= 
	let t_exp : Bil.exp = exp in
	Exp.to_string t_exp = "RBP" || Exp.to_string t_exp ="FS_BASE" || Exp.to_string t_exp ="RSP"
 
let detect_int exp = 
	let temp : Bil.exp = exp in
	match temp with
		| Int word -> true
		| _ -> false


let rec parse_derec exp def = 
	let temp : Bil.exp = exp in
	let _ = trace_terminate := false in
	let _ = trace_mem_exp := 0 in
	let _ = trace_reg_pos:= Option.some def in
	match temp with
		| Load (exp1,exp2,endian,size) ->
			let _ = trace_reg_long:= Option.some exp2 in
			let _ = trace_mem_exp := 1 in
			let reg_re = trace_reg_from_exp exp2 in
			if reg_re = None then
				begin
					printf "Trace reg from exp return None\n";
					false
				end
			else
				let reg = Option.value_exn (reg_re) in
				if check_target_exception reg then 
					begin
						print_endline("In safe white list\n");
						trace_reg_pos:= Option.some def;
						trace_reg:= Option.some reg;
						false
					end
				else
					begin
						print_endline("Not in Safe list, Danger!\n");
						trace_reg_pos:= Option.some def;
						trace_reg:= Option.some reg;
						true
					end
		| Cast (cast,int,exp1) -> parse_derec exp1 def
		| BinOp (binop,exp1,exp2) -> 
			let _ = trace_mem_exp := 2 in
			let _ = trace_reg_long:= Option.some temp in
			let _ = print_endline("Start to trace BinaryOP")in
			parse_derec exp1 def
		| Store (exp1,exp2,exp3,endian,size) -> 
			if detect_int exp3 then 
				let _ = trace_mem_exp := 4 in
				let _ = print_endline("Meet int in store stop!")in
				let _ = printf "Int is %a \n" Exp.ppo exp3 in
				let _ = trace_terminate := true in
				false
			else
				let _ = trace_mem_exp := 3 in
				let _ = trace_reg_long:= Option.some exp3 in
				let _ = print_endline("Start to trace store")in
				false
		| Int word -> 
			let _ = trace_mem_exp := 4 in
			let _ = trace_reg_long:= Option.some temp in
			let _ = print_endline("Meet int stop")in
			let _ = printf "Int is %a \n" Exp.ppo temp in
			let _ = trace_terminate := true in
			false

		| _ -> false

(*	= mem[RBX + 0x10, el] *)
let find_deref def blk sub = 
	let rhs = Def.rhs def in
	let temp : Bil.exp = rhs in
	parse_derec temp def





let find_goto_caller sub exp pos blk_tid: bool = 
	let _ = printf "--------- Start check security check pattern in or not ---------\n" in
	let _ = printf "--------- Check verify [%a] or not ----------\n" Exp.ppo exp in
	let _ = temp_bool_blk:= false in
	let blk_e = Term.enum blk_t sub in
	let _ = Seq.iter blk_e ~f:(fun blk ->
		let jmp_e = Term.enum jmp_t blk in
		let _ = Seq.find jmp_e ~f:(fun jmp ->
			let kind = Jmp.kind jmp in
			match kind with
			| Call _ | Int _ | Ret _ -> false
			| Goto label -> 
				(match label with
					| Indirect _ -> false
					| Direct tid ->
						let dst_str = Tid.name tid in
						let _ = printf "tis is %s\n" dst_str in
						if dst_str = blk_tid then
							begin
								let temp : Blk.t = blk in
								let _ = printf "matched tis is %s\n" (Tid.name (Term.tid temp)) in
								let _ = temp_bool_blk:= !temp_bool_blk||true in
								trace_blk_pos:= Option.some temp;
								true;
							end
						else
							false
				)
		)in
		print_endline("search finish")
	) in(*blk*)
	!temp_bool_blk





let check_rxx_exist blk reg_exp : bool = 
	let _ = temp_bool_blk:= false in
	let temp : Blk.t = blk in
	let rxx : Bil.exp = reg_exp in
	let defs = Term.enum def_t temp in
	let _ = Seq.find defs ~f:(fun def ->
		let rhs = Def.rhs def in
		let lhs = Def.lhs def in
		if Exp.to_string rhs = Exp.to_string rxx then
			let _ = temp_bool_blk:= true in
			let _ = if_lhs:= Option.some lhs in
			true
		else
			false
	) in 
	!temp_bool_blk




let rec striped_exp exp = 
	let temp : Bil.exp = exp in
	match temp with
		| Cast (cast,int,exp1) -> striped_exp exp1
		| _ -> temp

let rec check_parent exp pos blk : bool = 
	let temp : Blk.t = blk in
	let exp_t :Bil.exp = exp in
	let def_s : Def.t = pos in
	let _ = printf "input exp is [%a]  [IN]\n" Exp.ppo exp_t in
	let _ = temp_bool_parent:= false in
	let defs = Term.enum def_t temp in 
	let _ = Seq.iter defs ~f:(fun def ->
		let rhs = Def.rhs def in
		let lhs = Def.lhs def in
		if Exp.to_string(exp_t) = Var.name lhs && Tid.(>) (Term.tid pos) (Term.tid def) then 
			let _ = print_endline("find parent assignment case \n") in
			let _ = printf "parent is def [%a]\n" Def.ppo def in
			let _ = parent_exp := Option.some rhs in
			let _ = temp_index := 2 in
			let _ = parent_pos := Option.some def in
			temp_bool_parent:= !temp_bool_parent || true
		else if (check_rhs_store rhs (Exp.to_string(exp_t))) && Tid.(>) (Term.tid pos) (Term.tid def) then 
			let _ = print_endline("find parent store case \n") in
			let _ = printf "parent is def [%a]\n" Def.ppo def in
			let _ = printf "at possition [%s]\n" (Tid.name (Term.tid def)) in
			let _ = parent_exp := Option.some rhs in
			let _ = temp_index := 1 in
			let _ = parent_pos := Option.some def in
			temp_bool_parent:= !temp_bool_parent || true
		else
			temp_bool_parent:= !temp_bool_parent || false
	) in
	if !temp_bool_parent then
		let _ = parse_derec (Option.value_exn !parent_exp) (Option.value_exn !parent_pos)  in
		if !trace_reg_long <> None then 
			let input_exp = striped_exp (Option.value_exn !trace_reg_long) in
			if !trace_terminate then 
				let _ = printf "Meet INT Stop \n" in
				let _ = diif_flag := true in
				true
			else
				check_parent input_exp (Option.value_exn !parent_pos) temp
		else
			let _ = printf "expression long None \n"in
			let _ = diif_flag := false in
			false	
	else
		let _ = printf "not parent any more\n"in
		let rhss = Def.rhs def_s in
		let _ = parent_exp :=  Option.some rhss in
		let _ = parent_pos :=  Option.some def_s in
		let _ = printf "parent_exp is : [%a]\n" Exp.ppo rhss in
		let _ = diif_flag := false in
		false


let check_when_cond blk reg : bool = 
	let jmp_e = Term.enum jmp_t blk in
	let _ = Seq.iter jmp_e ~f:(fun jmp ->
		let cond = Jmp.cond jmp in
		print_endline("jmp Condition is "^Exp.to_string cond)
	) in 
	true
	



let get_binop_type binop = 
	let temp : Bil.binop = binop in
	match temp with
	| PLUS -> "PLUS"
	| MINUS -> "MINUS"
	| TIMES -> "TIMES"
	| DIVIDE -> "DIVIDE"
	| SDIVIDE -> "SDIVIDE"
	| MOD -> "MOD"
	| SMOD -> "SMOD"
	| LSHIFT -> "LSHIFT"
	| RSHIFT -> "RSHIFT"
	| ARSHIFT -> "ARSHIFT"
	| AND -> "AND"
	| OR -> "OR"
	| XOR -> "XOR"
	| EQ -> "EQ"
	| NEQ -> "NEQ"
	| LT -> "LT"	
	| LE -> "LE"	
	| SLT -> "SLT"	
	| SLE -> "SLE"



let check_var_or_reg exp : bool = 
	let temp : Bil.exp = exp in
	let ttemp = Exp.to_string temp in
	match ttemp with
	|"RDI" |"RSI"|"RDX"|"RCX"|"R8" |"R9" |"RAX"|"RBX"|"RSP"|"RBP"|"R10"|"R11"|"R12"|"R13"|"R14"|"R15" -> 
		if_reg:= Option.some temp;
		true
	| _ -> false




let rec check_flag exp = 
	let temp : Bil.exp = exp in
	let _ = if_flag_int := 0 in
	match temp with 
	| Load (exp1,exp2,endian,size) -> 
		let _ = printf "I am Load \n" in
		let _ = if_flag_int := 0 in
		Option.some temp

	| Cast (cast,int,exp1) -> 
		let _ = printf "I am Cast \n" in
		check_flag exp1

	| Var var -> 
		if (check_var_or_reg temp) then
			let _ = printf "---- I am RXX style \n" in
			let _ = if_flag_int := 2 in
			Option.some temp
		else
			let _ = print_endline("in #9999 case ") in
			let _ = if_flag_int:= 1 in
			Option.some temp

	| _ -> 
		let _ = if_flag_int := 99 in
		let _ = printf "Other case\n" in
		None



let trace_if_var exp def blk = 
	let texp : Bil.exp = exp in
	let tdef : Def.t = def in
	let tblk : Blk.t = blk in
	let def_e = Term.enum def_t tblk in
	let _ = Seq.iter def_e ~f:(fun def ->
		let rhs = Def.rhs def in
		let lhs = Def.lhs def in
		if Exp.to_string (texp) = Var.name lhs && Tid.(>) (Term.tid tdef) (Term.tid def) then 
			begin
				print_endline("get the matched var def");
				if_temp:= Option.some rhs;
			end
	)in
	let result = !if_temp in
	match result with
	| None -> None
	| Some exp ->
		result



let check_exp_type exp = 
	let temp : Bil.exp = exp in
	match temp with 
	| Load (exp1,exp2,endian,size) -> printf "I am Load \n";None
	| Store (exp1,exp2,exp3,endian,size) -> printf "I am Store \n";None
	| Cast (cast,int,exp1) -> printf "I am cast \n";None
	| BinOp (binop,exp1,exp2) -> None
	| UnOp (unop,exp1)-> printf "I am Unop \n";Option.some exp1
	| Var var -> printf "I am Var \n";Option.some temp
	| Int word -> printf "I am Int \n";None
	| Let (var,exp1,exp2) -> printf "I am Let \n";None
	| Ite (exp1,exp2,exp3) -> printf "I am Ite, IF then else \n";None
	| Concat (exp1,exp2) -> printf "I am Concat \n";None
	| Unknown (string,typ) -> printf "I am Unknown type \n";None
	| _ -> printf "Other case\n";None


let analyze_zf tdef blk = 
	let ttdef : Def.t = tdef in 
	let tblk :Blk.t = blk in
	let rhs = Def.rhs ttdef in
	match rhs with
	| BinOp (binop,exp1,exp2) -> 
		let result = check_flag exp2 in
		(match result with
		| None -> 
			let _ = print_endline("Return None") in
			None
		| Some exp ->
			if !if_flag_int = 0 then 
				Option.some exp
			else if !if_flag_int = 1 then 
				trace_if_var exp ttdef tblk
			else if !if_flag_int = 2 then
				Option.some exp
			else
				None)
	| _ -> None
	

let analyze_cf tdef blk = 
	None

let analyze_sf tdef blk = 
	None

let analyze_pf tdef blk = 
	None


let analyze_def tdef blk = 
	let tblk : Blk.t = blk in
	let ttdef : Def.t = tdef in
	let lhs = Def.lhs ttdef in
	if Var.name lhs = "ZF" then
		let _ = print_endline("Trace ZF case")in 
		let result = analyze_zf ttdef tblk in
		let _ = if_retn_reg:= result in
		let _ = print_endline("Finish Trace ZF case") in
		match result with
		|None -> print_endline("return None")
		|Some exp -> 
			print_endline("get the exp : "^Exp.to_string exp)
		
	else if Var.name lhs = "CF" then
		let _ = print_endline("Trace CF case") in
		let result = analyze_cf ttdef tblk in
		let _ = if_retn_reg:= result in
		print_endline("Finish Trace CF case")
	else if Var.name lhs = "SF" then
		let _ = print_endline("Trace SF case") in
		let result = analyze_sf ttdef tblk in
		let _ = if_retn_reg:= result in
		print_endline("Finish Trace SF case")
	else if Var.name lhs = "PF" then
		let _ = print_endline("Trace PF case") in
		let result = analyze_pf ttdef tblk in
		let _ = if_retn_reg:= result in
		print_endline("Finish Trace PF case")
	else 
		print_endline("Trace unknow case")


let check_if_def def = 
	match def with 
	| None -> print_endline("if_def is none")
	| Some defi -> printf "if def value is %a\n" Def.ppo defi

let check_cond cond_exp  blk = 
	let target = check_exp_type cond_exp in
	match target with 
	| None -> print_endline("can not handle pattern")
	| Some exp ->
		let ctar = ( match exp with 
		| Var var -> (Var.name var)
		| _ -> ""
		) in
		let _ = printf "collect the return condition exp %a\n" Exp.ppo (Option.value_exn target) in
		let def_e = Term.enum def_t blk in
		let _ = Seq.iter def_e ~f:(fun def ->
			let lhs = Def.lhs def in
			if Var.name lhs = ctar then
				let _ = if_def := Option.some def in
				let _ = print_endline("find match") in
				check_if_def !if_def
			else
				let _ = print_endline("No match") in
				check_if_def !if_def
		)in
		(match !if_def with
		| None -> 
			printf "can not find the Def \n"
		| Some def2 -> 
			let _ = printf "find the Def %a\nThen Start to analyze each def\n" Def.ppo def2 in
			let _ = analyze_def def2 blk in
			let return_value = !if_retn_reg in
			(match return_value with 
				|None -> print_endline("return None")
				|Some exp -> 
					print_endline("get the exp : "^Exp.to_string exp)
				)
			)



let detect_security_check blk =
	let blk_e : Blk.t = blk in
	let jmp_e = Term.enum jmp_t blk_e in
	let _ = Seq.iter jmp_e ~f:(fun jmp ->
			let cond = Jmp.cond jmp in
			let _ = print_endline("jmp Condition is "^ Exp.to_string cond) in
			if (Exp.to_string cond) = "1" then
				print_endline("jmp condition is 1 ignore")
			else
				let _ = print_endline("jmp condition is an expression analyze") in
				let _ = check_cond cond blk_e in
				let _ = printf "Checked Value is %a\n" Exp.ppo (Option.value_exn !if_retn_reg) in
				print_endline("finish check!!!! \n")
		) in
	let _ = print_endline("analyze finish\n") in
	!if_retn_reg
	

let check_if_exist sub exp pos blk : bool = 
	let rxx : Bil.exp = exp in
	let reg_re = trace_reg_from_exp rxx in
	if reg_re = None then
		begin
			printf "Trace reg from exp return None\n";
			false
		end
	else
		let reg_rere = Option.value_exn reg_re in
		let blk_tid : Blk.t = blk in
		let _ = printf " start to search if this is #11 = rxx[%a]\n" Exp.ppo reg_rere in
		let _ = check_parent reg_rere pos blk in
		if !diif_flag then 
			false	
		else
			let target = !parent_exp in
			(match target with
			| None ->
				let _ = print_endline("can not get the compare target it is none") in
				false
			| Some target_exp ->
				let _ = printf "print target is %a \n" Exp.ppo target_exp in
				let _ = printf "Check white list again\n" in
				let reg_t = trace_reg_from_exp target_exp in
				if reg_t = None then
					let _ = print_endline("can not trace the target register") in
					false
				else
					let reg_target = target_exp in
					let result_caller = find_goto_caller sub reg_target pos (Tid.name (Term.tid blk_tid)) in
					if result_caller then
						let _ = printf "start to search block %s " (Tid.name (Term.tid (Option.value_exn !trace_blk_pos)))in
						let _ = printf "with register %a \n" Exp.ppo reg_target in (*mem[RDO + 0x14]*)
						let blk_target = (Option.value_exn !trace_blk_pos) in
						let check_exp = detect_security_check blk_target in
							(match check_exp with
							| None -> 
								let _ = print_endline("Bad, can not get if target in target block") in
								false
							| Some exp2 ->
								let _ = printf "Get the security check target : %a\nThen compare with null target\n" Exp.ppo exp2 in
								if Exp.to_string(reg_target) = Exp.to_string(exp2) then
									let _ = printf "Good ---- Null pointer target [%a] found check null pattern [%a]" Exp.ppo reg_target Exp.ppo exp2 in
									let _ = printf "in Block [%s] !!!!----\n"(Tid.name (Term.tid (Option.value_exn !trace_blk_pos))) in
									true
								else
									let _ = print_endline("target differnt with security check") in
									false
							)
					else
						let _ = print_endline("can not find the caller block")in
						false
			)


let analyze_blk blk sub : bool = 
	let def_e = Term.enum def_t blk in
	Seq.iter def_e ~f:(fun def ->
		let _ = printf "\n\nDEF :: %a\n" Def.ppo def in
		let result = find_deref def blk sub in 
		if result then 
			let _ = printf "Found dereference :: %a\n" Exp.ppo (Option.value_exn !trace_reg) in
			let return_value = trace_exp_value sub (Option.value_exn !trace_reg) def true in
			if return_value < 0 then
				printf "[Return Value] Error happend errorcode: [%d] in\n[%a]\n" return_value Def.ppo def
			else if return_value = 0 then
				begin
					printf "\n\n\n May be dangerous !!!! : [Return Value][%d] in \n[%a]\nCheck where if exist\n" return_value Def.ppo def;
					let temp : Blk.t = blk in
					let name = Tid.name (Term.tid temp) in
					printf "Block Tid is [%s]\n" name;
					if check_if_exist sub (Option.value_exn !trace_reg_long) def temp then
						let _ = printf "null pointer check pattern exist, Safe! \n" in
						let _ = temp_bool_t:= false in
						let r_blk = Option.value_exn !trace_blk_pos in
						let r_name = Tid.name(Term.tid r_blk) in
						printf "get the caller block Tid is [%s]\n" r_name 
					else
						let _ = printf "No null pointer check pattern exist, Unsafe! \n"in
						let _ = temp_bool_t:= true in
						printf "[%d] Null Deference in \n[%a]" return_value Def.ppo def
				end
				
			else
				let _ = temp_bool_t:= false in
				printf "[Return Value]Traced dereference value is : [%d] in \n[%a]\n" return_value Def.ppo def
		else
			let _ = temp_bool_t:= false in
			printf "not dereference \n"
	);
	!temp_bool_t


(*
	Here start to analyze sub, 
	this case null pointer dereference.
	check every blk in subroutine 
	if exsit then analyze more
*)
let analyze_sub sub = 
	let blk_e = Term.enum blk_t sub in
	Seq.iter blk_e ~f:(fun blk ->
		let result = analyze_blk blk sub in
		if result then
			print_endline("detected nullpointer dereference in this subroutine")

		else
			print_endline("safe subroutine")
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