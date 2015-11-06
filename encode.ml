



let rec encode_term term = 
  match term with 
  
  | Var (s, ty) as v-> v  
  | Const (s, ty) as c -> c
 (*  | `T` -> `T`
  | `F` -> `F`   *) 

  	(* keep \/ the same *)
  | Comb (Comb (con, l), r) -> 
	  begin
	  	let l' = encode_term l in 
	  	let r' = encode_term r in
	  	if con = `\/` then  
		  	mk_neg(mk_neg(mk_comb(mk_comb(`\/`, l'), r')))
	  	else if con = `/\` then 
	  	(* keep /\ the same *) 
	  		mk_comb(mk_comb(`/\`, l'), r')
	  	else if con = `==>` then  
	  	(* ==> encode only the rhs *)
		  	let r' = mk_neg(mk_neg(encode_term r)) in
	  		mk_comb (mk_comb(`==>`, l'), r') 
	  	(* in all other cases, no double neg introduced*)
	  	else mk_comb (mk_comb (con, l'), r') 
	  end
  | Comb (con, t)  ->
  	begin
	  	(*keep ~ the same*)
	  	(* let ty_neg = type_of `~` in 
	  	let ty_univ = type_of `(!)` in 
	  	let ty_exist = type_of `(?)` in   *)
	  	let ty = type_of con in  	
	  	match con with 
	  	|Const("~", ty) -> 
	  	let t' = encode_term t in 	
	  		mk_comb (con, t') 
	  	(* !x. A    !x.~~A*)
	  	| Const("!", ty) ->
	  		(* let () = Printf.printf "Universal quantifier" in   *)
	  		let (x, a) = dest_abs t in 
	  		let a' = encode_term a in 
	  		let a_nn = mk_neg(mk_neg(a')) in 
	  		mk_comb (con, mk_abs(x, a_nn))
		(* ?x. A    ~~ ?x.A*)
	  	| Const("?", ty) -> 
	  		let (x, a) = dest_abs t in
	  		let a' = encode_term a in 
	  		let cm = mk_comb (con, mk_abs(x, a')) in 
	  		mk_neg(mk_neg(cm))
	  	|_-> 
		 	let t' = encode_term t in 
		 	let () = print_term con in  
		 	mk_comb (con, t')
	 end
  | Abs (t1, t2) -> mk_abs(t1, t2);;



let rec encode_thm thm = 
	let h = hyp thm in 
	let c = concl thm in 
	let p = read_proof thm in 
	let h' = List.map encode_term h in 
	let c' = encode_term c in 
	let p' = 
	begin 
	match p with
	Axiom_proof
	| Lem_proof -> p
	| Refl_proof(term) -> let term' = encode_term term in Refl_proof(term')
	| Sym_proof (thm) -> let thm' = encode_thm thm in Sym_proof(thm') 
	| Trans_proof (thm1, thm2) -> let thm1' = encode_thm thm1 and thm2' = encode_thm thm2 in Trans_proof(thm1', thm2') 
	| Mk_comb_proof (thm1, thm2) -> let thm1' = encode_thm thm1 and thm2' = encode_thm thm2 in Mk_comb_proof (thm1', thm2')
	| Abs_proof (term, thm2) -> let term' = encode_term term and thm2' = encode_thm thm2 in Abs_proof (term', thm2')
	| Beta_conv_proof (term) -> let term' = encode_term term in Beta_conv_proof(term')
	| Assume_proof (term) -> let term' = encode_term term in Assume_proof(term') 
	| Eq_mp_proof (thm1, thm2) -> let thm1' = encode_thm thm1 and thm2' = encode_thm thm2 in Eq_mp_proof(thm1', thm2') 
	| Deduct_antisym_rule_proof (thm1, thm2) -> let thm1' = encode_thm thm1 and thm2' = encode_thm thm2 in 
		Deduct_antisym_rule_proof(thm1', thm2')
	| Prove_hyp_proof (thm1, thm2) -> let thm1' = encode_thm thm1 and thm2' = encode_thm thm2 in 
		Prove_hyp_proof (thm1', thm2')
	| Subst_proof ((a , tt_list) , thm) -> (*a is the type, won't change*)
		let tt_list' = 
		let tt_term_encode (t1, t2) = 
		(encode_term t1, encode_term t2) in 
		List.map tt_term_encode tt_list in 
		let thm' = encode_thm thm in
		Subst_proof ((a, tt_list'), thm')
	| New_basic_definition_proof(s)-> p
	| New_basic_type_definition_proof (s,t) -> p
	| Define_const_list_proof(s) -> p
	| Mp_proof (thm1, thm2) -> let thm1' = encode_thm thm1 and thm2' = encode_thm thm2 in Mp_proof(thm1', thm2') 
	| Disch_proof(term, thm) -> let term' = encode_term term and thm' = encode_thm thm in Disch_proof(term', thm') 
	| Gen_proof (term, thm) -> let term' = encode_term term and thm' = encode_thm thm in Gen_proof(term', thm')
	| Spec_proof (term, thm) -> let term' = encode_term term and thm' = encode_thm thm in Spec_proof(term', thm')
	|_-> failwith "encode thm failed"
end in 
	(construct_thm h' c' p');;

(* encode_term `!p:bool. (p \/ ~ p)`;; *)