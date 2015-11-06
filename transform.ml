open Printf

(* this file is used to detect if we can find LEM_proof through rewriting using ~~p = p *)




(* 
let add_LEM_hyp thm = 
	let h = hyp thm in 
	let c = concl thm in 
	let p = read_proof thm in 
	let l = concl EXCLUDED_MIDDLE in 
	construct_thm (l::h) c p
 *)

(* let x = ref 0;; *)
(*)
let rec detect_add_LEM thm =
	(* let () = print_int !x in *)
	(* x := (!x +1);  *)
	let p = read_proof thm in 
	match p with 
	| Lem_proof -> (true, ASSUME (concl EXCLUDED_MIDDLE))
	| Refl_proof (_) | Beta_conv_proof (_) | Assume_proof (_) | Define_const_list_proof (_)
	| New_basic_definition_proof (_) | New_basic_type_definition_proof (_) | Axiom_proof -> 
	(false, thm)
	| Sym_proof(t1)  
	    -> let (b, t1') = detect_add_LEM (t1) in 
	    let thm = SYM t1' in 
	    (* let () = replace_proof thm (Sym_proof(t1')) in  *)
	    	(b, thm) 
	| Trans_proof(t1, t2) -> 
		let ((b1, t1'), (b2, t2')) = ((detect_add_LEM t1),(detect_add_LEM t2)) in 
		let thm = TRANS t1' t2' in 
		(* let () = replace_proof thm (Trans_proof(t1', t2')) in  *)
	 		((b1 or b2), thm)

	| Mk_comb_proof (t1, t2) ->
		let ((b1, t1'), (b2, t2')) = ((detect_add_LEM t1),(detect_add_LEM t2)) in 
		let thm = MK_COMB (t1', t2') in 
		(* let () = replace_proof thm (Mk_comb_proof(t1', t2')) in  *)
	 		((b1 or b2), thm)

	| Eq_mp_proof(t1, t2) ->
		let ((b1, t1'), (b2, t2')) = ((detect_add_LEM t1),(detect_add_LEM t2)) in 
		let thm = EQ_MP t1' t2' in 
		(* let () = replace_proof thm (Eq_mp_proof(t1', t2')) in  *)
	 	((b1 or b2), thm)

	| Deduct_antisym_rule_proof(t1 , t2)->
		let ((b1, t1'), (b2, t2')) = ((detect_add_LEM t1),(detect_add_LEM t2)) in 
		let thm = DEDUCT_ANTISYM_RULE t1' t2' in 
		(* let () = replace_proof thm (Deduct_antisym_rule_proof(t1', t2')) in  *)
	 	((b1 or b2), thm) 

	| Prove_hyp_proof(t1, t2) ->
	let ((b1, t1'), (b2, t2')) = ((detect_add_LEM t1),(detect_add_LEM t2)) in 
		let thm = PROVE_HYP t1' t2' in 
		(* let () = replace_proof thm (Prove_hyp_proof(t1', t2')) in  *)
	 	((b1 or b2), thm)

	| Mp_proof(t1, t2) ->
	let ((b1, t1'), (b2, t2')) = ((detect_add_LEM t1),(detect_add_LEM t2)) in 
		let thm = MP t1' t2' in 
		(* let () = replace_proof thm (Mp_proof(t1', t2')) in  *)
	 	((b1 or b2), thm)
	 	(* the following are of patterm (term * thm) *)
	| Abs_proof(term1, t1) ->
	let (b1, t1') = detect_add_LEM t1 in 
		let thm = ABS term1 t1' in 
		(* let () = replace_proof thm (Abs_proof(term1, t1')) in  *)
		(b1, thm)

	| Disch_proof (term1, t1) ->
	let (b1, t1') = detect_add_LEM t1 in 
		let thm = DISCH term1 t1' in 
		(* let () = replace_proof thm (Disch_proof(term1, t1')) in  *)
		(b1, thm)

	| Gen_proof (term1, t1) ->
	let (b1, t1') = detect_add_LEM t1 in 
		let thm = GEN term1 t1' in 
		(* let () = replace_proof thm (Disch_proof(term1, t1')) in  *)
		(b1, thm)

	| Spec_proof (term1 ,t1) ->
	let (b1, t1') = detect_add_LEM t1 in 
		let thm = SPEC term1 t1' in 
		(* let () = replace_proof thm (Spec_proof(term1, t1')) in  *)
		(b1, thm)

	|Subst_proof(l, t1) 
		-> let (b1, t1') = detect_add_LEM t1 in 
		let thm = 
			let (a, b) = l in 
				if List.length a == 0 then 
					INST b t1'
				else INST_TYPE a t1' in 
		(* let () = replace_proof thm (Subst_proof(l, t1')) in  *)
		(b1, thm);;
*)

(* result list *)
(* 1:bool used LEM or not *)
(* 2:bool after adding LEM, is LEM still in hyp list *)
(* if 2 is true then return the constructive thm *)
(*)
let transform thm  = 
	let (b, thm') = detect_add_LEM (thm) in 
	if b && (List.length (hyp thm') == List.length (hyp thm) + 1) then 
		let thm' = DISCH (concl EXCLUDED_MIDDLE) thm' in 
		(true, false, thm')
	else if b then (true, true, thm')
	else (false, false, thm')  ;;
*)

(* 
let load_proofs filename = 
	let all = import_article filename in 
	snd all ;;
 *)

let all_exported = Export.list_the_exported_thms ();;



let count_lem_thm all = 
	let count x (t,f) = 
		if x == true then (t +1,f) 
		else (t, f+1) 
		in 

	let thms = List.map detect_LEM all in 
	List.fold_right count thms (0, 0) ;;

(*
get_statistics_thm all;;
*)


let all_hol = snd (List.split (search []));;
(* same list from the following command *)
(* let thm_pair = search [];; *)


(*
get_statistics_thm all;;
*)

(*)

let get_gilbert_statistics_thm all = 
	let count (_,x,_) (t,f) = 
		if x == true then (t +1,f) 
		else (t, f+1) 
		in 

	let thms = List.map transform all in 
	List.fold_right count thms (0, 0) ;;


	get_statistics_thm all;;
	(* get_gilbert_statistics_thm all;; *)

	*)




let all' = first_10 all_hol;;

(* List.map get_operator all';;
List.map get_axiom all';;
 *)





let th1 = 
	let t1 = REFL `p:bool` in
	let t2 = ASSUME `p:bool = q` in 
	TRANS t1 t2;;


(* get_statistics_size all';; *)
(* get_statistics_size (first_100 all_hol);; *)
(* count_lem_thm (first_100 all_hol);; *)

