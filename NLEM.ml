let MyLEM = 
	let q = mk_var ("q", bool_ty) in
	let x = mk_var ("x", bool_ty) in  
	let y = mk_var ("y", bool_ty) in  
	(* p0 T = T ; p0 F = F *)
	let p0 = `\b:bool. ((T /\ (b = T)) \/ ( (b = F)))` in 
	let sp0 = `@b:bool. ((T /\ (b = T)) \/ ( (b = F)))` in 
	let ep0 = `?b:bool. ((T /\ (b = T)) \/ ((b = F)))` in 
	(* p1 T = t ; p1 F = T *)
	let p1 = `\b:bool. ((t /\ (b = T)) \/ ( (b = F)))` in 
	let sp1 = `@b:bool. ((t /\ (b = T)) \/ ( (b = F)))` in 
	let ep1 = `?b:bool. ((t /\ (b = T)) \/ ( (b = F)))` in 
	(* p2 T = T ; p2 F = t *)
	let p2 = `\b:bool. ((T /\ (b = T)) \/ (t /\ (b = F)))` in 
	let sp2 = `@b:bool. ((T /\ (b = T)) \/ (t /\ (b = F)))` in 
	let ep2 = `?b:bool. ((T /\ (b = T)) \/ (t /\ (b = F)))` in 
		

 	(* first, branch 1*)

 	let p0_proof = prove (ep0, (EXISTS_TAC `T`) THEN ITAUT_TAC) in 

 	let p1_proof = prove (ep1, (EXISTS_TAC `F`) THEN ITAUT_TAC) in 

 	let p2_proof = prove (ep2, (EXISTS_TAC `T`) THEN ITAUT_TAC) in

 	let ROOT0 = SELECT_RULE p0_proof in 
 	(* let ROOT = ONCE_ASM_REWRITE_RULE [ITAUT `(T /\ (b <=> T) \/ T /\ (b <=> F)) = (T /\ (b <=> T) \/ (b <=> F))`] ROOT0 in  *)
 	let ROOT = ONCE_ASM_REWRITE_RULE [] ROOT0 in 
	(* let ROOT = PURE_ONCE_ASM_REWRITE_RULE[ITAUT `(A <=> T) <=> A`] ROOT in  *)


 	let L1 = SELECT_RULE p1_proof in 
 	(* let L' = ONCE_ASM_REWRITE_RULE  [] L1 in  *)
 	let L2 = PURE_ONCE_ASM_REWRITE_RULE[ITAUT `A /\ B \/ C <=> (A \/ C) /\ (B \/ C)`] L1  in 
 	let L3 = CONJUNCT2 L2 in 
 	let L = PURE_ASM_REWRITE_RULE[
 	 ITAUT `T /\ ((@b. t /\ (b <=> T) \/ (b <=> F)) <=> F) = ((@b. t /\ (b <=> T) \/  (b <=> F)) <=> F)` ] L3 in 


 	(* 
 	let L = PURE_ONCE_ASM_REWRITE_RULE[ITAUT `(T /\ A) <=> A`] L in 
	 |- (@b. t /\ (b <=> T) \/ T /\ (b <=> F)) \/ ((@b. t /\ (b <=> T) \/ T /\ (b <=> F)) <=> F)
	let L = PURE_ONCE_ASM_REWRITE_RULE[ITAUT `(( t /\ (b <=> T) \/  (b <=> F)) <=> T) = (( t /\ (b <=> T) \/ T /\ (b <=> F)) <=> T)` 
] L in 
 *)


 	(* then, branch 1.1*)
 	let sp1' = `@b:bool. ((t /\ (b = T)) \/ (b = F))`  in 
 	let LL0 = EQT_ELIM  (ASSUME ((mk_eq(sp1, `T`)))) in 
 	let LL1 = (AP_TERM p1 (EQT_INTRO LL0)) in 
 	let LL2 =  BETA_RULE LL1 in 
 	let LL3 = REWRITE_RULE [] LL2 in 
 	let LL4 = SELECT_CONV `t /\ (@b. t /\ b \/ ~b) \/ ~(@b. t /\ b \/ ~b)` in 
 	(*I think we can use CONV_RULE here *)
 	let LL5 = TRANS (SYM LL3) LL4 in 
 	let LL6 = EQ_MP (SYM LL5) (REWRITE_RULE [] p1_proof) in 
 	let LL = DISJ1 LL6 `~t:bool`  in 

 	(* then, branch 1.2*)
 	let p0'= `\b:bool. ((T /\ (b = T)) \/ ((b = F)))`  in 
 	let p1'= `\b:bool. ((t /\ (b = T)) \/ ( (b = F)))` in 
 	let LR0 = prove (mk_imp (`t:bool`, mk_eq (p0', p1')), 
 		DISCH_TAC THEN ASM_REWRITE_TAC [] ) in 
 	let LR1 = UNDISCH_ALL LR0 in 
 	let sp0' = `@b:bool. ((T /\ (b = T)) \/ ((b = F)))` in 
 	let LR2 = ADD_ASSUM (mk_eq(sp0', `T`)) LR1 in 
 	let sp1' = `@b:bool. ((t /\ (b = T)) \/ ( (b = F)))`  in 
 	let LR3 = ADD_ASSUM (mk_eq(sp1', `F`)) LR2 in 
 	let LR4 = AP_TERM `(@):(bool->bool)-> bool` LR3 in 
 	let LR5 = PURE_ASM_REWRITE_RULE [] LR4 in 
 	(* let LR6 = EQT_ELIM (SYM LR5) in  *)
 	let LR7 = DISCH `t:bool` LR5 in 
 	let LR = REWRITE_RULE [] (DISJ2 `t:bool` LR7)  in  

 	(* put the above two cases together *)

 	let l_proof = DISJ_CASES L LL LR in 

 	let R1 = SELECT_RULE p2_proof in 
 	let R' = ONCE_ASM_REWRITE_RULE  [] R1 in 
 	let R'' = PURE_ONCE_ASM_REWRITE_RULE[ITAUT `A \/ (B /\ C) <=> (A \/ B) /\ (A \/ C)`] R'  in 
 	let R = CONJUNCT2 R'' in 
 	let R =  PURE_ONCE_ASM_REWRITE_RULE[ ITAUT `~A = (A = F)`] R in 
	(*  |- (@b. t /\ (b <=> T) \/ T /\ (b <=> F)) \/ ((@b. t /\ (b <=> T) \/ T /\ (b <=> F)) <=> F) *)


	let RR0 = ASSUME (mk_eq (sp2, `F`)) in 
	let RR1 = AP_TERM p2 RR0  in 
	let RR2 = BETA_RULE RR1 in 
	let RR3 = REWRITE_RULE [] RR2 in 
	let RR4 = SELECT_CONV `(@b. b \/ t /\ ~b) \/ t /\ ~(@b. b \/ t /\ ~b)` in 
	let RR5 = TRANS (SYM RR3) RR4 in 
	let RR6 = EQ_MP (SYM RR5) (REWRITE_RULE [] p2_proof) in 
	let RR = DISJ1 RR6 `~t:bool` in  
		(* RR6 : thm = (@b. T /\ (b <=> T) \/ t /\ (b <=> F)) <=> F |- t *)

	let p0'= `\b:bool. ((T /\ (b = T)) \/ ((b = F)))`  in 
	let RL0 = prove (mk_imp (`t = T`, mk_eq (p0', p2)), 
		DISCH_TAC THEN ASM_REWRITE_TAC []
	) in 
	let RL1 = UNDISCH_ALL RL0 in
	let sp0' = `@b:bool. ((T /\ (b = T)) \/ ((b = F)))` in  
	let RL2 = ADD_ASSUM (mk_neg(sp0')) RL1 in 
	let RL3 = ADD_ASSUM (mk_eq(sp2, `T`)) RL2 in 
	let RL4 = AP_TERM `(@):(bool->bool)-> bool` RL3  in 
	let RL5 = PURE_ASM_REWRITE_RULE [] RL4 in 
	let RL6 = EQT_ELIM RL5 in 
	let RL7 = DISCH `t = T` RL6 in 
	let RL8 = prove (`((t <=> T) ==> F) <=> ~t`, ITAUT_TAC)  in 
	let RL9 = EQ_MP RL8 RL7 in 
	let RL = DISJ2 `t:bool` RL9  in 

	let r_proof = DISJ_CASES R RL RR in 

	DISJ_CASES ROOT l_proof r_proof ;;


(* ACCEPT_TAC : thm_tactic ????*)


(* a classical way to prove NNLEM *)
(* let doubleNegLEM = prove (`~ ~ (p \/ ~ p)`, ITAUT_TAC) *)

(*T <=> ~F*)
let T_EQ_NOTF =
	let thm1 = REFL `F` in 
	let (thm2, _) = EQ_IMP_RULE thm1 in 
	let thm3 = NOT_INTRO thm2 in 
	SYM (EQT_INTRO thm3) ;;

(*F  <=> ~ T*)



(* !p. ~p <=> ( p = F)*)
let NOT_EQF = 
	let thml1 = ASSUME `~ p` in 
	let thml2 = EQF_INTRO thml1 in 
	let thmr1 = ASSUME `p = F` in 
	let thmr2 = EQF_ELIM thmr1 in 
	GEN `p:bool `(DEDUCT_ANTISYM_RULE thmr2 thml2) ;;

(* !p. ~p <=> (p ==> F) *)
let NOT_IMPF = 
	(* ~p ==> (p ==> F) *)
	let th1 = ASSUME `~ p` in 
	let th2 = NOT_ELIM th1 in 
	(*one direction then another (p ==> F) ==> ~p *)
	let th1' = ASSUME `p ==> F` in 
	let th2' = NOT_INTRO th1' in 
	GEN `p:bool` (DEDUCT_ANTISYM_RULE th2' th2);;

let EQF_IMPF = 
	let th1 = SPEC `x:bool` NOT_EQF in 
	let th2 = SPEC `x:bool` NOT_IMPF in 
	GEN `x:bool` (TRANS (SYM th1)  th2);;

(* thm = F *)
(*----------*)
(* thm ==> F *)
let EQF_IMP_RULE_FIRST thm = 
	let th1, _ = EQ_IMP_RULE thm in 
	th1;;

let EQF_IMPF_RULE thm = 
	let l,r = dest_eq (concl thm) in 
	if r == `F` then failwith "EDF_IMPF_RULE: not F on the right"
	else EQF_IMP_RULE_FIRST thm ;;


(*introduce of double negation. note that this rewriting uses the ~~t = t.*)
let DOUBLE_NEG_INTRO = 
	let thm1 = SPEC `~ p` NOT_EQF in 
	let thm2 = ONCE_REWRITE_RULE [SPEC `x:bool` NOT_EQF] thm1 in 
	let thm3 = GEN `p:bool` thm2 in 
	fun thm' -> 
		let c = concl thm' in 
		let thm4 = SPEC c thm3 in 
		EQ_MP thm4 thm';;

(* it may fail. Be careful!!!!!!!!!! *)
let DOUBLE_NEG_ELIM = 
	let thm1 = SPEC `~ p` NOT_EQF in 
	let thm2 = ONCE_REWRITE_RULE [SPEC `x:bool` NOT_EQF] thm1 in 
	let thm3 = GEN `p:bool` (SYM thm2) in 
	fun thm' -> 
		let c = concl thm' in 
		let c = dest_neg(dest_neg c) in 
		let thm4 = SPEC c thm3 in 
		EQ_MP thm4 thm';;



(* intuitionistic proofs *)



(* Sigma + ~p |- p  *)
(* -----------------*)
(*         ~p  |- F*)

let CONTRA_POSITIVE thm = 
	let c = concl thm in 
	let neg_c = mk_neg c in 
	let th = ASSUME neg_c in 
	let th1 = NOT_ELIM th in 
	MP th1 thm ;;

(* Sigma + p |- ~ p  *)
(* -----------------*)
(*         p  |- F*)

let CONTRA_NEGATIVE thm =
	let c = concl thm in 
	let pos_c = dest_neg c in 
	let th = ASSUME pos_c in 
	let th1 = NOT_ELIM thm in 
	MP th1 th;;


(* a constructive way to prove NNLEM *)
(* We can simply do: let doubleNegLEM = prove (`~ ~ (p \/ ~ p)`, ITAUT_TAC) *)
(* |- (`~ ~ (p \/ ~ p)` *)
let NNLEM = 
	let th1 = ASSUME `p:bool` in 
	let th2 = ADD_ASSUM `~ (p \/ ~ p)` th1 in
	let th3 = DISJ1 th2 `~ p` in (* |-p \/ ~ p*)
	let th4 = CONTRA_POSITIVE th3 in 
	let th5 = DISCH `p:bool` th4  in 
	let th6 = NOT_INTRO th5 in 
	let th7 = DISJ2 `p:bool` th6 in 
	let th8 = CONTRA_POSITIVE th7 in 
	let th9 = DISCH `~(p \/ ~ p)` th8 in 
	let th10 = NOT_INTRO th9 in 
	GEN `p:bool` th10;;



(* prove p ==> ~~p *)
let P_IMP_NNP = 
	let thm1 = ASSUME `p:bool` in 
	let thm2 = ASSUME `p ==> F` in 
	let thm3 = MP thm2 thm1 in 
	let thm4 = DISCH `p ==> F` thm3 in 
	let thm5 = PURE_ONCE_REWRITE_RULE[SYM(SPEC `x ==> F` NOT_IMPF)] thm4 in 
	let thm6 = PURE_ONCE_REWRITE_RULE[SYM(SPEC `x:bool` NOT_IMPF)] thm5 in 
	DISCH `p:bool` thm6;;

(* p \/ ~p |- ~~p ==> p *)


(*   |- ~p*)
(*  p|- F*)
let NEG_UNDISCH_FALSE thm = 
	let th1 = NOT_ELIM thm in 
	UNDISCH th1  ;;

(* (!p. ~ ~p <=> p) <==> (!p. p \/ ~p) *)
(* We prove it in two steps *)

(* LEM_EQLEM : thm = !p (p \/ ~p) ==> !p(p <=> ~ ~p) *)

let LEM_EQLEM = 
	let th_imp =  (* (p \/ ~p) ==> !p(~~ p <=> p)  *)
		let L = 
			let th1 = ASSUME `p \/ ~ p` in 
			ADD_ASSUM `~ ~ p` th1 in 
		let M = 
			let th1 = ASSUME `p:bool` in 
			let th2 = ADD_ASSUM `~ ~ p` th1 in 
			ADD_ASSUM `p \/ ~ p` th2 in 
		let R =
			let th1 = ASSUME `~ ~ p` in 
			let th2 = NEG_UNDISCH_FALSE th1 in 
			let th3 = ADD_ASSUM `p \/ ~ p` th2  in 
			CONTR `p:bool` th3 in 
		let th1 = DISJ_CASES L M R in 
		let NNP_P = DISCH  `~ ~ p` th1 in 
		let P_NNP = P_IMP_NNP in 
		IMP_ANTISYM_RULE P_NNP NNP_P in  
	(* Oops, I forgot the universal quantifier *)
		let th1 =  ASSUME `!p. (p \/ ~ p)` in 
		let th2 = SPEC  `p:bool` th1 in 
		let th3 = PROVE_HYP th2  th_imp in 
	DISCH_ALL  (GEN `p:bool` (SYM th3)) ;;
	



(* thm =  !p(~ ~ p <=> p) |- !p (p \/ ~p) *)
let EQLEM_LEM = 
	let th1 = ASSUME `!p. (~ ~ p <=> p)` in
	let th2 = SPEC `p \/ ~p` th1 in 
	let th3 = EQ_MP th2 (SPEC `p:bool` NNLEM) in 
	DISCH_ALL (GEN `p:bool` th3) ;;

 (* thm = |- (!p. p \/ ~p) <=> (!p. ~ ~p <=> p) *)

let EQLEM_EQ_LEM = 
	IMP_ANTISYM_RULE LEM_EQLEM EQLEM_LEM;;



(* prove ~~p ==> p using Axiom of selection and extenionality *)
