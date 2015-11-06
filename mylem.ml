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
(* |- T /\ ((@b. T /\ (b <=> T) \/ (b <=> F)) <=> T) \/ *)
     (* ((@b. T /\ (b <=> T) \/ (b <=> F)) <=> F) *)



 	let ROOT = ONCE_ASM_REWRITE_RULE [] ROOT0 in 

	(* let ROOT = PURE_ONCE_ASM_REWRITE_RULE[ITAUT `(A <=> T) <=> A`] ROOT in  *)

 (* |- ((@b. T /\ (b <=> T) \/ (b <=> F)) <=> T) \/ ~(@b. T /\ (b <=> T) \/ (b <=> F)) *)




 	let L1 = SELECT_RULE p1_proof in 

 	(* let L' = ONCE_ASM_REWRITE_RULE  [] L1 in  *)

 	let L2 = PURE_ONCE_ASM_REWRITE_RULE[ITAUT `A /\ B \/ D <=> (A \/ D) /\ (B \/ D)`] L1  in 

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
 (* (@b. t /\ (b <=> T) \/ (b <=> F)) <=> T |- t \/ ~t *)



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
 (* thm = (@b. T /\ (b <=> T) \/ (b <=> F)) <=> T,   (@b. t /\ (b <=> T) \/ (b <=> F)) <=> F |- t \/ ~t *)



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