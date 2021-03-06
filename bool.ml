(* ========================================================================= *)
(* Boolean theory including (intuitionistic) defs of logical connectives.    *)
(*                                                                           *)
(*       John Harrison, University of Cambridge Computer Laboratory          *)
(*                                                                           *)
(*            (c) Copyright, University of Cambridge 1998                    *)
(*              (c) Copyright, John Harrison 1998-2007                       *)
(* ========================================================================= *)

needs "equal.ml";;

(* ------------------------------------------------------------------------- *)
(* Set up parse status of basic and derived logical constants.               *)
(* ------------------------------------------------------------------------- *)

parse_as_prefix "~";;

parse_as_binder "\\";;
parse_as_binder "!";;
parse_as_binder "?";;
parse_as_binder "?!";;

parse_as_infix ("==>",(4,"right"));;
parse_as_infix ("\\/",(6,"right"));;
parse_as_infix ("/\\",(8,"right"));;

(* ------------------------------------------------------------------------- *)
(* Set up more orthodox notation for equations and equivalence.              *)
(* ------------------------------------------------------------------------- *)

parse_as_infix("<=>",(2,"right"));;
override_interface ("<=>",`(=):bool->bool->bool`);;
parse_as_infix("=",(12,"right"));;

(* ------------------------------------------------------------------------- *)
(* Special syntax for Boolean equations (IFF).                               *)
(* ------------------------------------------------------------------------- *)

let is_iff tm =
  match tm with
    Comb(Comb(Const("=",Tyapp("fun",[Tyapp("bool",[]);_])),l),r) -> true
  | _ -> false;;

let dest_iff tm =
  match tm with
    Comb(Comb(Const("=",Tyapp("fun",[Tyapp("bool",[]);_])),l),r) -> (l,r)
  | _ -> failwith "dest_iff";;

(* let mk_iff =
  let eq_tm = `(<=>)` in
  fun (l,r) -> mk_comb(mk_comb(eq_tm,l),r);; *)

(* ------------------------------------------------------------------------- *)
(* Rule allowing easy instantiation of polymorphic proformas.                *)
(* ------------------------------------------------------------------------- *)

let PINST tyin tmin =
  let tmin' = map (I F_F (inst tyin)) tmin in
  let iterm_fn = INST tmin'
  and itype_fn = INST_TYPE tyin in
  fun th -> try let res = iterm_fn (itype_fn th) in
                let () = replace_proof res (Subst_proof ((tyin,tmin'),th)) in
                res
            with Failure _ -> failwith "PINST";;

(* ------------------------------------------------------------------------- *)
(* Useful derived deductive rule.                                            *)
(* ------------------------------------------------------------------------- *)

let PROVE_HYP ath bth =
  if exists (aconv (concl ath)) (hyp bth)
  then let res = EQ_MP (DEDUCT_ANTISYM_RULE ath bth) ath in
       let () = replace_proof res (Prove_hyp_proof (ath,bth)) in
       res
  else bth;;

(* ------------------------------------------------------------------------- *)
(* Rules for T                                                               *)
(* ------------------------------------------------------------------------- *)

logfile "bool-def";;

let T_DEF = new_basic_definition
`T = (!x:bool. (x ==> x))`;;

export_thm T_DEF;; 

logfile "bool-int";; 

let TRUTH =
  EQ_MP (SYM T_DEF) (GEN `x:bool` (DISCH `x:bool` (ASSUME `x:bool`))) ;;

export_thm TRUTH;;

let EQT_ELIM th =
  try EQ_MP (SYM th) TRUTH
  with Failure _ -> failwith "EQT_ELIM";;

let EQT_INTRO =
  let t = `t:bool` in
  let pth =
    let th1 = DEDUCT_ANTISYM_RULE (ASSUME t) TRUTH in
    let th2 = EQT_ELIM(ASSUME(concl th1)) in
    DEDUCT_ANTISYM_RULE th2 th1 in
  fun th -> EQ_MP (INST[concl th,t] pth) th;;



(* ------------------------------------------------------------------------- *)
(* Rules for ==>                                                             *)
(* ------------------------------------------------------------------------- *)

let mk_imp = mk_binary "==>";;



let rec DISCH_ALL th =
  try DISCH_ALL (DISCH (hd (hyp th)) th)
  with Failure _ -> th;;

let UNDISCH th =
  try MP th (ASSUME(rand(rator(concl th))))
  with Failure _ -> failwith "UNDISCH";;

let rec UNDISCH_ALL th =
  if is_imp (concl th) then UNDISCH_ALL (UNDISCH th)
  else th;;

let IMP_ANTISYM_RULE th1 th2 = 
    let p1,q1 = dest_imp(concl th1) and q2,p2 = dest_imp(concl th2) in
    let th3 = MP th1 (ASSUME p1) and th4 = MP th2 (ASSUME q2) in
    DEDUCT_ANTISYM_RULE th4 th3;;

let ADD_ASSUM tm th = MP (DISCH tm th) (ASSUME tm);;

let EQ_IMP_RULE =
  let peq = `p <=> q` in
  let p,q = dest_iff peq in
  let pth1 = DISCH peq (DISCH p (EQ_MP (ASSUME peq) (ASSUME p)))
  and pth2 = DISCH peq (DISCH q (EQ_MP (SYM(ASSUME peq)) (ASSUME q))) in
  fun th -> let l,r = dest_iff(concl th) in
            MP (INST [l,p; r,q] pth1) th,MP (INST [l,p; r,q] pth2) th;;

let IMP_TRANS =
  let pq = `p ==> q`
  and qr = `q ==> r` in
  let p,q = dest_imp pq and r = rand qr in
  let pth =
    itlist DISCH [pq; qr; p] (MP (ASSUME qr) (MP (ASSUME pq) (ASSUME p))) in
  fun th1 th2 ->
        let x,y = dest_imp(concl th1)
        and y',z = dest_imp(concl th2) in
        if y <> y' then failwith "IMP_TRANS" else
        MP (MP (INST [x,p; y,q; z,r] pth) th1) th2;;

(* ------------------------------------------------------------------------- *)
(* Rules for !                                                               *)
(* ------------------------------------------------------------------------- *)

let mk_forall = mk_binder "!";;
let list_mk_forall(vs,bod) = itlist (curry mk_forall) vs bod;;

let SPECL tms th =
  try rev_itlist SPEC tms th
  with Failure _ -> failwith "SPECL";;

let SPEC_VAR th =
  let bv = variant (thm_frees th) (bndvar(rand(concl th))) in
  bv,SPEC bv th;;

let rec SPEC_ALL th =
  if is_forall(concl th) then SPEC_ALL(snd(SPEC_VAR th)) else th;;

let ISPEC t th =
  let x,_ = try dest_forall(concl th) with Failure _ ->
    failwith "ISPEC: input theorem not universally quantified" in
  let tyins = try type_match (snd(dest_var x)) (type_of t) [] with Failure _ ->
    failwith "ISPEC can't type-instantiate input theorem" in
  try SPEC t (INST_TYPE tyins th)
  with Failure _ -> failwith "ISPEC: type variable(s) free in assumptions";;

let ISPECL tms th =
  try if tms = [] then th else
      let avs = fst (chop_list (length tms) (fst(strip_forall(concl th)))) in
      let tyins = itlist2 type_match (map (snd o dest_var) avs)
                          (map type_of tms) [] in
      SPECL tms (INST_TYPE tyins th)
  with Failure _ -> failwith "ISPECL";;

let GENL = itlist GEN;;

let GEN_ALL th =
  let asl,c = dest_thm th in
  let vars = subtract (frees c) (freesl asl) in
  GENL vars th;;
(* ------------------------------------------------------------------------- *)
(* Rules for /\                                                              *)
(* ------------------------------------------------------------------------- *)

logfile "bool-def";;

let AND_DEF = new_basic_definition
 `(/\) = \p:bool q:bool. (!x:bool. ((p ==> (q ==>x)) ==>x))`;;

export_thm AND_DEF;;

let mk_conj = mk_binary "/\\";;
let list_mk_conj = end_itlist (curry mk_conj);;
let CONJ =
  let p = `p:bool`
  and q = `q:bool`
  and x = `x:bool` in
  let pth1 =
    let th1 = CONV_RULE (RAND_CONV BETA_CONV) (AP_THM AND_DEF p) in
    let th2 = CONV_RULE (RAND_CONV BETA_CONV) (AP_THM th1 q) in
    let th3 = EQ_MP th2 (ASSUME(mk_conj(p,q))) in
    let th4 = EQ_MP (DEDUCT_ANTISYM_RULE(ASSUME p) (ASSUME q)) (ASSUME p) in (*weaken*)
    let th5 = DISCH p (DISCH q th4) in
    let th6 = SPEC q th3 in
    MP th6 th5 in
  let pth2 =
    let th1 = ASSUME (mk_imp(p, mk_imp (q, x))) in
    let th2 = UNDISCH_ALL th1 in
    let th3 = DISCH (mk_imp(p, mk_imp (q, x))) th2 in
    let th4 = GEN x th3 in
    let th5 = CONV_RULE (RAND_CONV BETA_CONV) (AP_THM AND_DEF p) in
    let th6 = CONV_RULE (RAND_CONV BETA_CONV) (AP_THM th5 q) in
    EQ_MP (SYM th6) th4 in
  let pth = DEDUCT_ANTISYM_RULE pth1 pth2 in
  fun th1 th2 ->
    let th = INST [concl th1,p; concl th2,q] pth in
    EQ_MP (PROVE_HYP th1 th) th2;;

let CONJUNCT1 =
  let p = `p:bool` and q = `q:bool` in
  let pth =
    let th1 = CONV_RULE (RAND_CONV BETA_CONV) (AP_THM AND_DEF p) in
    let th2 = CONV_RULE (RAND_CONV BETA_CONV) (AP_THM th1 q) in
    let th3 = EQ_MP th2 (ASSUME(mk_conj(p,q))) in
    let th4 = SPEC p th3 in
    let th5 = EQ_MP (SYM (DEDUCT_ANTISYM_RULE(ASSUME p) (ASSUME q))) (ASSUME q) in (*weaken*)
    let th6 = DISCH q th5 in
    let th7 = DISCH p th6 in
    MP th4 th7 in
  fun th ->
    try let l,r = dest_conj(concl th) in
        PROVE_HYP th (INST [l,p; r,q] pth)
    with Failure _ -> failwith "CONJUNCT1";;

let CONJUNCT2 =
   let p = `p:bool` and q = `q:bool` in
   let pth =
    let th1 = CONV_RULE (RAND_CONV BETA_CONV) (AP_THM AND_DEF p) in
    let th2 = CONV_RULE (RAND_CONV BETA_CONV) (AP_THM th1 q) in
    let th3 = EQ_MP th2 (ASSUME(mk_conj(p,q))) in
    let th4 = SPEC q th3 in
    let th5 = EQ_MP (SYM (DEDUCT_ANTISYM_RULE(ASSUME q) (ASSUME p))) (ASSUME p) in (*weaken*)
    let th6 = DISCH q th5 in
    let th7 = DISCH p th6 in
    MP th4 th7 in
  fun th ->
    try let l,r = dest_conj(concl th) in
        PROVE_HYP th (INST [l,p; r,q] pth)
    with Failure _ -> failwith "CONJUNCT2";;

let CONJ_PAIR th =
  try CONJUNCT1 th,CONJUNCT2 th
  with Failure _ -> failwith "CONJ_PAIR: Not a conjunction";;

let CONJ_TRIPLE th =
  let (c1,c23) = CONJ_PAIR th in
  let (c2,c3) = CONJ_PAIR c23 in
  (c1,c2,c3);;

let CONJUNCTS = striplist CONJ_PAIR;;


(* ------------------------------------------------------------------------- *)
(* Rules for ?                                                               *)
(* ------------------------------------------------------------------------- *)

logfile "bool-def";;

let EXISTS_DEF = new_basic_definition
 `(?) = \p:A->bool. !q. (!x. p x ==> q) ==> q`;;

export_thm EXISTS_DEF;; 

let mk_exists =  mk_binder "?";;
let list_mk_exists(vs,bod) =  itlist (curry mk_exists) vs bod;;

let EXISTS =
  let P = `P:A->bool` and x = `x:A` in
  let pth =
    let th1 = CONV_RULE (RAND_CONV BETA_CONV) (AP_THM EXISTS_DEF P) in
    let th2 = SPEC `x:A` (ASSUME `!x:A. P x ==> Q`) in
    let th3 = DISCH `!x:A. P x ==> Q` (MP th2 (ASSUME `(P:A->bool) x`)) in
    EQ_MP (SYM th1) (GEN `Q:bool` th3) in
  fun (etm,stm) th ->
    try let qf,abs = dest_comb etm in
        let bth = BETA_CONV(mk_comb(abs,stm)) in
        let cth = PINST [type_of stm,aty] [abs,P; stm,x] pth in
        PROVE_HYP (EQ_MP (SYM bth) th) cth
    with Failure _ -> failwith "EXISTS";;

let SIMPLE_EXISTS v th =
  EXISTS (mk_exists(v,concl th),v) th;;

let CHOOSE =
  let P = `P:A->bool` and Q = `Q:bool` in
  let pth =
    let th1 = CONV_RULE (RAND_CONV BETA_CONV) (AP_THM EXISTS_DEF P) in
    let th2 = SPEC `Q:bool` (UNDISCH(fst(EQ_IMP_RULE th1))) in
    DISCH_ALL (DISCH `(?) (P:A->bool)` (UNDISCH th2)) in
  fun (v,th1) th2 ->
    try let abs = rand(concl th1) in
        let bv,bod = dest_abs abs in
        let cmb = mk_comb(abs,v) in
        let pat = vsubst[v,bv] bod in
        let th3 = CONV_RULE BETA_CONV (ASSUME cmb) in
        let th4 = GEN v (DISCH cmb (MP (DISCH pat th2) th3)) in
        let th5 = PINST [snd(dest_var v),aty] [abs,P; concl th2,Q] pth in
        MP (MP th5 th4) th1
    with Failure _ -> failwith "CHOOSE";;

let SIMPLE_CHOOSE v th =
  CHOOSE(v,ASSUME (mk_exists(v,hd(hyp th)))) th;;

(* ------------------------------------------------------------------------- *)
(* Rules for \/                                                              *)
(* ------------------------------------------------------------------------- *)

logfile "bool-def";; 

let OR_DEF = new_basic_definition
 `(\/) = \p q. !r. (p ==> r) ==> (q ==> r) ==> r`;;

export_thm OR_DEF;; 

let mk_disj = mk_binary "\\/";;
let list_mk_disj = end_itlist (curry mk_disj);;

let DISJ1 =
  let P = `P:bool` and Q = `Q:bool` in
  let pth =
    let th1 = CONV_RULE (RAND_CONV BETA_CONV) (AP_THM OR_DEF `P:bool`) in
    let th2 = CONV_RULE (RAND_CONV BETA_CONV) (AP_THM th1 `Q:bool`) in
    let th3 = MP (ASSUME `P ==> t`) (ASSUME `P:bool`) in
    let th4 = GEN `t:bool` (DISCH `P ==> t` (DISCH `Q ==> t` th3)) in
    EQ_MP (SYM th2) th4 in
  fun th tm ->
    try PROVE_HYP th (INST [concl th,P; tm,Q] pth)
    with Failure _ -> failwith "DISJ1";;

let DISJ2 =
  let P = `P:bool` and Q = `Q:bool` in
  let pth =
    let th1 = CONV_RULE (RAND_CONV BETA_CONV) (AP_THM OR_DEF `P:bool`) in
    let th2 = CONV_RULE (RAND_CONV BETA_CONV) (AP_THM th1 `Q:bool`) in
    let th3 = MP (ASSUME `Q ==> t`) (ASSUME `Q:bool`) in
    let th4 = GEN `t:bool` (DISCH `P ==> t` (DISCH `Q ==> t` th3)) in
    EQ_MP (SYM th2) th4 in
  fun tm th ->
    try PROVE_HYP th (INST [tm,P; concl th,Q] pth)
    with Failure _ -> failwith "DISJ2";;

let DISJ_CASES =
  let P = `P:bool` and Q = `Q:bool` and R = `R:bool` in
  let pth =
    let th1 = CONV_RULE (RAND_CONV BETA_CONV) (AP_THM OR_DEF `P:bool`) in
    let th2 = CONV_RULE (RAND_CONV BETA_CONV) (AP_THM th1 `Q:bool`) in
    let th3 = SPEC `R:bool` (EQ_MP th2 (ASSUME `P \/ Q`)) in
    UNDISCH (UNDISCH th3) in
  fun th0 th1 th2 ->
    try let c1 = concl th1 and c2 = concl th2 in
        if not (aconv c1 c2) then failwith "DISJ_CASES" else
        let l,r = dest_disj (concl th0) in
        let th = INST [l,P; r,Q; c1,R] pth in
        PROVE_HYP (DISCH r th2) (PROVE_HYP (DISCH l th1) (PROVE_HYP th0 th))
    with Failure _ -> failwith "DISJ_CASES";;

let SIMPLE_DISJ_CASES th1 th2 =
  DISJ_CASES (ASSUME(mk_disj(hd(hyp th1),hd(hyp th2)))) th1 th2;;

(* ------------------------------------------------------------------------- *)
(* Rules for negation and falsity.                                           *)
(* ------------------------------------------------------------------------- *)

 logfile "bool-def";; 

let F_DEF = new_basic_definition
 `F = !p:bool. p`;;

 export_thm F_DEF;; 

logfile "bool-def";;

let NOT_DEF = new_basic_definition
 `(~) = \p. p ==> F`;;

export_thm NOT_DEF;; 

let mk_neg =
  let neg_tm = `(~)` in
  fun tm -> try mk_comb(neg_tm,tm)
            with Failure _ -> failwith "mk_neg";;

let NOT_ELIM =
  let P = `P:bool` in
  let pth = CONV_RULE(RAND_CONV BETA_CONV) (AP_THM NOT_DEF P) in
  fun th ->
    try EQ_MP (INST [rand(concl th),P] pth) th
    with Failure _ -> failwith "NOT_ELIM";;

let NOT_INTRO =
  let P = `P:bool` in
  let pth = SYM(CONV_RULE(RAND_CONV BETA_CONV) (AP_THM NOT_DEF P)) in
  fun th ->
    try EQ_MP (INST [rand(rator(concl th)),P] pth) th
    with Failure _ -> failwith "NOT_INTRO";;

let EQF_INTRO =
  let P = `P:bool` in
  let pth =
    let th1 = NOT_ELIM (ASSUME `~ P`)
    and th2 = DISCH `F` (SPEC P (EQ_MP F_DEF (ASSUME `F`))) in
    DISCH_ALL (IMP_ANTISYM_RULE th1 th2) in
  fun th ->
    try MP (INST [rand(concl th),P] pth) th
    with Failure _ -> failwith "EQF_INTRO";;

let EQF_ELIM =
  let P = `P:bool` in
  let pth =
    let th1 = EQ_MP (ASSUME `P = F`) (ASSUME `P:bool`) in
    let th2 = DISCH P (SPEC `F` (EQ_MP F_DEF th1)) in
    DISCH_ALL (NOT_INTRO th2) in
  fun th ->
    try MP (INST [rand(rator(concl th)),P] pth) th
    with Failure _ -> failwith "EQF_ELIM";;

let CONTR =
  let P = `P:bool` and f_tm = `F` in
  let pth = SPEC P (EQ_MP F_DEF (ASSUME `F`)) in
  fun tm th ->
    if concl th <> f_tm then failwith "CONTR"
    else PROVE_HYP th (INST [tm,P] pth);;

(* ------------------------------------------------------------------------- *)
(* Rules for unique existence.                                               *)
(* ------------------------------------------------------------------------- *)

logfile "bool-def";; 

let EXISTS_UNIQUE_DEF = new_basic_definition
 `(?!) = \p:A->bool. ((?) p) /\ (!x y. p x /\ p y ==> x = y)`;;

export_thm EXISTS_UNIQUE_DEF;; 

let mk_uexists = mk_binder "?!";;

let EXISTENCE =
  let P = `P:A->bool` in
  let pth =
    let th1 = CONV_RULE (RAND_CONV BETA_CONV) (AP_THM EXISTS_UNIQUE_DEF P) in
    let th2 = UNDISCH (fst(EQ_IMP_RULE th1)) in
    DISCH_ALL (CONJUNCT1 th2) in
  fun th ->
    try let abs = rand(concl th) in
        let ty = snd(dest_var(bndvar abs)) in
        MP (PINST [ty,aty] [abs,P] pth) th
    with Failure _ -> failwith "EXISTENCE";;

logfile_end ();;
