(* ========================================================================= *)
(* The axiom of infinity; construction of the natural numbers.               *)
(*                                                                           *)
(*       John Harrison, University of Cambridge Computer Laboratory          *)
(*                                                                           *)
(*            (c) Copyright, University of Cambridge 1998                    *)
(*              (c) Copyright, John Harrison 1998-2007                       *)
(* ========================================================================= *)

needs "pair.ml";;

(* ------------------------------------------------------------------------- *)
(* Declare a new type "ind" of individuals.                                  *)
(* ------------------------------------------------------------------------- *)

new_type ("ind",0);;

(* ------------------------------------------------------------------------- *)
(* We assert the axiom of infinity as in HOL88, but then we can forget it!   *)
(* ------------------------------------------------------------------------- *)

logfile "function-def";;

let ONE_ONE = new_definition
  `!(f:A->B). ONE_ONE f = !x1 x2. (f x1 = f x2) ==> (x1 = x2)`;;

export_thm ONE_ONE;;

let ONTO = new_definition
  `!(f:A->B). ONTO f = !y. ?x. y = f x`;;

export_thm ONTO;;

logfile "axiom-infinity";;

let INFINITY_AX = 
   new_axiom `?f:ind->ind. ONE_ONE f /\ ~(ONTO f)`;;

export_thm INFINITY_AX;;

(* ------------------------------------------------------------------------- *)
(* Actually introduce constants.                                             *)
(* ------------------------------------------------------------------------- *)

logfile "natural-def";;

let IND_SUC_0_EXISTS = prove
 (`?(f:ind->ind) z. (!x1 x2. (f x1 = f x2) = (x1 = x2)) /\ (!x. ~(f x = z))`,
  X_CHOOSE_TAC `f:ind->ind` INFINITY_AX THEN EXISTS_TAC `f:ind->ind` THEN
  POP_ASSUM MP_TAC THEN REWRITE_TAC[ONE_ONE; ONTO] THEN MESON_TAC[]);;

let IND_SUC_SPEC =
  let th1 = new_definition
   `IND_SUC = @f:ind->ind. ?z. (!x1 x2. (f x1 = f x2) = (x1 = x2)) /\
                                (!x. ~(f x = z))` in
  let th2 = REWRITE_RULE[GSYM th1] (SELECT_RULE IND_SUC_0_EXISTS) in
  let th3 = new_definition
   `IND_0 = @z:ind. (!x1 x2. IND_SUC x1 = IND_SUC x2 <=> x1 = x2) /\
                    (!x. ~(IND_SUC x = z))` in
  REWRITE_RULE[GSYM th3] (SELECT_RULE th2);;

let IND_SUC_INJ,IND_SUC_0 = CONJ_PAIR IND_SUC_SPEC;;

(* ------------------------------------------------------------------------- *)
(* Carve out the natural numbers inductively.                                *)
(* ------------------------------------------------------------------------- *)

let NUM_REP_RULES,NUM_REP_INDUCT,NUM_REP_CASES =
  new_inductive_definition
   `NUM_REP IND_0 /\
    (!i. NUM_REP i ==> NUM_REP (IND_SUC i))`;;

let num_tydef = new_basic_type_definition
  "num" ("mk_num","dest_num")
    (CONJUNCT1 NUM_REP_RULES);;

let ZERO_DEF = new_definition
 `_0 = mk_num IND_0`;;

let SUC_DEF = new_definition
 `SUC n = mk_num(IND_SUC(dest_num n))`;;

(* ------------------------------------------------------------------------- *)
(* Distinctness and injectivity of constructors.                             *)
(* ------------------------------------------------------------------------- *)

let NOT_SUC = prove
 (`!n. ~(SUC n = _0)`,
  REWRITE_TAC[SUC_DEF; ZERO_DEF] THEN
  MESON_TAC[NUM_REP_RULES; fst num_tydef; snd num_tydef; IND_SUC_0]);;

export_thm NOT_SUC;;

let SUC_INJ = prove
 (`!m n. SUC m = SUC n <=> m = n`,
  REPEAT GEN_TAC THEN REWRITE_TAC[SUC_DEF] THEN
  EQ_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  POP_ASSUM(MP_TAC o AP_TERM `dest_num`) THEN
  SUBGOAL_THEN `!p. NUM_REP (IND_SUC (dest_num p))` MP_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC (CONJUNCT2 NUM_REP_RULES); ALL_TAC] THEN
  REWRITE_TAC[fst num_tydef; snd num_tydef] THEN
  DISCH_TAC THEN ASM_REWRITE_TAC[IND_SUC_INJ] THEN
  DISCH_THEN(MP_TAC o AP_TERM `mk_num`) THEN
  REWRITE_TAC[fst num_tydef]);;

export_thm SUC_INJ;;

(* ------------------------------------------------------------------------- *)
(* Induction.                                                                *)
(* ------------------------------------------------------------------------- *)

let num_INDUCTION = prove
 (`!p. p (_0) /\ (!n. p (n) ==> p (SUC n)) ==> !n. p n`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `\i. NUM_REP i /\ p (mk_num i):bool` NUM_REP_INDUCT) THEN
  ASM_REWRITE_TAC[GSYM ZERO_DEF; NUM_REP_RULES] THEN
  W(C SUBGOAL_THEN (fun t -> REWRITE_TAC[t]) o funpow 2 lhand o snd) THENL
   [REPEAT STRIP_TAC THENL
     [MATCH_MP_TAC(CONJUNCT2 NUM_REP_RULES) THEN ASM_REWRITE_TAC[];
      SUBGOAL_THEN `mk_num(IND_SUC i) = SUC(mk_num i)` SUBST1_TAC THENL
       [REWRITE_TAC[SUC_DEF] THEN REPEAT AP_TERM_TAC THEN
        CONV_TAC SYM_CONV THEN REWRITE_TAC[GSYM(snd num_tydef)] THEN
        FIRST_ASSUM MATCH_ACCEPT_TAC;
        FIRST_ASSUM MATCH_MP_TAC THEN FIRST_ASSUM MATCH_ACCEPT_TAC]];
    DISCH_THEN(MP_TAC o SPEC `dest_num n`) THEN
    REWRITE_TAC[fst num_tydef; snd num_tydef]]);;

export_thm num_INDUCTION;;

(* ------------------------------------------------------------------------- *)
(* Recursion.                                                                *)
(* ------------------------------------------------------------------------- *)

logfile "natural-thm";;

let num_Axiom = prove
 (`!(e:A) f. ?!fn. (fn _0 = e) /\
                   (!n. fn (SUC n) = f (fn n) n)`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[EXISTS_UNIQUE_THM] THEN CONJ_TAC THENL
   [(MP_TAC o prove_inductive_relations_exist)
      `PRG _0 e /\ (!b:A n:num. PRG n b ==> PRG (SUC n) (f b n))` THEN
    DISCH_THEN(CHOOSE_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (ASSUME_TAC o GSYM)) THEN
    SUBGOAL_THEN `!n:num. ?!y:A. PRG n y` MP_TAC THENL
     [MATCH_MP_TAC num_INDUCTION THEN REPEAT STRIP_TAC THEN
      FIRST_ASSUM(fun th -> GEN_REWRITE_TAC BINDER_CONV [GSYM th]) THEN
      REWRITE_TAC[GSYM NOT_SUC; NOT_SUC; SUC_INJ; EXISTS_UNIQUE_REFL] THEN
      REWRITE_TAC[UNWIND_THM1] THEN
      UNDISCH_TAC `?!y. PRG (n:num) (y:A)` THEN
      REWRITE_TAC[EXISTS_UNIQUE_THM] THEN
      DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC `y:A`) ASSUME_TAC) THEN
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THENL
       [MAP_EVERY EXISTS_TAC [`(f:A->num->A) y n`; `y:A`];
        AP_THM_TAC THEN AP_TERM_TAC THEN FIRST_ASSUM MATCH_MP_TAC] THEN
      ASM_REWRITE_TAC[];
      REWRITE_TAC[UNIQUE_SKOLEM_ALT] THEN
      DISCH_THEN(X_CHOOSE_THEN `fn:num->A` (ASSUME_TAC o GSYM)) THEN
      EXISTS_TAC `fn:num->A` THEN ASM_REWRITE_TAC[] THEN
      GEN_TAC THEN FIRST_ASSUM(MATCH_MP_TAC o CONJUNCT2) THEN
      FIRST_ASSUM(fun th -> GEN_REWRITE_TAC I [GSYM th]) THEN REFL_TAC];
    REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[FUN_EQ_THM] THEN
    MATCH_MP_TAC num_INDUCTION THEN ASM_REWRITE_TAC[] THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[]]);;

export_thm num_Axiom;;

(* ------------------------------------------------------------------------- *)
(* The basic numeral tag; rewrite existing instances of "_0".                *)
(* ------------------------------------------------------------------------- *)

let NUMERAL =
  let def = new_basic_definition `NUMERAL = \n. (n : num)` in
  let () = delete_const_definition ["NUMERAL"] in
  let () = delete_proof def in
  prove
  (`!(n:num). NUMERAL n = n`,
   REWRITE_TAC [def]);;

let [NOT_SUC; num_INDUCTION; num_Axiom] =
  let th = prove(`_0 = 0`,REWRITE_TAC[NUMERAL]) in
  map (GEN_REWRITE_RULE DEPTH_CONV [th])
    [NOT_SUC; num_INDUCTION; num_Axiom];;

(* ------------------------------------------------------------------------- *)
(* Induction tactic.                                                         *)
(* ------------------------------------------------------------------------- *)

let (INDUCT_TAC:tactic) =
  MATCH_MP_TAC num_INDUCTION THEN
  CONJ_TAC THENL [ALL_TAC; GEN_TAC THEN DISCH_TAC];;

let num_RECURSION =
  let avs = fst(strip_forall(concl num_Axiom)) in
  GENL avs (EXISTENCE (SPECL avs num_Axiom));;

(* ------------------------------------------------------------------------- *)
(* Cases theorem.                                                            *)
(* ------------------------------------------------------------------------- *)

let num_CASES = prove
 (`!m. (m = 0) \/ (?n. m = SUC n)`,
  INDUCT_TAC THEN MESON_TAC[]);;

export_thm num_CASES;;

(* ------------------------------------------------------------------------- *)
(* Augmenting inductive type store.                                          *)
(* ------------------------------------------------------------------------- *)

let num_RECURSION_STD = prove
 (`!e:Z f. ?fn. (fn 0 = e) /\ (!n. fn (SUC n) = f n (fn n))`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`e:Z`; `(\z n. (f:num->Z->Z) n z)`] num_RECURSION) THEN
  REWRITE_TAC[]);;

inductive_type_store :=
 ("num",(2,num_INDUCTION,num_RECURSION_STD))::(!inductive_type_store);;

(* ------------------------------------------------------------------------- *)
(* "Bitwise" binary representation of numerals.                              *)
(* ------------------------------------------------------------------------- *)

logfile "natural-numeral-def";;

let (BIT0_ZERO,BIT0_SUC) =
  let def = new_definition
    `BIT0 = @fn. fn 0 = 0 /\ (!n. fn (SUC n) = SUC (SUC (fn n)))`
  and th = BETA_RULE(ISPECL [`0`; `\m n:num. SUC (SUC m)`] num_RECURSION) in
  CONJ_PAIR (REWRITE_RULE [GSYM def] (SELECT_RULE th));;

export_thm BIT0_ZERO;;
export_thm BIT0_SUC;;

let BIT0_DEF = CONJ BIT0_ZERO BIT0_SUC;;

let BIT1_DEF = new_definition
 `!n. BIT1 n = SUC (BIT0 n)`;;

export_thm BIT1_DEF;;

(* ------------------------------------------------------------------------- *)
(* Following is handy before num_CONV arrives.                               *)
(* ------------------------------------------------------------------------- *)

let ONE = prove
 (`1 = SUC 0`,
  REWRITE_TAC [NUMERAL; REWRITE_RULE [NUMERAL] BIT1_DEF;
               REWRITE_RULE [NUMERAL] BIT0_DEF]);;

let TWO = prove
 (`2 = SUC 1`,
  REWRITE_TAC [NUMERAL; REWRITE_RULE [NUMERAL] BIT1_DEF;
               REWRITE_RULE [NUMERAL] BIT0_DEF]);;

(* ------------------------------------------------------------------------- *)
(* Syntax operations on numerals.                                            *)
(* ------------------------------------------------------------------------- *)

let mk_numeral =
  let pow24 = pow2 24 and num_0 = Int 0
  and zero_tm = mk_const("_0",[])
  and BIT0_tm = mk_const("BIT0",[])
  and BIT1_tm = mk_const("BIT1",[])
  and NUMERAL_tm = mk_const("NUMERAL",[]) in
  let rec stripzeros l = match l with false::t -> stripzeros t | _ -> l in
  let rec raw_list_of_num l n =
    if n =/ num_0 then stripzeros l else
    let h = Num.int_of_num(mod_num n pow24) in
    raw_list_of_num
     ((h land 8388608 <> 0)::(h land 4194304 <> 0)::(h land 2097152 <> 0)::
      (h land 1048576 <> 0)::(h land 524288 <> 0)::(h land 262144 <> 0)::
      (h land 131072 <> 0)::(h land 65536 <> 0)::(h land 32768 <> 0)::
      (h land 16384 <> 0)::(h land 8192 <> 0)::(h land 4096 <> 0)::
      (h land 2048 <> 0)::(h land 1024 <> 0)::(h land 512 <> 0)::
      (h land 256 <> 0)::(h land 128 <> 0)::(h land 64 <> 0)::
      (h land 32 <> 0)::(h land 16 <> 0)::(h land 8 <> 0)::(h land 4 <> 0)::
      (h land 2 <> 0)::(h land 1 <> 0)::l) (quo_num n pow24) in
  let rec numeral_of_list t l =
    match l with
      [] -> t
    | b::r -> numeral_of_list(mk_comb((if b then BIT1_tm else BIT0_tm),t)) r in
  let mk_raw_numeral n = numeral_of_list zero_tm (raw_list_of_num [] n) in
  fun n -> if n </ num_0 then failwith "mk_numeral: negative argument" else
           mk_comb(NUMERAL_tm,mk_raw_numeral n);;

let mk_small_numeral n = mk_numeral(Int n);;

let dest_small_numeral t = Num.int_of_num(dest_numeral t);;

let is_numeral = can dest_numeral;;

(* ------------------------------------------------------------------------- *)
(* Derived principles of definition based on existence.                      *)
(*                                                                           *)
(* This is put here because we use numerals as tags to force different       *)
(* constants specified with equivalent theorems to have different underlying *)
(* definitions, ensuring that there are no provable equalities between them  *)
(* and so in some sense the constants are "underspecified" as the user might *)
(* want for some applications.                                               *)
(* ------------------------------------------------------------------------- *)

let the_specifications = ref [];;

let new_specification =
  let code c = mk_small_numeral (Char.code (c.[0])) in
  let mk_code name =
      end_itlist (curry mk_pair) (map code (explode name)) in
  let check_distinct l =
    try itlist (fun t res -> if mem t res then fail() else t::res) l []; true
    with Failure _ -> false in
  let specify name th =
    let ntm = mk_code name in
    let gv = genvar(type_of ntm) in
    let th0 = CONV_RULE(REWR_CONV SKOLEM_THM) (GEN gv th) in
    let th1 = CONV_RULE(RATOR_CONV (REWR_CONV EXISTS_THM) THENC
                        BETA_CONV) th0 in
    let l,r = dest_comb(concl th1) in
    let rn = mk_comb(r,ntm) in
    let ty = type_of rn in
    let th2 = new_definition(mk_eq(mk_var(name,ty),rn)) in
    GEN_REWRITE_RULE ONCE_DEPTH_CONV [GSYM th2]
     (SPEC ntm (CONV_RULE BETA_CONV th1)) in
  let rec specifies names th =
    match names with
      [] -> th
    | name::onames -> let th' = specify name th in
                      specifies onames th' in
  fun names th ->
    let asl,c = dest_thm th in
    if not (asl = []) then
      failwith "new_specification: Assumptions not allowed in theorem" else
    if not (frees c = []) then
      failwith "new_specification: Free variables in predicate" else
    let avs = fst(strip_exists c) in
    if length names = 0 or length names > length avs then
      failwith "new_specification: Unsuitable number of constant names" else
    if not (check_distinct names) then
      failwith "new_specification: Constant names not distinct"
    else
      try let sth = snd(find (fun ((names',th'),sth') ->
                               names' = names & aconv (concl th') (concl th))
                             (!the_specifications)) in
          warn true ("Benign respecification"); sth
      with Failure _ ->
          let sth = specifies names th in
          the_specifications := ((names,th),sth)::(!the_specifications);
          sth;;

(* ------------------------------------------------------------------------- *)
(* The new principle of constant definition.                                 *)
(* ------------------------------------------------------------------------- *)

let define_const_list =
    let maps (f : 'a -> 's -> 'b * 's) =
        let rec m xs s =
            match xs with
              [] -> ([],s)
            | x :: xs ->
              let (y,s) = f x s in
              let (ys,s) = m xs s in
              (y :: ys, s) in
         m in
    let vassoc (v : term) =
        let pred (u, (_ : term)) = u = v in
        fun vm ->
        match partition pred vm with
          ([],vm) -> (None,vm)
        | ([(_,tm)],vm) -> (Some tm, vm)
        | (_ :: _ :: _, _) -> failwith "repeated vars" in
    let add tm vm =
        let (v,tm) = dest_eq tm in
        let () =
            match vassoc v vm with
              (None,_) -> ()
            | (Some _, _) -> failwith "repeated vars in assumptions" in
        (v,tm) :: vm in
    let del (n,v) vm =
        let (tm,vm) =
            match vassoc v vm with
              (None,_) -> failwith "given var not in assumptions"
            | (Some tm, vm) -> (tm,vm) in
        let def = new_basic_definition (mk_eq (mk_var (n, type_of v), tm)) in
        let (c,_) = dest_eq (concl def) in
        (((n,(c,v)),def),vm) in
    fun nvs -> fun th ->
    let vm = rev_itlist add (hyp th) [] in
    let () =
        if subset (frees (concl th)) (map snd nvs) then () else
        failwith "additional free vars in definition theorem" in
    let (cs,sub,defs) =
        let (cs_sub_defs,vm) = maps del nvs vm in
        let () =
            match vm with
              [] -> ()
            | _ :: _ ->
              failwith "additional assumptions in definition theorem" in
        let (cs_sub,defs) = unzip cs_sub_defs in
        let (cs,sub) = unzip cs_sub in
        (cs,sub,defs) in
    let res = rev_itlist PROVE_HYP defs (INST sub th) in
    let () =
        match cs with
          [] -> ()
        | c :: _ -> replace_proof res (Define_const_list_proof c) in
    let () =
        let f c i =
            let cdef = Const_list_definition (((nvs,th),res),i) in
            let () = replace_const_definition c cdef in
            i + 1 in
        let _ = rev_itlist f cs 0 in
        () in
    res;;

let new_specification =
    let exists_conv = RATOR_CONV (REWR_CONV EXISTS_THM) THENC BETA_CONV in
    let f n th =
        let (v,_) = dest_exists (concl th) in
        let th = CONV_RULE exists_conv th in
        let rth = SYM (ASSUME (mk_eq (v, rand (concl th)))) in
        let th = CONV_RULE (RAND_CONV (K rth) THENC BETA_CONV) th in
        define_const_list [(n,v)] th in
    rev_itlist f;;

logfile_end ();;
