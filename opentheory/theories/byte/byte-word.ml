(*BEGIN-PARAMETRIC*)
new_constant ("byte_size", `:num`);;

let byte_size_def = new_axiom
  `byte_size = 2 EXP byte_width`;;

let byte_size_nonzero = new_axiom
  `~(byte_size = 0)`;;

let mod_refl_byte_size = new_axiom
  `byte_size MOD byte_size = 0`;;

let mod_lt_byte_size = new_axiom
  `!n. n < byte_size ==> n MOD byte_size = n`;;

let mod_le_byte_size = new_axiom
  `!n. n MOD byte_size <= n`;;

let zero_mod_byte_size = new_axiom
  `0 MOD byte_size = 0`;;

let lt_mod_byte_size = new_axiom
  `!n. n MOD byte_size < byte_size`;;

let mod_mod_refl_byte_size = new_axiom
  `!n. n MOD byte_size MOD byte_size = n MOD byte_size`;;

let mod_add_mod_byte_size = new_axiom
  `!m n. (m MOD byte_size + n MOD byte_size) MOD byte_size = (m + n) MOD byte_size`;;

let mod_mult_mod_byte_size = new_axiom
  `!m n. (m MOD byte_size * n MOD byte_size) MOD byte_size = (m * n) MOD byte_size`;;

let divides_mod_byte_size = new_axiom
   `!n. divides byte_size n <=> n MOD byte_size = 0`;;

new_type ("byte",0);;

new_constant ("num_to_byte", `:num -> byte`);;

new_constant ("byte_to_num", `:byte -> num`);;

let byte_to_num_to_byte = new_axiom
  `!x. num_to_byte (byte_to_num x) = x`;;

let num_to_byte_inj = new_axiom
   `!x y.
      x < byte_size /\ y < byte_size /\ num_to_byte x = num_to_byte y ==>
      x = y`;;

let num_to_byte_to_num = new_axiom
  `!n. byte_to_num (num_to_byte n) = n MOD byte_size`;;

let num_to_byte_to_num_bound = new_axiom
  `!n. n < byte_size ==> byte_to_num (num_to_byte n) = n`;;

new_constant ("byte_add", `:byte -> byte -> byte`);;

let num_to_byte_add = new_axiom
  `!x1 y1.
     num_to_byte (x1 + y1) =
     byte_add (num_to_byte x1) (num_to_byte y1)`;;

new_constant ("byte_mult", `:byte -> byte -> byte`);;

let num_to_byte_mult = new_axiom
  `!x1 y1.
     num_to_byte (x1 * y1) =
     byte_mult (num_to_byte x1) (num_to_byte y1)`;;

new_constant ("byte_exp", `:byte -> num -> byte`);;

let byte_exp_zero = new_axiom
  `!x. byte_exp x 0 = num_to_byte 1`;;

let byte_exp_suc = new_axiom
  `!x n. byte_exp x (SUC n) = byte_mult x (byte_exp x n)`;;

let byte_exp_def = CONJ byte_exp_zero byte_exp_suc;;

new_constant ("byte_neg", `:byte -> byte`);;

let byte_neg_def = new_axiom
  `!x. byte_neg x = num_to_byte (byte_size - byte_to_num x)`;;

new_constant ("byte_sub", `:byte -> byte -> byte`);;

let byte_sub_def = new_axiom
  `!x y. byte_sub x y = byte_add x (byte_neg y)`;;

new_constant ("byte_le", `:byte -> byte -> bool`);;

let byte_le_def = new_axiom
  `!x y. byte_le x y <=> byte_to_num x <= byte_to_num y`;;

new_constant ("byte_lt", `:byte -> byte -> bool`);;

let byte_lt_def = new_axiom
  `!x y. byte_lt x y <=> byte_to_num x < byte_to_num y`;;

new_constant ("random_byte", `:random -> byte`);;

let random_byte_def = new_axiom
  `!r. random_byte r = num_to_byte (random_uniform byte_size r)`;;

let byte_to_num_inj = new_axiom
  `!x y. byte_to_num x = byte_to_num y ==> x = y`;;

let num_to_byte_eq = new_axiom
   `!x y.
      num_to_byte x = num_to_byte y <=> x MOD byte_size = y MOD byte_size`;;

let num_to_byte_is_zero = new_axiom
   `!x. num_to_byte x = num_to_byte 0 <=> divides byte_size x`;;

let byte_to_num_bound = new_axiom
  `!x. byte_to_num x < byte_size`;;

let byte_to_num_div_bound = new_axiom
  `!x. byte_to_num x DIV byte_size = 0`;;

let byte_to_num_mod_bound = new_axiom
  `!x. byte_to_num x MOD byte_size = byte_to_num x`;;

let byte_add_to_num = new_axiom
   `!x y.
      byte_to_num (byte_add x y) =
      (byte_to_num x + byte_to_num y) MOD byte_size`;;

let byte_mult_to_num = new_axiom
   `!x y.
      byte_to_num (byte_mult x y) =
      (byte_to_num x * byte_to_num y) MOD byte_size`;;

let byte_not_lt = new_axiom
   `!x y. ~(byte_lt x y) <=> byte_le y x`;;

let byte_not_le = new_axiom
   `!x y. ~(byte_le x y) <=> byte_lt y x`;;

let num_to_byte_byte_size = new_axiom
   `num_to_byte byte_size = num_to_byte 0`;;

let byte_add_comm = new_axiom
   `!x y. byte_add x y = byte_add y x`;;

let byte_add_assoc = new_axiom
   `!x y z. byte_add (byte_add x y) z = byte_add x (byte_add y z)`;;

let byte_add_left_zero = new_axiom
   `!x. byte_add (num_to_byte 0) x = x`;;

let byte_add_right_zero = new_axiom
   `!x. byte_add x (num_to_byte 0) = x`;;

let byte_add_left_neg = new_axiom
   `!x. byte_add (byte_neg x) x = num_to_byte 0`;;

let byte_add_right_neg = new_axiom
   `!x. byte_add x (byte_neg x) = num_to_byte 0`;;

let byte_add_left_cancel = new_axiom
   `!x y z. byte_add x y = byte_add x z <=> y = z`;;

let byte_add_right_cancel = new_axiom
   `!x y z. byte_add y x = byte_add z x <=> y = z`;;

let byte_add_left_cancel_zero = new_axiom
   `!x y. byte_add x y = x <=> y = num_to_byte 0`;;

let byte_add_right_cancel_zero = new_axiom
   `!x y. byte_add y x = x <=> y = num_to_byte 0`;;

let byte_neg_neg = new_axiom
   `!x. byte_neg (byte_neg x) = x`;;

let byte_neg_inj = new_axiom
   `!x y. byte_neg x = byte_neg y ==> x = y`;;

let byte_neg_zero = new_axiom
   `byte_neg (num_to_byte 0) = num_to_byte 0`;;

let byte_neg_is_zero = new_axiom
   `!x. byte_neg x = num_to_byte 0 <=> x = num_to_byte 0`;;

let byte_neg_add = new_axiom
   `!x y.
      byte_add (byte_neg x) (byte_neg y) =
      byte_neg (byte_add x y)`;;

let byte_mult_comm = new_axiom
   `!x y. byte_mult x y = byte_mult y x`;;

let byte_mult_assoc = new_axiom
   `!x y z.
      byte_mult (byte_mult x y) z = byte_mult x (byte_mult y z)`;;

let byte_add_left_distrib = new_axiom
   `!x y z.
      byte_mult x (byte_add y z) =
      byte_add (byte_mult x y) (byte_mult x z)`;;

let byte_add_right_distrib = new_axiom
   `!x y z.
      byte_mult (byte_add y z) x =
      byte_add (byte_mult y x) (byte_mult z x)`;;

let byte_mult_left_zero = new_axiom
   `!x. byte_mult (num_to_byte 0) x = num_to_byte 0`;;

let byte_mult_right_zero = new_axiom
   `!x. byte_mult x (num_to_byte 0) = num_to_byte 0`;;

let byte_mult_left_one = new_axiom
   `!x. byte_mult (num_to_byte 1) x = x`;;

let byte_mult_right_one = new_axiom
   `!x. byte_mult x (num_to_byte 1) = x`;;

let byte_mult_left_neg = new_axiom
   `!x y. byte_mult (byte_neg x) y = byte_neg (byte_mult x y)`;;

let byte_mult_right_neg = new_axiom
   `!x y. byte_mult x (byte_neg y) = byte_neg (byte_mult x y)`;;

let num_to_byte_exp = new_axiom
   `!m n. num_to_byte (m EXP n) = byte_exp (num_to_byte m) n`;;

let byte_zero_exp = new_axiom
   `!n.
      byte_exp (num_to_byte 0) n =
      if n = 0 then num_to_byte 1 else num_to_byte 0`;;

let byte_exp_add = new_axiom
   `!x m n.
      byte_mult (byte_exp x m) (byte_exp x n) =
      byte_exp x (m + n)`;;

let byte_exp_one = new_axiom
   `!x. byte_exp x 1 = x`;;

let byte_le_refl = new_axiom
  `!x. byte_le x x`;;

let byte_le_trans = new_axiom
  `!x1 x2 x3. byte_le x1 x2 /\ byte_le x2 x3 ==> byte_le x1 x3`;;

let byte_lt_refl = new_axiom
  `!x. ~byte_lt x x`;;

let byte_lte_trans = new_axiom
  `!x1 x2 x3. byte_lt x1 x2 /\ byte_le x2 x3 ==> byte_lt x1 x3`;;

let byte_let_trans = new_axiom
  `!x1 x2 x3. byte_le x1 x2 /\ byte_lt x2 x3 ==> byte_lt x1 x3`;;

let byte_lt_trans = new_axiom
  `!x1 x2 x3. byte_lt x1 x2 /\ byte_lt x2 x3 ==> byte_lt x1 x3`;;

new_constant ("byte_shl", `:byte -> num -> byte`);;

let byte_shl_def = new_axiom
  `!w n. byte_shl w n = num_to_byte (bit_shl (byte_to_num w) n)`;;

new_constant ("byte_shr", `:byte -> num -> byte`);;

let byte_shr_def = new_axiom
  `!w n. byte_shr w n = num_to_byte (bit_shr (byte_to_num w) n)`;;

new_constant ("byte_bit", `:byte -> num -> bool`);;

let byte_bit_def = new_axiom
  `!w n. byte_bit w n = bit_nth (byte_to_num w) n`;;

new_constant ("byte_to_list", `:byte -> bool list`);;

let byte_to_list_def = new_axiom
  `!w. byte_to_list w = num_to_bitvec (byte_to_num w) byte_width`;;

new_constant ("list_to_byte", `:bool list -> byte`);;

let list_to_byte_def = new_axiom
  `!l. list_to_byte l = num_to_byte (bits_to_num l)`;;

new_constant ("is_byte_list", `:bool list -> bool`);;

let is_byte_list_def = new_axiom
  `!l. is_byte_list (l : bool list) <=> LENGTH l = byte_width`;;

new_constant ("byte_and", `:byte -> byte -> byte`);;

let byte_and_def = new_axiom
  `!w1 w2.
      byte_and w1 w2 =
      num_to_byte (bit_and (byte_to_num w1) (byte_to_num w2))`;;

new_constant ("byte_or", `:byte -> byte -> byte`);;

let byte_or_def = new_axiom
  `!w1 w2.
      byte_or w1 w2 =
      num_to_byte (bit_or (byte_to_num w1) (byte_to_num w2))`;;

new_constant ("byte_not", `:byte -> byte`);;

let byte_not_def = new_axiom
  `!w. byte_not w = list_to_byte (MAP (~) (byte_to_list w))`;;

new_constant ("byte_bits_lte", `:bool -> bool list -> bool list -> bool`);;

let byte_bits_lte_nil = new_axiom
   `!q. byte_bits_lte q [] [] = q`
and byte_bits_lte_cons = new_axiom
   `!q h1 h2 t1 t2.
      byte_bits_lte q (CONS h1 t1) (CONS h2 t2) =
      byte_bits_lte ((~h1 /\ h2) \/ (~(h1 /\ ~h2) /\ q)) t1 t2`;;

let byte_bits_lte_def = CONJ byte_bits_lte_nil byte_bits_lte_cons;;

let length_byte_to_list = new_axiom
  `!w. LENGTH (byte_to_list w) = byte_width`;;

let is_byte_to_list = new_axiom
  `!w. is_byte_list (byte_to_list w)`;;

let list_to_byte_nil = new_axiom
   `list_to_byte [] = num_to_byte 0`;;

let list_to_byte_cons = new_axiom
   `!h t.
      list_to_byte (CONS h t) =
      if h then byte_add (num_to_byte 1) (byte_shl (list_to_byte t) 1)
      else byte_shl (list_to_byte t) 1`;;

let bit_bound_byte_to_num = new_axiom
  `!w. bit_bound (byte_to_num w) byte_width = byte_to_num w`;;

let num_to_byte_to_num_bit_bound = new_axiom
  `!n. byte_to_num (num_to_byte n) = bit_bound n byte_width`;;

let nil_to_byte_to_num = new_axiom
  `byte_to_num (list_to_byte []) = 0`;;

let list_to_byte_to_num_bound = new_axiom
  `!l. byte_to_num (list_to_byte l) < 2 EXP (LENGTH l)`;;

let bit_width_byte_to_num = new_axiom
  `!w. bit_width (byte_to_num w) <= byte_width`;;

let byte_to_list_to_num = new_axiom
  `!w. bits_to_num (byte_to_list w) = byte_to_num w`;;

let byte_to_list_to_byte = new_axiom
  `!w. list_to_byte (byte_to_list w) = w`;;

let byte_to_list_inj = new_axiom
  `!w1 w2. byte_to_list w1 = byte_to_list w2 ==> w1 = w2`;;

let byte_to_list_inj_eq = new_axiom
  `!w1 w2. byte_to_list w1 = byte_to_list w2 <=> w1 = w2`;;

let list_to_byte_bit = new_axiom
  `!l n.
     byte_bit (list_to_byte l) n =
     (n < byte_width /\ n < LENGTH l /\ nth l n)`;;

let byte_bit_and = new_axiom
  `!k w1 w2. byte_bit (byte_and w1 w2) k <=> byte_bit w1 k /\ byte_bit w2 k`;;

let byte_and_list = new_axiom
  `!w1 w2.
     byte_and w1 w2 =
     list_to_byte (zipwith ( /\ ) (byte_to_list w1) (byte_to_list w2))`;;

let byte_bit_or = new_axiom
  `!k w1 w2. byte_bit (byte_or w1 w2) k <=> byte_bit w1 k \/ byte_bit w2 k`;;

let byte_or_list = new_axiom
  `!w1 w2.
     byte_or w1 w2 =
     list_to_byte (zipwith ( \/ ) (byte_to_list w1) (byte_to_list w2))`;;

let byte_bit_not = new_axiom
  `!k w. byte_bit (byte_not w) k <=> k < byte_width /\ ~byte_bit w k`;;

let list_to_byte_to_list_eq = new_axiom
  `!l.
     byte_to_list (list_to_byte l) =
     if LENGTH l <= byte_width then
       APPEND l (REPLICATE F (byte_width - LENGTH l))
     else
       take byte_width l`;;

let list_to_byte_to_list = new_axiom
  `!l. LENGTH l = byte_width <=> byte_to_list (list_to_byte l) = l`;;

let byte_shl_list = new_axiom
  `!l n.
     byte_shl (list_to_byte l) n =
     list_to_byte (APPEND (REPLICATE F n) l)`;;

let short_byte_shr_list = new_axiom
  `!l n.
     LENGTH l <= byte_width ==>
     byte_shr (list_to_byte l) n =
     (if LENGTH l <= n then list_to_byte []
      else list_to_byte (drop n l))`;;

let long_byte_shr_list = new_axiom
  `!l n.
     byte_width <= LENGTH l ==>
     byte_shr (list_to_byte l) n =
     if byte_width <= n then list_to_byte []
     else list_to_byte (drop n (take byte_width l))`;;

let byte_shr_list = new_axiom
  `!l n.
     byte_shr (list_to_byte l) n =
     (if LENGTH l <= byte_width then
        if LENGTH l <= n then list_to_byte []
        else list_to_byte (drop n l)
      else
        if byte_width <= n then list_to_byte []
        else list_to_byte (drop n (take byte_width l)))`;;

let byte_eq_bits = new_axiom
  `!w1 w2.
     (!i. i < byte_width ==> byte_bit w1 i = byte_bit w2 i) ==> w1 = w2`;;

let byte_lte_cmp = new_axiom
  `!q l1 l2.
     LENGTH l1 = LENGTH l2 ==>
     byte_bits_lte q l1 l2 = bit_cmp q (bits_to_num l1) (bits_to_num l2)`;;

let byte_lte_list = new_axiom
  `!q w1 w2.
     byte_bits_lte q (byte_to_list w1) (byte_to_list w2) <=>
     (if q then byte_le w1 w2 else byte_lt w1 w2)`;;

let byte_le_list = new_axiom
  `!w1 w2.
     byte_bits_lte T (byte_to_list w1) (byte_to_list w2) <=> byte_le w1 w2`;;

let byte_lt_list = new_axiom
  `!w1 w2.
     byte_bits_lte F (byte_to_list w1) (byte_to_list w2) <=> byte_lt w1 w2`;;

let byte_reduce_conv =
  REWRITE_CONV
    [byte_to_num_to_byte;
     byte_le_def; byte_lt_def] THENC
  REWRITE_CONV
    [num_to_byte_to_num] THENC
  REWRITE_CONV
    [byte_width_def; byte_size_def; num_to_byte_eq] THENC
  NUM_REDUCE_CONV;;

let byte_width_conv = REWR_CONV byte_width_def;;

let list_to_byte_to_list_conv =
  REWR_CONV list_to_byte_to_list_eq THENC
  cond_conv
    (LAND_CONV length_conv THENC
     RAND_CONV byte_width_conv THENC
     NUM_REDUCE_CONV)
    (RAND_CONV
       (RAND_CONV
          (LAND_CONV byte_width_conv THENC
           RAND_CONV length_conv THENC
           NUM_REDUCE_CONV) THENC
        replicate_conv) THENC
     append_conv)
    (LAND_CONV byte_width_conv THENC
     take_conv);;

let numeral_to_byte_list_conv =
  let list_to_byte_conv = REWR_CONV (GSYM list_to_byte_def) in
  RAND_CONV numeral_to_bits_conv THENC
  list_to_byte_conv;;

let byte_and_list_conv =
  let th = SPECL [`list_to_byte l1`; `list_to_byte l2`] byte_and_list in
  REWR_CONV th THENC
  RAND_CONV
    (LAND_CONV list_to_byte_to_list_conv THENC
     RAND_CONV list_to_byte_to_list_conv THENC
     zipwith_conv and_simp_conv);;

let byte_or_list_conv =
  let th = SPECL [`list_to_byte l1`; `list_to_byte l2`] byte_or_list in
  REWR_CONV th THENC
  RAND_CONV
    (LAND_CONV list_to_byte_to_list_conv THENC
     RAND_CONV list_to_byte_to_list_conv THENC
     zipwith_conv or_simp_conv);;

let byte_shr_list_conv =
  let th = SPECL [`l : bool list`; `NUMERAL n`] byte_shr_list in
  REWR_CONV th THENC
  cond_conv
    (RATOR_CONV (RAND_CONV length_conv) THENC
     RAND_CONV byte_width_conv THENC
     NUM_REDUCE_CONV)
    (cond_conv
      (RATOR_CONV (RAND_CONV length_conv) THENC
       NUM_REDUCE_CONV)
      ALL_CONV
      (RAND_CONV drop_conv))
    (cond_conv
      (RATOR_CONV (RAND_CONV byte_width_conv) THENC
       NUM_REDUCE_CONV)
      ALL_CONV
      (RAND_CONV
         (RAND_CONV
            (RATOR_CONV (RAND_CONV byte_width_conv) THENC
             take_conv) THENC
          drop_conv)));;

let byte_shl_list_conv =
  let th = SPECL [`l : bool list`; `NUMERAL n`] byte_shl_list in
  REWR_CONV th THENC
  RAND_CONV
    (LAND_CONV replicate_conv THENC
     append_conv);;

let byte_bit_list_conv =
  let th = SPECL [`l : bool list`; `NUMERAL n`] list_to_byte_bit in
  REWR_CONV th THENC
  andalso_conv
    (RAND_CONV byte_width_conv THENC
     NUM_REDUCE_CONV)
    (andalso_conv
      (RAND_CONV length_conv THENC
       NUM_REDUCE_CONV)
      nth_conv);;

let byte_bits_lte_conv =
  let nil_conv = REWR_CONV (CONJUNCT1 byte_bits_lte_def) in
  let cons_conv = REWR_CONV (CONJUNCT2 byte_bits_lte_def) in
  let rec rewr_conv tm =
      (nil_conv ORELSEC
       (cons_conv THENC
        (RATOR_CONV o RATOR_CONV o RAND_CONV)
          ((RATOR_CONV o RAND_CONV)
             (RATOR_CONV (RAND_CONV (TRY_CONV not_simp_conv)) THENC
              TRY_CONV and_simp_conv) THENC
           RAND_CONV
             ((RATOR_CONV o RAND_CONV)
                (RAND_CONV
                  (RAND_CONV (TRY_CONV not_simp_conv) THENC
                   TRY_CONV and_simp_conv) THENC
                 TRY_CONV not_simp_conv) THENC
              TRY_CONV and_simp_conv) THENC
           TRY_CONV or_simp_conv) THENC
        rewr_conv)) tm in
  rewr_conv;;

let byte_le_list_conv =
  let th = SYM (SPECL [`list_to_byte l1`; `list_to_byte l2`] byte_le_list) in
  REWR_CONV th THENC
  LAND_CONV list_to_byte_to_list_conv THENC
  RAND_CONV list_to_byte_to_list_conv THENC
  byte_bits_lte_conv;;

let byte_lt_list_conv =
  let th = SYM (SPECL [`list_to_byte l1`; `list_to_byte l2`] byte_lt_list) in
  REWR_CONV th THENC
  LAND_CONV list_to_byte_to_list_conv THENC
  RAND_CONV list_to_byte_to_list_conv THENC
  byte_bits_lte_conv;;

let byte_eq_list_conv =
  let th = SYM (SPECL [`list_to_byte l1`; `list_to_byte l2`]
                  byte_to_list_inj_eq) in
  REWR_CONV th THENC
  LAND_CONV list_to_byte_to_list_conv THENC
  RAND_CONV list_to_byte_to_list_conv THENC
  list_eq_conv iff_simp_conv;;

let byte_bit_conv =
  byte_width_conv ORELSEC
  list_to_byte_to_list_conv ORELSEC
  numeral_to_byte_list_conv ORELSEC
  byte_and_list_conv ORELSEC
  byte_or_list_conv ORELSEC
  byte_shr_list_conv ORELSEC
  byte_shl_list_conv ORELSEC
  byte_bit_list_conv ORELSEC
  byte_le_list_conv ORELSEC
  byte_lt_list_conv ORELSEC
  byte_eq_list_conv;;

let bit_blast_subterm_conv = byte_bit_conv ORELSEC bit_blast_subterm_conv;;
let bit_blast_conv = DEPTH_CONV bit_blast_subterm_conv;;  (* byte *)
let bit_blast_tac = CONV_TAC bit_blast_conv;;  (* byte *)

let prove_byte_list_cases n =
  let interval =
      let rec intv i n = if n = 0 then [] else i :: intv (i + 1) (n - 1) in
      intv 0 in
  let lemma1 =
      let nunary = funpow n (fun t -> mk_comb (`SUC`,t)) `0` in
      let goal = mk_eq (`LENGTH (byte_to_list w)`,nunary) in
      let tac =
          REWRITE_TAC [length_byte_to_list; byte_width_def] THEN
          NUM_REDUCE_TAC in
      prove (goal,tac) in
  let witnesses =
      let addtl l = mk_comb (`TL : bool list -> bool list`, hd l) :: l in
      let tls = rev (funpow (n - 1) addtl [`l : bool list`]) in
      map (fun t -> mk_comb (`HD : bool list -> bool`, t)) tls in
  let goal =
      let is = interval n in
      let xs = map (fun i -> mk_var ("x" ^ string_of_int i, bool_ty)) is in
      let w = mk_var ("w", `:byte`) in
      let body = mk_eq (w, mk_comb (`list_to_byte`, mk_list (xs,bool_ty))) in
      mk_forall (w, list_mk_exists (xs,body)) in
  let tac =
      GEN_TAC THEN
      CONV_TAC
        (funpow n (RAND_CONV o ABS_CONV)
           (LAND_CONV (ONCE_REWRITE_CONV [GSYM byte_to_list_to_byte]))) THEN
      MP_TAC lemma1 THEN
      SPEC_TAC (`byte_to_list w`, `l : bool list`) THEN
      REPEAT STRIP_TAC THEN
      EVERY (map EXISTS_TAC witnesses) THEN
      AP_TERM_TAC THEN
      POP_ASSUM MP_TAC THEN
      N_TAC n
        (MP_TAC (ISPEC `l : bool list` list_cases) THEN
         STRIP_TAC THENL
         [ASM_REWRITE_TAC [LENGTH; NOT_SUC];
          ALL_TAC] THEN
         POP_ASSUM SUBST_VAR_TAC THEN
         REWRITE_TAC [LENGTH; SUC_INJ; HD; TL; CONS_11] THEN
         SPEC_TAC (`t : bool list`, `l : bool list`) THEN
         GEN_TAC) THEN
      REWRITE_TAC [LENGTH_EQ_NIL] in
  prove (goal,tac);;
(*END-PARAMETRIC*)
