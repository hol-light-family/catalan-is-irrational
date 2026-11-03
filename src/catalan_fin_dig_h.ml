(* ========================================================================= *)
(* fin_dig: digit congruences (32)-(35) of the paper for H*_z, m_z, k^-, k^+. *)
(* ========================================================================= *)

needs "src/catalan_fin_dig_base.ml";;
needs "src/catalan_fin_bdry.ml";;
needs "src/catalan_fin_dig_c.ml";;

prioritize_real();;

let FIN_DIG_NUM_ARITH_TAC : tactic = fun (asl,w) ->
  let has_real tm = can (find_term (fun t -> type_of t = `:real`)) tm in
  let ths = filter (fun (_,th) -> not (has_real (concl th))) asl in
  (MAP_EVERY (MP_TAC o snd) ths THEN ARITH_TAC) (asl,w);;

let FIN_DIG_ARITH_TAC =
  REPEAT CONJ_TAC THEN (FIRST_ASSUM ACCEPT_TAC ORELSE FIN_DIG_NUM_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Basic facts.                                                              *)
(* ------------------------------------------------------------------------- *)

let FIN_DIG_ODDP = prove
 (`forall p. prime p /\ ~(p = 2) ==> exists q. 2 * q + 1 = p /\ 1 <= q /\ (p - 1) DIV 2 = q`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `p:num` PRIME_ODD) THEN ASM_REWRITE_TAC[ODD_EXISTS; ADD1] THEN
  DISCH_THEN(X_CHOOSE_THEN `q:num` SUBST_ALL_TAC) THEN EXISTS_TAC `q:num` THEN
  REWRITE_TAC[ARITH_RULE `(2 * q + 1) - 1 = 2 * q`] THEN
  CONJ_TAC THENL
   [ASM_CASES_TAC `q:num = 0` THENL [ASM_MESON_TAC[PRIME_1; ARITH_RULE `2 * 0 + 1 = 1`]; FIN_DIG_NUM_ARITH_TAC];
    MATCH_MP_TAC DIV_UNIQ THEN EXISTS_TAC `0` THEN ARITH_TAC]);;

let FIN_DIG_EPS_SQ = prove
 (`forall n. ((--(&1)) pow n) pow 2 = &1`,
  REWRITE_TAC[GSYM REAL_POW_MUL; REAL_POW_POW] THEN
  GEN_TAC THEN ONCE_REWRITE_TAC[MULT_SYM] THEN REWRITE_TAC[GSYM REAL_POW_POW] THEN
  REWRITE_TAC[REAL_POW_2; REAL_MUL_LNEG; REAL_MUL_RNEG; REAL_NEG_NEG; REAL_MUL_LID; REAL_POW_ONE]);;

let FIN_DIG_EPS_UNIT = prove
 (`forall p n. prime p ==> fin_dig_unit p ((--(&1)) pow n)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC FIN_DIG_UNIT_POW THEN
  ASM_SIMP_TAC[FIN_DIG_UNIT_NEG; FIN_DIG_UNIT_1]);;

let FIN_DIG_EPS_INV = prove
 (`forall n. inv((--(&1)) pow n) = (--(&1)) pow n`,
  REWRITE_TAC[GSYM REAL_POW_INV; REAL_INV_NEG; REAL_INV_1]);;

let FIN_DIG_HSTAR_EVEN = FIN_BDRY_HSTAR_EVEN2;;
let FIN_DIG_HSTAR_ODD = FIN_BDRY_HSTAR_ODD2;;

let FIN_DIG_NDIV_RES = prove
 (`forall p P r. 0 < r /\ r < p ==> ~(p divides (P * p + r))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `p divides r` MP_TAC THENL
   [MATCH_MP_TAC(NUMBER_RULE `p divides (P * p + r) ==> p divides r`) THEN
    ASM_REWRITE_TAC[];
    DISCH_THEN(MP_TAC o MATCH_MP DIVIDES_LE) THEN FIN_DIG_ARITH_TAC]);;

let FIN_DIG_CG_RES = prove
 (`forall p P r. prime p ==> fin_dig_cg p (&(P * p + r)) (&r)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC FIN_DIG_CG_NUM THEN
  ASM_REWRITE_TAC[] THEN NUMBER_TAC);;

let FIN_DIG_UNIT_RES = prove
 (`forall p P r. prime p /\ 0 < r /\ r < p ==> fin_dig_unit p (&(P * p + r))`,
  SIMP_TAC[FIN_DIG_UNIT_NUM; FIN_DIG_NDIV_RES]);;

let FIN_DIG_CG_INV2 = prove
 (`forall p u v. prime p /\ fin_dig_unit p u /\ fin_dig_cg p u v
           ==> fin_dig_cg p (inv u) (inv v)`,
  MESON_TAC[FIN_DIG_CG_INV]);;

let FIN_DIG_CG_ZERO_LMUL = prove
 (`forall p x y. prime p /\ fin_dig_cg p x (&0) /\ fin_zp p y ==> fin_dig_cg p (x * y) (&0)`,
  MESON_TAC[FIN_DIG_CG_ZERO_MUL]);;

let FIN_DIG_CG_ZERO_RMUL = prove
 (`forall p x y. prime p /\ fin_dig_cg p x (&0) /\ fin_zp p y ==> fin_dig_cg p (y * x) (&0)`,
  MESON_TAC[FIN_DIG_CG_ZERO_MUL]);;

let FIN_DIG_CG_UNIT = prove
 (`forall p x y. prime p /\ fin_dig_cg p x y /\ fin_dig_unit p y ==> fin_dig_unit p x`,
  MESON_TAC[FIN_DIG_CG_INV; FIN_DIG_CG_SYM]);;

(* ------------------------------------------------------------------------- *)
(* Digit calculations (32), (33) for H*_z, z = P p + r.                      *)
(* ------------------------------------------------------------------------- *)

let FIN_DIG_HSTAR_EE = prove
 (`forall p P r. prime p /\ ~(p = 2) /\ r < p /\ P + 2 <= p /\ EVEN P /\ EVEN r
           ==> fin_dig_unit p (fin_hstar (P * p + r)) /\
               fin_dig_cg p (fin_hstar (P * p + r)) (fin_hstar P * cat_c (r DIV 2))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[EVEN_EXISTS] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (X_CHOOSE_THEN `m:num` SUBST_ALL_TAC) (X_CHOOSE_THEN `n:num` SUBST_ALL_TAC)))))) THEN
  REWRITE_TAC[ARITH_RULE `(2 * m) * p + 2 * n = 2 * (m * p + n)`] THEN
  REWRITE_TAC[FIN_DIG_HSTAR_EVEN; ARITH_RULE `(2 * n) DIV 2 = n`] THEN
  SUBGOAL_THEN `fin_dig_cg p (cat_c (m * p + n)) (cat_c m * cat_c n)` ASSUME_TAC THENL
   [MATCH_MP_TAC FIN_DIG_C_NOCARRY THEN FIN_DIG_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC FIN_DIG_CG_UNIT THEN
  EXISTS_TAC `cat_c m * cat_c n` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC FIN_DIG_UNIT_MUL THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THEN MATCH_MP_TAC FIN_DIG_C_UNIT THEN FIN_DIG_ARITH_TAC);;

let FIN_DIG_HSTAR_EO = prove
 (`forall p P r. prime p /\ ~(p = 2) /\ r < p /\ P + 2 <= p /\ ODD P /\ ODD r
           ==> fin_dig_unit p (fin_hstar (P * p + r) / &p)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ODD_EXISTS; ADD1] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (X_CHOOSE_THEN `m:num` SUBST_ALL_TAC) (X_CHOOSE_THEN `n:num` SUBST_ALL_TAC)))))) THEN
  MP_TAC(SPEC `p:num` FIN_DIG_ODDP) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `q:num` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(2 * m + 1) * p + 2 * n + 1 = 2 * (m * p + (q + n + 1))` SUBST1_TAC THENL
   [UNDISCH_TAC `2 * q + 1 = p` THEN ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[FIN_DIG_HSTAR_EVEN] THEN MATCH_MP_TAC FIN_DIG_C_CARRY THEN
  FIN_DIG_ARITH_TAC);;

let FIN_DIG_HSTAR_OO = prove
 (`forall p P r. prime p /\ ~(p = 2) /\ r < p /\ P + 2 <= p /\ EVEN P /\ ODD r
           ==> fin_dig_unit p (fin_hstar (P * p + r))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[EVEN_EXISTS; ODD_EXISTS; ADD1] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (X_CHOOSE_THEN `m:num` SUBST_ALL_TAC) (X_CHOOSE_THEN `n:num` SUBST_ALL_TAC)))))) THEN
  SUBGOAL_THEN `fin_dig_unit p (&((2 * m) * p + 2 * n + 1))` MP_TAC THENL
   [MATCH_MP_TAC FIN_DIG_UNIT_RES THEN FIN_DIG_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[ARITH_RULE `(2 * m) * p + 2 * n + 1 = 2 * (m * p + n) + 1`] THEN
  DISCH_TAC THEN REWRITE_TAC[FIN_DIG_HSTAR_ODD] THEN
  MATCH_MP_TAC FIN_DIG_UNIT_INV THEN MATCH_MP_TAC FIN_DIG_UNIT_MUL THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC FIN_DIG_CG_UNIT THEN
  EXISTS_TAC `cat_c m * cat_c n` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC FIN_DIG_C_NOCARRY THEN FIN_DIG_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC FIN_DIG_UNIT_MUL THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THEN MATCH_MP_TAC FIN_DIG_C_UNIT THEN FIN_DIG_ARITH_TAC);;

let FIN_DIG_HSTAR_OE0 = prove
 (`forall p a. prime p /\ ~(p = 2) /\ 2 * a + 3 <= p
         ==> fin_dig_cg p (&p * fin_hstar ((2 * a + 1) * p))
                (((--(&1)) pow ((p - 1) DIV 2)) * fin_hstar (2 * a + 1))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `p:num` FIN_DIG_ODDP) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `q:num` STRIP_ASSUME_TAC) THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(2 * a + 1) * p = 2 * (a * p + q) + 1` SUBST1_TAC THENL
   [UNDISCH_TAC `2 * q + 1 = p` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[FIN_DIG_HSTAR_ODD] THEN
  SUBGOAL_THEN `&(2 * (a * p + q) + 1) = &(2 * a + 1) * &p` SUBST1_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_MUL; REAL_OF_NUM_EQ] THEN
    UNDISCH_TAC `2 * q + 1 = p` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `~(&p = &0)` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_EQ] THEN ASM_MESON_TAC[PRIME_IMP_NZ]; ALL_TAC] THEN
  SUBGOAL_THEN
   `&p * inv((&(2 * a + 1) * &p) * cat_c (a * p + q)) =
    inv(&(2 * a + 1) * cat_c (a * p + q))` SUBST1_TAC THENL
   [REWRITE_TAC[REAL_INV_MUL] THEN UNDISCH_TAC `~(&p = &0)` THEN
    CONV_TAC REAL_FIELD; ALL_TAC] THEN
  SUBGOAL_THEN
   `(--(&1)) pow q * inv(&(2 * a + 1) * cat_c a) =
    inv(&(2 * a + 1) * cat_c a * (--(&1)) pow q)` SUBST1_TAC THENL
   [REWRITE_TAC[REAL_INV_MUL; FIN_DIG_EPS_INV] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `fin_dig_unit p (&(2 * a + 1) * cat_c a * (--(&1)) pow q)` ASSUME_TAC THENL
   [MATCH_MP_TAC FIN_DIG_UNIT_MUL THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC FIN_DIG_UNIT_NUM_LT THEN FIN_DIG_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC FIN_DIG_UNIT_MUL THEN ASM_SIMP_TAC[FIN_DIG_EPS_UNIT] THEN
    MATCH_MP_TAC FIN_DIG_C_UNIT THEN FIN_DIG_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `fin_dig_cg p (&(2 * a + 1) * cat_c (a * p + q)) (&(2 * a + 1) * cat_c a * (--(&1)) pow q)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC FIN_DIG_CG_MUL THEN ASM_SIMP_TAC[FIN_DIG_CG_REFL; FIN_ZP_NUM] THEN
    MATCH_MP_TAC FIN_DIG_CG_TRANS THEN EXISTS_TAC `cat_c a * cat_c q` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC FIN_DIG_C_NOCARRY THEN FIN_DIG_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC FIN_DIG_CG_MUL THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC FIN_DIG_CG_REFL THEN ASM_SIMP_TAC[FIN_DIG_C_ZP];
      MP_TAC(SPEC `p:num` FIN_DIG_C_HALF) THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC FIN_DIG_CG_INV2 THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC FIN_DIG_CG_UNIT THEN
  EXISTS_TAC `&(2 * a + 1) * cat_c a * (--(&1)) pow q` THEN ASM_REWRITE_TAC[]);;

let FIN_DIG_HSTAR_OE = prove
 (`forall p P r. prime p /\ ~(p = 2) /\ r < p /\ P + 2 <= p /\ ODD P /\ EVEN r
           ==> fin_dig_cg p (&p * fin_hstar (P * p + r))
                 ((--(&1)) pow ((p - 1) DIV 2) * cat_c (r DIV 2) * fin_hstar P)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[EVEN_EXISTS; ODD_EXISTS; ADD1] THEN
  REWRITE_TAC[IMP_CONJ; LEFT_IMP_EXISTS_THM] THEN
  REPEAT DISCH_TAC THEN X_GEN_TAC `a:num` THEN DISCH_THEN SUBST_ALL_TAC THEN
  X_GEN_TAC `t:num` THEN DISCH_THEN SUBST_ALL_TAC THEN
  REWRITE_TAC[ARITH_RULE `(2 * t) DIV 2 = t`] THEN
  UNDISCH_TAC `2 * t < p` THEN SPEC_TAC(`t:num`,`t:num`) THEN
  INDUCT_TAC THENL
   [DISCH_TAC THEN REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES] THEN
    REWRITE_TAC[cat_c; MULT_CLAUSES; BINOM_REFL; real_pow; REAL_DIV_1; REAL_MUL_LID] THEN
    MATCH_MP_TAC FIN_DIG_HSTAR_OE0 THEN FIN_DIG_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
  ANTS_TAC THENL [FIN_DIG_NUM_ARITH_TAC; DISCH_TAC] THEN
  REWRITE_TAC[ARITH_RULE `x + 2 * SUC t = (x + 2 * t) + 2`; FIN_BDRY_HSTAR_STEP] THEN
  SUBGOAL_THEN
   `(--(&1)) pow ((p - 1) DIV 2) * cat_c (SUC t) * fin_hstar (2 * a + 1) =
    ((--(&1)) pow ((p - 1) DIV 2) * cat_c t * fin_hstar (2 * a + 1)) * &(2 * t + 1) / &(2 * t + 2)`
  SUBST1_TAC THENL
   [MP_TAC(SPEC `t:num` FIN_BDRY_C_REC) THEN REWRITE_TAC[ADD1] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_ADD; GSYM REAL_OF_NUM_MUL] THEN
    CONV_TAC REAL_FIELD; ALL_TAC] THEN
  REWRITE_TAC[REAL_MUL_ASSOC; real_div] THEN
  MATCH_MP_TAC FIN_DIG_CG_MUL THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC FIN_DIG_CG_MUL THEN ASM_REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN
    REWRITE_TAC[ARITH_RULE `((2 * a + 1) * p + 2 * t) + 1 = (2 * a + 1) * p + (2 * t + 1)`] THEN
    ASM_SIMP_TAC[FIN_DIG_CG_RES];
    MATCH_MP_TAC FIN_DIG_CG_INV2 THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[ARITH_RULE `((2 * a + 1) * p + 2 * t) + 2 = (2 * a + 1) * p + (2 * t + 2)`] THEN
    ASM_SIMP_TAC[FIN_DIG_CG_RES] THEN MATCH_MP_TAC FIN_DIG_UNIT_RES THEN
    FIN_DIG_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Automation: local integrality and structural congruence.                  *)
(* ------------------------------------------------------------------------- *)

let FIN_DIG_CG_SYM_EQ = prove
 (`forall p x y. fin_dig_cg p x y <=> fin_dig_cg p y x`,
  MESON_TAC[FIN_DIG_CG_SYM]);;

let FIN_DIG_UNIT_ZP1 = prove
 (`forall p u. fin_dig_unit p u ==> fin_zp p u`, SIMP_TAC[fin_dig_unit]);;

let FIN_DIG_UNIT_ZP2 = prove
 (`forall p u. fin_dig_unit p u ==> fin_zp p (inv u)`, SIMP_TAC[fin_dig_unit]);;

let FIN_DIG_CG_ZP1 = prove
 (`forall p x y. fin_dig_cg p x y ==> fin_zp p x`, SIMP_TAC[fin_dig_cg]);;

let FIN_DIG_CG_ZP2 = prove
 (`forall p x y. fin_dig_cg p x y ==> fin_zp p y`, SIMP_TAC[fin_dig_cg]);;

let FIN_DIG_E_ZP = prove
 (`forall p d. prime p ==> fin_zp p (fin_E p d)`,
  SIMP_TAC[FIN_ZP_INTEGER; FIN_DIG_E_INTEGER]);;

let FIN_DIG_EPS_ZP = prove
 (`forall p n. prime p ==> fin_zp p ((--(&1)) pow n)`,
  SIMP_TAC[FIN_DIG_EPS_UNIT; FIN_DIG_UNIT_ZP1]);;

let FIN_DIG_ZP_DIV_UNIT = prove
 (`forall p x u. prime p /\ fin_zp p x /\ fin_dig_unit p u ==> fin_zp p (x / u)`,
  SIMP_TAC[real_div; FIN_ZP_MUL; FIN_DIG_UNIT_ZP2]);;

let FIN_DIG_ZP_ATOMS = ref [FIN_ZP_NUM; FIN_ZP_0; FIN_ZP_1; FIN_DIG_E_ZP; FIN_DIG_EPS_ZP;
                            FIN_DIG_C_ZP];;

let rec FIN_DIG_ZP_TAC g =
  let mp lem th g = ACCEPT_TAC(MATCH_MP lem th) g in
  let asm_tac = FIRST_ASSUM(fun th -> FIRST
     [ACCEPT_TAC th; mp FIN_DIG_UNIT_ZP1 th; mp FIN_DIG_UNIT_ZP2 th;
      mp FIN_DIG_CG_ZP1 th; mp FIN_DIG_CG_ZP2 th]) in
  let atom_tac = FIRST (map (fun th -> MATCH_MP_TAC th THEN ASM_REWRITE_TAC[] THEN NO_TAC)
                            (!FIN_DIG_ZP_ATOMS)) in
  let bin th = MATCH_MP_TAC th THEN REPEAT CONJ_TAC THEN
               (FIRST_ASSUM ACCEPT_TAC ORELSE FIN_DIG_ZP_TAC) in
  (asm_tac ORELSE atom_tac ORELSE
   bin FIN_ZP_MUL ORELSE bin FIN_ZP_ADD ORELSE bin FIN_ZP_SUB ORELSE
   (MATCH_MP_TAC FIN_ZP_NEG THEN FIN_DIG_ZP_TAC) ORELSE
   bin FIN_ZP_POW ORELSE
   (MATCH_MP_TAC FIN_DIG_ZP_DIV_UNIT THEN REPEAT CONJ_TAC THEN
    (FIRST_ASSUM ACCEPT_TAC ORELSE FIN_DIG_ZP_TAC ORELSE
     FIRST_ASSUM(fun th g -> ACCEPT_TAC(MATCH_MP FIN_DIG_UNIT_INV th) g) ORELSE
     FIRST_ASSUM ACCEPT_TAC))) g;;

let rec FIN_DIG_CONG_TAC g =
  let asm_tac = FIRST_ASSUM(fun th -> ACCEPT_TAC th ORELSE
                   (fun g -> ACCEPT_TAC(MATCH_MP FIN_DIG_CG_SYM th) g)) in
  let refl_tac = MATCH_MP_TAC FIN_DIG_CG_REFL THEN CONJ_TAC THENL
                   [FIRST_ASSUM ACCEPT_TAC; FIN_DIG_ZP_TAC] in
  let bin th = MATCH_MP_TAC th THEN REPEAT CONJ_TAC THEN
               (FIRST_ASSUM ACCEPT_TAC ORELSE FIN_DIG_CONG_TAC) in
  (asm_tac ORELSE refl_tac ORELSE
   bin FIN_DIG_CG_MUL ORELSE bin FIN_DIG_CG_ADD ORELSE bin FIN_DIG_CG_SUB ORELSE
   (MATCH_MP_TAC FIN_DIG_CG_NEG THEN FIN_DIG_CONG_TAC) ORELSE
   bin FIN_DIG_CG_POW) g;;

(* ------------------------------------------------------------------------- *)
(* Equation (34): p m_(z-1) == E_(p-1-r) m_(P-1), z = P p + r.               *)
(* ------------------------------------------------------------------------- *)

let FIN_DIG_M_ODD0 = prove
 (`forall i. ODD i ==> cat_m i = &0`,
  SIMP_TAC[cat_m; GSYM NOT_ODD]);;

let FIN_DIG_E_ODD0 = prove
 (`forall p d. ODD d ==> fin_E p d = &0`,
  SIMP_TAC[fin_E; GSYM NOT_ODD]);;

let FIN_DIG_EVEN_REFL = prove
 (`forall p r. prime p /\ ~(p = 2) /\ r < p ==> (EVEN ((p - 1) - r) <=> EVEN r)`,
  REPEAT STRIP_TAC THEN MP_TAC(SPEC `p:num` FIN_DIG_ODDP) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `q:num` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> rand(concl th) = `p:num`)) THEN
  REWRITE_TAC[ARITH_RULE `(2 * q + 1) - 1 = 2 * q`] THEN
  REWRITE_TAC[EVEN_SUB; EVEN_DOUBLE] THEN
  ASM_CASES_TAC `2 * q <= r:num` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `r = 2 * q` SUBST1_TAC THENL [FIN_DIG_NUM_ARITH_TAC; REWRITE_TAC[EVEN_DOUBLE]]);;

let FIN_DIG_EVEN_DIGITS = prove
 (`forall p P r. prime p /\ ~(p = 2) ==> (EVEN (P * p + r) <=> (EVEN P <=> EVEN r))`,
  REPEAT STRIP_TAC THEN MP_TAC(SPEC `p:num` PRIME_ODD) THEN
  ASM_REWRITE_TAC[GSYM NOT_EVEN] THEN
  REWRITE_TAC[EVEN_ADD; EVEN_MULT] THEN CONV_TAC TAUT);;

let FIN_DIG_HSTAR_SMALL = prove
 (`forall p P. prime p /\ ~(p = 2) /\ P < p ==> fin_dig_unit p (fin_hstar P)`,
  REPEAT STRIP_TAC THEN
  DISJ_CASES_THEN (X_CHOOSE_THEN `a:num` SUBST_ALL_TAC)
   (SPEC `P:num` EVEN_OR_ODD |> REWRITE_RULE[EVEN_EXISTS; ODD_EXISTS; ADD1]) THEN
  REWRITE_TAC[FIN_DIG_HSTAR_EVEN; FIN_DIG_HSTAR_ODD] THENL
   [MATCH_MP_TAC FIN_DIG_C_UNIT THEN FIN_DIG_ARITH_TAC;
    MATCH_MP_TAC FIN_DIG_UNIT_INV THEN MATCH_MP_TAC FIN_DIG_UNIT_MUL THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC FIN_DIG_UNIT_NUM_LT THEN FIN_DIG_ARITH_TAC;
      MATCH_MP_TAC FIN_DIG_C_UNIT THEN FIN_DIG_ARITH_TAC]]);;

let FIN_DIG_ODD_PRED = prove
 (`forall z. EVEN z /\ 1 <= z ==> ODD (z - 1)`,
  INDUCT_TAC THEN REWRITE_TAC[EVEN; SUC_SUB1; GSYM NOT_EVEN; ARITH_RULE `~(1 <= 0)`] THEN
  MESON_TAC[]);;

let FIN_DIG_EVEN_PRED = prove
 (`forall z. ODD z ==> EVEN (z - 1)`,
  INDUCT_TAC THEN REWRITE_TAC[ODD; EVEN; SUC_SUB1; GSYM NOT_EVEN]);;

let FIN_DIG_M34 = prove
 (`forall p P r. prime p /\ ~(p = 2) /\ r < p /\ P + 2 <= p /\ 1 <= P * p + r
           ==> fin_dig_cg p (&p * cat_m ((P * p + r) - 1))
                 (fin_E p ((p - 1) - r) * (if P = 0 then &0 else cat_m (P - 1)))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`p:num`; `P:num`; `r:num`] FIN_DIG_EVEN_DIGITS) THEN
  MP_TAC(SPECL [`p:num`; `r:num`] FIN_DIG_EVEN_REFL) THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
  ASM_CASES_TAC `EVEN r` THENL
   [ALL_TAC;
    SUBGOAL_THEN `fin_E p ((p - 1) - r) = &0` SUBST1_TAC THENL
     [MATCH_MP_TAC FIN_DIG_E_ODD0 THEN ASM_REWRITE_TAC[GSYM NOT_EVEN]; ALL_TAC] THEN
    REWRITE_TAC[REAL_MUL_LZERO] THEN ASM_CASES_TAC `EVEN P` THENL
     [SUBGOAL_THEN `ODD (P * p + r)` ASSUME_TAC THENL
       [ASM_REWRITE_TAC[GSYM NOT_EVEN]; ALL_TAC] THEN
      FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP FIN_BDRY_M_ODD th]) THEN
      SUBGOAL_THEN `fin_dig_unit p (fin_hstar (P * p + r))` ASSUME_TAC THENL
       [MATCH_MP_TAC FIN_DIG_HSTAR_OO THEN ASM_REWRITE_TAC[GSYM NOT_EVEN]; ALL_TAC] THEN
      MATCH_MP_TAC FIN_DIG_CG_PMUL THEN ASM_REWRITE_TAC[] THEN FIN_DIG_ZP_TAC;
      SUBGOAL_THEN `ODD ((P * p + r) - 1)` ASSUME_TAC THENL
     [MATCH_MP_TAC FIN_DIG_ODD_PRED THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      ASM_SIMP_TAC[FIN_DIG_M_ODD0; REAL_MUL_RZERO] THEN
      MATCH_MP_TAC FIN_DIG_CG_REFL THEN ASM_SIMP_TAC[FIN_ZP_0]]] THEN
  ASM_CASES_TAC `EVEN P` THENL
   [SUBGOAL_THEN `ODD ((P * p + r) - 1)` ASSUME_TAC THENL
     [MATCH_MP_TAC FIN_DIG_ODD_PRED THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[FIN_DIG_M_ODD0; REAL_MUL_RZERO] THEN
    COND_CASES_TAC THEN REWRITE_TAC[REAL_MUL_RZERO] THENL
     [MATCH_MP_TAC FIN_DIG_CG_REFL THEN ASM_SIMP_TAC[FIN_ZP_0]; ALL_TAC] THEN
    SUBGOAL_THEN `ODD (P - 1)` ASSUME_TAC THENL
     [MATCH_MP_TAC FIN_DIG_ODD_PRED THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `~(P = 0)` THEN ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[FIN_DIG_M_ODD0; REAL_MUL_RZERO] THEN
    MATCH_MP_TAC FIN_DIG_CG_REFL THEN ASM_SIMP_TAC[FIN_ZP_0];
    ALL_TAC] THEN
  SUBGOAL_THEN `ODD (P * p + r) /\ ODD P /\ ~(P = 0)` STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[GSYM NOT_EVEN] THEN DISCH_THEN SUBST_ALL_TAC THEN
    ASM_MESON_TAC[EVEN]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[MATCH_MP FIN_BDRY_M_ODD (ASSUME `ODD (P * p + r)`)] THEN
  SUBGOAL_THEN `cat_m (P - 1) = &2 * fin_hstar P` SUBST1_TAC THENL
   [ASM_SIMP_TAC[FIN_BDRY_M_ODD]; ALL_TAC] THEN
  ASM_SIMP_TAC[FIN_DIG_E_REFL] THEN
  SUBGOAL_THEN `fin_dig_cg p (fin_E p r) (cat_c (r DIV 2))` ASSUME_TAC THENL
   [MATCH_MP_TAC FIN_DIG_E_CG THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `fin_dig_unit p (fin_hstar P)` ASSUME_TAC THENL
   [MATCH_MP_TAC FIN_DIG_HSTAR_SMALL THEN FIN_DIG_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`p:num`; `P:num`; `r:num`] FIN_DIG_HSTAR_OE) THEN
  ANTS_TAC THENL [FIN_DIG_ARITH_TAC; DISCH_TAC] THEN
  MATCH_MP_TAC FIN_DIG_CG_TRANS THEN
  EXISTS_TAC `&2 * ((--(&1)) pow ((p - 1) DIV 2) * cat_c (r DIV 2) * fin_hstar P)` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ONCE_REWRITE_TAC[REAL_ARITH `&p * &2 * h = &2 * (&p * h)`] THEN FIN_DIG_CONG_TAC;
    ONCE_REWRITE_TAC[REAL_ARITH `(e * x) * &2 * h = &2 * (e * x * h)`] THEN
    FIN_DIG_CONG_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Digits and summation helpers.                                             *)
(* ------------------------------------------------------------------------- *)

let FIN_DIG_DIV_DIGITS = prove
 (`forall p P r. r < p ==> (P * p + r) DIV p = P /\ (P * p + r) MOD p = r`,
  REPEAT STRIP_TAC THENL
   [MATCH_MP_TAC DIV_UNIQ THEN EXISTS_TAC `r:num`;
    MATCH_MP_TAC MOD_UNIQ THEN EXISTS_TAC `P:num`] THEN ASM_REWRITE_TAC[]);;

let FIN_DIG_DIGITS_EQ = prove
 (`forall p z. ~(p = 0) ==> (z DIV p) * p + z MOD p = z`,
  MESON_TAC[DIVISION]);;

let FIN_DIG_MULT_SET1 = prove
 (`forall p u. ~(p = 0) ==> {m | 1 <= m * p /\ m * p <= u} = 1..u DIV p`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_NUMSEG] THEN
  X_GEN_TAC `m:num` THEN ASM_SIMP_TAC[LE_RDIV_EQ] THEN
  REWRITE_TAC[ARITH_RULE `1 <= m <=> ~(m = 0)`; MULT_EQ_0] THEN
  ASM_REWRITE_TAC[MULT_SYM]);;

let FIN_DIG_SUM_MULT1 = prove
 (`forall p u f g.
        prime p /\
        (forall k. 1 <= k /\ k <= u /\ ~(p divides k) ==> fin_dig_cg p (f k) (&0)) /\
        (forall m. 1 <= m /\ m <= u DIV p ==> fin_dig_cg p (f (m * p)) (g m))
        ==> fin_dig_cg p (sum (1..u) f) (sum (1..u DIV p) g)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(p:num = 0)` ASSUME_TAC THENL [ASM_MESON_TAC[PRIME_IMP_NZ]; ALL_TAC] THEN
  FIRST_ASSUM(SUBST1_TAC o SYM o SPEC `u:num` o MATCH_MP FIN_DIG_MULT_SET1) THEN
  MATCH_MP_TAC FIN_DIG_SUM_MULTIPLES THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `m:num` THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_SIMP_TAC[LE_RDIV_EQ] THEN
  REWRITE_TAC[ARITH_RULE `1 <= m <=> ~(m = 0)`] THEN
  CONJ_TAC THENL [DISCH_THEN SUBST_ALL_TAC THEN FIN_DIG_NUM_ARITH_TAC;
                  ONCE_REWRITE_TAC[MULT_SYM] THEN ASM_REWRITE_TAC[]]);;

(* the quotient digit of anything below u = P p + r is at most P *)
let FIN_DIG_DIV_LE = prove
 (`forall p P r k. r < p /\ k <= P * p + r ==> k DIV p <= P`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(p:num = 0)` ASSUME_TAC THENL [FIN_DIG_NUM_ARITH_TAC; ALL_TAC] THEN
  TRANS_TAC LE_TRANS `(P * p + r) DIV p` THEN ASM_SIMP_TAC[DIV_MONO] THEN
  ASM_SIMP_TAC[FIN_DIG_DIV_DIGITS; LE_REFL]);;

(* ------------------------------------------------------------------------- *)
(* Starting congruence (35) for k^-, odd index.                              *)
(* ------------------------------------------------------------------------- *)

let FIN_DIG_ODD_DIGITS = prove
 (`forall p m. prime p /\ ~(p = 2) ==> (ODD (m * p) <=> ODD m)`,
  REPEAT STRIP_TAC THEN MP_TAC(SPEC `p:num` PRIME_ODD) THEN
  ASM_REWRITE_TAC[ODD_MULT] THEN CONV_TAC TAUT);;

let FIN_DIG_KM_ODDSUM = prove
 (`forall p P r. prime p /\ ~(p = 2) /\ r < p /\ P < p
           ==> fin_dig_cg p (sum (1..P * p + r) (\z. &p * (if ODD z then &2 / &z else &0)))
                            (sum (1..P) (\m. if ODD m then &2 / &m else &0))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`p:num`; `P:num`; `r:num`] FIN_DIG_DIV_DIGITS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> GEN_REWRITE_TAC (RAND_CONV o LAND_CONV o RAND_CONV) [GSYM(CONJUNCT1 th)]) THEN
  MATCH_MP_TAC FIN_DIG_SUM_MULT1 THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `~(&p = &0)` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_EQ] THEN ASM_MESON_TAC[PRIME_IMP_NZ]; ALL_TAC] THEN
  CONJ_TAC THENL
   [X_GEN_TAC `k:num` THEN STRIP_TAC THEN MATCH_MP_TAC FIN_DIG_CG_PMUL THEN
    ASM_REWRITE_TAC[] THEN COND_CASES_TAC THEN ASM_SIMP_TAC[FIN_ZP_0] THEN
    MATCH_MP_TAC FIN_ZP_DIV_NUM THEN ASM_SIMP_TAC[FIN_ZP_NUM];
    ALL_TAC] THEN
  X_GEN_TAC `m:num` THEN STRIP_TAC THEN
  ASM_SIMP_TAC[FIN_DIG_ODD_DIGITS] THEN
  SUBGOAL_THEN `m:num < p` ASSUME_TAC THENL
   [UNDISCH_TAC `m <= (P * p + r) DIV p` THEN ASM_SIMP_TAC[FIN_DIG_DIV_DIGITS] THEN
    FIN_DIG_NUM_ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `ODD m` THEN ASM_REWRITE_TAC[] THENL
   [ALL_TAC; REWRITE_TAC[REAL_MUL_RZERO] THEN MATCH_MP_TAC FIN_DIG_CG_REFL THEN
    ASM_SIMP_TAC[FIN_ZP_0]] THEN
  SUBGOAL_THEN `&p * &2 / &(m * p) = &2 / &m` SUBST1_TAC THENL
   [REWRITE_TAC[GSYM REAL_OF_NUM_MUL] THEN
    SUBGOAL_THEN `~(&m = &0)` MP_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_EQ] THEN FIN_DIG_NUM_ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `~(&p = &0)` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  MATCH_MP_TAC FIN_DIG_CG_REFL THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC FIN_ZP_DIV_NUM THEN ASM_SIMP_TAC[FIN_ZP_NUM] THEN
  DISCH_THEN(MP_TAC o MATCH_MP DIVIDES_LE) THEN FIN_DIG_NUM_ARITH_TAC);;

let FIN_DIG_KMINUS35_ODD = prove
 (`forall p P r. prime p /\ ~(p = 2) /\ r < p /\ P + 2 <= p /\ ODD (P * p + r)
           ==> fin_dig_cg p (&p pow 2 * cat_kminus (P * p + r))
                            (fin_E p ((p - 1) - r) * cat_kminus P)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP FIN_BDRY_KMINUS_ODD th]) THEN
  SUBGOAL_THEN
   `&p pow 2 * fin_hstar (P * p + r) * sum (1..P * p + r) (\z. if ODD z then &2 / &z else &0) =
    (&p * fin_hstar (P * p + r)) *
    sum (1..P * p + r) (\z. &p * (if ODD z then &2 / &z else &0))` SUBST1_TAC THENL
   [REWRITE_TAC[SUM_LMUL] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`p:num`; `P:num`; `r:num`] FIN_DIG_KM_ODDSUM) THEN
  ANTS_TAC THENL [FIN_DIG_ARITH_TAC; DISCH_TAC] THEN
  MP_TAC(SPECL [`p:num`; `P:num`; `r:num`] FIN_DIG_EVEN_DIGITS) THEN
  MP_TAC(SPECL [`p:num`; `r:num`] FIN_DIG_EVEN_REFL) THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
  ASM_CASES_TAC `EVEN r` THENL
   [ALL_TAC;
    SUBGOAL_THEN `fin_E p ((p - 1) - r) = &0` SUBST1_TAC THENL
     [MATCH_MP_TAC FIN_DIG_E_ODD0 THEN ASM_REWRITE_TAC[GSYM NOT_EVEN]; ALL_TAC] THEN
    REWRITE_TAC[REAL_MUL_LZERO] THEN
    SUBGOAL_THEN `fin_dig_unit p (fin_hstar (P * p + r))` ASSUME_TAC THENL
     [MATCH_MP_TAC FIN_DIG_HSTAR_OO THEN ASM_REWRITE_TAC[GSYM NOT_EVEN] THEN
      UNDISCH_TAC `ODD (P * p + r)` THEN ASM_REWRITE_TAC[GSYM NOT_EVEN] THEN
      CONV_TAC TAUT; ALL_TAC] THEN
    MATCH_MP_TAC FIN_DIG_CG_ZERO_LMUL THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [MATCH_MP_TAC FIN_DIG_CG_PMUL THEN ASM_REWRITE_TAC[] THEN FIN_DIG_ZP_TAC;
                    FIN_DIG_ZP_TAC]] THEN
  SUBGOAL_THEN `ODD P` ASSUME_TAC THENL
   [UNDISCH_TAC `ODD (P * p + r)` THEN ASM_REWRITE_TAC[GSYM NOT_EVEN]; ALL_TAC] THEN
  MP_TAC(SPECL [`p:num`; `P:num`; `r:num`] FIN_DIG_HSTAR_OE) THEN
  ANTS_TAC THENL [FIN_DIG_ARITH_TAC; DISCH_TAC] THEN
  ASM_SIMP_TAC[FIN_DIG_E_REFL; FIN_BDRY_KMINUS_ODD] THEN
  SUBGOAL_THEN `fin_dig_cg p (fin_E p r) (cat_c (r DIV 2))` ASSUME_TAC THENL
   [MATCH_MP_TAC FIN_DIG_E_CG THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `fin_dig_unit p (fin_hstar P)` ASSUME_TAC THENL
   [MATCH_MP_TAC FIN_DIG_HSTAR_SMALL THEN FIN_DIG_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC FIN_DIG_CG_TRANS THEN
  EXISTS_TAC `((--(&1)) pow ((p - 1) DIV 2) * cat_c (r DIV 2) * fin_hstar P) *
              sum (1..P) (\m. if ODD m then &2 / &m else &0)` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [FIN_DIG_CONG_TAC;
    ONCE_REWRITE_TAC[REAL_ARITH `(e * x) * h * s = (e * x * h) * s`] THEN
    FIN_DIG_CONG_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Starting congruence (35) for k^-, even index: the block calculation.      *)
(* ------------------------------------------------------------------------- *)

let fin_dig_kmg = new_definition
 `fin_dig_kmg p z = if EVEN z then &2 * (&p / (&z * fin_hstar z)) pow 2 else &0`;;

let fin_dig_kmt = new_definition
 `fin_dig_kmt z = if EVEN z then &2 / (&z pow 2 * fin_hstar z pow 2) else &0`;;

let FIN_DIG_PNZ = prove
 (`forall p. prime p ==> ~(&p = &0)`,
  REWRITE_TAC[REAL_OF_NUM_EQ] THEN MESON_TAC[PRIME_IMP_NZ]);;

let FIN_DIG_KB = prove
 (`forall p Q t. prime p /\ ~(p = 2) /\ 0 < t /\ t < p /\ Q + 2 <= p /\ EVEN Q /\ EVEN t
           ==> fin_dig_cg p (&p / (&(Q * p + t) * fin_hstar (Q * p + t))) (&0)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[real_div] THEN
  MATCH_MP_TAC FIN_DIG_CG_PMUL THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC FIN_DIG_UNIT_ZP2 THEN MATCH_MP_TAC FIN_DIG_UNIT_MUL THEN
  ASM_SIMP_TAC[FIN_DIG_UNIT_RES] THEN
  MP_TAC(SPECL [`p:num`; `Q:num`; `t:num`] FIN_DIG_HSTAR_EE) THEN
  ANTS_TAC THENL [FIN_DIG_ARITH_TAC; SIMP_TAC[]]);;

let FIN_DIG_KMG_ZERO = prove
 (`forall p z. prime p /\ fin_dig_cg p (&p / (&z * fin_hstar z)) (&0)
         ==> fin_dig_cg p (fin_dig_kmg p z) (&0)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[fin_dig_kmg] THEN COND_CASES_TAC THENL
   [MATCH_MP_TAC FIN_DIG_CG_ZERO_RMUL THEN ASM_SIMP_TAC[FIN_ZP_NUM] THEN
    REWRITE_TAC[REAL_POW_2] THEN MATCH_MP_TAC FIN_DIG_CG_ZERO_LMUL THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[FIN_DIG_CG_ZP1];
    MATCH_MP_TAC FIN_DIG_CG_REFL THEN ASM_SIMP_TAC[FIN_ZP_0]]);;

let FIN_DIG_KA = prove
 (`forall p Q t. prime p /\ ~(p = 2) /\ t < p /\ Q + 2 <= p /\ 1 <= Q * p + t /\
           EVEN (Q * p + t)
           ==> fin_zp p (&p / (&(Q * p + t) * fin_hstar (Q * p + t)))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`p:num`; `Q:num`; `t:num`] FIN_DIG_EVEN_DIGITS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP FIN_DIG_PNZ) THEN
  ASM_CASES_TAC `t:num = 0` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    SUBGOAL_THEN `EVEN Q /\ 0 < Q` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `EVEN Q <=> EVEN 0` THEN REWRITE_TAC[EVEN] THEN
      DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `1 <= Q * p + 0` THEN REWRITE_TAC[ADD_CLAUSES] THEN
      ASM_CASES_TAC `Q:num = 0` THEN ASM_REWRITE_TAC[MULT_CLAUSES] THEN FIN_DIG_NUM_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(SPECL [`p:num`; `Q:num`; `0`] FIN_DIG_HSTAR_EE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[EVEN] THEN FIN_DIG_ARITH_TAC; STRIP_TAC] THEN
    SUBGOAL_THEN `&p / (&(Q * p + 0) * fin_hstar (Q * p + 0)) = inv(&Q * fin_hstar (Q * p + 0))`
    SUBST1_TAC THENL
     [REWRITE_TAC[ADD_CLAUSES; GSYM REAL_OF_NUM_MUL; REAL_INV_MUL] THEN
      UNDISCH_TAC `~(&p = &0)` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
    MATCH_MP_TAC FIN_DIG_UNIT_ZP2 THEN MATCH_MP_TAC FIN_DIG_UNIT_MUL THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC FIN_DIG_UNIT_NUM_LT THEN FIN_DIG_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `EVEN t` THENL
   [MATCH_MP_TAC FIN_DIG_CG_ZP1 THEN EXISTS_TAC `&0` THEN
    MATCH_MP_TAC FIN_DIG_KB THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `EVEN Q <=> EVEN t` THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    FIN_DIG_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`p:num`; `Q:num`; `t:num`] FIN_DIG_HSTAR_EO) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[GSYM NOT_EVEN] THEN
    UNDISCH_TAC `EVEN Q <=> EVEN t` THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    FIN_DIG_ARITH_TAC; DISCH_TAC] THEN
  SUBGOAL_THEN `&p / (&(Q * p + t) * fin_hstar (Q * p + t)) =
                inv(&(Q * p + t) * (fin_hstar (Q * p + t) / &p))` SUBST1_TAC THENL
   [REWRITE_TAC[real_div; REAL_INV_MUL; REAL_INV_INV] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC FIN_DIG_UNIT_ZP2 THEN MATCH_MP_TAC FIN_DIG_UNIT_MUL THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC FIN_DIG_UNIT_RES THEN FIN_DIG_ARITH_TAC);;

let FIN_DIG_KA_GEN = prove
 (`forall p z. prime p /\ ~(p = 2) /\ z DIV p + 2 <= p /\ 1 <= z /\ EVEN z
         ==> fin_zp p (&p / (&z * fin_hstar z))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(p:num = 0)` ASSUME_TAC THENL [ASM_MESON_TAC[PRIME_IMP_NZ]; ALL_TAC] THEN
  SUBGOAL_THEN `z = (z DIV p) * p + z MOD p` SUBST1_TAC THENL
   [ASM_SIMP_TAC[FIN_DIG_DIGITS_EQ]; ALL_TAC] THEN
  MATCH_MP_TAC FIN_DIG_KA THEN ASM_SIMP_TAC[FIN_DIG_DIGITS_EQ; DIVISION]);;

let FIN_DIG_CG_NEGRES = prove
 (`forall p M k. prime p /\ k <= M * p ==> fin_dig_cg p (&(M * p - k)) (--(&k))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC FIN_DIG_CG_INTEGER THEN
  ASM_SIMP_TAC[INTEGER_CLOSED] THEN EXISTS_TAC `&M:real` THEN
  ASM_SIMP_TAC[INTEGER_CLOSED; GSYM REAL_OF_NUM_SUB] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_MUL] THEN REAL_ARITH_TAC);;

let FIN_DIG_KC0 = prove
 (`forall p m. prime p /\ ~(p = 2) /\ EVEN m /\ 2 <= m /\ m + 2 <= p
         ==> fin_dig_cg p (&p / (&(m * p) * fin_hstar (m * p))) (inv(&m * fin_hstar m))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP FIN_DIG_PNZ) THEN
  MP_TAC(SPECL [`p:num`; `m:num`; `0`] FIN_DIG_HSTAR_EE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[EVEN] THEN FIN_DIG_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[ADD_CLAUSES; ARITH_RULE `0 DIV 2 = 0`; FIN_BDRY_C_0; REAL_MUL_RID] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `&p / (&(m * p) * fin_hstar (m * p)) = inv(&m * fin_hstar (m * p))`
  SUBST1_TAC THENL
   [REWRITE_TAC[GSYM REAL_OF_NUM_MUL; REAL_INV_MUL] THEN
    UNDISCH_TAC `~(&p = &0)` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  SUBGOAL_THEN `fin_dig_unit p (&m)` ASSUME_TAC THENL
   [MATCH_MP_TAC FIN_DIG_UNIT_NUM_LT THEN FIN_DIG_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC FIN_DIG_CG_INV2 THEN ASM_SIMP_TAC[FIN_DIG_UNIT_MUL] THEN
  FIN_DIG_CONG_TAC);;

let FIN_DIG_KC = prove
 (`forall p m j. prime p /\ ~(p = 2) /\ EVEN m /\ 2 <= m /\ m + 2 <= p /\ 2 * j < p
           ==> fin_dig_cg p (&p / (&(m * p - 2 * j) * fin_hstar (m * p - 2 * j)))
                            (cat_c j / (&m * fin_hstar m))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN REPLICATE_TAC 5 DISCH_TAC THEN
  SPEC_TAC(`j:num`,`j:num`) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP FIN_DIG_PNZ) THEN
  SUBGOAL_THEN `2 * p <= m * p` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[LE_MULT_RCANCEL]; ALL_TAC] THEN
  SUBGOAL_THEN `fin_dig_unit p (&m * fin_hstar m)` ASSUME_TAC THENL
   [MATCH_MP_TAC FIN_DIG_UNIT_MUL THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC FIN_DIG_UNIT_NUM_LT; MATCH_MP_TAC FIN_DIG_HSTAR_SMALL] THEN
    FIN_DIG_ARITH_TAC; ALL_TAC] THEN
  INDUCT_TAC THENL
   [DISCH_TAC THEN REWRITE_TAC[MULT_CLAUSES; SUB_0; FIN_BDRY_C_0] THEN
    REWRITE_TAC[real_div; REAL_MUL_LID] THEN REWRITE_TAC[GSYM real_div] THEN
    MATCH_MP_TAC FIN_DIG_KC0 THEN FIN_DIG_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
  ANTS_TAC THENL [FIN_DIG_ARITH_TAC; DISCH_TAC] THEN
  ABBREV_TAC `y = m * p - 2 * SUC j` THEN
  SUBGOAL_THEN `m * p - 2 * j = y + 2` SUBST_ALL_TAC THENL
   [EXPAND_TAC "y" THEN FIN_DIG_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `fin_dig_cg p (&(y + 1)) (--(&(2 * j + 1)))` ASSUME_TAC THENL
   [SUBGOAL_THEN `y + 1 = m * p - (2 * j + 1)` SUBST1_TAC THENL
     [EXPAND_TAC "y" THEN FIN_DIG_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC FIN_DIG_CG_NEGRES THEN FIN_DIG_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `fin_dig_cg p (&y) (--(&(2 * j + 2)))` ASSUME_TAC THENL
   [EXPAND_TAC "y" THEN REWRITE_TAC[ARITH_RULE `2 * SUC j = 2 * j + 2`] THEN
    MATCH_MP_TAC FIN_DIG_CG_NEGRES THEN FIN_DIG_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `fin_dig_unit p (--(&(2 * j + 2)))` ASSUME_TAC THENL
   [MATCH_MP_TAC FIN_DIG_UNIT_NEG THEN MATCH_MP_TAC FIN_DIG_UNIT_NUM_LT THEN
    FIN_DIG_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `~(&y = &0) /\ ~(&(y + 1) = &0) /\ ~(&(y + 2) = &0)` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_EQ] THEN EXPAND_TAC "y" THEN FIN_DIG_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPEC `y:num` FIN_BDRY_HSTAR_NZ) THEN DISCH_TAC THEN
  MP_TAC(SPEC `y + 2` FIN_BDRY_HSTAR_NZ) THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `&p / (&y * fin_hstar y) =
    (&p / (&(y + 2) * fin_hstar (y + 2))) * &(y + 1) / &y`
  SUBST1_TAC THENL
   [REWRITE_TAC[FIN_BDRY_HSTAR_STEP] THEN
    UNDISCH_TAC `~(&y = &0)` THEN UNDISCH_TAC `~(&(y + 1) = &0)` THEN
    UNDISCH_TAC `~(&(y + 2) = &0)` THEN UNDISCH_TAC `~(fin_hstar y = &0)` THEN
    UNDISCH_TAC `~(&p = &0)` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  SUBGOAL_THEN
   `cat_c (SUC j) / (&m * fin_hstar m) =
    (cat_c j / (&m * fin_hstar m)) * (--(&(2 * j + 1))) / (--(&(2 * j + 2)))`
  SUBST1_TAC THENL
   [REWRITE_TAC[ADD1; FIN_BDRY_C_STEP] THEN REWRITE_TAC[real_div; REAL_INV_NEG] THEN
    REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC FIN_DIG_CG_MUL THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC FIN_DIG_CG_DIV THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC FIN_DIG_CG_UNIT THEN EXISTS_TAC `--(&(2 * j + 2))` THEN
  ASM_REWRITE_TAC[]);;

let FIN_DIG_SUM_EVEN = prove
 (`forall f s. sum (0..2 * s) (\l. if EVEN l then f (l DIV 2) else &0) = sum (0..s) f`,
  GEN_TAC THEN INDUCT_TAC THENL
   [REWRITE_TAC[MULT_CLAUSES; SUM_SING_NUMSEG; EVEN; ARITH_RULE `0 DIV 2 = 0`];
    REWRITE_TAC[ARITH_RULE `2 * SUC s = SUC(SUC(2 * s))`; SUM_CLAUSES_NUMSEG; LE_0] THEN
    ASM_REWRITE_TAC[EVEN; EVEN_DOUBLE; ARITH_RULE `SUC(SUC(2 * s)) DIV 2 = SUC s`] THEN
    REAL_ARITH_TAC]);;

let FIN_DIG_KM_RUN = prove
 (`forall p Q n. prime p /\ ~(p = 2) /\ EVEN Q /\ Q + 2 <= p /\ n <= p
           ==> fin_dig_cg p (sum (1..n) (\t. fin_dig_kmg p (t + Q * p))) (&0)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 = sum (1..n) (\t. &0)` SUBST1_TAC THENL
   [REWRITE_TAC[SUM_0]; ALL_TAC] THEN
  MATCH_MP_TAC FIN_DIG_CG_SUM THEN ASM_REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
  X_GEN_TAC `t:num` THEN STRIP_TAC THEN
  ASM_CASES_TAC `EVEN (t + Q * p)` THENL
   [ALL_TAC;
    ASM_REWRITE_TAC[fin_dig_kmg] THEN MATCH_MP_TAC FIN_DIG_CG_REFL THEN
    ASM_SIMP_TAC[FIN_ZP_0]] THEN
  SUBGOAL_THEN `EVEN t` ASSUME_TAC THENL
   [UNDISCH_TAC `EVEN (t + Q * p)` THEN ASM_REWRITE_TAC[EVEN_ADD; EVEN_MULT]; ALL_TAC] THEN
  SUBGOAL_THEN `t:num < p` ASSUME_TAC THENL
   [REWRITE_TAC[LT_LE] THEN CONJ_TAC THENL [FIN_DIG_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN SUBST_ALL_TAC THEN
    MP_TAC(SPEC `p:num` PRIME_ODD) THEN ASM_REWRITE_TAC[GSYM NOT_EVEN];
    ALL_TAC] THEN
  MATCH_MP_TAC FIN_DIG_KMG_ZERO THEN ASM_REWRITE_TAC[] THEN
  ONCE_REWRITE_TAC[ADD_SYM] THEN MATCH_MP_TAC FIN_DIG_KB THEN FIN_DIG_ARITH_TAC);;

let FIN_DIG_KM_B2 = prove
 (`forall p m. prime p /\ ~(p = 2) /\ EVEN m /\ 2 <= m /\ m + 2 <= p
         ==> fin_dig_cg p (sum (0..p - 1) (\i. fin_dig_kmg p (m * p - i)))
                          ((--(&1)) pow ((p - 1) DIV 2) * fin_dig_kmt m)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `p:num` FIN_DIG_ODDP) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `q:num` STRIP_ASSUME_TAC) THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `p - 1 = 2 * q` SUBST1_TAC THENL [FIN_DIG_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `fin_dig_unit p (&m * fin_hstar m)` ASSUME_TAC THENL
   [MATCH_MP_TAC FIN_DIG_UNIT_MUL THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC FIN_DIG_UNIT_NUM_LT; MATCH_MP_TAC FIN_DIG_HSTAR_SMALL] THEN
    FIN_DIG_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `2 * p <= m * p` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[LE_MULT_RCANCEL]; ALL_TAC] THEN
  MATCH_MP_TAC FIN_DIG_CG_TRANS THEN
  EXISTS_TAC `sum (0..2 * q) (\l. if EVEN l then (\j. &2 * (cat_c j / (&m * fin_hstar m)) pow 2) (l DIV 2) else &0)` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC FIN_DIG_CG_SUM THEN ASM_REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    SUBGOAL_THEN `EVEN (m * p - i) <=> EVEN i` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[EVEN_SUB; EVEN_MULT] THEN
      SUBGOAL_THEN `~(m * p <= i:num)` (fun th -> REWRITE_TAC[th]) THEN FIN_DIG_ARITH_TAC;
      ALL_TAC] THEN
    ASM_REWRITE_TAC[fin_dig_kmg] THEN ASM_CASES_TAC `EVEN i` THEN ASM_REWRITE_TAC[] THENL
     [ALL_TAC; MATCH_MP_TAC FIN_DIG_CG_REFL THEN ASM_SIMP_TAC[FIN_ZP_0]] THEN
    FIRST_X_ASSUM(X_CHOOSE_THEN `j:num` SUBST_ALL_TAC o REWRITE_RULE[EVEN_EXISTS]) THEN
    REWRITE_TAC[ARITH_RULE `(2 * j) DIV 2 = j`] THEN
    MP_TAC(SPECL [`p:num`; `m:num`; `j:num`] FIN_DIG_KC) THEN
    ANTS_TAC THENL [FIN_DIG_ARITH_TAC; DISCH_TAC] THEN
    FIN_DIG_CONG_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\j. &2 * (cat_c j / (&m * fin_hstar m)) pow 2`; `q:num`] FIN_DIG_SUM_EVEN) THEN
  REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN
   `sum (0..q) (\j. &2 * (cat_c j / (&m * fin_hstar m)) pow 2) =
    (&2 / (&m * fin_hstar m) pow 2) * sum (0..q) (\j. cat_c j pow 2)` SUBST1_TAC THENL
   [REWRITE_TAC[GSYM SUM_LMUL] THEN MATCH_MP_TAC SUM_EQ THEN
    REWRITE_TAC[real_div; REAL_POW_MUL; REAL_POW_INV] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(--(&1)) pow q * fin_dig_kmt m =
                (&2 / (&m * fin_hstar m) pow 2) * (--(&1)) pow q` SUBST1_TAC THENL
   [ASM_REWRITE_TAC[fin_dig_kmt; REAL_POW_MUL] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC FIN_DIG_CG_MUL THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC FIN_DIG_CG_REFL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC FIN_DIG_ZP_DIV_UNIT THEN ASM_SIMP_TAC[FIN_ZP_NUM; FIN_DIG_UNIT_POW];
    MP_TAC(SPEC `p:num` FIN_DIG_C_SQSUM) THEN ASM_REWRITE_TAC[]]);;

let FIN_DIG_KM_BLOCK = prove
 (`forall p. prime p /\ ~(p = 2)
       ==> forall a. 2 * a + 2 <= p
         ==> fin_dig_cg p (sum (1..(2 * a) * p) (fin_dig_kmg p))
                ((--(&1)) pow ((p - 1) DIV 2) * sum (1..2 * a) fin_dig_kmt)`,
  GEN_TAC THEN STRIP_TAC THEN INDUCT_TAC THENL
   [DISCH_TAC THEN REWRITE_TAC[MULT_CLAUSES; SUM_CLAUSES_NUMSEG; ARITH_EQ] THEN
    REWRITE_TAC[REAL_MUL_RZERO] THEN MATCH_MP_TAC FIN_DIG_CG_REFL THEN
    ASM_SIMP_TAC[FIN_ZP_0];
    ALL_TAC] THEN
  DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
  ANTS_TAC THENL [FIN_DIG_ARITH_TAC; DISCH_TAC] THEN
  SUBGOAL_THEN `(2 * SUC a) * p = ((2 * a) * p + p) + (p:num)` SUBST1_TAC THENL
   [ARITH_TAC; ALL_TAC] THEN
  SIMP_TAC[SUM_ADD_SPLIT; ARITH_RULE `1 <= (x + p) + 1`; ARITH_RULE `1 <= x + 1`] THEN
  REWRITE_TAC[ARITH_RULE `2 * SUC a = SUC(SUC(2 * a))`; SUM_CLAUSES_NUMSEG;
              ARITH_RULE `1 <= SUC n`] THEN
  REWRITE_TAC[ARITH_RULE `SUC(SUC(2 * a)) = 2 * a + 2`; ADD1] THEN
  SUBGOAL_THEN `fin_dig_kmt (2 * a + 1) = &0` SUBST1_TAC THENL
   [REWRITE_TAC[fin_dig_kmt; EVEN_ADD; EVEN_DOUBLE; ARITH_EVEN]; ALL_TAC] THEN
  REWRITE_TAC[REAL_ADD_RID; REAL_ADD_LDISTRIB] THEN
  REWRITE_TAC[GSYM REAL_ADD_ASSOC] THEN MATCH_MP_TAC FIN_DIG_CG_ADD THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[REAL_MUL_RZERO] THEN
  MATCH_MP_TAC FIN_DIG_CG_ADD THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [SUBGOAL_THEN `(2 * a) * p + 1 = 1 + (2 * a) * p /\ (2 * a) * p + p = p + (2 * a) * (p:num)`
      (fun th -> REWRITE_TAC[th]) THENL [ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[SUM_OFFSET] THEN MATCH_MP_TAC FIN_DIG_KM_RUN THEN
    ASM_REWRITE_TAC[EVEN_DOUBLE] THEN FIN_DIG_ARITH_TAC;
    ALL_TAC] THEN
  ONCE_REWRITE_TAC[SUM_REFLECT] THEN
  SUBGOAL_THEN `~(((2 * a) * p + p) + p < ((2 * a) * p + p) + (1:num))`
    (fun th -> REWRITE_TAC[th]) THENL [FIN_DIG_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `((2 * a) * p + p) + p = (2 * a + 2) * (p:num)` SUBST1_TAC THENL
   [ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(2 * a + 2) * p - ((((2 * a) * p + p) + 1)) = p - (1:num)` SUBST1_TAC THENL
   [ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC FIN_DIG_KM_B2 THEN
  REWRITE_TAC[EVEN_ADD; EVEN_DOUBLE; ARITH_EVEN] THEN FIN_DIG_ARITH_TAC);;

let FIN_DIG_KMT_ETA = prove
 (`fin_dig_kmt = (\z. if EVEN z then &2 / (&z pow 2 * fin_hstar z pow 2) else &0)`,
  REWRITE_TAC[FUN_EQ_THM; fin_dig_kmt]);;

let FIN_DIG_KMT_SUM_ZP = prove
 (`forall p P. prime p /\ ~(p = 2) /\ P < p ==> fin_zp p (sum (1..P) fin_dig_kmt)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC FIN_ZP_SUM THEN
  ASM_REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN X_GEN_TAC `z:num` THEN STRIP_TAC THEN
  REWRITE_TAC[fin_dig_kmt] THEN COND_CASES_TAC THEN ASM_SIMP_TAC[FIN_ZP_0] THEN
  MATCH_MP_TAC FIN_DIG_ZP_DIV_UNIT THEN ASM_SIMP_TAC[FIN_ZP_NUM] THEN
  MATCH_MP_TAC FIN_DIG_UNIT_MUL THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THEN
  MATCH_MP_TAC FIN_DIG_UNIT_POW THEN ASM_REWRITE_TAC[] THENL
   [MATCH_MP_TAC FIN_DIG_UNIT_NUM_LT; MATCH_MP_TAC FIN_DIG_HSTAR_SMALL] THEN
  FIN_DIG_ARITH_TAC);;

let FIN_DIG_KMINUS35_EVEN = prove
 (`forall p P r. prime p /\ ~(p = 2) /\ r < p /\ P + 2 <= p /\ EVEN (P * p + r)
           ==> fin_dig_cg p (&p pow 2 * cat_kminus (P * p + r))
                            (fin_E p ((p - 1) - r) * cat_kminus P)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP FIN_BDRY_KMINUS_EVEN th]) THEN
  SUBGOAL_THEN
   `&p pow 2 * fin_hstar (P * p + r) *
    sum (1..P * p + r) (\z. if EVEN z then &2 / (&z pow 2 * fin_hstar z pow 2) else &0) =
    fin_hstar (P * p + r) * sum (1..P * p + r) (fin_dig_kmg p)` SUBST1_TAC THENL
   [MATCH_MP_TAC(REAL_RING `a * s = t ==> a * h * s = h * t:real`) THEN
    REWRITE_TAC[GSYM SUM_LMUL] THEN MATCH_MP_TAC SUM_EQ THEN
    X_GEN_TAC `z:num` THEN DISCH_TAC THEN REWRITE_TAC[fin_dig_kmg] THEN
    COND_CASES_TAC THEN REWRITE_TAC[REAL_MUL_RZERO] THEN
    REWRITE_TAC[real_div; REAL_POW_MUL; REAL_POW_INV; REAL_INV_MUL] THEN
    REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`p:num`; `P:num`; `r:num`] FIN_DIG_EVEN_DIGITS) THEN
  MP_TAC(SPECL [`p:num`; `r:num`] FIN_DIG_EVEN_REFL) THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
  ASM_CASES_TAC `EVEN r` THENL
   [ALL_TAC;
    SUBGOAL_THEN `fin_E p ((p - 1) - r) = &0` SUBST1_TAC THENL
     [MATCH_MP_TAC FIN_DIG_E_ODD0 THEN ASM_REWRITE_TAC[GSYM NOT_EVEN]; ALL_TAC] THEN
    REWRITE_TAC[REAL_MUL_LZERO] THEN
    MATCH_MP_TAC FIN_DIG_CG_ZERO_LMUL THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MP_TAC(SPECL [`p:num`; `P:num`; `r:num`] FIN_DIG_HSTAR_EO) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[GSYM NOT_EVEN] THEN
        UNDISCH_TAC `EVEN (P * p + r)` THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
        FIN_DIG_ARITH_TAC; DISCH_TAC] THEN
      SUBGOAL_THEN `fin_hstar (P * p + r) = &p * (fin_hstar (P * p + r) / &p)` SUBST1_TAC THENL
       [FIRST_ASSUM(ASSUME_TAC o MATCH_MP FIN_DIG_PNZ) THEN
        UNDISCH_TAC `~(&p = &0)` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
      MATCH_MP_TAC FIN_DIG_CG_PMUL THEN ASM_REWRITE_TAC[] THEN FIN_DIG_ZP_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC FIN_ZP_SUM THEN ASM_REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
    X_GEN_TAC `z:num` THEN STRIP_TAC THEN REWRITE_TAC[fin_dig_kmg] THEN
    COND_CASES_TAC THEN ASM_SIMP_TAC[FIN_ZP_0] THEN
    MATCH_MP_TAC FIN_ZP_MUL THEN ASM_SIMP_TAC[FIN_ZP_NUM] THEN
    MATCH_MP_TAC FIN_ZP_POW THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC FIN_DIG_KA_GEN THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(SPECL [`p:num`; `P:num`; `r:num`; `z:num`] FIN_DIG_DIV_LE) THEN
    ASM_REWRITE_TAC[] THEN FIN_DIG_ARITH_TAC] THEN
  SUBGOAL_THEN `EVEN P` ASSUME_TAC THENL
   [UNDISCH_TAC `EVEN (P * p + r)` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(SPECL [`p:num`; `P:num`; `r:num`] FIN_DIG_HSTAR_EE) THEN
  ANTS_TAC THENL [FIN_DIG_ARITH_TAC; STRIP_TAC] THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `a:num` SUBST_ALL_TAC o REWRITE_RULE[EVEN_EXISTS] o
    check (fun th -> concl th = `EVEN P`)) THEN
  MP_TAC(SPECL [`p:num`] FIN_DIG_KM_BLOCK) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `a:num`) THEN ANTS_TAC THENL [FIN_DIG_ARITH_TAC; DISCH_TAC] THEN
  SUBGOAL_THEN `fin_dig_cg p (sum (1..(2 * a) * p + r) (fin_dig_kmg p))
                             (sum (1..(2 * a) * p) (fin_dig_kmg p))` ASSUME_TAC THENL
   [SIMP_TAC[SUM_ADD_SPLIT; ARITH_RULE `1 <= x + 1`] THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM REAL_ADD_RID] THEN
    MATCH_MP_TAC FIN_DIG_CG_ADD THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC FIN_DIG_CG_REFL THEN ASM_MESON_TAC[FIN_DIG_CG_ZP1]; ALL_TAC] THEN
    SUBGOAL_THEN `(2 * a) * p + 1 = 1 + (2 * a) * p /\ (2 * a) * p + r = r + (2 * a) * (p:num)`
      (fun th -> REWRITE_TAC[th]) THENL [ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[SUM_OFFSET] THEN MATCH_MP_TAC FIN_DIG_KM_RUN THEN
    ASM_REWRITE_TAC[EVEN_DOUBLE] THEN FIN_DIG_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[FIN_DIG_E_REFL; FIN_BDRY_KMINUS_EVEN; EVEN_DOUBLE] THEN
  REWRITE_TAC[GSYM FIN_DIG_KMT_ETA] THEN
  SUBGOAL_THEN `fin_dig_cg p (fin_E p r) (cat_c (r DIV 2))` ASSUME_TAC THENL
   [MATCH_MP_TAC FIN_DIG_E_CG THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `fin_dig_unit p (fin_hstar (2 * a))` ASSUME_TAC THENL
   [MATCH_MP_TAC FIN_DIG_HSTAR_SMALL THEN FIN_DIG_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `fin_zp p (sum (1..2 * a) fin_dig_kmt)` ASSUME_TAC THENL
   [MATCH_MP_TAC FIN_DIG_KMT_SUM_ZP THEN FIN_DIG_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC FIN_DIG_CG_TRANS THEN
  EXISTS_TAC `(fin_hstar (2 * a) * cat_c (r DIV 2)) *
              ((--(&1)) pow ((p - 1) DIV 2) * sum (1..2 * a) fin_dig_kmt)` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC FIN_DIG_CG_MUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC FIN_DIG_CG_TRANS THEN
    EXISTS_TAC `sum (1..(2 * a) * p) (fin_dig_kmg p)` THEN ASM_REWRITE_TAC[];
    GEN_REWRITE_TAC (RATOR_CONV o RAND_CONV) [REAL_ARITH `(h * c) * e * s = (e * c) * h * s:real`] THEN
    FIN_DIG_CONG_TAC]);;

let FIN_DIG_KMINUS35 = prove
 (`forall p P r. prime p /\ ~(p = 2) /\ r < p /\ P + 2 <= p
           ==> fin_dig_cg p (&p pow 2 * cat_kminus (P * p + r))
                            (fin_E p ((p - 1) - r) * cat_kminus P)`,
  MESON_TAC[FIN_DIG_KMINUS35_EVEN; FIN_DIG_KMINUS35_ODD; NOT_EVEN]);;

(* ------------------------------------------------------------------------- *)
(* Starting congruence (35) for k^+.                                         *)
(* ------------------------------------------------------------------------- *)

let FIN_DIG_KP2 = prove
 (`forall z. ODD z ==> &2 / (&z pow 2 * fin_hstar z) = &2 * cat_c ((z - 1) DIV 2) / &z`,
  GEN_TAC THEN REWRITE_TAC[ODD_EXISTS; ADD1] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:num` SUBST1_TAC) THEN
  REWRITE_TAC[FIN_DIG_HSTAR_ODD; ADD_SUB; ARITH_RULE `(2 * a) DIV 2 = a`] THEN
  MP_TAC(SPEC `a:num` FIN_BDRY_C_POS) THEN
  SUBGOAL_THEN `~(&(2 * a + 1) = &0)` MP_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_EQ] THEN ARITH_TAC; ALL_TAC] THEN
  CONV_TAC REAL_FIELD);;

let FIN_DIG_KD = prove
 (`forall p m. prime p /\ ~(p = 2) /\ ODD m /\ m + 2 <= p
         ==> fin_dig_cg p (cat_c ((m * p - 1) DIV 2))
                ((--(&1)) pow ((p - 1) DIV 2) * cat_c ((m - 1) DIV 2))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 (X_CHOOSE_THEN `a:num` ASSUME_TAC o REWRITE_RULE[ODD_EXISTS; ADD1])
    ASSUME_TAC))) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq(concl th) && lhs(concl th) = `m:num`)) THEN
  MP_TAC(SPEC `p:num` FIN_DIG_ODDP) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `q:num` STRIP_ASSUME_TAC) THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `((2 * a + 1) * p - 1) DIV 2 = a * p + q` SUBST1_TAC THENL
   [MATCH_MP_TAC DIV_UNIQ THEN EXISTS_TAC `0` THEN
    UNDISCH_TAC `2 * q + 1 = p` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[ADD_SUB; ARITH_RULE `(2 * a) DIV 2 = a`] THEN
  MATCH_MP_TAC FIN_DIG_CG_TRANS THEN EXISTS_TAC `cat_c a * cat_c q` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC FIN_DIG_C_NOCARRY THEN FIN_DIG_ARITH_TAC; ALL_TAC] THEN
  GEN_REWRITE_TAC RAND_CONV [REAL_MUL_SYM] THEN MATCH_MP_TAC FIN_DIG_CG_MUL THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC FIN_DIG_CG_REFL THEN ASM_SIMP_TAC[FIN_DIG_C_ZP];
    MP_TAC(SPEC `p:num` FIN_DIG_C_HALF) THEN ASM_REWRITE_TAC[]]);;

let FIN_DIG_KP1 = prove
 (`forall p Q t. prime p /\ ~(p = 2) /\ 0 < t /\ t < p /\ Q + 2 <= p /\ EVEN (Q * p + t)
           ==> fin_dig_cg p (&p pow 2 * (&2 / (&(Q * p + t) pow 2 * fin_hstar (Q * p + t))))
                            (&0)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`p:num`; `Q:num`; `t:num`] FIN_DIG_EVEN_DIGITS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP FIN_DIG_PNZ) THEN
  SUBGOAL_THEN `fin_dig_unit p (&(Q * p + t))` ASSUME_TAC THENL
   [MATCH_MP_TAC FIN_DIG_UNIT_RES THEN FIN_DIG_ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `EVEN t` THENL
   [MP_TAC(SPECL [`p:num`; `Q:num`; `t:num`] FIN_DIG_HSTAR_EE) THEN
    ANTS_TAC THENL
     [UNDISCH_TAC `EVEN Q <=> EVEN t` THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
      FIN_DIG_ARITH_TAC; STRIP_TAC] THEN
    REWRITE_TAC[REAL_POW_2; GSYM REAL_MUL_ASSOC] THEN
    MATCH_MP_TAC FIN_DIG_CG_PMUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC FIN_ZP_MUL THEN ASM_SIMP_TAC[FIN_ZP_NUM] THEN
    MATCH_MP_TAC FIN_DIG_ZP_DIV_UNIT THEN ASM_SIMP_TAC[FIN_ZP_NUM] THEN
    MATCH_MP_TAC FIN_DIG_UNIT_MUL THEN ASM_SIMP_TAC[FIN_DIG_UNIT_MUL];
    ALL_TAC] THEN
  MP_TAC(SPECL [`p:num`; `Q:num`; `t:num`] FIN_DIG_HSTAR_EO) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[GSYM NOT_EVEN] THEN
    UNDISCH_TAC `EVEN Q <=> EVEN t` THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    FIN_DIG_ARITH_TAC; DISCH_TAC] THEN
  SUBGOAL_THEN
   `&p pow 2 * (&2 / (&(Q * p + t) pow 2 * fin_hstar (Q * p + t))) =
    &p * (&2 / (&(Q * p + t) pow 2 * (fin_hstar (Q * p + t) / &p)))` SUBST1_TAC THENL
   [REWRITE_TAC[real_div; REAL_INV_MUL; REAL_INV_INV; REAL_POW_2] THEN
    UNDISCH_TAC `~(&p = &0)` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  MATCH_MP_TAC FIN_DIG_CG_PMUL THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC FIN_DIG_ZP_DIV_UNIT THEN ASM_SIMP_TAC[FIN_ZP_NUM] THEN
  MATCH_MP_TAC FIN_DIG_UNIT_MUL THEN ASM_SIMP_TAC[FIN_DIG_UNIT_POW]);;

let FIN_DIG_KP1_GEN = prove
 (`forall p z. prime p /\ ~(p = 2) /\ z DIV p + 2 <= p /\ ~(p divides z) /\ EVEN z
         ==> fin_dig_cg p (&p pow 2 * (&2 / (&z pow 2 * fin_hstar z))) (&0)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(p:num = 0)` ASSUME_TAC THENL [ASM_MESON_TAC[PRIME_IMP_NZ]; ALL_TAC] THEN
  SUBGOAL_THEN `~(z MOD p = 0)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[GSYM DIVIDES_MOD]; ALL_TAC] THEN
  SUBGOAL_THEN `z = (z DIV p) * p + z MOD p` SUBST1_TAC THENL
   [ASM_SIMP_TAC[FIN_DIG_DIGITS_EQ]; ALL_TAC] THEN
  MATCH_MP_TAC FIN_DIG_KP1 THEN ASM_SIMP_TAC[FIN_DIG_DIGITS_EQ; DIVISION] THEN
  FIN_DIG_ARITH_TAC);;

let FIN_DIG_KP_EVENSUM = prove
 (`forall p P r. prime p /\ ~(p = 2) /\ r < p /\ P + 2 <= p
           ==> fin_dig_cg p
                (sum (1..P * p + r) (\z. &p pow 2 *
                    (if EVEN z then &2 / (&z pow 2 * fin_hstar z) else &0)))
                (sum (1..P) (\m. if EVEN m then &2 / (&m pow 2 * fin_hstar m) else &0))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`p:num`; `P:num`; `r:num`] FIN_DIG_DIV_DIGITS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> GEN_REWRITE_TAC (RAND_CONV o LAND_CONV o RAND_CONV) [GSYM(CONJUNCT1 th)]) THEN
  MATCH_MP_TAC FIN_DIG_SUM_MULT1 THEN ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP FIN_DIG_PNZ) THEN
  CONJ_TAC THENL
   [X_GEN_TAC `k:num` THEN STRIP_TAC THEN
    ASM_CASES_TAC `EVEN k` THEN ASM_REWRITE_TAC[REAL_MUL_RZERO] THENL
     [MATCH_MP_TAC FIN_DIG_KP1_GEN THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(SPECL [`p:num`; `P:num`; `r:num`; `k:num`] FIN_DIG_DIV_LE) THEN
      ASM_REWRITE_TAC[] THEN FIN_DIG_ARITH_TAC;
      MATCH_MP_TAC FIN_DIG_CG_REFL THEN ASM_SIMP_TAC[FIN_ZP_0]];
    ALL_TAC] THEN
  X_GEN_TAC `m:num` THEN STRIP_TAC THEN
  SUBGOAL_THEN `m <= P:num` ASSUME_TAC THENL
   [UNDISCH_TAC `m <= (P * p + r) DIV p` THEN ASM_SIMP_TAC[FIN_DIG_DIV_DIGITS]; ALL_TAC] THEN
  SUBGOAL_THEN `EVEN (m * p) <=> EVEN m` SUBST1_TAC THENL
   [MP_TAC(SPEC `p:num` PRIME_ODD) THEN ASM_REWRITE_TAC[GSYM NOT_EVEN; EVEN_MULT] THEN
    CONV_TAC TAUT; ALL_TAC] THEN
  ASM_CASES_TAC `EVEN m` THEN ASM_REWRITE_TAC[REAL_MUL_RZERO] THENL
   [ALL_TAC; MATCH_MP_TAC FIN_DIG_CG_REFL THEN ASM_SIMP_TAC[FIN_ZP_0]] THEN
  MP_TAC(SPECL [`p:num`; `m:num`; `0`] FIN_DIG_HSTAR_EE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[EVEN] THEN FIN_DIG_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[ADD_CLAUSES; ARITH_RULE `0 DIV 2 = 0`; FIN_BDRY_C_0; REAL_MUL_RID] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `&p pow 2 * &2 / (&(m * p) pow 2 * fin_hstar (m * p)) =
                &2 / (&m pow 2 * fin_hstar (m * p))` SUBST1_TAC THENL
   [REWRITE_TAC[GSYM REAL_OF_NUM_MUL; REAL_POW_MUL] THEN
    REWRITE_TAC[real_div; REAL_INV_MUL] THEN
    MP_TAC(SPECL [`p:num`; `2`] FIN_PPOW_NZ) THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC REAL_FIELD; ALL_TAC] THEN
  MATCH_MP_TAC FIN_DIG_CG_DIV THEN ASM_SIMP_TAC[FIN_DIG_CG_REFL; FIN_ZP_NUM] THEN
  SUBGOAL_THEN `fin_dig_unit p (&m pow 2)` ASSUME_TAC THENL
   [MATCH_MP_TAC FIN_DIG_UNIT_POW THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC FIN_DIG_UNIT_NUM_LT THEN FIN_DIG_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[FIN_DIG_UNIT_MUL] THEN FIN_DIG_CONG_TAC);;

let FIN_DIG_KP_ODDSUM = prove
 (`forall p P r. prime p /\ ~(p = 2) /\ r < p /\ P + 2 <= p
           ==> fin_dig_cg p
                (sum (1..P * p + r) (\z. &p *
                    (if ~EVEN z then &2 / (&z pow 2 * fin_hstar z) else &0)))
                ((--(&1)) pow ((p - 1) DIV 2) *
                 sum (1..P) (\m. if ~EVEN m then &2 / (&m pow 2 * fin_hstar m) else &0))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM SUM_LMUL] THEN
  MP_TAC(SPECL [`p:num`; `P:num`; `r:num`] FIN_DIG_DIV_DIGITS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> GEN_REWRITE_TAC (RAND_CONV o LAND_CONV o RAND_CONV) [GSYM(CONJUNCT1 th)]) THEN
  MATCH_MP_TAC FIN_DIG_SUM_MULT1 THEN ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP FIN_DIG_PNZ) THEN
  CONJ_TAC THENL
   [X_GEN_TAC `k:num` THEN STRIP_TAC THEN
    ASM_CASES_TAC `EVEN k` THEN ASM_REWRITE_TAC[REAL_MUL_RZERO] THENL
     [MATCH_MP_TAC FIN_DIG_CG_REFL THEN ASM_SIMP_TAC[FIN_ZP_0]; ALL_TAC] THEN
    ASM_SIMP_TAC[FIN_DIG_KP2; GSYM NOT_EVEN] THEN
    MATCH_MP_TAC FIN_DIG_CG_PMUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC FIN_ZP_MUL THEN ASM_SIMP_TAC[FIN_ZP_NUM] THEN
    MATCH_MP_TAC FIN_ZP_DIV_NUM THEN ASM_SIMP_TAC[FIN_DIG_C_ZP];
    ALL_TAC] THEN
  X_GEN_TAC `m:num` THEN STRIP_TAC THEN
  SUBGOAL_THEN `m <= P:num` ASSUME_TAC THENL
   [UNDISCH_TAC `m <= (P * p + r) DIV p` THEN ASM_SIMP_TAC[FIN_DIG_DIV_DIGITS]; ALL_TAC] THEN
  SUBGOAL_THEN `EVEN (m * p) <=> EVEN m` SUBST1_TAC THENL
   [MP_TAC(SPEC `p:num` PRIME_ODD) THEN ASM_REWRITE_TAC[GSYM NOT_EVEN; EVEN_MULT] THEN
    CONV_TAC TAUT; ALL_TAC] THEN
  ASM_CASES_TAC `EVEN m` THEN ASM_REWRITE_TAC[REAL_MUL_RZERO] THENL
   [MATCH_MP_TAC FIN_DIG_CG_REFL THEN ASM_SIMP_TAC[FIN_ZP_0]; ALL_TAC] THEN
  SUBGOAL_THEN `ODD m /\ ODD (m * p)` STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[GSYM NOT_EVEN; EVEN_MULT] THEN
    MP_TAC(SPEC `p:num` PRIME_ODD) THEN ASM_REWRITE_TAC[GSYM NOT_EVEN]; ALL_TAC] THEN
  ASM_SIMP_TAC[FIN_DIG_KP2] THEN
  SUBGOAL_THEN `&p * &2 * cat_c ((m * p - 1) DIV 2) / &(m * p) =
                &2 * cat_c ((m * p - 1) DIV 2) / &m` SUBST1_TAC THENL
   [REWRITE_TAC[GSYM REAL_OF_NUM_MUL] THEN
    SUBGOAL_THEN `~(&m = &0)` MP_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_EQ] THEN FIN_DIG_ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `~(&p = &0)` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  MP_TAC(SPECL [`p:num`; `m:num`] FIN_DIG_KD) THEN
  ANTS_TAC THENL [FIN_DIG_ARITH_TAC; DISCH_TAC] THEN
  REWRITE_TAC[real_div] THEN
  ONCE_REWRITE_TAC[REAL_ARITH `e * &2 * c * i = &2 * (e * c) * i:real`] THEN
  MATCH_MP_TAC FIN_DIG_CG_MUL THEN ASM_SIMP_TAC[FIN_DIG_CG_REFL; FIN_ZP_NUM] THEN
  MATCH_MP_TAC FIN_DIG_CG_MUL THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC FIN_DIG_CG_REFL THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC FIN_ZP_INV_NUM THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o MATCH_MP DIVIDES_LE) THEN FIN_DIG_ARITH_TAC);;

let FIN_DIG_KP_SUM_ZP = prove
 (`forall p P b. prime p /\ ~(p = 2) /\ P < p
           ==> fin_zp p (sum (1..P) (\m. if b m then &2 / (&m pow 2 * fin_hstar m) else &0))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC FIN_ZP_SUM THEN
  ASM_REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN X_GEN_TAC `z:num` THEN STRIP_TAC THEN
  COND_CASES_TAC THEN ASM_SIMP_TAC[FIN_ZP_0] THEN
  MATCH_MP_TAC FIN_DIG_ZP_DIV_UNIT THEN ASM_SIMP_TAC[FIN_ZP_NUM] THEN
  MATCH_MP_TAC FIN_DIG_UNIT_MUL THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC FIN_DIG_UNIT_POW THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC FIN_DIG_UNIT_NUM_LT; MATCH_MP_TAC FIN_DIG_HSTAR_SMALL] THEN
  FIN_DIG_ARITH_TAC);;

let FIN_DIG_KPLUS35 = prove
 (`forall p P r. prime p /\ ~(p = 2) /\ r < p /\ P + 2 <= p
           ==> fin_dig_cg p (&p pow 2 * cat_kplus ((P * p + r) + 1))
                            (fin_E p r * cat_kplus (P + 1))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[FIN_BDRY_KPLUS] THEN
  MP_TAC(SPECL [`p:num`; `P:num`; `r:num`] FIN_DIG_EVEN_DIGITS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP FIN_DIG_PNZ) THEN
  SUBGOAL_THEN `fin_dig_unit p (fin_hstar P)` ASSUME_TAC THENL
   [MATCH_MP_TAC FIN_DIG_HSTAR_SMALL THEN FIN_DIG_ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `EVEN (P * p + r)` THEN FIRST_ASSUM(fun th -> REWRITE_TAC[th]) THENL
   [SUBGOAL_THEN
     `&p pow 2 * fin_hstar (P * p + r) *
      sum (1..P * p + r) (\z. if EVEN z then &2 / (&z pow 2 * fin_hstar z) else &0) =
      fin_hstar (P * p + r) *
      sum (1..P * p + r) (\z. &p pow 2 *
                    (if EVEN z then &2 / (&z pow 2 * fin_hstar z) else &0))` SUBST1_TAC THENL
     [REWRITE_TAC[SUM_LMUL] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(SPECL [`p:num`; `P:num`; `r:num`] FIN_DIG_KP_EVENSUM) THEN
    ANTS_TAC THENL [FIN_DIG_ARITH_TAC; DISCH_TAC] THEN
    MP_TAC(SPECL [`p:num`; `P:num`; `\m:num. EVEN m`] FIN_DIG_KP_SUM_ZP) THEN
    ANTS_TAC THENL [FIN_DIG_ARITH_TAC; REWRITE_TAC[] THEN DISCH_TAC] THEN
    ASM_CASES_TAC `EVEN r` THENL
     [SUBGOAL_THEN `EVEN P` ASSUME_TAC THENL
       [UNDISCH_TAC `EVEN (P * p + r) <=> EVEN P <=> EVEN r` THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN
      MP_TAC(SPECL [`p:num`; `P:num`; `r:num`] FIN_DIG_HSTAR_EE) THEN
      ANTS_TAC THENL [FIN_DIG_ARITH_TAC; STRIP_TAC] THEN
      SUBGOAL_THEN `fin_dig_cg p (fin_E p r) (cat_c (r DIV 2))` ASSUME_TAC THENL
       [MATCH_MP_TAC FIN_DIG_E_CG THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      MATCH_MP_TAC FIN_DIG_CG_TRANS THEN
      EXISTS_TAC `(fin_hstar P * cat_c (r DIV 2)) *
                  sum (1..P) (\m. if EVEN m then &2 / (&m pow 2 * fin_hstar m) else &0)` THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [MATCH_MP_TAC FIN_DIG_CG_MUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      GEN_REWRITE_TAC (RATOR_CONV o RAND_CONV)
        [REAL_ARITH `(h * c) * s = c * h * s:real`] THEN
      FIN_DIG_CONG_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `fin_E p r = &0` SUBST1_TAC THENL
     [MATCH_MP_TAC FIN_DIG_E_ODD0 THEN ASM_REWRITE_TAC[GSYM NOT_EVEN]; ALL_TAC] THEN
    REWRITE_TAC[REAL_MUL_LZERO] THEN
    MATCH_MP_TAC FIN_DIG_CG_ZERO_LMUL THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [ALL_TAC; ASM_MESON_TAC[FIN_DIG_CG_ZP1]] THEN
    MP_TAC(SPECL [`p:num`; `P:num`; `r:num`] FIN_DIG_HSTAR_EO) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[GSYM NOT_EVEN] THEN
      UNDISCH_TAC `EVEN (P * p + r) <=> EVEN P <=> EVEN r` THEN ASM_REWRITE_TAC[] THEN
      DISCH_TAC THEN FIN_DIG_ARITH_TAC; DISCH_TAC] THEN
    SUBGOAL_THEN `fin_hstar (P * p + r) = &p * (fin_hstar (P * p + r) / &p)` SUBST1_TAC THENL
     [UNDISCH_TAC `~(&p = &0)` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
    MATCH_MP_TAC FIN_DIG_CG_PMUL THEN ASM_REWRITE_TAC[] THEN FIN_DIG_ZP_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `&p pow 2 * fin_hstar (P * p + r) *
    sum (1..P * p + r) (\z. if ~EVEN z then &2 / (&z pow 2 * fin_hstar z) else &0) =
    (&p * fin_hstar (P * p + r)) *
    sum (1..P * p + r) (\z. &p *
                  (if ~EVEN z then &2 / (&z pow 2 * fin_hstar z) else &0))` SUBST1_TAC THENL
   [REWRITE_TAC[SUM_LMUL] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`p:num`; `P:num`; `r:num`] FIN_DIG_KP_ODDSUM) THEN
  ANTS_TAC THENL [FIN_DIG_ARITH_TAC; DISCH_TAC] THEN
  MP_TAC(SPECL [`p:num`; `P:num`; `\m:num. ~EVEN m`] FIN_DIG_KP_SUM_ZP) THEN
  ANTS_TAC THENL [FIN_DIG_ARITH_TAC; REWRITE_TAC[] THEN DISCH_TAC] THEN
  ASM_CASES_TAC `EVEN r` THENL
   [SUBGOAL_THEN `~EVEN P` ASSUME_TAC THENL
     [UNDISCH_TAC `~EVEN (P * p + r)` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(SPECL [`p:num`; `P:num`; `r:num`] FIN_DIG_HSTAR_OE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[GSYM NOT_EVEN] THEN FIN_DIG_ARITH_TAC; DISCH_TAC] THEN
    SUBGOAL_THEN `fin_dig_cg p (fin_E p r) (cat_c (r DIV 2))` ASSUME_TAC THENL
     [MATCH_MP_TAC FIN_DIG_E_CG THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC FIN_DIG_CG_TRANS THEN
    EXISTS_TAC `((--(&1)) pow ((p - 1) DIV 2) * cat_c (r DIV 2) * fin_hstar P) *
                ((--(&1)) pow ((p - 1) DIV 2) *
                 sum (1..P) (\m. if ~EVEN m then &2 / (&m pow 2 * fin_hstar m) else &0))` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC FIN_DIG_CG_MUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    GEN_REWRITE_TAC (RATOR_CONV o RAND_CONV)
      [REAL_ARITH `(e * c * h) * e * s = (e pow 2) * c * h * s:real`] THEN
    REWRITE_TAC[FIN_DIG_EPS_SQ; REAL_MUL_LID] THEN FIN_DIG_CONG_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `fin_E p r = &0` SUBST1_TAC THENL
   [MATCH_MP_TAC FIN_DIG_E_ODD0 THEN ASM_REWRITE_TAC[GSYM NOT_EVEN]; ALL_TAC] THEN
  REWRITE_TAC[REAL_MUL_LZERO] THEN
  MATCH_MP_TAC FIN_DIG_CG_ZERO_LMUL THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [ALL_TAC; ASM_MESON_TAC[FIN_DIG_CG_ZP1]] THEN
  MP_TAC(SPECL [`p:num`; `P:num`; `r:num`] FIN_DIG_HSTAR_OO) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[GSYM NOT_EVEN] THEN
    UNDISCH_TAC `~EVEN (P * p + r)` THEN ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MATCH_MP_TAC FIN_DIG_CG_PMUL THEN ASM_REWRITE_TAC[] THEN FIN_DIG_ZP_TAC);;
