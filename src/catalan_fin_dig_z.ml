(* ========================================================================= *)
(* fin_dig_z: congruences for harmonic numbers and Z'(i,j) modulo p.        *)
(* (End of proof of Lemma 3.1 and the Z' part of Lemma 3.2.)                 *)
(* ========================================================================= *)

needs "src/catalan_fin_dig_base.ml";;

prioritize_real();;

let FIN_DIG_Z_TERM_ZP = prove
 (`forall p k d. prime p /\ ~(p divides k) ==> fin_zp p (&1 / &k pow d)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[REAL_OF_NUM_POW] THEN
  MATCH_MP_TAC FIN_ZP_DIV_NUM THEN ASM_SIMP_TAC[FIN_ZP_1] THEN
  ASM_MESON_TAC[PRIME_DIVEXP]);;

let FIN_DIG_Z_LT_NDIV = prove
 (`forall p k. prime p /\ 0 < k /\ k < p ==> ~(p divides k)`,
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o MATCH_MP DIVIDES_LE) THEN
  ASM_ARITH_TAC);;

let FIN_DIG_Z_HARM_0 = prove
 (`forall d. cat_harm d 0 = &0`,
  REWRITE_TAC[cat_harm; SUM_CLAUSES_NUMSEG; ARITH]);;

let FIN_DIG_Z_HARM_1 = prove
 (`forall d. cat_harm d 1 = &1`,
  REWRITE_TAC[cat_harm; SUM_SING_NUMSEG; REAL_POW_ONE; REAL_DIV_1]);;

let FIN_DIG_HARM_ZP = prove
 (`forall p d n. prime p /\ n < p ==> fin_zp p (cat_harm d n)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[cat_harm] THEN
  MATCH_MP_TAC FIN_ZP_SUM THEN ASM_REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC FIN_DIG_Z_TERM_ZP THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC FIN_DIG_Z_LT_NDIV THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

let FIN_DIG_Z_HARM = prove
 (`forall p d i. prime p /\ 1 <= d /\ i < p * p
           ==> fin_dig_cg p (&p pow d * cat_harm d i) (cat_harm d (i DIV p))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP PRIME_IMP_NZ) THEN
  SUBGOAL_THEN `exists e. d = SUC e` (X_CHOOSE_THEN `e:num` SUBST_ALL_TAC) THENL
   [EXISTS_TAC `(d:num) - 1` THEN ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[cat_harm; GSYM SUM_LMUL] THEN
  SUBGOAL_THEN `1..(i DIV p) = {m | 1 <= m * p /\ m * p <= i}` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_NUMSEG; IN_ELIM_THM] THEN X_GEN_TAC `m:num` THEN
    ASM_SIMP_TAC[LE_RDIV_EQ; ARITH_RULE `1 <= n <=> ~(n = 0)`; MULT_EQ_0] THEN
    MESON_TAC[MULT_SYM];
    ALL_TAC] THEN
  MATCH_MP_TAC FIN_DIG_SUM_MULTIPLES THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `k:num` THEN STRIP_TAC THEN
    SUBGOAL_THEN `forall x. &p pow SUC e * x = &p * (&p pow e * x)`
      (fun th -> REWRITE_TAC[th]) THENL
     [REWRITE_TAC[real_pow; REAL_MUL_ASSOC]; ALL_TAC] THEN
    MATCH_MP_TAC FIN_DIG_CG_PMUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC FIN_ZP_MUL THEN ASM_SIMP_TAC[FIN_ZP_POW; FIN_ZP_NUM] THEN
    MATCH_MP_TAC FIN_DIG_Z_TERM_ZP THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `m:num` THEN STRIP_TAC THEN
    SUBGOAL_THEN `~(m = 0)` ASSUME_TAC THENL
     [DISCH_THEN SUBST_ALL_TAC THEN UNDISCH_TAC `1 <= 0 * p` THEN ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `m < p:num` ASSUME_TAC THENL
     [SUBGOAL_THEN `(m:num) * p < p * p` MP_TAC THENL
       [ASM_ARITH_TAC; SIMP_TAC[LT_MULT_RCANCEL]];
      ALL_TAC] THEN
    SUBGOAL_THEN `&p pow SUC e * &1 / &(m * p) pow SUC e = &1 / &m pow SUC e`
      SUBST1_TAC THENL
     [REWRITE_TAC[GSYM REAL_OF_NUM_MUL; REAL_POW_MUL] THEN
      MATCH_MP_TAC(REAL_FIELD
       `~(a = &0) /\ ~(b = &0) ==> a * &1 / (b * a) = &1 / b`) THEN
      ASM_REWRITE_TAC[REAL_POW_EQ_0; REAL_OF_NUM_EQ];
      ALL_TAC] THEN
    MATCH_MP_TAC FIN_DIG_CG_REFL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC FIN_DIG_Z_TERM_ZP THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC FIN_DIG_Z_LT_NDIV THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC]);;

let FIN_DIG_HARM1 = prove
 (`forall p i. prime p /\ i < p * p ==> fin_dig_cg p (&p * cat_harm 1 i) (cat_harm 1 (i DIV p))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`p:num`; `1:num`; `i:num`] FIN_DIG_Z_HARM) THEN
  ASM_REWRITE_TAC[REAL_POW_1; LE_REFL]);;

let FIN_DIG_HARM2 = prove
 (`forall p i. prime p /\ i < p * p ==> fin_dig_cg p (&p pow 2 * cat_harm 2 i) (cat_harm 2 (i DIV p))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`p:num`; `2:num`; `i:num`] FIN_DIG_Z_HARM) THEN
  ASM_REWRITE_TAC[ARITH]);;

(* ------------------------------------------------------------------------- *)
(* Differences of integers with distinct residues are units.                *)
(* ------------------------------------------------------------------------- *)

let FIN_DIG_Z_UNIT_DIFF_LE = prove
 (`forall p a b. prime p /\ a <= b /\ ~(a MOD p = b MOD p) ==> fin_dig_unit p (&b - &a)`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[REAL_OF_NUM_SUB] THEN
  MATCH_MP_TAC FIN_DIG_UNIT_NUM THEN ASM_REWRITE_TAC[divides] THEN
  DISCH_THEN(X_CHOOSE_TAC `x:num`) THEN
  UNDISCH_TAC `~(a MOD p = b MOD p)` THEN REWRITE_TAC[] THEN
  SUBGOAL_THEN `(b:num) = p * x + a` SUBST1_TAC THENL
   [ASM_ARITH_TAC; REWRITE_TAC[MOD_MULT_ADD]]);;

let FIN_DIG_Z_UNIT_DIFF = prove
 (`forall p a b. prime p /\ ~(a MOD p = b MOD p) ==> fin_dig_unit p (&a - &b)`,
  REPEAT STRIP_TAC THEN DISJ_CASES_TAC(SPECL [`a:num`; `b:num`] LE_CASES) THENL
   [ONCE_REWRITE_TAC[REAL_ARITH `x - y = --(y - x)`] THEN
    MATCH_MP_TAC FIN_DIG_UNIT_NEG;
    ALL_TAC] THEN
  MATCH_MP_TAC FIN_DIG_Z_UNIT_DIFF_LE THEN ASM_MESON_TAC[]);;

let FIN_DIG_Z_ZP_DIV = prove
 (`forall p x u. prime p /\ fin_zp p x /\ fin_dig_unit p u ==> fin_zp p (x / u)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[real_div] THEN
  MATCH_MP_TAC FIN_ZP_MUL THEN ASM_MESON_TAC[FIN_DIG_UNIT_ZP]);;

let FIN_DIG_Z0_ZP = prove
 (`forall p a j. prime p /\ a < p /\ j < p ==> fin_zp p (cat_Z0 a j)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[cat_Z0] THEN COND_CASES_TAC THENL
   [ASM_SIMP_TAC[FIN_ZP_NEG_EQ; FIN_DIG_HARM_ZP]; ALL_TAC] THEN
  MATCH_MP_TAC FIN_DIG_Z_ZP_DIV THEN ASM_SIMP_TAC[FIN_ZP_SUB; FIN_DIG_HARM_ZP] THEN
  MATCH_MP_TAC FIN_DIG_Z_UNIT_DIFF THEN ASM_SIMP_TAC[MOD_LT]);;

let FIN_DIG_Z_PH1_ZP = prove
 (`forall p i. prime p /\ i < p * p ==> fin_zp p (&p * cat_harm 1 i)`,
  MESON_TAC[FIN_DIG_HARM1; FIN_DIG_CG_ZP]);;

(* ------------------------------------------------------------------------- *)
(* Lemma 3.1, Z' part.                                                       *)
(* ------------------------------------------------------------------------- *)

let FIN_DIG_Z_L31 = prove
 (`forall p H i j. prime p /\ 4 * H < p * p /\ i < H /\ j < H
   ==> fin_dig_cg p (&p pow 2 * cat_Z0 i j)
                    (if i MOD p = j MOD p then cat_Z0 (i DIV p) (j DIV p) else &0)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(i:num) < p * p /\ (j:num) < p * p` STRIP_ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP PRIME_IMP_NZ) THEN
  SUBGOAL_THEN `i DIV p < p /\ j DIV p < p` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[RDIV_LT_EQ]; ALL_TAC] THEN
  ASM_CASES_TAC `i:num = j` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN REWRITE_TAC[cat_Z0; REAL_MUL_RNEG] THEN
    MATCH_MP_TAC FIN_DIG_CG_NEG THEN
    MATCH_MP_TAC FIN_DIG_Z_HARM THEN ASM_REWRITE_TAC[ARITH];
    ALL_TAC] THEN
  ASM_CASES_TAC `i MOD p = j MOD p` THEN ASM_REWRITE_TAC[] THENL
   [SUBGOAL_THEN `&i - &j = &p * (&(i DIV p) - &(j DIV p))` ASSUME_TAC THENL
     [SUBGOAL_THEN `&i = &(i DIV p) * &p + &(i MOD p) /\
                    &j = &(j DIV p) * &p + &(j MOD p)` MP_TAC THENL
       [REWRITE_TAC[REAL_OF_NUM_MUL; REAL_OF_NUM_ADD; REAL_OF_NUM_EQ] THEN
        ASM_MESON_TAC[DIVISION];
        ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RING];
      ALL_TAC] THEN
    SUBGOAL_THEN `~(i DIV p = j DIV p)` ASSUME_TAC THENL
     [DISCH_TAC THEN UNDISCH_TAC `&i - &j = &p * (&(i DIV p) - &(j DIV p))` THEN
      ASM_REWRITE_TAC[REAL_SUB_REFL; REAL_MUL_RZERO; REAL_SUB_0; REAL_OF_NUM_EQ];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[cat_Z0] THEN
    SUBGOAL_THEN
     `&p pow 2 * (cat_harm 1 i - cat_harm 1 j) / (&p * (&(i DIV p) - &(j DIV p))) =
      (&p * cat_harm 1 i - &p * cat_harm 1 j) / (&(i DIV p) - &(j DIV p))`
    SUBST1_TAC THENL
     [MATCH_MP_TAC(REAL_FIELD
       `~(p = &0) /\ ~(d = &0) ==> p pow 2 * (a - b) / (p * d) = (p * a - p * b) / d`) THEN
      ASM_REWRITE_TAC[REAL_OF_NUM_EQ; REAL_SUB_0];
      ALL_TAC] THEN
    MATCH_MP_TAC FIN_DIG_CG_DIV THEN REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[];
      MATCH_MP_TAC FIN_DIG_CG_SUB THEN ASM_SIMP_TAC[FIN_DIG_HARM1];
      MATCH_MP_TAC FIN_DIG_Z_UNIT_DIFF THEN ASM_SIMP_TAC[MOD_LT];
      MATCH_MP_TAC FIN_DIG_CG_REFL THEN ASM_SIMP_TAC[FIN_ZP_SUB; FIN_ZP_NUM]];
    REWRITE_TAC[cat_Z0] THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN
     `&p pow 2 * (cat_harm 1 i - cat_harm 1 j) / (&i - &j) =
      &p * ((&p * cat_harm 1 i - &p * cat_harm 1 j) / (&i - &j))`
    SUBST1_TAC THENL [REWRITE_TAC[real_div] THEN CONV_TAC REAL_RING; ALL_TAC] THEN
    MATCH_MP_TAC FIN_DIG_CG_PMUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC FIN_DIG_Z_ZP_DIV THEN ASM_SIMP_TAC[FIN_DIG_Z_UNIT_DIFF] THEN
    MATCH_MP_TAC FIN_ZP_SUB THEN ASM_SIMP_TAC[FIN_DIG_Z_PH1_ZP]]);;

let FIN_DIG_LEMMA31_Z = prove
 (`forall p H i j. prime p /\ ~(p = 2) /\ 4 * H < p * p /\ p <= H /\ i < H /\ j < H
   ==> fin_zp p (&p pow 2 * cat_Z0 i j) /\
       fin_vge p (&1) (&p pow 2 * cat_Z0 i j -
                       (if i MOD p = j MOD p then cat_Z0 (i DIV p) (j DIV p) else &0))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`p:num`; `H:num`; `i:num`; `j:num`] FIN_DIG_Z_L31) THEN
  ASM_REWRITE_TAC[] THEN SIMP_TAC[fin_dig_cg]);;

(* ------------------------------------------------------------------------- *)
(* Lemma 3.2, Z' part (central columns j < p, H < 2p).                       *)
(* ------------------------------------------------------------------------- *)

let FIN_DIG_Z_CEN = prove
 (`forall p H i j. prime p /\ H < 2 * p /\ H <= j + p /\ j < p /\ i < H
   ==> fin_dig_cg p (&p * cat_Z0 i j)
                    (if p <= i /\ i < H then &1 / (&(i - p) - &j) else &0)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP PRIME_IMP_NZ) THEN
  SUBGOAL_THEN `2 * (p:num) <= p * p` ASSUME_TAC THENL
   [REWRITE_TAC[LE_MULT_RCANCEL] THEN ASM_MESON_TAC[PRIME_GE_2]; ALL_TAC] THEN
  SUBGOAL_THEN `(i:num) < p * p /\ (j:num) < p * p` STRIP_ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `i:num = j` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    SUBGOAL_THEN `~(p <= j:num)` (fun th -> REWRITE_TAC[th]) THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[cat_Z0; REAL_MUL_RNEG] THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM REAL_NEG_0] THEN
    MATCH_MP_TAC FIN_DIG_CG_NEG THEN MATCH_MP_TAC FIN_DIG_CG_PMUL THEN
    ASM_SIMP_TAC[FIN_DIG_HARM_ZP];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[cat_Z0] THEN
  SUBGOAL_THEN
   `&p * (cat_harm 1 i - cat_harm 1 j) / (&i - &j) =
    (&p * cat_harm 1 i - &p * cat_harm 1 j) / (&i - &j)`
  SUBST1_TAC THENL [REWRITE_TAC[real_div] THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  SUBGOAL_THEN `fin_dig_cg p (&p * cat_harm 1 j) (&0)` ASSUME_TAC THENL
   [MP_TAC(SPECL [`p:num`; `j:num`] FIN_DIG_HARM1) THEN
    ASM_SIMP_TAC[DIV_LT; FIN_DIG_Z_HARM_0];
    ALL_TAC] THEN
  ASM_CASES_TAC `p <= i:num` THEN ASM_REWRITE_TAC[] THENL
   [SUBGOAL_THEN `fin_dig_cg p (&p * cat_harm 1 i) (&1)` ASSUME_TAC THENL
     [MP_TAC(SPECL [`p:num`; `i:num`] FIN_DIG_HARM1) THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `i DIV p = 1` (fun th -> REWRITE_TAC[th; FIN_DIG_Z_HARM_1]) THEN
      MATCH_MP_TAC DIV_UNIQ THEN EXISTS_TAC `i - p:num` THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `&1 / (&(i - p) - &j) = (&1 - &0) / (&(i - p) - &j)`
    SUBST1_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC FIN_DIG_CG_DIV THEN REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[];
      MATCH_MP_TAC FIN_DIG_CG_SUB THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC FIN_DIG_Z_UNIT_DIFF THEN ASM_SIMP_TAC[MOD_LT] THEN
      SUBGOAL_THEN `i MOD p = i - p` SUBST1_TAC THENL
       [MATCH_MP_TAC MOD_UNIQ THEN EXISTS_TAC `1:num` THEN ASM_ARITH_TAC;
        ASM_ARITH_TAC];
      MATCH_MP_TAC FIN_DIG_CG_SUB THEN ASM_SIMP_TAC[FIN_DIG_CG_REFL; FIN_ZP_NUM] THEN
      MATCH_MP_TAC FIN_DIG_CG_INTEGER THEN ASM_REWRITE_TAC[INTEGER_CLOSED] THEN
      EXISTS_TAC `&1` THEN ASM_SIMP_TAC[GSYM REAL_OF_NUM_SUB; INTEGER_CLOSED] THEN
      REAL_ARITH_TAC];
    SUBGOAL_THEN `(&0:real) = (&0 - &0) / (&i - &j)`
      (fun th -> GEN_REWRITE_TAC RAND_CONV [th]) THENL
     [REWRITE_TAC[REAL_SUB_REFL; real_div; REAL_MUL_LZERO]; ALL_TAC] THEN
    MATCH_MP_TAC FIN_DIG_CG_DIV THEN REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[];
      MATCH_MP_TAC FIN_DIG_CG_SUB THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(SPECL [`p:num`; `i:num`] FIN_DIG_HARM1) THEN
      ASM_SIMP_TAC[DIV_LT; FIN_DIG_Z_HARM_0; GSYM NOT_LE];
      MATCH_MP_TAC FIN_DIG_Z_UNIT_DIFF THEN ASM_SIMP_TAC[MOD_LT; GSYM NOT_LE];
      MATCH_MP_TAC FIN_DIG_CG_REFL THEN ASM_SIMP_TAC[FIN_ZP_SUB; FIN_ZP_NUM]]]);;

let FIN_DIG_CENTRAL_Z = prove
 (`forall p H i j. prime p /\ ~(p = 2) /\ H < 2 * p /\ p <= H /\ H <= j + p /\ j < p /\ i < H
   ==> fin_zp p (&p * cat_Z0 i j) /\
       fin_vge p (&1) (&p * cat_Z0 i j -
                       (if p <= i /\ i < H then &1 / (&(i - p) - &j) else &0))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`p:num`; `H:num`; `i:num`; `j:num`] FIN_DIG_Z_CEN) THEN
  ASM_REWRITE_TAC[] THEN SIMP_TAC[fin_dig_cg]);;
