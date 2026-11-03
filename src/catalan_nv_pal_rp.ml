(* ========================================================================= *)
(* CAT_NONVANISHING, part P: reversed coefficient polynomials               *)
(*   nv_pal_rp D w x = sum_{K<=D} w K x^(D-K)                                *)
(* products, digit expansions, coefficient extraction, and the rows.         *)
(* ========================================================================= *)

needs "src/catalan_nv_pal_key.ml";;

let nv_pal_rp = new_definition
 `nv_pal_rp D (w:num->real) (x:real) = sum(0..D) (\K. w K * x pow (D - K))`;;

let NV_PAL_SUM_ZERO_EXT = prove
 (`forall m n (f:num->real). m <= n /\ (forall j. m < j /\ j <= n ==> f j = &0)
       ==> sum(0..n) f = sum(0..m) f`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUM_SUPERSET THEN
  REWRITE_TAC[SUBSET_NUMSEG; IN_NUMSEG] THEN
  CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC);;

let NV_PAL_SUM_COND_EXT = prove
 (`forall K N (f:num->real). K <= N
       ==> sum(0..K) f = sum(0..N) (\a. if a <= K then f a else &0)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`K:num`; `N:num`; `\a. if a <= K then (f:num->real) a else &0`]
    NV_PAL_SUM_ZERO_EXT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN BETA_TAC THEN
    COND_CASES_TAC THEN REWRITE_TAC[] THEN ASM_ARITH_TAC;
    DISCH_THEN SUBST1_TAC] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN SIMP_TAC[]);;

let NV_PAL_SHIFTV = prove
 (`forall v H (f:num->real). v <= H
    ==> sum(0..H) (\i. if v <= i then f i else &0) =
        sum(0..H-v) (\j. f(j + v))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\i. if v <= i then (f:num->real) i else &0`; `v..H`; `0..H`]
    SUM_SUPERSET) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[SUBSET_NUMSEG; IN_NUMSEG] THEN
    CONJ_TAC THENL [ARITH_TAC; ALL_TAC] THEN
    REPEAT STRIP_TAC THEN COND_CASES_TAC THEN ASM_ARITH_TAC;
    DISCH_THEN SUBST1_TAC] THEN
  ASM_SIMP_TAC[SUM_OFFSET_0] THEN
  REWRITE_TAC[ARITH_RULE `v <= i + v:num`]);;

(* ------------------------------------------------------------------------- *)
(* Product of reversed polynomials.                                          *)
(* ------------------------------------------------------------------------- *)

let NV_PAL_RP_MUL = prove
 (`forall A B u v x. (forall a. A < a ==> u a = &0) /\ (forall b. B < b ==> v b = &0)
     ==> nv_pal_rp A u x * nv_pal_rp B v x =
         nv_pal_rp (A + B) (\K. sum(0..K) (\a. u a * v (K - a))) x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[nv_pal_rp] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `sum(0..A+B) (\a. sum(0..A+B) (\K. if a <= K then
        u a * v (K - a) * x pow ((A + B) - K) else &0))` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    GEN_REWRITE_TAC LAND_CONV [SUM_SWAP_NUMSEG] THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `K:num` THEN STRIP_TAC THEN
    BETA_TAC THEN
    MP_TAC(ISPECL [`K:num`; `A + B:num`; `\a. (u:num->real) a * (v:num->real) (K - a)`]
      NV_PAL_SUM_COND_EXT) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[GSYM SUM_RMUL] THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN REPEAT STRIP_TAC THEN BETA_TAC THEN
    COND_CASES_TAC THEN REWRITE_TAC[REAL_MUL_LZERO; REAL_MUL_ASSOC]] THEN
  REWRITE_TAC[GSYM SUM_RMUL] THEN
  MP_TAC(ISPECL [`A:num`; `A + B:num`;
    `\a. ((u:num->real) a * (x:real) pow (A - a)) *
         sum (0..B) (\K. (v:num->real) K * x pow (B - K))`]
    NV_PAL_SUM_ZERO_EXT) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL [ARITH_TAC; ALL_TAC] THEN REPEAT STRIP_TAC THEN
    ASM_SIMP_TAC[REAL_MUL_LZERO];
    DISCH_THEN(SUBST1_TAC o SYM)] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `a:num` THEN STRIP_TAC THEN
  BETA_TAC THEN ASM_SIMP_TAC[NV_PAL_SHIFTV] THEN
  ASM_CASES_TAC `A < a:num` THENL
   [ASM_SIMP_TAC[REAL_MUL_LZERO; SUM_0]; ALL_TAC] THEN
  MP_TAC(ISPECL [`B:num`; `(A + B) - a:num`;
    `\j. (u:num->real) a * (v:num->real) ((j + a) - a) * (x:real) pow ((A + B) - (j + a))`]
    NV_PAL_SUM_ZERO_EXT) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN REPEAT STRIP_TAC THEN
    BETA_TAC THEN REWRITE_TAC[ADD_SUB] THEN ASM_SIMP_TAC[REAL_MUL_LZERO; REAL_MUL_RZERO];
    DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[GSYM SUM_LMUL] THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN
  X_GEN_TAC `j:num` THEN STRIP_TAC THEN BETA_TAC THEN REWRITE_TAC[ADD_SUB] THEN
  MP_TAC(SPECL [`A:num`;`B:num`;`a:num`;`j:num`] (ARITH_RULE
    `forall A B a j. j <= B /\ a <= A ==> (A + B) - (j + a) = (A - a) + (B - j:num)`)) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[REAL_POW_ADD] THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Digit expansion: A(x) B(x^p) with deg A < p.                              *)
(* ------------------------------------------------------------------------- *)

let NV_PAL_DIGIT_DM = prove
 (`forall p u l. l < p ==> (p * u + l) DIV p = u /\ (p * u + l) MOD p = l`,
  REPEAT STRIP_TAC THENL
   [MATCH_MP_TAC DIV_UNIQ THEN EXISTS_TAC `l:num`;
    MATCH_MP_TAC MOD_UNIQ THEN EXISTS_TAC `u:num`] THEN
  ASM_REWRITE_TAC[] THEN ARITH_TAC);;

let NV_PAL_DIGSUM = prove
 (`forall p (f:num->real) W. 1 <= p
     ==> sum(0..p * (W + 1) - 1) f = sum(0..W) (\u. sum(0..p-1) (\l. f(p * u + l)))`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN DISCH_TAC THENL
   [REWRITE_TAC[SUM_SING_NUMSEG; ADD_CLAUSES; MULT_CLAUSES; ETA_AX]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN
  REWRITE_TAC[SUM_CLAUSES_NUMSEG; LE_0] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  SUBGOAL_THEN `p * (SUC W + 1) - 1 = (p * (W + 1) - 1) + p:num` SUBST1_TAC THENL
   [REWRITE_TAC[ARITH_RULE `SUC W + 1 = (W + 1) + 1:num`; LEFT_ADD_DISTRIB;
                MULT_CLAUSES] THEN
    SUBGOAL_THEN `1 <= p * (W + 1):num` MP_TAC THENL
     [REWRITE_TAC[ARITH_RULE `1 <= n <=> ~(n = 0:num)`; MULT_EQ_0] THEN
      UNDISCH_TAC `1 <= p` THEN ARITH_TAC;
      ARITH_TAC];
    ALL_TAC] THEN
  SIMP_TAC[SUM_ADD_SPLIT; ARITH_RULE `0 <= n + 1:num`] THEN AP_TERM_TAC THEN
  SUBGOAL_THEN `(p * (W + 1) - 1) + 1 = 0 + p * SUC W /\
                (p * (W + 1) - 1) + p = (p - 1) + p * SUC W:num` (CONJUNCTS_THEN SUBST1_TAC)
  THENL
   [REWRITE_TAC[ADD1] THEN
    SUBGOAL_THEN `1 <= p * (W + 1):num` MP_TAC THENL
     [REWRITE_TAC[ARITH_RULE `1 <= n <=> ~(n = 0:num)`; MULT_EQ_0] THEN
      UNDISCH_TAC `1 <= p` THEN ARITH_TAC;
      UNDISCH_TAC `1 <= p` THEN ARITH_TAC];
    REWRITE_TAC[SUM_OFFSET] THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN
    REPEAT STRIP_TAC THEN REWRITE_TAC[ADD_SYM]]);;

let NV_PAL_RP_DIGIT = prove
 (`forall p W a c x. 1 <= p
     ==> nv_pal_rp (p - 1) a x * nv_pal_rp W c (x pow p) =
         nv_pal_rp (p * (W + 1) - 1) (\K. a (K MOD p) * c (K DIV p)) x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[nv_pal_rp] THEN
  ASM_SIMP_TAC[NV_PAL_DIGSUM] THEN
  REWRITE_TAC[REAL_MUL_SUM_NUMSEG] THEN
  GEN_REWRITE_TAC LAND_CONV [SUM_SWAP_NUMSEG] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `u:num` THEN STRIP_TAC THEN
  BETA_TAC THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `l:num` THEN
  STRIP_TAC THEN BETA_TAC THEN
  SUBGOAL_THEN `l < p:num` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[NV_PAL_DIGIT_DM] THEN
  SUBGOAL_THEN `p * (W + 1) - 1 - (p * u + l) = (p - 1 - l) + p * (W - u):num`
  SUBST1_TAC THENL
   [REWRITE_TAC[LEFT_SUB_DISTRIB; LEFT_ADD_DISTRIB; MULT_CLAUSES] THEN
    SUBGOAL_THEN `p * u <= p * W:num` MP_TAC THENL
     [REWRITE_TAC[LE_MULT_LCANCEL] THEN UNDISCH_TAC `u <= W:num` THEN ARITH_TAC;
      ALL_TAC] THEN
    UNDISCH_TAC `l < p:num` THEN ARITH_TAC;
    REWRITE_TAC[REAL_POW_ADD; REAL_POW_POW] THEN REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Reflection, padding, integrality and coefficient extraction.              *)
(* ------------------------------------------------------------------------- *)

let NV_PAL_RP_STD = prove
 (`forall D w x. nv_pal_rp D w x = sum(0..D) (\k. w (D - k) * x pow k)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[nv_pal_rp] THEN
  GEN_REWRITE_TAC LAND_CONV [SUM_REFLECT] THEN
  REWRITE_TAC[ARITH_RULE `~(D < 0:num)`; SUB_0] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN REPEAT STRIP_TAC THEN BETA_TAC THEN
  ASM_SIMP_TAC[ARITH_RULE `i <= D ==> D - (D - i) = i:num`]);;

let NV_PAL_RP_PAD = prove
 (`forall D s w x. nv_pal_rp D w x =
             nv_pal_rp (D + s) (\K. if s <= K then w (K - s) else &0) x`,
  REPEAT GEN_TAC THEN REWRITE_TAC[nv_pal_rp; COND_RATOR; COND_RAND;
    REAL_MUL_LZERO] THEN
  SIMP_TAC[NV_PAL_SHIFTV; ARITH_RULE `s <= D + s:num`; ADD_SUB] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN REPEAT STRIP_TAC THEN BETA_TAC THEN
  REWRITE_TAC[ARITH_RULE `(D + s) - (i + s) = D - i:num`]);;

let NV_PAL_RP_IP = prove
 (`forall p D w. prime p /\ (forall K. nv_pint p (w K)) ==> nv_pal_ip p (\x. nv_pal_rp D w x)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[NV_PAL_RP_STD] THEN
  MATCH_MP_TAC NV_PAL_IP_PINTPOLY THEN ASM_REWRITE_TAC[]);;

let NV_PAL_RP_COEFF = prove
 (`forall p D w w'. prime p /\ nv_pal_pc p (\x. nv_pal_rp D w x) (\x. nv_pal_rp D w' x)
     ==> forall K. K <= D ==> nv_cong p (w K) (w' K)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[NV_PAL_RP_STD] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`p:num`; `D:num`; `\k. (w:num->real) (D - k)`;
                 `\k. (w':num->real) (D - k)`] NV_PAL_PC_COEFF) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN X_GEN_TAC `K:num` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `D - K:num`) THEN
  ASM_SIMP_TAC[ARITH_RULE `K <= D ==> D - (D - K) = K:num`; ARITH_RULE `D - K <= D:num`]);;

(* ------------------------------------------------------------------------- *)
(* G, S_(p-i) and S_i as reversed polynomials of degree p - 1.               *)
(* ------------------------------------------------------------------------- *)

let NV_PAL_SUM_EVEN = prove
 (`forall m (f:num->real). sum(0..2 * m) (\d. if EVEN d then f (d DIV 2) else &0) =
                     sum(0..m) f`,
  INDUCT_TAC THEN GEN_TAC THENL
   [REWRITE_TAC[MULT_CLAUSES; SUM_SING_NUMSEG; EVEN] THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[ARITH_RULE `2 * SUC m = SUC(SUC(2 * m))`; SUM_CLAUSES_NUMSEG] THEN
  ASM_REWRITE_TAC[LE_0; EVEN; EVEN_DOUBLE] THEN
  REWRITE_TAC[ARITH_RULE `SUC(SUC(2 * m)) = 2 * SUC m`; NV_PAL_DIV2] THEN
  REAL_ARITH_TAC);;

let NV_PAL_G_RP = prove
 (`forall p x. ODD p ==> nv_pal_G p x = nv_pal_rp (p - 1) (nv_Ecoef p) x`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ODD_EXISTS] THEN
  DISCH_THEN(X_CHOOSE_THEN `m:num` SUBST1_TAC) THEN
  REWRITE_TAC[nv_pal_G; nv_pal_rp; nv_Ecoef; SUC_SUB1; NV_PAL_DIV2] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `sum(0..2 * m) (\d. if EVEN d then
     (\j. (--(&1)) pow j * &(binom(m,j)) * (x pow 2) pow (m - j)) (d DIV 2)
     else &0)` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[NV_PAL_SUM_EVEN] THEN
    REWRITE_TAC[REAL_ARITH `x pow 2 - &1 = --(&1) + x pow 2`;
                REAL_BINOMIAL_THEOREM] THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN REPEAT STRIP_TAC THEN BETA_TAC THEN
    REAL_ARITH_TAC;
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `d:num` THEN STRIP_TAC THEN
    BETA_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[REAL_MUL_LZERO] THEN
    FIRST_X_ASSUM(X_CHOOSE_THEN `j:num` SUBST_ALL_TAC o REWRITE_RULE[EVEN_EXISTS]) THEN
    REWRITE_TAC[NV_PAL_DIV2; REAL_POW_POW; GSYM LEFT_SUB_DISTRIB] THEN
    REAL_ARITH_TAC]);;

let NV_PAL_CHEB_RP = prove
 (`forall n D x. n <= D ==> sum(0..n) (\k. cheb_U n k * x pow k) =
                      nv_pal_rp D (\l. cheb_U n (D - l)) x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[NV_PAL_RP_STD] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `sum(0..D) (\k. cheb_U n k * x pow k)` THEN CONJ_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC NV_PAL_TRUNC THEN
    ASM_SIMP_TAC[NV_CHEB_U_DEG];
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN REPEAT STRIP_TAC THEN BETA_TAC THEN
    ASM_SIMP_TAC[ARITH_RULE `i <= D ==> D - (D - i) = i:num`]]);;

let NV_PAL_SA_RP = prove
 (`forall p i x. i < p ==> nv_pal_S (p - i) x = nv_pal_rp (p - 1) (\l. nv_a p l i) x`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[nv_pal_S; nv_a; ARITH_RULE `i < p ==> ~(p - i = 0:num)`;
               ARITH_RULE `i < p ==> p - i - 1 = p - 1 - i:num`] THEN
  MATCH_MP_TAC NV_PAL_CHEB_RP THEN ARITH_TAC);;

let NV_PAL_SB_RP = prove
 (`forall p i x. i <= p ==> nv_pal_S i x = nv_pal_rp (p - 1) (\l. nv_b p l i) x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[nv_pal_S; nv_b] THEN
  ASM_CASES_TAC `i = 0` THEN ASM_REWRITE_TAC[] THENL
   [REWRITE_TAC[nv_pal_rp; REAL_MUL_LZERO; SUM_0]; ALL_TAC] THEN
  MATCH_MP_TAC NV_PAL_CHEB_RP THEN ASM_ARITH_TAC);;
