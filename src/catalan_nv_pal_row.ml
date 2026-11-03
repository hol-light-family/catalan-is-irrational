(* ========================================================================= *)
(* CAT_NONVANISHING, part P: the rows cat_pcoef / cat_dcoef as reversed      *)
(* polynomials in x = 1/t:                                                   *)
(*   rp (65N-1) (cat_pcoef N r) x = (x-1)^(2N) T_d(x),                       *)
(*   rp (65N-1) (cat_dcoef N r) x = sgn (x-1)^(2N) U_(d-1)(x),  d = |r-4N|. *)
(* ========================================================================= *)

needs "src/catalan_nv_pal_rp.ml";;

let NV_PAL_REVC = prove
 (`forall C H c t. ~(t = &0) /\ 1 <= C /\ C - 1 <= H
    ==> sum(0..H) (\m. cat_revc C c m * t pow m) =
        t pow (C - 1) * sum(0..C-1) (\j. c j * inv t pow j)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\m. cat_revc C c m * (t:real) pow m`; `0..C-1`; `0..H`]
    SUM_SUPERSET) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[SUBSET_NUMSEG; IN_NUMSEG; cat_revc] THEN
    CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    REPEAT STRIP_TAC THEN COND_CASES_TAC THEN
    REWRITE_TAC[REAL_MUL_LZERO] THEN ASM_ARITH_TAC;
    DISCH_THEN SUBST1_TAC] THEN
  GEN_REWRITE_TAC LAND_CONV [SUM_REFLECT] THEN
  REWRITE_TAC[ARITH_RULE `~(n < 0:num)`; SUB_0; GSYM SUM_LMUL] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[cat_revc; ARITH_RULE `1 <= C /\ i <= C - 1 ==> C - 1 - i < C:num`;
    ARITH_RULE `i <= C - 1 ==> C - 1 - (C - 1 - i) = i:num`; REAL_POW_SUB;
    REAL_POW_INV] THEN
  REWRITE_TAC[real_div] THEN REAL_ARITH_TAC);;

let NV_PAL_BINOM1 = prove
 (`forall h (t:real). (&1 - t) pow h =
         sum(0..h) (\v. (--(&1)) pow v * &(binom(h,v)) * t pow v)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[REAL_ARITH `&1 - t = --(&1) * t + &1`; REAL_BINOMIAL_THEOREM;
              REAL_POW_ONE; REAL_MUL_RID; REAL_POW_MUL] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
  REAL_ARITH_TAC);;

let NV_PAL_MULFAC = prove
 (`forall h H (c:num->real) (t:real). h <= H /\ (forall j. H - h < j ==> c j = &0)
    ==> sum(0..H) (\i. cat_mulfac h c i * t pow i) =
        (&1 - t) pow h * sum(0..H-h) (\j. c j * t pow j)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[cat_mulfac; GSYM SUM_RMUL] THEN
  GEN_REWRITE_TAC LAND_CONV [SUM_SWAP_NUMSEG] THEN
  REWRITE_TAC[NV_PAL_BINOM1; GSYM SUM_RMUL] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `v:num` THEN STRIP_TAC THEN
  REWRITE_TAC[COND_RATOR; COND_RAND; REAL_MUL_LZERO] THEN
  SUBGOAL_THEN `v:num <= H` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[NV_PAL_SHIFTV; ADD_SUB] THEN
  MP_TAC(ISPECL [`H - h:num`; `H - v:num`; `c:num->real`; `t:real`]
    NV_PAL_TRUNC) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[GSYM SUM_LMUL; GSYM SUM_RMUL] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[REAL_POW_ADD] THEN REAL_ARITH_TAC);;

let NV_PAL_ROWGEN = prove
 (`forall N c (t:real). 1 <= N /\ ~(t = &0)
    ==> sum(0..65 * N)
          (\i. cat_mulfac (2 * N) (cat_revc (63 * N) c) i * t pow i) =
        (&1 - t) pow (2 * N) * t pow (63 * N - 1) *
        sum(0..63 * N - 1) (\j. c j * inv t pow j)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`2 * N`; `65 * N`; `cat_revc (63 * N) c`; `t:real`]
    NV_PAL_MULFAC) THEN
  REWRITE_TAC[ARITH_RULE `65 * N - 2 * N = 63 * N`] THEN
  ANTS_TAC THENL
   [REWRITE_TAC[cat_revc] THEN CONJ_TAC THENL [ARITH_TAC; ALL_TAC] THEN
    REPEAT STRIP_TAC THEN COND_CASES_TAC THEN ASM_ARITH_TAC;
    DISCH_THEN SUBST1_TAC] THEN
  AP_TERM_TAC THEN MATCH_MP_TAC NV_PAL_REVC THEN
  ASM_ARITH_TAC);;

let NV_PAL_MULFAC_TOP = prove
 (`forall N c. cat_mulfac (2 * N) (cat_revc (63 * N) c) (65 * N) = &0`,
  REPEAT GEN_TAC THEN REWRITE_TAC[cat_mulfac; cat_revc] THEN
  MATCH_MP_TAC SUM_EQ_0 THEN X_GEN_TAC `v:num` THEN
  REWRITE_TAC[IN_NUMSEG] THEN STRIP_TAC THEN
  COND_CASES_TAC THEN REWRITE_TAC[] THEN
  COND_CASES_TAC THEN REWRITE_TAC[REAL_MUL_RZERO] THEN ASM_ARITH_TAC);;

let NV_PAL_RP_INV = prove
 (`forall D w x. ~(x = &0)
     ==> nv_pal_rp D w x = x pow D * sum(0..D) (\K. w K * inv x pow K)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[nv_pal_rp; GSYM SUM_LMUL] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN REPEAT STRIP_TAC THEN BETA_TAC THEN
  ASM_SIMP_TAC[REAL_POW_SUB; REAL_POW_INV; real_div] THEN REAL_ARITH_TAC);;

let NV_PAL_ROWGEN_X = prove
 (`forall N c x. 1 <= N /\ ~(x = &0)
    ==> nv_pal_rp (65 * N - 1) (cat_mulfac (2 * N) (cat_revc (63 * N) c)) x =
        (x - &1) pow (2 * N) * sum(0..63 * N - 1) (\j. c j * x pow j)`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[NV_PAL_RP_INV] THEN
  SUBGOAL_THEN
   `sum(0..65 * N - 1) (\K. cat_mulfac (2 * N) (cat_revc (63 * N) c) K * inv x pow K) =
    sum(0..65 * N) (\K. cat_mulfac (2 * N) (cat_revc (63 * N) c) K * inv x pow K)`
  SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC NV_PAL_SUM_ZERO_EXT THEN
    CONJ_TAC THENL [ARITH_TAC; ALL_TAC] THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN
    SUBGOAL_THEN `j = 65 * N` SUBST1_TAC THENL
     [ASM_ARITH_TAC; REWRITE_TAC[NV_PAL_MULFAC_TOP; REAL_MUL_LZERO]];
    ALL_TAC] THEN
  ASM_SIMP_TAC[NV_PAL_ROWGEN; REAL_INV_EQ_0; REAL_INV_INV] THEN
  SUBGOAL_THEN `(x:real) pow (65 * N - 1) = x pow (2 * N) * x pow (63 * N - 1)`
  SUBST1_TAC THENL
   [REWRITE_TAC[GSYM REAL_POW_ADD] THEN AP_TERM_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `((x:real) - &1) pow (2 * N) = x pow (2 * N) * (&1 - inv x) pow (2 * N)`
  SUBST1_TAC THENL
   [REWRITE_TAC[GSYM REAL_POW_MUL] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    UNDISCH_TAC `~(x = &0)` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  SUBGOAL_THEN `(x:real) pow (63 * N - 1) * inv x pow (63 * N - 1) = &1` MP_TAC THENL
   [ASM_SIMP_TAC[GSYM REAL_POW_MUL; REAL_MUL_RINV; REAL_POW_ONE]; ALL_TAC] THEN
  CONV_TAC REAL_RING);;

let NV_PAL_DIST_LE = prove
 (`forall N r. r <= 48 * N ==> cat_dist N r <= 44 * N`,
  REWRITE_TAC[cat_dist] THEN ARITH_TAC);;

let NV_PAL_ROWP_NZ = prove
 (`forall N r x. 1 <= N /\ r <= 48 * N /\ ~(x = &0)
    ==> nv_pal_rp (65 * N - 1) (cat_pcoef N r) x =
        (x - &1) pow (2 * N) * nv_pal_T (cat_dist N r) x`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `cat_pcoef N r =
     cat_mulfac (2 * N) (cat_revc (63 * N) (cheb_T (cat_dist N r)))` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; cat_pcoef]; ALL_TAC] THEN
  ASM_SIMP_TAC[NV_PAL_ROWGEN_X; nv_pal_T] THEN AP_TERM_TAC THEN
  MATCH_MP_TAC NV_PAL_TRUNC THEN SIMP_TAC[NV_CHEB_T_DEG] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP NV_PAL_DIST_LE) THEN
  UNDISCH_TAC `1 <= N` THEN ARITH_TAC);;

let NV_PAL_ROWD_NZ = prove
 (`forall N r x. 1 <= N /\ r <= 48 * N /\ ~(x = &0)
    ==> nv_pal_rp (65 * N - 1) (cat_dcoef N r) x =
        cat_sgn N r * (x - &1) pow (2 * N) * nv_pal_S (cat_dist N r) x`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `cat_dcoef N r =
     (\i. cat_sgn N r * cat_mulfac (2 * N)
              (cat_revc (63 * N) (cheb_U (cat_dist N r - 1))) i)` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; cat_dcoef]; ALL_TAC] THEN
  REWRITE_TAC[nv_pal_rp; GSYM REAL_MUL_ASSOC; SUM_LMUL] THEN
  REWRITE_TAC[GSYM nv_pal_rp; ETA_AX] THEN
  ASM_SIMP_TAC[NV_PAL_ROWGEN_X; nv_pal_S] THEN
  ASM_CASES_TAC `cat_dist N r = 0` THENL
   [SUBGOAL_THEN `cat_sgn N r = &0` (fun th -> REWRITE_TAC[th; REAL_MUL_LZERO]) THEN
    UNDISCH_TAC `cat_dist N r = 0` THEN REWRITE_TAC[cat_dist; cat_sgn] THEN
    REPEAT COND_CASES_TAC THEN ASM_ARITH_TAC;
    ASM_REWRITE_TAC[]] THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN
  MATCH_MP_TAC NV_PAL_TRUNC THEN SIMP_TAC[NV_CHEB_U_DEG] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP NV_PAL_DIST_LE) THEN
  UNDISCH_TAC `1 <= N` THEN ARITH_TAC);;

let NV_PAL_PCOEF_IP = prove
 (`forall p N r. prime p ==> nv_pal_ip p (\x. nv_pal_rp (65 * N - 1) (cat_pcoef N r) x) /\
                       nv_pal_ip p (\x. nv_pal_rp (65 * N - 1) (cat_dcoef N r) x)`,
  SIMP_TAC[NV_PAL_RP_IP; NV_PINT_INTEGER; NV_PCOEF_INT]);;

let NV_PAL_SGN_PINT = prove
 (`forall p N r. prime p ==> nv_pint p (cat_sgn N r)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[cat_sgn] THEN
  REPEAT COND_CASES_TAC THEN ASM_SIMP_TAC[NV_PINT_NUM; NV_PINT_NEG]);;

let NV_PAL_ROWP = prove
 (`forall N r x. 1 <= N /\ r <= 48 * N
    ==> nv_pal_rp (65 * N - 1) (cat_pcoef N r) x =
        (x - &1) pow (2 * N) * nv_pal_T (cat_dist N r) x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN SPEC_TAC(`x:real`,`x:real`) THEN
  MATCH_MP_TAC(ISPEC `2` NV_PAL_IP_EXT) THEN ASSUME_TAC PRIME_2 THEN
  ASM_SIMP_TAC[NV_PAL_PCOEF_IP] THEN CONJ_TAC THENL
   [NV_PAL_IP_TAC;
    REPEAT STRIP_TAC THEN MATCH_MP_TAC NV_PAL_ROWP_NZ THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]);;

let NV_PAL_ROWD = prove
 (`forall N r x. 1 <= N /\ r <= 48 * N
    ==> nv_pal_rp (65 * N - 1) (cat_dcoef N r) x =
        cat_sgn N r * (x - &1) pow (2 * N) * nv_pal_S (cat_dist N r) x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN SPEC_TAC(`x:real`,`x:real`) THEN
  MATCH_MP_TAC(ISPEC `2` NV_PAL_IP_EXT) THEN ASSUME_TAC PRIME_2 THEN
  ASM_SIMP_TAC[NV_PAL_PCOEF_IP] THEN CONJ_TAC THENL
   [MATCH_MP_TAC NV_PAL_IP_CMUL THEN ASM_SIMP_TAC[NV_PAL_SGN_PINT] THEN
    NV_PAL_IP_TAC;
    REPEAT STRIP_TAC THEN MATCH_MP_TAC NV_PAL_ROWD_NZ THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]);;
