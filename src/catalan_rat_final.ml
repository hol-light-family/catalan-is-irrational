(* ========================================================================= *)
(* CAT_RATIONALITY (Proposition 2.1): cat_detq G N = cat_det N.            *)
(* ========================================================================= *)

needs "src/catalan_components.ml";;
needs "src/catalan_rat_base.ml";;
needs "src/catalan_rat_alg.ml";;
needs "src/catalan_rat_series.ml";;
needs "src/catalan_rat_kvals.ml";;
needs "src/catalan_rat_mom.ml";;

(* ------------------------------------------------------------------------- *)
(* Evaluation of the monomial moments, Equation (17).                        *)
(* ------------------------------------------------------------------------- *)

let RAT_M00 = prove
 (`rat_M 0 0 = &4 * catalan_constant`,
  REWRITE_TAC[RAT_M_INTEGRAL; real_pow; REAL_MUL_LID] THEN
  MATCH_MP_TAC RAT_K0 THEN
  MP_TAC(SPECL [`0`; `0`] RAT_MIX_SERIES) THEN
  SIMP_TAC[real_pow; REAL_MUL_LID]);;

let RAT_M01 = prove
 (`rat_M 0 1 = &3 / &2 * rat_kappa`,
  REWRITE_TAC[RAT_M_INTEGRAL; rat_kappa; RAT_Z_INTEGRAL; real_pow;
              REAL_MUL_LID] THEN
  MATCH_MP_TAC RAT_K1 THEN
  MP_TAC(SPECL [`0`; `1`] RAT_MIX_SERIES) THEN
  MP_TAC(SPECL [`0`; `0`] RAT_ZETA_SERIES) THEN
  SIMP_TAC[real_pow; REAL_MUL_LID] THEN REWRITE_TAC[ETA_AX] THEN
  SIMP_TAC[]);;

let RAT_M_EVAL = prove
 (`forall i j. rat_M i j = cat_M0 i j + &4 * catalan_constant * cat_ckern i j +
                     &3 / &2 * rat_kappa *
                     (if i < j then cat_ckern (j - 1) i else &0)`,
  MATCH_MP_TAC RAT_MSERIES_EVAL THEN
  REWRITE_TAC[RAT_M_SUMS; RAT_M00; RAT_M01]);;

let RAT_Z_EVAL = prove
 (`forall i j. rat_Z i j = cat_Z0 i j + (if i = j then rat_kappa else &0)`,
  REWRITE_TAC[rat_kappa] THEN MATCH_MP_TAC RAT_ZSERIES_EVAL THEN
  REWRITE_TAC[RAT_Z_SUMS]);;

(* ------------------------------------------------------------------------- *)
(* Raw entries, Equation (20), using the zeta(2) cancellation.              *)
(* ------------------------------------------------------------------------- *)

let RAT_RAW = prove
 (`forall N r j. 1 <= N /\ r < 48 * N /\ j < 59 * N
     ==> sum(0..65 * N) (\i. cat_pcoef N r i * rat_M i j) -
         &3 / &2 * sum(0..65 * N) (\i. cat_dcoef N r i * rat_Z i j) =
         cat_rawq catalan_constant N r j`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `sum(0..65 * N) (\i. cat_pcoef N r i * rat_M i j) =
    sum(0..65 * N) (\i. cat_pcoef N r i *
                        (cat_M0 i j + &4 * catalan_constant * cat_ckern i j)) +
    &3 / &2 * rat_kappa * cat_dcoef N r j` SUBST1_TAC THENL
   [FIRST_ASSUM(fun th -> REWRITE_TAC[GSYM(MATCH_MP RAT_CANCEL th)] o
      check (fun t -> false)) ORELSE ALL_TAC THEN
    MP_TAC(SPECL [`N:num`; `r:num`; `j:num`] RAT_CANCEL) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[RAT_M_EVAL; GSYM SUM_LMUL; GSYM SUM_ADD_NUMSEG] THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `sum(0..65 * N) (\i. cat_dcoef N r i * rat_Z i j) =
    sum(0..65 * N) (\i. cat_dcoef N r i * cat_Z0 i j) +
    rat_kappa * cat_dcoef N r j` SUBST1_TAC THENL
   [REWRITE_TAC[RAT_Z_EVAL; REAL_ADD_LDISTRIB; SUM_ADD_NUMSEG] THEN
    AP_TERM_TAC THEN
    TRANS_TAC EQ_TRANS
     `sum(0..65 * N) (\i. if i = j then rat_kappa * cat_dcoef N r j else &0)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SUM_EQ_NUMSEG THEN REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC[REAL_MUL_RZERO] THEN REAL_ARITH_TAC;
      REWRITE_TAC[SUM_DELTA; IN_NUMSEG] THEN
      COND_CASES_TAC THEN REWRITE_TAC[] THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[cat_rawq] THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Filtered entries.                                                         *)
(* ------------------------------------------------------------------------- *)

let RAT_ROWP = prove
 (`forall N r. cat_rowP N r = (\t. sum(0..65 * N) (\i. cat_pcoef N r i * t pow i))`,
  REWRITE_TAC[FUN_EQ_THM; cat_rowP; cat_poly]);;

let RAT_ROWD = prove
 (`forall N r. cat_rowD N r = (\t. sum(0..65 * N) (\i. cat_dcoef N r i * t pow i))`,
  REWRITE_TAC[FUN_EQ_THM; cat_rowD; cat_poly]);;

let RAT_NEG_POW = prove
 (`forall s v. (--s) pow v = (--(&1)) pow v * s pow v`,
  REWRITE_TAC[GSYM REAL_POW_MUL; REAL_MUL_LNEG; REAL_MUL_LID]);;

let RAT_PSI = prove
 (`forall N k. cat_psi N k =
         (\s. sum(0..4 * N) (\v. ((--(&1)) pow v * &(binom(4 * N,v))) *
                                 s pow (7 * N + k + v)))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[FUN_EQ_THM; cat_psi] THEN X_GEN_TAC `s:real` THEN
  REWRITE_TAC[REAL_ARITH `&1 - s = --s + &1`] THEN REWRITE_TAC[REAL_BINOMIAL_THEOREM] THEN
  REWRITE_TAC[GSYM SUM_LMUL; REAL_POW_ONE; REAL_MUL_RID] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
  ONCE_REWRITE_TAC[RAT_NEG_POW] THEN REWRITE_TAC[REAL_POW_ONE; REAL_MUL_RID; ADD_ASSOC; REAL_POW_ADD] THEN
  REAL_ARITH_TAC);;

let RAT_ENTRY = prove
 (`forall N r k. 1 <= N /\ r < 48 * N /\ k < 48 * N
     ==> cat_entryq catalan_constant N r k = cat_entry N r k`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[cat_entry; RAT_ROWP; RAT_ROWD; RAT_PSI; RAT_MIXED_LIN;
              RAT_ZETA_LIN; cat_entryq] THEN
  ONCE_REWRITE_TAC[SUM_SWAP_NUMSEG] THEN
  REWRITE_TAC[GSYM SUM_LMUL; GSYM SUM_SUB_NUMSEG] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `v:num` THEN STRIP_TAC THEN
  REWRITE_TAC[] THEN
  MP_TAC(SPECL [`N:num`; `r:num`; `7 * N + k + v`] RAT_RAW) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[REAL_MUL_ASSOC; GSYM SUM_LMUL; GSYM SUM_RMUL; REAL_SUB_LDISTRIB;
              GSYM SUM_SUB_NUMSEG] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
  REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Determinants.                                                             *)
(* ------------------------------------------------------------------------- *)

let RAT_NDET_EQ = prove
 (`forall s a b. (forall i j. i IN s /\ j IN s ==> a i j = b i j) ==> ndet s a = ndet s b`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[ndet] THEN
  MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `p:num->num` THEN
  REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN REWRITE_TAC[] THEN
  AP_TERM_TAC THEN MATCH_MP_TAC PRODUCT_EQ THEN
  ASM_MESON_TAC[PERMUTES_IN_IMAGE]);;

let CAT_RATIONALITY_THM = prove
 (`CAT_RATIONALITY`,
  REWRITE_TAC[CAT_RATIONALITY; cat_detq; cat_det] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC RAT_NDET_EQ THEN REWRITE_TAC[IN_NUMSEG] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC RAT_ENTRY THEN ASM_ARITH_TAC);;
