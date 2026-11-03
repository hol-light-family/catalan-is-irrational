(* ========================================================================= *)
(* rp_ip final: Proposition 5.2 (interpolation estimate) from RP_LA_STMT    *)
(* (|det| <= norm^n for a positive definite form) and RP_PICK_STMT (Pick   *)
(* form bound for the interpolation data h_i = c_i x_i^D).                  *)
(* ========================================================================= *)

needs "src/catalan_rp_ip_main.ml";;

(* xi_f x^m + xi_n x^(r+D) = (x^m + h(x) x^r) xi_f, h = rp_hval D *)
let RP_IP_ROW_FACTOR = prove
 (`forall D x r m.
     rp_xif x * x pow m + rp_xin x * x pow (r + D) =
     (x pow m + rp_hval D x * x pow r) * rp_xif x`,
  REPEAT GEN_TAC THEN REWRITE_TAC[rp_xif; rp_xin; rp_hval; REAL_POW_ADD] THEN
  COND_CASES_TAC THEN CONV_TAC REAL_RING);;

let RP_IP_THM = prove
 (`RP_LA_STMT /\ RP_PICK_STMT ==> RP_INTERP_STMT`,
  REWRITE_TAC[RP_INTERP_STMT] THEN STRIP_TAC THEN
  MAP_EVERY X_GEN_TAC [`N:num`; `x:num->real`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `rp_ip_ok (48 * N) x` ASSUME_TAC THENL
   [UNDISCH_TAC `rp_nodes (48 * N) x` THEN REWRITE_TAC[rp_nodes; rp_ip_ok] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ASM_ARITH_TAC;
      ASM_MESON_TAC[REAL_ARITH `--(&1) < a /\ a < &1 ==> abs a < &1`]];
    ALL_TAC] THEN
  REWRITE_TAC[rp_R] THEN
  SUBGOAL_THEN
   `ndet {i | i < 48 * N}
      (\r i. rp_xif (x i) * x i pow (48 * N - 1 - r) +
             rp_xin (x i) * x i pow (r + 40 * N - 1)) =
    ndet {i | i < 48 * N}
      (\r i. x i pow (48 * N - 1 - r) +
             rp_hval (40 * N - 1) (x i) * x i pow r) *
    product {i | i < 48 * N} (\i. rp_xif (x i))`
  SUBST1_TAC THENL
   [MP_TAC(ISPECL [`{i:num | i < 48 * N}`; `\i. rp_xif((x:num->real) i)`;
      `\r i. (x:num->real) i pow (48 * N - 1 - r) +
             rp_hval (40 * N - 1) (x i) * x i pow r`]
      RP_IP_NDET_COLUMNS_MUL) THEN
    REWRITE_TAC[FINITE_NUMSEG_LT] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC RP_IP_NDET_EQ THEN REPEAT STRIP_TAC THEN
    REWRITE_TAC[RP_IP_ROW_FACTOR];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `abs(ndet {i | i < 48 * N}
         (\r i. (x:num->real) i pow (48 * N - 1 - r) +
                rp_hval (40 * N - 1) (x i) * x i pow r))` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[REAL_ABS_MUL] THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_ABS_POS] THEN
    SIMP_TAC[GSYM PRODUCT_ABS; FINITE_NUMSEG_LT] THEN
    MATCH_MP_TAC PRODUCT_LE_1 THEN REWRITE_TAC[FINITE_NUMSEG_LT; REAL_ABS_POS] THEN
    REPEAT STRIP_TAC THEN REWRITE_TAC[rp_xif] THEN COND_CASES_TAC THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC RP_IP_MAIN THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[rp_K0] THEN MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL
     [MP_TAC(SPEC `&12` REAL_EXP_POS_LT) THEN REAL_ARITH_TAC;
      REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  X_GEN_TAC `a:num->real` THEN REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`48 * N`; `40 * N - 1`; `x:num->real`;
                                `a:num->real`] o
                GEN_REWRITE_RULE I [RP_PICK_STMT]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_ARITH_TAC);;
