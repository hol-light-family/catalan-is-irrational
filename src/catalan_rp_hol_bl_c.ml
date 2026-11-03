(* ========================================================================= *)
(* rp_hol_bl_: conjunct 8 of RP_HOL_BL_STMT, part 1: real inequalities and  *)
(* the bound |F(iu)| <= 1 on the imaginary axis                              *)
(* ========================================================================= *)

needs "src/catalan_rp_hol_bl_b.ml";;

let RP_HOL_BL_LOG_DERIV = prove
 (`forall c t. &0 < c /\ &0 < t ==>
   ((\t. (&1 - c) / (&1 + c) * log t - log(t + c) + log(&1 + c * t))
    has_real_derivative
    ((&1 - c) / (&1 + c) * inv t - inv(t + c) + c * inv(&1 + c * t)))
   (atreal t)`,
  REPEAT STRIP_TAC THEN REAL_DIFF_TAC THEN
  MP_TAC(SPECL [`c:real`; `t:real`] REAL_LT_MUL) THEN ASM_REWRITE_TAC[] THEN
  ASM_REAL_ARITH_TAC);;

let RP_HOL_BL_LOG_DERIV_POS = prove
 (`forall c t. &0 < c /\ c < &1 /\ &0 < t ==>
   &0 <= (&1 - c) / (&1 + c) * inv t - inv(t + c) + c * inv(&1 + c * t)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < c * t` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_MUL]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(&1 - c) / (&1 + c) * inv t - inv(t + c) + c * inv(&1 + c * t) =
    ((&1 - c) * c * (t - &1) pow 2) / ((&1 + c) * t * (t + c) * (&1 + c * t))`
  SUBST1_TAC THENL
   [MATCH_MP_TAC(REAL_FIELD
     `~(&1 + c = &0) /\ ~(t = &0) /\ ~(t + c = &0) /\ ~(&1 + c * t = &0)
      ==> (&1 - c) / (&1 + c) * inv t - inv(t + c) + c * inv(&1 + c * t) =
          ((&1 - c) * c * (t - &1) pow 2) /
          ((&1 + c) * t * (t + c) * (&1 + c * t))`) THEN
    ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_DIV THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[REAL_LE_POW_2];
    REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN ASM_REAL_ARITH_TAC]);;

let RP_HOL_BL_LOG_INEQ = prove
 (`forall c s. &0 < c /\ c < &1 /\ &0 < s /\ s <= &1
     ==> (&1 - c) / (&1 + c) * log s <= log(s + c) - log(&1 + c * s)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL
   [`\t. (&1 - c) / (&1 + c) * log t - log(t + c) + log(&1 + c * t)`;
    `\t. (&1 - c) / (&1 + c) * inv t - inv(t + c) + c * inv(&1 + c * t)`;
    `{t:real | &0 < t}`; `s:real`; `&1`] HAS_REAL_DERIVATIVE_INCREASING_IMP) THEN
  REWRITE_TAC[IN_ELIM_THM; LOG_1] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_LT_01] THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[is_realinterval; IN_ELIM_THM] THEN REAL_ARITH_TAC;
      REPEAT STRIP_TAC THEN MATCH_MP_TAC HAS_REAL_DERIVATIVE_ATREAL_WITHIN THEN
      MATCH_MP_TAC RP_HOL_BL_LOG_DERIV THEN ASM_REWRITE_TAC[];
      REPEAT STRIP_TAC THEN MATCH_MP_TAC RP_HOL_BL_LOG_DERIV_POS THEN
      ASM_REWRITE_TAC[]];
    REWRITE_TAC[REAL_MUL_RID; REAL_MUL_RZERO] THEN REAL_ARITH_TAC]);;

let RP_HOL_BL_PROD_INEQ = prove
 (`forall n D (c:num->real) s.
     (forall i. i < n ==> &0 < c i /\ c i < &1) /\ &0 < s /\ s <= &1 /\
     sum {i | i < n} (\i. (&1 - c i) / (&1 + c i)) <= &D
     ==> s pow D <= product {i | i < n} (\i. (s + c i) / (&1 + c i * s))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `forall i:num. i < n ==> &0 < (s + (c:num->real) i) / (&1 + c i * s)` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LT_DIV THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN MP_TAC(SPECL [`(c:num->real) i`; `s:real`] REAL_LT_MUL) THEN
    ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`(s:real) pow D`;
     `product {i | i < n} (\i. (s + (c:num->real) i) / (&1 + c i * s))`] LOG_MONO_LE) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[REAL_POW_LT] THEN MATCH_MP_TAC PRODUCT_POS_LT THEN
    ASM_SIMP_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM]; ALL_TAC] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  ASM_SIMP_TAC[LOG_POW; LOG_PRODUCT; FINITE_NUMSEG_LT; IN_ELIM_THM] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum {i | i < n} (\i. (&1 - (c:num->real) i) / (&1 + c i) * log s)` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[SUM_RMUL] THEN
    SUBGOAL_THEN `log s <= &0` ASSUME_TAC THENL
     [REWRITE_TAC[GSYM LOG_1] THEN MATCH_MP_TAC LOG_MONO_LE_IMP THEN
      ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ABBREV_TAC `S = sum {i | i < n} (\i. (&1 - (c:num->real) i) / (&1 + c i))` THEN
    MP_TAC(SPECL [`&D - S:real`; `--log(s:real)`] REAL_LE_MUL) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
    MATCH_MP_TAC SUM_LE THEN REWRITE_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM] THEN
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN ASM_REWRITE_TAC[] THEN
    REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `&0 < c(i:num) * s` ASSUME_TAC THENL
     [ASM_SIMP_TAC[REAL_LT_MUL]; ALL_TAC] THEN
    ASM_SIMP_TAC[LOG_DIV; REAL_ARITH `&0 < s /\ &0 < c ==> &0 < s + c`;
                 REAL_ARITH `&0 < x ==> &0 < &1 + x`] THEN
    MATCH_MP_TAC RP_HOL_BL_LOG_INEQ THEN ASM_REWRITE_TAC[]]);;

let RP_HOL_BL_PROD_POW2 = prove
 (`forall f s:A->bool. FINITE s ==> product s f pow 2 = product s (\i. f i pow 2)`,
  SIMP_TAC[REAL_POW_2; PRODUCT_MUL]);;

let RP_HOL_BL_AXIS_FACTOR = prove
 (`forall x u. (norm(Cx(&1) - Cx x * (ii * Cx u)) / norm(ii * Cx u - Cx x)) pow 2 =
         (&1 + x pow 2 * u pow 2) / (u pow 2 + x pow 2)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[REAL_POW_DIV; COMPLEX_SQNORM] THEN
  REWRITE_TAC[RE_SUB; IM_SUB; RE_MUL_CX; IM_MUL_CX; RE_MUL_II; IM_MUL_II;
              RE_CX; IM_CX] THEN
  BINOP_TAC THEN CONV_TAC REAL_RING);;
let RP_HOL_BL_SQ_LE1 = prove
 (`forall a. &0 <= a /\ a pow 2 <= &1 ==> a <= &1`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`a - &1`; `a + &1`] REAL_LT_MUL) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  UNDISCH_TAC `a pow 2 <= &1` THEN REWRITE_TAC[REAL_POW_2] THEN REAL_ARITH_TAC);;

let RP_HOL_BL_AXIS = prove
 (`forall n D (x:num->real) u.
     ~(D = 0) /\ (forall i. i < n ==> ~(x i = &0) /\ abs(x i) < &1) /\
     sum {i | i < n} (\i. (&1 - x i pow 2) / (&1 + x i pow 2)) <= &D /\
     abs u <= &1
     ==> norm(rp_hol_F n D x (ii * Cx u)) <= &1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `u:real = &0` THENL
   [ASM_REWRITE_TAC[rp_hol_F; COMPLEX_MUL_RZERO; COMPLEX_POW_ZERO;
                    COMPLEX_MUL_LZERO; COMPLEX_NORM_0] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < (u:real) pow 2 /\ u pow 2 <= &1` STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[REAL_LT_POW_2] THEN ONCE_REWRITE_TAC[GSYM REAL_POW2_ABS] THEN
    MATCH_MP_TAC REAL_POW_1_LE THEN ASM_REWRITE_TAC[REAL_ABS_POS]; ALL_TAC] THEN
  MP_TAC(ISPECL [`n:num`; `D:num`; `\i. (x:num->real) i pow 2`; `(u:real) pow 2`]
    RP_HOL_BL_PROD_INEQ) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN
    ASM_REWRITE_TAC[REAL_LT_POW_2] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    ONCE_REWRITE_TAC[GSYM REAL_POW2_ABS] THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM(SPEC `2` REAL_POW_ONE)] THEN
    MATCH_MP_TAC REAL_POW_LT2 THEN ASM_REWRITE_TAC[REAL_ABS_POS] THEN ARITH_TAC;
    ALL_TAC] THEN
  DISCH_TAC THEN
  ABBREV_TAC `P = product {i | i < n}
     (\i. (u pow 2 + (x:num->real) i pow 2) / (&1 + x i pow 2 * u pow 2))` THEN
  SUBGOAL_THEN `&0 < P` ASSUME_TAC THENL
   [ASM_MESON_TAC[REAL_POW_LT; REAL_LTE_TRANS]; ALL_TAC] THEN
  REWRITE_TAC[rp_hol_F; COMPLEX_NORM_MUL; COMPLEX_NORM_POW] THEN
  SIMP_TAC[NORM_CPRODUCT; FINITE_NUMSEG_LT; COMPLEX_NORM_DIV] THEN
  REWRITE_TAC[COMPLEX_NORM_MUL; COMPLEX_NORM_II; COMPLEX_NORM_CX; REAL_MUL_LID] THEN
  MATCH_MP_TAC RP_HOL_BL_SQ_LE1 THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN SIMP_TAC[REAL_POW_LE; REAL_ABS_POS] THEN
    MATCH_MP_TAC PRODUCT_POS_LE THEN
    SIMP_TAC[FINITE_NUMSEG_LT; REAL_LE_DIV; NORM_POS_LE];
    ALL_TAC] THEN
  SIMP_TAC[REAL_POW_MUL; RP_HOL_BL_PROD_POW2; FINITE_NUMSEG_LT;
           RP_HOL_BL_AXIS_FACTOR] THEN
  REWRITE_TAC[REAL_POW_POW] THEN ONCE_REWRITE_TAC[MULT_SYM] THEN
  REWRITE_TAC[GSYM REAL_POW_POW; REAL_POW2_ABS] THEN
  SUBGOAL_THEN
   `product {i | i < n}
      (\i. (&1 + (x:num->real) i pow 2 * u pow 2) / (u pow 2 + x i pow 2)) =
    inv P` SUBST1_TAC THENL
   [EXPAND_TAC "P" THEN
    SIMP_TAC[GSYM PRODUCT_INV; FINITE_NUMSEG_LT; REAL_INV_DIV]; ALL_TAC] THEN
  REWRITE_TAC[GSYM real_div] THEN ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_MUL_LID]);;
