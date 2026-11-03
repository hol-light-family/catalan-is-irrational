(* ========================================================================= *)
(* rp_hol_bl_: conjuncts 1-6 of RP_HOL_BL_STMT                              *)
(* ========================================================================= *)

needs "src/catalan_rp_hol_base.ml";;

let RP_HOL_BL_FDIFF = prove
 (`forall n D (x:num->real) w. (forall i. i < n ==> ~(w = Cx(x i)))
             ==> rp_hol_F n D x complex_differentiable at w`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `rp_hol_F n D x =
     (\z. z pow D * cproduct {i | i < n}
            (\i. (Cx(&1) - Cx(x i) * z) / (z - Cx(x i))))` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; rp_hol_F]; ALL_TAC] THEN
  MATCH_MP_TAC COMPLEX_DIFFERENTIABLE_MUL_AT THEN CONJ_TAC THENL
   [MATCH_MP_TAC COMPLEX_DIFFERENTIABLE_POW_AT THEN
    REWRITE_TAC[COMPLEX_DIFFERENTIABLE_ID]; ALL_TAC] THEN
  MP_TAC(ISPECL [`\i z. (Cx(&1) - Cx(x i) * z) / (z - Cx(x (i:num)))`;
                 `{i:num | i < n}`; `w:complex`]
         COMPLEX_DIFFERENTIABLE_CPRODUCT_AT) THEN
  REWRITE_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM] THEN DISCH_THEN MATCH_MP_TAC THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC COMPLEX_DIFFERENTIABLE_DIV_AT THEN
  ASM_SIMP_TAC[COMPLEX_DIFFERENTIABLE_SUB; COMPLEX_DIFFERENTIABLE_CONST;
               COMPLEX_DIFFERENTIABLE_ID; COMPLEX_DIFFERENTIABLE_MUL_AT;
               COMPLEX_SUB_0]);;

let RP_HOL_BL_BDIFF = prove
 (`forall n (x:num->real) w. (forall i. i < n ==> ~(Cx(x i) * w = Cx(&1)))
           ==> rp_hol_B n x complex_differentiable at w`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `rp_hol_B n x =
     (\z. cproduct {i | i < n}
            (\i. (z - Cx(x i)) / (Cx(&1) - Cx(x i) * z)))` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; rp_hol_B]; ALL_TAC] THEN
  MP_TAC(ISPECL [`\i z. (z - Cx(x (i:num))) / (Cx(&1) - Cx(x i) * z)`;
                 `{i:num | i < n}`; `w:complex`]
         COMPLEX_DIFFERENTIABLE_CPRODUCT_AT) THEN
  REWRITE_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM] THEN DISCH_THEN MATCH_MP_TAC THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC COMPLEX_DIFFERENTIABLE_DIV_AT THEN
  ASM_SIMP_TAC[COMPLEX_DIFFERENTIABLE_SUB; COMPLEX_DIFFERENTIABLE_CONST;
               COMPLEX_DIFFERENTIABLE_ID; COMPLEX_DIFFERENTIABLE_MUL_AT;
               COMPLEX_SUB_0] THEN
  ASM_MESON_TAC[]);;

let RP_HOL_BL_BF = prove
 (`forall n D (x:num->real) w. (forall i. i < n ==> ~(w = Cx(x i)) /\ ~(Cx(x i) * w = Cx(&1)))
             ==> rp_hol_B n x w * rp_hol_F n D x w = w pow D`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[rp_hol_B; rp_hol_F] THEN
  ONCE_REWRITE_TAC[COMPLEX_RING `a * (b * c) = b * (a * c):complex`] THEN
  SIMP_TAC[GSYM CPRODUCT_MUL; FINITE_NUMSEG_LT] THEN
  MATCH_MP_TAC(COMPLEX_RING `c = Cx(&1) ==> b * c = b`) THEN
  MATCH_MP_TAC CPRODUCT_EQ_1 THEN REWRITE_TAC[IN_ELIM_THM] THEN
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(COMPLEX_FIELD
   `~(a = Cx(&0)) /\ ~(b = Cx(&0)) ==> a / b * (b / a) = Cx(&1)`) THEN
  ASM_SIMP_TAC[COMPLEX_SUB_0] THEN ASM_MESON_TAC[]);;

let RP_HOL_BL_BZERO = prove
 (`forall n (x:num->real) j. j < n ==> rp_hol_B n x (Cx(x j)) = Cx(&0)`,
  REPEAT STRIP_TAC THEN
  SIMP_TAC[rp_hol_B; CPRODUCT_EQ_0; FINITE_NUMSEG_LT; IN_ELIM_THM] THEN
  EXISTS_TAC `j:num` THEN
  ASM_REWRITE_TAC[COMPLEX_SUB_REFL; complex_div; COMPLEX_MUL_LZERO]);;

let RP_HOL_BL_NORM_EQ = prove
 (`forall x z. norm z = &1 ==> norm(Cx(&1) - Cx x * z) = norm(z - Cx x)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[complex_norm] THEN AP_TERM_TAC THEN
  SUBGOAL_THEN `Re z pow 2 + Im z pow 2 = &1` MP_TAC THENL
   [ASM_REWRITE_TAC[GSYM COMPLEX_SQNORM] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[RE_SUB; IM_SUB; RE_CX; IM_CX; RE_MUL_CX; IM_MUL_CX] THEN
  CONV_TAC REAL_RING);;

let RP_HOL_BL_BNORM = prove
 (`forall n (x:num->real) z. (forall i. i < n ==> abs(x i) < &1) /\ norm z = &1
           ==> norm(rp_hol_B n x z) = &1`,
  REPEAT STRIP_TAC THEN
  SIMP_TAC[rp_hol_B; NORM_CPRODUCT; FINITE_NUMSEG_LT] THEN
  MATCH_MP_TAC PRODUCT_EQ_1 THEN REWRITE_TAC[IN_ELIM_THM] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  ASM_SIMP_TAC[COMPLEX_NORM_DIV; RP_HOL_BL_NORM_EQ] THEN
  MATCH_MP_TAC REAL_DIV_REFL THEN REWRITE_TAC[COMPLEX_NORM_ZERO; COMPLEX_SUB_0] THEN
  DISCH_THEN(MP_TAC o AP_TERM `norm:complex->real`) THEN
  ASM_REWRITE_TAC[COMPLEX_NORM_CX] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN ASM_REWRITE_TAC[] THEN
  REAL_ARITH_TAC);;

let RP_HOL_BL_RADIUS_LEMMA = prove
 (`forall n (x:num->real). (forall i. i < n ==> abs(x i) < &1)
         ==> exists r. &1 < r /\ forall i. i < n ==> r * abs(x i) < &1`,
  GEN_TAC THEN GEN_TAC THEN SPEC_TAC(`n:num`,`n:num`) THEN INDUCT_TAC THENL
   [DISCH_TAC THEN EXISTS_TAC `&2` THEN REWRITE_TAC[LT] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[ARITH_RULE `i < n ==> i < SUC n`]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `abs(x(n:num)) < &1` ASSUME_TAC THENL
   [ASM_MESON_TAC[ARITH_RULE `n < SUC n`]; ALL_TAC] THEN
  ABBREV_TAC `a = abs(x(n:num))` THEN
  SUBGOAL_THEN `&0 <= a` ASSUME_TAC THENL
   [EXPAND_TAC "a" THEN REAL_ARITH_TAC; ALL_TAC] THEN
  EXISTS_TAC `min r (&2 / (&1 + a))` THEN CONJ_TAC THENL
   [REWRITE_TAC[REAL_LT_MIN] THEN ASM_SIMP_TAC[REAL_LT_RDIV_EQ;
      REAL_ARITH `&0 <= a ==> &0 < &1 + a`] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  X_GEN_TAC `i:num` THEN REWRITE_TAC[LT] THEN STRIP_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC `&2 / (&1 + a) * a` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_ARITH `&2 / b * a = (&2 * a) / b`; REAL_LT_LDIV_EQ;
      REAL_ARITH `&0 <= a ==> &0 < &1 + a`] THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `r * abs(x(i:num))` THEN
    ASM_SIMP_TAC[] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
    REWRITE_TAC[REAL_ABS_POS] THEN REAL_ARITH_TAC]);;

let RP_HOL_BL_RADIUS = prove
 (`forall n (x:num->real). (forall i. i < n ==> abs(x i) < &1)
         ==> exists r. &1 < r /\
                 forall w i. norm w < r /\ i < n ==> ~(Cx(x i) * w = Cx(&1))`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP RP_HOL_BL_RADIUS_LEMMA) THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `r:real` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o AP_TERM `norm:complex->real`) THEN
  REWRITE_TAC[COMPLEX_NORM_MUL; COMPLEX_NORM_CX; REAL_ABS_NUM] THEN
  MATCH_MP_TAC(REAL_ARITH `x < &1 ==> ~(x = &1)`) THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `abs(x(i:num)) * r` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_ABS_POS; REAL_LT_IMP_LE];
    ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN ASM_SIMP_TAC[]]);;
