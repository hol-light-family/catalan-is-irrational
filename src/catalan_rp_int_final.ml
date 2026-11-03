(* ========================================================================= *)
(* rp_int: RP_INT_THM : |- RP_INT_STMT.                                      *)
(* ========================================================================= *)

needs "src/catalan_rp_int_sum.ml";;
needs "src/catalan_rp_int_cb.ml";;

let RP_INT_CONFIG_EXISTS = prove
 (`forall N. exists x s. rp_config N x s`,
  GEN_TAC THEN
  EXISTS_TAC `\i. &(i + 1) / &(48 * N + 2)` THEN
  EXISTS_TAC `\i. &(i + 1) / &(48 * N + 2)` THEN
  SUBGOAL_THEN `&0 < &(48 * N + 2)` ASSUME_TAC THENL
  [REWRITE_TAC[REAL_OF_NUM_LT] THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `forall i. i < 48 * N ==> &0 < &(i + 1) / &(48 * N + 2) /\
                                   &(i + 1) / &(48 * N + 2) < &1`
  ASSUME_TAC THENL
  [REPEAT STRIP_TAC THENL
   [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[REAL_OF_NUM_LT] THEN ARITH_TAC;
    ASM_SIMP_TAC[REAL_LT_LDIV_EQ; REAL_MUL_LID; REAL_OF_NUM_LT] THEN
    ASM_ARITH_TAC]; ALL_TAC] THEN
  SUBGOAL_THEN `forall i j. &(i + 1) / &(48 * N + 2) = &(j + 1) / &(48 * N + 2)
                      ==> i = j`
  ASSUME_TAC THENL
  [ASM_SIMP_TAC[REAL_LT_IMP_NZ;
     REAL_FIELD `&0 < d ==> (x / d = y / d <=> x = y)`; REAL_OF_NUM_EQ] THEN
   ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[rp_config; rp_nodes] THEN ASM_MESON_TAC[REAL_LT_IMP_NZ;
    REAL_ARITH `&0 < x ==> --(&1) < x`]);;

let RP_INT_DISCRETE_BOUND = prove
 (`forall N M Mc. 1 <= N /\ (forall x s. rp_config N x s ==> abs(rp_integrand N x s) <= M) /\
            &0 <= M /\ ~(Mc = 0)
   ==> abs(ndet {i | i < 48 * N} (\r k. rp_int_E N Mc r k)) <=
       &2 pow (48 * N) * M`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`48 * N`; `2 * Mc`; `Mc:num`;
                 `\r a. rp_row N r (rp_int_xn Mc a)`;
                 `\a:num. (&1 - --(&1)) / &(2 * Mc)`;
                 `\a b. inv(&1 - rp_t (rp_int_xn Mc a) * rp_int_sn Mc b)`;
                 `\b:num. (&1 - &0) / &Mc`;
                 `\b k. cat_psi N k (rp_int_sn Mc b)`; `M:real`]
    RP_INT_CB_BOUND) THEN
  BETA_TAC THEN REWRITE_TAC[rp_int_E] THEN ANTS_TAC THENL
  [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC REAL_LE_DIV THEN
    REWRITE_TAC[REAL_POS] THEN REAL_ARITH_TAC;
    GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC REAL_LE_DIV THEN
    REWRITE_TAC[REAL_POS] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
   MAP_EVERY X_GEN_TAC [`f:num->num`; `g:num->num`] THEN STRIP_TAC THEN
   FIRST_X_ASSUM(MP_TAC o SPECL [`\i:num. rp_int_xn Mc (f i)`;
                                 `\j:num. rp_int_sn Mc (g j)`]) THEN
   REWRITE_TAC[rp_integrand] THEN DISCH_THEN MATCH_MP_TAC THEN
   REWRITE_TAC[rp_config; rp_nodes] THEN
   REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THENL
   [MATCH_MP_TAC RP_INT_XN_PROPS THEN ASM_SIMP_TAC[];
    ASM_MESON_TAC[RP_INT_XN_INJ];
    MATCH_MP_TAC RP_INT_SN_PROPS THEN ASM_SIMP_TAC[];
    ASM_MESON_TAC[RP_INT_XN_INJ]];
   ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `x = y ==> a <= x ==> a <= y`) THEN
  SIMP_TAC[SUM_CONST; FINITE_NUMSEG_LT; CARD_NUMSEG_LT] THEN
  SUBGOAL_THEN `&(2 * Mc) * (&1 - -- &1) / &(2 * Mc) = &2 /\
                &Mc * (&1 - &0) / &Mc = &1`
  (fun th -> REWRITE_TAC[th; REAL_POW_ONE; REAL_MUL_LID]) THEN
  SUBGOAL_THEN `~(&Mc = &0)` MP_TAC THENL
  [ASM_REWRITE_TAC[REAL_OF_NUM_EQ]; ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_MUL] THEN CONV_TAC REAL_FIELD);;

let RP_INT_THM = prove
 (`RP_INT_STMT`,
  REWRITE_TAC[RP_INT_STMT] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= M` ASSUME_TAC THENL
  [MP_TAC(SPEC `N:num` RP_INT_CONFIG_EXISTS) THEN STRIP_TAC THEN
   FIRST_X_ASSUM(MP_TAC o SPECL [`x:num->real`; `s:num->real`]) THEN
   ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`48 * N`; `\Mc r k. rp_int_E N Mc r k`; `cat_entry N`]
    RP_INT_CB_NDET_LIM) THEN
  BETA_TAC THEN ANTS_TAC THENL
  [REPEAT STRIP_TAC THEN MATCH_MP_TAC RP_INT_E_CONV THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  SUBGOAL_THEN `cat_det N = ndet {i | i < 48 * N} (cat_entry N)`
  SUBST1_TAC THENL
  [REWRITE_TAC[cat_det] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
   MATCH_MP_TAC RP_NUMSEG_LT THEN ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP REALLIM_ABS) THEN BETA_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC(ISPEC `sequentially` REALLIM_UBOUND) THEN
  EXISTS_TAC `\m. abs(ndet {i | i < 48 * N} (\r k. rp_int_E N m r k))` THEN
  ASM_REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY] THEN
  REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN EXISTS_TAC `1` THEN X_GEN_TAC `Mc:num` THEN DISCH_TAC THEN BETA_TAC THEN
  MATCH_MP_TAC RP_INT_DISCRETE_BOUND THEN ASM_REWRITE_TAC[] THEN
  ASM_ARITH_TAC);;
