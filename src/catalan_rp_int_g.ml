(* ========================================================================= *)
(* rp_int: the kernel h(t,s) = psi(s)/(1 - t s) and its moduli of           *)
(* continuity, uniformly for t in [-1,1].                                    *)
(* ========================================================================= *)

needs "src/catalan_rp_int_rs.ml";;

let rp_int_h = new_definition
 `rp_int_h m q t s = inv(&1 - t * s) * (s pow m * (&1 - s) pow q)`;;

let RP_INT_H_BASIC = prove
 (`forall t s. abs t <= &1 /\ &0 <= s /\ s <= &1
         ==> &0 <= &1 - s /\ &1 - s <= &1 - t * s /\
             &1 - t <= &2 * (&1 - t * s)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= s * (&1 - t)` ASSUME_TAC THENL
  [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `abs(t * (&2 * s - &1)) <= &1` ASSUME_TAC THENL
  [REWRITE_TAC[REAL_ABS_MUL] THEN
   MATCH_MP_TAC(REAL_ARITH `x <= &1 * &1 ==> x <= &1`) THEN
   MATCH_MP_TAC REAL_LE_MUL2 THEN REWRITE_TAC[REAL_ABS_POS] THEN
   ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

let RP_INT_H_AT1 = prove
 (`forall m q t. ~(q = 0) ==> rp_int_h m q t (&1) = &0`,
  SIMP_TAC[rp_int_h; REAL_SUB_REFL; REAL_POW_ZERO; REAL_MUL_RZERO]);;

let RP_INT_H_LIP_T = prove
 (`forall m q t t' s. 2 <= q /\ abs t <= &1 /\ abs t' <= &1 /\ &0 <= s /\ s <= &1
     ==> abs(rp_int_h m q t s - rp_int_h m q t' s) <= abs(t - t')`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `s = &1` THENL
  [ASM_SIMP_TAC[RP_INT_H_AT1; ARITH_RULE `2 <= q ==> ~(q = 0)`] THEN
   REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`t:real`; `s:real`] RP_INT_H_BASIC) THEN
  MP_TAC(SPECL [`t':real`; `s:real`] RP_INT_H_BASIC) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[rp_int_h] THEN
  ABBREV_TAC `P = s pow m * (&1 - s) pow q` THEN
  SUBGOAL_THEN `&0 <= P /\ P * s <= (&1 - s) pow 2` STRIP_ASSUME_TAC THENL
  [EXPAND_TAC "P" THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THEN MATCH_MP_TAC REAL_POW_LE THEN
    ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   REWRITE_TAC[REAL_ARITH `(a * b) * c = (a * c) * b:real`] THEN
   GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
   MATCH_MP_TAC REAL_LE_MUL2 THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_POW_LE];
    MATCH_MP_TAC(REAL_ARITH `x <= &1 * &1 ==> x <= &1`) THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_SIMP_TAC[REAL_POW_LE; REAL_POW_1_LE];
    MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_POW_MONO_INV THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
   ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &1 - t * s /\ &0 < &1 - t' * s` STRIP_ASSUME_TAC THENL
  [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `inv(&1 - t * s) * P - inv(&1 - t' * s) * P =
                (t - t') * ((P * s) / ((&1 - t * s) * (&1 - t' * s)))`
  SUBST1_TAC THENL
  [REPEAT(POP_ASSUM MP_TAC) THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  REWRITE_TAC[REAL_ABS_MUL] THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_ABS_POS] THEN
  SUBGOAL_THEN `&0 < (&1 - t * s) * (&1 - t' * s)` ASSUME_TAC THENL
  [ASM_SIMP_TAC[REAL_LT_MUL]; ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `&0 <= x /\ x <= &1 ==> abs x <= &1`) THEN
  ASM_SIMP_TAC[REAL_LE_DIV; REAL_LT_IMP_LE; REAL_LE_MUL; REAL_LE_LDIV_EQ] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(&1 - s) pow 2` THEN
  CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[REAL_MUL_LID; REAL_POW_2] THEN
  MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REAL_ARITH_TAC);;

let RP_INT_U_BOUND = prove
 (`forall t x. abs t <= &1 /\ &0 <= x /\ x <= &1
         ==> &0 <= (&1 - x) * inv(&1 - t * x) /\
             (&1 - x) * inv(&1 - t * x) <= &1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`t:real`; `x:real`] RP_INT_H_BASIC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_CASES_TAC `&1 - t * x = &0` THEN
  ASM_REWRITE_TAC[REAL_INV_0; REAL_MUL_RZERO; REAL_POS] THEN
  SUBGOAL_THEN `&0 < &1 - t * x` ASSUME_TAC THENL
  [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[GSYM real_div] THEN
  ASM_SIMP_TAC[REAL_LE_DIV; REAL_LT_IMP_LE; REAL_LE_LDIV_EQ] THEN
  ASM_REAL_ARITH_TAC);;

let RP_INT_U_LEMMA = prove
 (`forall t x x' c. abs t <= &1 /\ &0 <= x /\ x <= &1 /\ &0 <= x' /\ x' <= &1 /\
              &0 <= c /\ c <= &1 - x'
     ==> c * abs((&1 - x) * inv(&1 - t * x) - (&1 - x') * inv(&1 - t * x'))
         <= &2 * abs(x - x')`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`t:real`; `x:real`] RP_INT_H_BASIC) THEN
  MP_TAC(SPECL [`t:real`; `x':real`] RP_INT_H_BASIC) THEN
  MP_TAC(SPECL [`t:real`; `x:real`] RP_INT_U_BOUND) THEN
  MP_TAC(SPECL [`t:real`; `x':real`] RP_INT_U_BOUND) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `&1 - t * x' = &0` THENL
  [SUBGOAL_THEN `c = &0` SUBST1_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   REWRITE_TAC[REAL_MUL_LZERO] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `&1 - t * x = &0` THENL
  [SUBGOAL_THEN `x = &1` SUBST_ALL_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   REWRITE_TAC[REAL_SUB_REFL; REAL_MUL_LZERO; REAL_SUB_LZERO; REAL_ABS_NEG] THEN
   MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `c * &1` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
   ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &1 - t * x /\ &0 < &1 - t * x'` STRIP_ASSUME_TAC THENL
  [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(&1 - x) * inv(&1 - t * x) - (&1 - x') * inv(&1 - t * x') =
                (x' - x) * ((&1 - t) / ((&1 - t * x) * (&1 - t * x')))`
  SUBST1_TAC THENL
  [REPEAT(POP_ASSUM MP_TAC) THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < (&1 - t * x) * (&1 - t * x')` ASSUME_TAC THENL
  [ASM_SIMP_TAC[REAL_LT_MUL]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= &1 - t` ASSUME_TAC THENL
  [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[REAL_ABS_MUL] THEN
  SUBGOAL_THEN `abs((&1 - t) / ((&1 - t * x) * (&1 - t * x'))) =
                (&1 - t) / ((&1 - t * x) * (&1 - t * x'))` SUBST1_TAC THENL
  [REWRITE_TAC[REAL_ABS_REFL] THEN ASM_SIMP_TAC[REAL_LE_DIV; REAL_LT_IMP_LE];
   ALL_TAC] THEN
  SUBGOAL_THEN `c * abs(x' - x) * (&1 - t) / ((&1 - t * x) * (&1 - t * x')) =
                (c * (&1 - t) / ((&1 - t * x) * (&1 - t * x'))) * abs(x - x')`
  SUBST1_TAC THENL
  [REWRITE_TAC[REAL_ARITH `abs(x' - x) = abs(x - x')`] THEN REAL_ARITH_TAC;
   ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[REAL_ABS_POS] THEN
  REWRITE_TAC[real_div; REAL_MUL_ASSOC] THEN
  REWRITE_TAC[GSYM real_div] THEN ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
  ONCE_REWRITE_TAC[REAL_ARITH `&2 * a * b = b * (&2 * a)`] THEN
  MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REAL_ARITH_TAC);;

let RP_INT_CONT_TAC =
  REPEAT(FIRST
   [MATCH_ACCEPT_TAC REAL_CONTINUOUS_ON_CONST;
    MATCH_ACCEPT_TAC REAL_CONTINUOUS_ON_ID;
    MATCH_MP_TAC REAL_CONTINUOUS_ON_ADD THEN CONJ_TAC;
    MATCH_MP_TAC REAL_CONTINUOUS_ON_SUB THEN CONJ_TAC;
    MATCH_MP_TAC REAL_CONTINUOUS_ON_MUL THEN CONJ_TAC;
    MATCH_MP_TAC REAL_CONTINUOUS_ON_POW;
    MATCH_MP_TAC REAL_CONTINUOUS_ON_ABS]);;

let RP_INT_H_SPLIT = prove
 (`forall m q t x. 1 <= q
     ==> rp_int_h m q t x =
         (x pow m * (&1 - x) pow (q - 1)) * ((&1 - x) * inv(&1 - t * x))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[rp_int_h] THEN
  SUBGOAL_THEN `(&1 - x) pow q = (&1 - x) pow (q - 1) * (&1 - x)` SUBST1_TAC THENL
  [GEN_REWRITE_TAC (LAND_CONV o RAND_CONV)
     [MATCH_MP (ARITH_RULE `1 <= q ==> q = (q - 1) + 1`) (ASSUME `1 <= q`)] THEN
   REWRITE_TAC[REAL_POW_ADD; REAL_POW_1]; ALL_TAC] THEN
  REAL_ARITH_TAC);;

let RP_INT_H_MOD_S = prove
 (`forall m q t s s'. 2 <= q /\ abs t <= &1 /\ &0 <= s /\ s <= &1 /\
                &0 <= s' /\ s' <= &1
     ==> abs(rp_int_h m q t s - rp_int_h m q t s') <=
         abs(s pow m * (&1 - s) pow (q - 1) - s' pow m * (&1 - s') pow (q - 1)) +
         &2 * abs(s - s')`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[RP_INT_H_SPLIT; ARITH_RULE `2 <= q ==> 1 <= q`] THEN
  MP_TAC(SPECL [`t:real`; `s:real`] RP_INT_U_BOUND) THEN
  MP_TAC(SPECL [`t:real`; `s:real`; `s':real`;
                `s' pow m * (&1 - s') pow (q - 1)`] RP_INT_U_LEMMA) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&0 <= s' pow m * (&1 - s') pow (q - 1) /\
                s' pow m * (&1 - s') pow (q - 1) <= &1 - s'`
  (fun th -> REWRITE_TAC[th] THEN STRIP_ASSUME_TAC th) THENL
  [CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THEN MATCH_MP_TAC REAL_POW_LE THEN
    ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
   MATCH_MP_TAC REAL_LE_MUL2 THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_POW_1_LE THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC;
    GEN_REWRITE_TAC RAND_CONV [GSYM REAL_POW_1] THEN
    MATCH_MP_TAC REAL_POW_MONO_INV THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN ASM_ARITH_TAC];
   ALL_TAC] THEN
  ABBREV_TAC `p = s pow m * (&1 - s) pow (q - 1)` THEN
  ABBREV_TAC `p' = s' pow m * (&1 - s') pow (q - 1)` THEN
  ABBREV_TAC `u = (&1 - s) * inv(&1 - t * s)` THEN
  ABBREV_TAC `u' = (&1 - s') * inv(&1 - t * s')` THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(p:real) * u - p' * u' = (p - p') * u + p' * (u - u')` SUBST1_TAC THENL
  [REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH
   `abs a <= x /\ abs b <= y ==> abs(a + b) <= x + y`) THEN
  REWRITE_TAC[REAL_ABS_MUL] THEN CONJ_TAC THENL
  [GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
   MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_ABS_POS] THEN
   ASM_REAL_ARITH_TAC;
   ASM_SIMP_TAC[REAL_ARITH `&0 <= x ==> abs x = x`]]);;

let RP_INT_H_UNIF = prove
 (`forall m q e. 2 <= q /\ &0 < e
     ==> exists d. &0 < d /\
             forall t s s'. abs t <= &1 /\ s IN real_interval[&0,&1] /\
                      s' IN real_interval[&0,&1] /\ abs(s - s') <= d
                      ==> abs(rp_int_h m q t s - rp_int_h m q t s') <= e`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\s. s pow m * (&1 - s) pow (q - 1)`; `real_interval[&0,&1]`]
    REAL_COMPACT_UNIFORMLY_CONTINUOUS) THEN
  REWRITE_TAC[REAL_COMPACT_INTERVAL] THEN ANTS_TAC THENL
  [RP_INT_CONT_TAC; ALL_TAC] THEN
  REWRITE_TAC[real_uniformly_continuous_on] THEN
  DISCH_THEN(MP_TAC o SPEC `e / &2`) THEN ASM_REWRITE_TAC[REAL_HALF] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `min (d / &2) (e / &4)` THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[IN_REAL_INTERVAL] THEN REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`m:num`; `q:num`; `t:real`; `s:real`; `s':real`]
    RP_INT_H_MOD_S) THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`s':real`; `s:real`]) THEN
  ASM_REWRITE_TAC[IN_REAL_INTERVAL] THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

let rp_int_G = new_definition
 `rp_int_G m q t = real_integral (real_interval[&0,&1]) (rp_int_h m q t)`;;

let RP_INT_H_CONT_S = prove
 (`forall m q t. 2 <= q /\ abs t <= &1
           ==> rp_int_h m q t real_continuous_on real_interval[&0,&1]`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC REAL_UNIFORMLY_CONTINUOUS_IMP_REAL_CONTINUOUS THEN
  REWRITE_TAC[real_uniformly_continuous_on] THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  MP_TAC(SPECL [`m:num`; `q:num`; `e / &2`] RP_INT_H_UNIF) THEN
  ASM_REWRITE_TAC[REAL_HALF] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(REAL_ARITH `x <= e / &2 /\ &0 < e ==> x < e`) THEN
  ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

let RP_INT_G_LIP = prove
 (`forall m q t t'. 2 <= q /\ abs t <= &1 /\ abs t' <= &1
              ==> abs(rp_int_G m q t - rp_int_G m q t') <= abs(t - t')`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[rp_int_G] THEN
  ASM_SIMP_TAC[GSYM REAL_INTEGRAL_SUB; REAL_INTEGRABLE_CONTINUOUS;
               RP_INT_H_CONT_S] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `real_integral (real_interval[&0,&1]) (\s. abs(t - t'))` THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC REAL_INTEGRAL_ABS_BOUND_INTEGRAL THEN
   REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC REAL_INTEGRABLE_SUB THEN
    ASM_SIMP_TAC[REAL_INTEGRABLE_CONTINUOUS; RP_INT_H_CONT_S; ETA_AX];
    REWRITE_TAC[REAL_INTEGRABLE_CONST]; ALL_TAC] THEN
   REWRITE_TAC[IN_REAL_INTERVAL] THEN REPEAT STRIP_TAC THEN
   MATCH_MP_TAC RP_INT_H_LIP_T THEN ASM_REWRITE_TAC[];
   SIMP_TAC[REAL_INTEGRAL_CONST; REAL_POS] THEN REAL_ARITH_TAC]);;

let RP_INT_G_CONT = prove
 (`forall m q. 2 <= q ==> rp_int_G m q real_continuous_on real_interval[--(&1),&1]`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[real_continuous_on; IN_REAL_INTERVAL] THEN
  REPEAT STRIP_TAC THEN EXISTS_TAC `e:real` THEN ASM_REWRITE_TAC[] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LET_TRANS THEN
  EXISTS_TAC `abs(x' - x)` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC RP_INT_G_LIP THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

let RP_INT_G_RS = prove
 (`forall m q e. 2 <= q /\ &0 < e
     ==> exists M0. forall M t. M0 <= M /\ abs t <= &1
                    ==> abs(rp_int_G m q t - rp_int_rsum (rp_int_h m q t) (&0) (&1) M)
                        <= e`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`m:num`; `q:num`; `e:real`] RP_INT_H_UNIF) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(SPEC `inv(d:real)` REAL_ARCH_SIMPLE) THEN
  DISCH_THEN(X_CHOOSE_TAC `N0:num`) THEN EXISTS_TAC `N0 + 1` THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < &M /\ &1 / &M <= d` STRIP_ASSUME_TAC THENL
  [SUBGOAL_THEN `inv d < &M` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `&N0` THEN
    ASM_REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC; ALL_TAC] THEN
   SUBGOAL_THEN `&0 < &M` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC; ALL_TAC] THEN
   ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
   SUBGOAL_THEN `&1 / d < &M` MP_TAC THENL
   [ASM_REWRITE_TAC[real_div; REAL_MUL_LID]; ASM_SIMP_TAC[REAL_LT_LDIV_EQ]] THEN
   REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`rp_int_h m q t`; `&0`; `&1`; `M:num`; `e:real`]
    RP_INT_RS_ERR) THEN
  ASM_SIMP_TAC[RP_INT_H_CONT_S; REAL_LT_01; rp_int_G] THEN
  REWRITE_TAC[REAL_SUB_RZERO; REAL_MUL_LID] THEN DISCH_THEN MATCH_MP_TAC THEN
  CONJ_TAC THENL [REWRITE_TAC[GSYM REAL_OF_NUM_EQ] THEN ASM_REAL_ARITH_TAC;
                  ALL_TAC] THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;
