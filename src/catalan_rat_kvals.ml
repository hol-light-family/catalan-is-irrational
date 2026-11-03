needs "src/catalan_rat_base.ml";;
let RAT_C_POS = prove
 (`forall t s. abs t < &1 /\ &0 <= s /\ s <= &1 ==> &0 < &1 - t * s`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `abs t * abs s <= abs t * &1` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_ABS_MUL] THEN ASM_REAL_ARITH_TAC);;

let RAT_C_FTC01 = prove
 (`forall f f' i. (forall x. &0 <= x /\ x <= &1 ==> (f has_real_derivative f' x) (atreal x)) /\
            f(&1) - f(&0) = i
            ==> (f' has_real_integral i) (real_interval[&0,&1])`,
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC REAL_FUNDAMENTAL_THEOREM_OF_CALCULUS THEN
  REWRITE_TAC[REAL_POS; IN_REAL_INTERVAL] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC HAS_REAL_DERIVATIVE_ATREAL_WITHIN THEN ASM_SIMP_TAC[]);;

let RAT_C_G0 = prove
 (`forall t. abs t < &1 /\ ~(t = &0) ==> rat_g 0 t = --log(&1 - t) / t`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[rat_g] THEN MATCH_MP_TAC REAL_INTEGRAL_UNIQUE THEN
  MATCH_MP_TAC RAT_C_FTC01 THEN EXISTS_TAC `\s. --log(&1 - t * s) / t` THEN
  REWRITE_TAC[REAL_MUL_RZERO; REAL_SUB_RZERO; LOG_1; REAL_MUL_RID] THEN
  CONJ_TAC THENL [ALL_TAC; REAL_ARITH_TAC] THEN
  REPEAT STRIP_TAC THEN REAL_DIFF_TAC THEN
  SUBGOAL_THEN `&0 < &1 - t * x` MP_TAC THENL
   [MATCH_MP_TAC RAT_C_POS THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN CONV_TAC REAL_FIELD);;

let RAT_C_G1 = prove
 (`forall t. abs t < &1 /\ ~(t = &0) ==> rat_g 1 t = --log(&1 - t) / t pow 2 - &1 / t`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[rat_g] THEN MATCH_MP_TAC REAL_INTEGRAL_UNIQUE THEN
  MATCH_MP_TAC RAT_C_FTC01 THEN EXISTS_TAC `\s. --log(&1 - t * s) / t pow 2 - s / t` THEN
  REWRITE_TAC[REAL_MUL_RZERO; REAL_SUB_RZERO; LOG_1; REAL_MUL_RID] THEN
  CONJ_TAC THENL [ALL_TAC; REAL_ARITH_TAC] THEN
  REPEAT STRIP_TAC THEN REAL_DIFF_TAC THEN
  SUBGOAL_THEN `&0 < &1 - t * x` MP_TAC THENL
   [MATCH_MP_TAC RAT_C_POS THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN CONV_TAC REAL_FIELD);;

let RAT_C_SPIKE = prove
 (`forall f g a b K. (f has_real_integral K) (real_interval[a,b]) /\
               (forall x. a < x /\ x < b ==> g x = f x)
               ==> (g has_real_integral K) (real_interval[a,b])`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HAS_REAL_INTEGRAL_SPIKE_FINITE THEN
  MAP_EVERY EXISTS_TAC [`f:real->real`; `{a:real,b}`] THEN
  ASM_REWRITE_TAC[FINITE_INSERT; FINITE_EMPTY; IN_DIFF; IN_REAL_INTERVAL;
                  IN_INSERT; NOT_IN_EMPTY] THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC);;

let RAT_C_SUBST = prove
 (`forall f g g' c d K.
     (f has_real_integral K) (real_interval[c,d]) /\ c <= d /\
     g(&0) = c /\ g(&1) = d /\
     (forall x. &0 <= x /\ x <= &1
          ==> (g has_real_derivative g' x) (atreal x) /\ c <= g x /\ g x <= d) /\
     (forall x. &0 < x /\ x < &1 ==> f real_continuous atreal (g x))
     ==> ((\x. f(g x) * g' x) has_real_integral K) (real_interval[&0,&1])`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `K = real_integral (real_interval[g(&0),g(&1)]) f` SUBST1_TAC THENL
   [ASM_MESON_TAC[REAL_INTEGRAL_UNIQUE]; ALL_TAC] THEN
  MATCH_MP_TAC HAS_REAL_INTEGRAL_SUBSTITUTION_STRONG THEN
  MAP_EVERY EXISTS_TAC [`c:real`; `d:real`; `{&0,&1}`] THEN
  ASM_REWRITE_TAC[REAL_POS] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC FINITE_IMP_COUNTABLE THEN REWRITE_TAC[FINITE_INSERT; FINITE_EMPTY];
    ASM_MESON_TAC[real_integrable_on];
    REWRITE_TAC[REAL_CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN; IN_REAL_INTERVAL] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_CONTINUOUS_ATREAL_WITHINREAL THEN
    ASM_MESON_TAC[HAS_REAL_DERIVATIVE_IMP_CONTINUOUS_ATREAL];
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_REAL_INTERVAL] THEN ASM_MESON_TAC[];
    REWRITE_TAC[IN_DIFF; IN_REAL_INTERVAL; IN_INSERT; NOT_IN_EMPTY] THEN
    REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC HAS_REAL_DERIVATIVE_ATREAL_WITHIN THEN ASM_MESON_TAC[];
      MATCH_MP_TAC REAL_CONTINUOUS_ATREAL_WITHINREAL THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC]]);;

let RAT_C_LOGMOM = prove
 (`forall m. ((\y. y pow m * --log y) has_real_integral &1 / (&m + &1) pow 2)
       (real_interval[&0,&1])`,
  GEN_TAC THEN
  ABBREV_TAC `ff = \y. y pow (m + 1) / (&m + &1) pow 2 - y pow m * (y * log y) / (&m + &1)` THEN
  SUBGOAL_THEN `&1 / (&m + &1) pow 2 = ff(&1) - ff(&0)` SUBST1_TAC THENL
   [EXPAND_TAC "ff" THEN
    REWRITE_TAC[REAL_POW_ONE; LOG_1; REAL_MUL_LZERO; REAL_MUL_RZERO; REAL_POW_ZERO;
     ADD_EQ_0; ARITH_EQ] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_FUNDAMENTAL_THEOREM_OF_CALCULUS_INTERIOR THEN
  EXPAND_TAC "ff" THEN REWRITE_TAC[REAL_POS; real_div] THEN CONJ_TAC THENL
   [REWRITE_TAC[REAL_CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN; IN_REAL_INTERVAL] THEN
    X_GEN_TAC `x:real` THEN STRIP_TAC THEN ASM_CASES_TAC `x = &0` THENL
     [ALL_TAC;
      MATCH_MP_TAC REAL_CONTINUOUS_ATREAL_WITHINREAL THEN
      MATCH_MP_TAC REAL_DIFFERENTIABLE_IMP_CONTINUOUS_ATREAL THEN
      REAL_DIFFERENTIABLE_TAC THEN ASM_REAL_ARITH_TAC] THEN
    FIRST_X_ASSUM SUBST1_TAC THEN
    MATCH_MP_TAC REAL_CONTINUOUS_SUB THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_CONTINUOUS_MUL THEN REWRITE_TAC[REAL_CONTINUOUS_CONST] THEN
      MATCH_MP_TAC REAL_CONTINUOUS_POW THEN REWRITE_TAC[REAL_CONTINUOUS_WITHIN_ID];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_CONTINUOUS_MUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_CONTINUOUS_POW THEN REWRITE_TAC[REAL_CONTINUOUS_WITHIN_ID];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_CONTINUOUS_MUL THEN REWRITE_TAC[REAL_CONTINUOUS_CONST] THEN
    REWRITE_TAC[REAL_CONTINUOUS_WITHINREAL; REAL_MUL_LZERO] THEN
    MATCH_MP_TAC REALLIM_WITHINREAL_SUBSET THEN
    EXISTS_TAC `{x | &0 <= x}` THEN REWRITE_TAC[REALLIM_X_TIMES_LOG] THEN
    REWRITE_TAC[SUBSET; IN_REAL_INTERVAL; IN_ELIM_THM] THEN REAL_ARITH_TAC;
    REWRITE_TAC[IN_REAL_INTERVAL] THEN REPEAT STRIP_TAC THEN REAL_DIFF_TAC THEN
    ASM_REWRITE_TAC[ADD_SUB; GSYM REAL_OF_NUM_ADD] THEN
    SUBGOAL_THEN `&m * x pow (m - 1) * x = &m * x pow m` MP_TAC THENL
     [ASM_CASES_TAC `m = 0` THEN ASM_REWRITE_TAC[REAL_MUL_LZERO] THEN
      REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN AP_TERM_TAC THEN
      ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN REWRITE_TAC[GSYM(CONJUNCT2 real_pow)] THEN
      AP_TERM_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= &m` MP_TAC THENL [REWRITE_TAC[REAL_POS]; ALL_TAC] THEN
    UNDISCH_TAC `&0 < x` THEN CONV_TAC REAL_FIELD]);;
let RAT_C_PSUM_INT = prove
 (`forall n. ((\y. sum(0..n) (\k. --(&1) pow k * (y pow (2 * k) * --log y)))
        has_real_integral sum(0..n) (\j. --(&1) pow j / &(2 * j + 1) pow 2))
       (real_interval[&0,&1])`,
  GEN_TAC THEN MATCH_MP_TAC HAS_REAL_INTEGRAL_SUM THEN
  REWRITE_TAC[FINITE_NUMSEG] THEN X_GEN_TAC `k:num` THEN DISCH_TAC THEN
  REWRITE_TAC[real_div] THEN MATCH_MP_TAC HAS_REAL_INTEGRAL_LMUL THEN
  MP_TAC(SPEC `2 * k` RAT_C_LOGMOM) THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_ADD; GSYM REAL_OF_NUM_MUL; real_div; REAL_MUL_LID]);;

let RAT_C_PSUM_EQ = prove
 (`forall n y. sum(0..n) (\k. --(&1) pow k * (y pow (2 * k) * --log y)) =
         (&1 - (--(y pow 2)) pow (SUC n)) / (&1 + y pow 2) * --log y`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `forall k. --(&1) pow k * (y pow (2 * k) * --log y) = (--(y pow 2)) pow k * --log y`
   (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN REWRITE_TAC[REAL_POW_NEG; GSYM REAL_POW_POW; REAL_POW_ONE] THEN
    COND_CASES_TAC THEN REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[SUM_RMUL] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  SUBGOAL_THEN `(&1 + y pow 2) * sum(0..n) (\k. --(y pow 2) pow k) = &1 - --(y pow 2) pow SUC n`
  MP_TAC THENL
   [MP_TAC(ISPECL [`--((y:real) pow 2)`; `n:num`] SUM_GP_BASIC) THEN
    DISCH_THEN(ACCEPT_TAC o REWRITE_RULE[REAL_ARITH `&1 - --x = &1 + x`]); ALL_TAC] THEN
  MP_TAC(SPEC `y:real` REAL_LE_POW_2) THEN CONV_TAC REAL_FIELD);;

let RAT_C_CATSERIES = prove
 (`(\y. --log y / (&1 + y pow 2)) real_integrable_on real_interval[&0,&1] /\
   ((\j. --(&1) pow j / &(2 * j + 1) pow 2) real_sums
     real_integral (real_interval[&0,&1]) (\y. --log y / (&1 + y pow 2))) (from 0)`,
  MP_TAC(ISPECL [`\n y. sum(0..n) (\k. --(&1) pow k * (y pow (2 * k) * --log y))`;
                 `\y. --log y / (&1 + y pow 2)`; `\y. &2 * abs(log y)`;
                 `real_interval[&0,&1]`] REAL_DOMINATED_CONVERGENCE) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MESON_TAC[RAT_C_PSUM_INT; real_integrable_on];
      MATCH_MP_TAC REAL_INTEGRABLE_LMUL THEN
      REWRITE_TAC[real_integrable_on] THEN EXISTS_TAC `&1 / (&0 + &1) pow 2` THEN
      MATCH_MP_TAC RAT_C_SPIKE THEN EXISTS_TAC `\y:real. y pow 0 * --log y` THEN
      REWRITE_TAC[RAT_C_LOGMOM] THEN
      REPEAT STRIP_TAC THEN REWRITE_TAC[real_pow; REAL_MUL_LID] THEN
      MATCH_MP_TAC(REAL_ARITH `x <= &0 ==> abs x = --x`) THEN
      ONCE_REWRITE_TAC[GSYM LOG_1] THEN MATCH_MP_TAC LOG_MONO_LE_IMP THEN
      ASM_REAL_ARITH_TAC;
      REWRITE_TAC[RAT_C_PSUM_EQ; IN_REAL_INTERVAL] THEN REPEAT STRIP_TAC THEN
      REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_NEG] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[REAL_ABS_POS] THEN
      REWRITE_TAC[REAL_ABS_DIV] THEN
      SUBGOAL_THEN `&0 < abs(&1 + x pow 2)` ASSUME_TAC THENL
       [MP_TAC(SPEC `x:real` REAL_LE_POW_2) THEN REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
      SUBGOAL_THEN `abs((--(x pow 2)) pow SUC k) <= &1` MP_TAC THENL
       [REWRITE_TAC[REAL_ABS_POW; REAL_ABS_NEG] THEN MATCH_MP_TAC REAL_POW_1_LE THEN
        CONJ_TAC THENL [MATCH_MP_TAC REAL_POW_LE THEN REWRITE_TAC[REAL_ABS_POS];
          MATCH_MP_TAC REAL_POW_1_LE THEN ASM_REAL_ARITH_TAC]; ALL_TAC] THEN
      MP_TAC(SPEC `x:real` REAL_LE_POW_2) THEN REAL_ARITH_TAC;
      REWRITE_TAC[RAT_C_PSUM_EQ; IN_REAL_INTERVAL] THEN REPEAT STRIP_TAC THEN
      ASM_CASES_TAC `x = &1` THENL
       [ASM_REWRITE_TAC[LOG_1; REAL_NEG_0; REAL_MUL_RZERO; real_div; REAL_MUL_LZERO;
                        REALLIM_CONST]; ALL_TAC] THEN
      SUBGOAL_THEN `--log x / (&1 + x pow 2) = (&1 - --(x pow 2) * &0) / (&1 + x pow 2) * --log x`
       SUBST1_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REALLIM_RMUL THEN REWRITE_TAC[real_div] THEN
      MATCH_MP_TAC REALLIM_RMUL THEN MATCH_MP_TAC REALLIM_SUB THEN
      REWRITE_TAC[REALLIM_CONST; real_pow] THEN MATCH_MP_TAC REALLIM_LMUL THEN
      MATCH_MP_TAC REALLIM_POWN THEN REWRITE_TAC[REAL_ABS_NEG; REAL_ABS_POW] THEN
      MATCH_MP_TAC REAL_POW_1_LT THEN REWRITE_TAC[REAL_ABS_POS; ARITH_EQ] THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[real_sums; FROM_0; INTER_UNIV] THEN
  FIRST_X_ASSUM(MP_TAC) THEN MATCH_MP_TAC EQ_IMP THEN
  AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN
  GEN_TAC THEN MATCH_MP_TAC REAL_INTEGRAL_UNIQUE THEN REWRITE_TAC[RAT_C_PSUM_INT]);;

let RAT_C_CATALAN = prove
 (`catalan_constant = real_integral (real_interval[&0,&1]) (\y. --log y / (&1 + y pow 2))`,
  REWRITE_TAC[catalan_constant] THEN MATCH_MP_TAC REAL_INFSUM_UNIQUE THEN
  REWRITE_TAC[RAT_C_CATSERIES]);;
let RAT_C_PSI0 = prove
 (`forall u. --(&1) < u /\ u < &0
       ==> abs u / sqrt(&1 - u pow 2) * rat_g 0 u +
           abs(--u) / sqrt(&1 - (--u) pow 2) * rat_g 0 (--u) =
           (log(&1 - u) - log(&1 + u)) / sqrt(&1 - u pow 2)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `rat_g 0 u = --log(&1 - u) / u /\ rat_g 0 (--u) = --log(&1 - --u) / --u`
   (CONJUNCTS_THEN SUBST1_TAC) THENL
   [CONJ_TAC THEN MATCH_MP_TAC RAT_C_G0 THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[REAL_RING `(--u:real) pow 2 = u pow 2`; REAL_ARITH `&1 - --u = &1 + u`] THEN
  SUBGOAL_THEN `abs u = --u /\ abs(--u) = --u` (CONJUNCTS_THEN SUBST1_TAC) THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SPEC_TAC(`sqrt(&1 - u pow 2)`, `q:real`) THEN
  SPEC_TAC(`log(&1 - u)`, `a:real`) THEN SPEC_TAC(`log(&1 + u)`, `b:real`) THEN
  UNDISCH_TAC `u < &0` THEN CONV_TAC REAL_FIELD);;

let RAT_C_K0PT = prove
 (`forall y. &0 < y /\ y < &1
       ==> (log(&1 - (y pow 2 - &1) / (y pow 2 + &1)) -
            log(&1 + (y pow 2 - &1) / (y pow 2 + &1))) /
           sqrt(&1 - ((y pow 2 - &1) / (y pow 2 + &1)) pow 2) *
           (&4 * y / (y pow 2 + &1) pow 2) =
           &4 * (--log y / (&1 + y pow 2))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < y pow 2 + &1` ASSUME_TAC THENL
   [MP_TAC(SPEC `y:real` REAL_LE_POW_2) THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&1 - (y pow 2 - &1) / (y pow 2 + &1) = &2 / (y pow 2 + &1) /\
                &1 + (y pow 2 - &1) / (y pow 2 + &1) = &2 / (y pow 2 + &1) * y pow 2`
   (CONJUNCTS_THEN SUBST1_TAC) THENL
   [UNDISCH_TAC `&0 < y pow 2 + &1` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &2 / (y pow 2 + &1)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[LOG_MUL; REAL_POW_LT; LOG_POW] THEN
  SUBGOAL_THEN `sqrt(&1 - ((y pow 2 - &1) / (y pow 2 + &1)) pow 2) = &2 * y / (y pow 2 + &1)`
   SUBST1_TAC THENL
   [MATCH_MP_TAC SQRT_UNIQUE THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
       [REAL_ARITH_TAC; MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC];
      UNDISCH_TAC `&0 < y pow 2 + &1` THEN CONV_TAC REAL_FIELD]; ALL_TAC] THEN
  SPEC_TAC(`log(&2 / (y pow 2 + &1))`, `a:real`) THEN
  SPEC_TAC(`log y`, `b:real`) THEN
  UNDISCH_TAC `&0 < y pow 2 + &1` THEN UNDISCH_TAC `&0 < y` THEN CONV_TAC REAL_FIELD);;

let RAT_K0 = prove
 (`(\t. abs t / sqrt(&1 - t pow 2) * rat_g 0 t) real_integrable_on real_interval[--(&1),&1]
   ==> real_integral (real_interval[--(&1),&1]) (\t. abs t / sqrt(&1 - t pow 2) * rat_g 0 t) = &4 * catalan_constant`,
  ABBREV_TAC `fq = \t. abs t / sqrt(&1 - t pow 2) * rat_g 0 t` THEN DISCH_TAC THEN
  ABBREV_TAC `kk = real_integral (real_interval[--(&1),&1]) fq` THEN
  SUBGOAL_THEN `((\u. (log(&1 - u) - log(&1 + u)) / sqrt(&1 - u pow 2)) has_real_integral kk)
                (real_interval[--(&1),&0])` ASSUME_TAC THENL
   [MATCH_MP_TAC RAT_C_SPIKE THEN EXISTS_TAC `\u:real. fq u + (fq:real->real)(--u)` THEN
    CONJ_TAC THENL
     [ALL_TAC; EXPAND_TAC "fq" THEN REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
      CONV_TAC SYM_CONV THEN MATCH_MP_TAC RAT_C_PSI0 THEN ASM_REWRITE_TAC[]] THEN
    EXPAND_TAC "kk" THEN
    MP_TAC(ISPECL [`fq:real->real`; `--(&1)`; `&1`; `&0`] REAL_INTEGRAL_COMBINE) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [REAL_ARITH_TAC; DISCH_THEN(SUBST1_TAC o SYM)] THEN
    MATCH_MP_TAC HAS_REAL_INTEGRAL_ADD THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_INTEGRABLE_INTEGRAL THEN
      MATCH_MP_TAC REAL_INTEGRABLE_SUBINTERVAL THEN
      MAP_EVERY EXISTS_TAC [`--(&1)`; `&1`] THEN ASM_REWRITE_TAC[SUBSET_REAL_INTERVAL] THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(ISPECL [`fq:real->real`; `real_integral (real_interval[&0,&1]) fq`; `&0`; `&1`]
           HAS_REAL_INTEGRAL_REFLECT) THEN REWRITE_TAC[REAL_NEG_0] THEN
    DISCH_THEN SUBST1_TAC THEN
    MATCH_MP_TAC REAL_INTEGRABLE_INTEGRAL THEN
    MATCH_MP_TAC REAL_INTEGRABLE_SUBINTERVAL THEN
    MAP_EVERY EXISTS_TAC [`--(&1)`; `&1`] THEN ASM_REWRITE_TAC[SUBSET_REAL_INTERVAL] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\u:real. (log(&1 - u) - log(&1 + u)) / sqrt(&1 - u pow 2)`;
                 `\y:real. (y pow 2 - &1) / (y pow 2 + &1)`;
                 `\y:real. &4 * y / (y pow 2 + &1) pow 2`;
                 `--(&1)`; `&0`; `kk:real`] RAT_C_SUBST) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL [REAL_ARITH_TAC; CONV_TAC REAL_RAT_REDUCE_CONV;
      CONV_TAC REAL_RAT_REDUCE_CONV; ALL_TAC; ALL_TAC] THEN
    X_GEN_TAC `x:real` THEN STRIP_TAC THENL
     [SUBGOAL_THEN `&0 < x pow 2 + &1 /\ x pow 2 <= &1` STRIP_ASSUME_TAC THENL
       [CONJ_TAC THENL [MP_TAC(SPEC `x:real` REAL_LE_POW_2) THEN REAL_ARITH_TAC;
                        MATCH_MP_TAC REAL_POW_1_LE THEN ASM_REAL_ARITH_TAC]; ALL_TAC] THEN
      CONJ_TAC THENL [ALL_TAC; CONJ_TAC] THENL
       [REAL_DIFF_TAC THEN UNDISCH_TAC `&0 < x pow 2 + &1` THEN CONV_TAC REAL_FIELD;
        ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN MP_TAC(SPEC `x:real` REAL_LE_POW_2) THEN
        REAL_ARITH_TAC;
        ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN ASM_REAL_ARITH_TAC];
      SUBGOAL_THEN `&0 < x pow 2 + &1 /\ x pow 2 < &1 /\ &0 < x pow 2` STRIP_ASSUME_TAC THENL
       [REPEAT CONJ_TAC THENL
         [MP_TAC(SPEC `x:real` REAL_LE_POW_2) THEN REAL_ARITH_TAC;
          MATCH_MP_TAC REAL_POW_1_LT THEN REWRITE_TAC[ARITH_EQ] THEN ASM_REAL_ARITH_TAC;
          MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC]; ALL_TAC] THEN
      ABBREV_TAC `u = (x pow 2 - &1) / (x pow 2 + &1)` THEN
      SUBGOAL_THEN `--(&1) < u /\ u < &0` STRIP_ASSUME_TAC THENL
       [EXPAND_TAC "u" THEN ASM_SIMP_TAC[REAL_LT_RDIV_EQ; REAL_LT_LDIV_EQ] THEN
        ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `&0 < &1 - u pow 2` ASSUME_TAC THENL
       [MATCH_MP_TAC(REAL_ARITH `&0 < (&1 - u) * (&1 + u) /\ (&1 - u) * (&1 + u) = &1 - u pow 2
                                 ==> &0 < &1 - u pow 2`) THEN
        CONJ_TAC THENL [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC; CONV_TAC REAL_RING];
        ALL_TAC] THEN
      MATCH_MP_TAC REAL_DIFFERENTIABLE_IMP_CONTINUOUS_ATREAL THEN
      REAL_DIFFERENTIABLE_TAC THEN ASM_SIMP_TAC[SQRT_POS_LT; REAL_LT_IMP_NZ] THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `((\y. &4 * (--log y / (&1 + y pow 2))) has_real_integral kk) (real_interval[&0,&1])`
  MP_TAC THENL
   [MATCH_MP_TAC RAT_C_SPIKE THEN
    FIRST_X_ASSUM(fun th -> EXISTS_TAC(rand(rator(rator(concl th)))) THEN REWRITE_TAC[th]) THEN
    REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC RAT_C_K0PT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(MATCH_MP REAL_INTEGRABLE_INTEGRAL (CONJUNCT1 RAT_C_CATSERIES)) THEN
  DISCH_THEN(MP_TAC o SPEC `&4` o MATCH_MP HAS_REAL_INTEGRAL_LMUL) THEN
  REWRITE_TAC[RAT_C_CATALAN; IMP_IMP] THEN
  MESON_TAC[HAS_REAL_INTEGRAL_UNIQUE]);;
let RAT_C_G0NEG_INT = prove
 (`(\v. rat_g 0 (--v)) real_integrable_on real_interval[&0,&1]`,
  MATCH_MP_TAC REAL_INTEGRABLE_DECREASING THEN
  REWRITE_TAC[IN_REAL_INTERVAL; rat_g] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC REAL_INTEGRAL_LE THEN
  SUBGOAL_THEN `forall z. &0 <= z ==> (\s. s pow 0 / (&1 - --z * s)) real_integrable_on real_interval[&0,&1]`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_INTEGRABLE_CONTINUOUS THEN
    REWRITE_TAC[REAL_CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN; IN_REAL_INTERVAL] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_CONTINUOUS_ATREAL_WITHINREAL THEN
    MATCH_MP_TAC REAL_DIFFERENTIABLE_IMP_CONTINUOUS_ATREAL THEN
    REAL_DIFFERENTIABLE_TAC THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= z * x ==> ~(&1 - --z * x = &0)`) THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  X_GEN_TAC `s:real` THEN REWRITE_TAC[IN_REAL_INTERVAL; real_pow; real_div; REAL_MUL_LID] THEN
  STRIP_TAC THEN MATCH_MP_TAC REAL_LE_INV2 THEN
  SUBGOAL_THEN `&0 <= x * s /\ x * s <= y * s` MP_TAC THENL
   [CONJ_TAC THENL [MATCH_MP_TAC REAL_LE_MUL; MATCH_MP_TAC REAL_LE_RMUL] THEN
    ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REAL_ARITH_TAC);;

let RAT_C_PSI1 = prove
 (`forall x. &0 < x /\ x < &1
       ==> abs x / sqrt(&1 - x pow 2) * rat_g 1 x +
           abs(--x) / sqrt(&1 - (--x) pow 2) * rat_g 1 (--x) =
           --(log(&1 - x) + log(&1 + x)) / (x * sqrt(&1 - x pow 2))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `rat_g 1 x = --log(&1 - x) / x pow 2 - &1 / x /\
                rat_g 1 (--x) = --log(&1 - --x) / (--x) pow 2 - &1 / --x`
   (CONJUNCTS_THEN SUBST1_TAC) THENL
   [CONJ_TAC THEN MATCH_MP_TAC RAT_C_G1 THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[REAL_RING `(--u:real) pow 2 = u pow 2`; REAL_ARITH `&1 - --u = &1 + u`] THEN
  SUBGOAL_THEN `abs x = x /\ abs(--x) = x` (CONJUNCTS_THEN SUBST1_TAC) THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < sqrt(&1 - x pow 2)` MP_TAC THENL
   [MATCH_MP_TAC SQRT_POS_LT THEN
    MATCH_MP_TAC(REAL_ARITH `x pow 2 < &1 ==> &0 < &1 - x pow 2`) THEN
    MATCH_MP_TAC REAL_POW_1_LT THEN REWRITE_TAC[ARITH_EQ] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SPEC_TAC(`sqrt(&1 - x pow 2)`, `q:real`) THEN
  SPEC_TAC(`log(&1 - x)`, `a:real`) THEN SPEC_TAC(`log(&1 + x)`, `b:real`) THEN
  UNDISCH_TAC `&0 < x` THEN CONV_TAC REAL_FIELD);;

let RAT_C_K1PT = prove
 (`forall w. &0 < w /\ w < &1
       ==> --(log(&1 - &2 * w / (&1 + w pow 2)) + log(&1 + &2 * w / (&1 + w pow 2))) /
           ((&2 * w / (&1 + w pow 2)) * sqrt(&1 - (&2 * w / (&1 + w pow 2)) pow 2)) *
           (&2 * (&1 - w pow 2) / (&1 + w pow 2) pow 2) =
           (--log(&1 - w pow 2) / w pow 2 + log(&1 + w pow 2) / w pow 2) * (&2 * w)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < &1 + w pow 2 /\ &0 < &1 - w /\ &0 < &1 + w /\ &0 < &1 - w pow 2`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MP_TAC(SPEC `w:real` REAL_LE_POW_2) THEN REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC(REAL_ARITH `w pow 2 < &1 ==> &0 < &1 - w pow 2`) THEN
      MATCH_MP_TAC REAL_POW_1_LT THEN REWRITE_TAC[ARITH_EQ] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `log(&1 - &2 * w / (&1 + w pow 2)) = &2 * log(&1 - w) - log(&1 + w pow 2) /\
                log(&1 + &2 * w / (&1 + w pow 2)) = &2 * log(&1 + w) - log(&1 + w pow 2) /\
                log(&1 - w pow 2) = log(&1 - w) + log(&1 + w)`
  (REPEAT_TCL CONJUNCTS_THEN SUBST1_TAC) THENL
   [REPEAT CONJ_TAC THENL
     [SUBGOAL_THEN `&1 - &2 * w / (&1 + w pow 2) = (&1 - w) pow 2 / (&1 + w pow 2)` SUBST1_TAC THENL
       [UNDISCH_TAC `&0 < &1 + w pow 2` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
      ASM_SIMP_TAC[LOG_DIV; REAL_POW_LT; LOG_POW];
      SUBGOAL_THEN `&1 + &2 * w / (&1 + w pow 2) = (&1 + w) pow 2 / (&1 + w pow 2)` SUBST1_TAC THENL
       [UNDISCH_TAC `&0 < &1 + w pow 2` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
      ASM_SIMP_TAC[LOG_DIV; REAL_POW_LT; LOG_POW];
      SUBGOAL_THEN `&1 - w pow 2 = (&1 - w) * (&1 + w)` SUBST1_TAC THENL
       [CONV_TAC REAL_RING; ALL_TAC] THEN
      ASM_SIMP_TAC[LOG_MUL]];
    ALL_TAC] THEN
  SUBGOAL_THEN `sqrt(&1 - (&2 * w / (&1 + w pow 2)) pow 2) = (&1 - w pow 2) / (&1 + w pow 2)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC SQRT_UNIQUE THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC;
      UNDISCH_TAC `&0 < &1 + w pow 2` THEN CONV_TAC REAL_FIELD]; ALL_TAC] THEN
  SPEC_TAC(`log(&1 - w)`, `a:real`) THEN SPEC_TAC(`log(&1 + w)`, `b:real`) THEN
  SPEC_TAC(`log(&1 + w pow 2)`, `c:real`) THEN
  UNDISCH_TAC `&0 < &1 + w pow 2` THEN UNDISCH_TAC `&0 < &1 - w pow 2` THEN
  UNDISCH_TAC `&0 < w` THEN CONV_TAC REAL_FIELD);;

let RAT_C_FDPT = prove
 (`forall v. &0 < v /\ v < &1
       ==> --log(&1 - v pow 2) / v pow 2 * (&2 * v) =
           &2 * (--log(&1 - v) / v - log(&1 + v) / v)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `log(&1 - v pow 2) = log(&1 - v) + log(&1 + v)` SUBST1_TAC THENL
   [SUBGOAL_THEN `&1 - v pow 2 = (&1 - v) * (&1 + v)` SUBST1_TAC THENL
     [CONV_TAC REAL_RING; ALL_TAC] THEN
    MATCH_MP_TAC LOG_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SPEC_TAC(`log(&1 - v)`, `a:real`) THEN SPEC_TAC(`log(&1 + v)`, `b:real`) THEN
  UNDISCH_TAC `&0 < v` THEN CONV_TAC REAL_FIELD);;

let RAT_K1 = prove
 (`(\t. abs t / sqrt(&1 - t pow 2) * rat_g 1 t) real_integrable_on real_interval[--(&1),&1] /\
   (\t. rat_g 0 t) real_integrable_on real_interval[&0,&1]
   ==> real_integral (real_interval[--(&1),&1]) (\t. abs t / sqrt(&1 - t pow 2) * rat_g 1 t) =
       &3 / &2 * real_integral (real_interval[&0,&1]) (\t. rat_g 0 t)`,
  (ABBREV_TAC `fq = \t. abs t / sqrt(&1 - t pow 2) * rat_g 1 t` THEN STRIP_TAC THEN
   ABBREV_TAC `kk:real = real_integral (real_interval[--(&1),&1]) fq` THEN
   ABBREV_TAC `iq:real = real_integral (real_interval[&0,&1]) (\t. rat_g 0 t)` THEN
   ABBREV_TAC `jq:real = real_integral (real_interval[&0,&1]) (\v:real. rat_g 0 (--v))`) THEN
  (SUBGOAL_THEN `((\x. --(log(&1 - x) + log(&1 + x)) / (x * sqrt(&1 - x pow 2))) has_real_integral kk)
                 (real_interval[&0,&1])` ASSUME_TAC THENL
   [MATCH_MP_TAC RAT_C_SPIKE THEN EXISTS_TAC `\x:real. fq x + (fq:real->real)(--x)` THEN
    CONJ_TAC THENL
     [ALL_TAC; EXPAND_TAC "fq" THEN REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
      CONV_TAC SYM_CONV THEN MATCH_MP_TAC RAT_C_PSI1 THEN ASM_REWRITE_TAC[]] THEN
    EXPAND_TAC "kk" THEN
    MP_TAC(ISPECL [`fq:real->real`; `--(&1)`; `&1`; `&0`] REAL_INTEGRAL_COMBINE) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [REAL_ARITH_TAC; DISCH_THEN(SUBST1_TAC o SYM o ONCE_REWRITE_RULE[REAL_ADD_SYM])] THEN
    MATCH_MP_TAC HAS_REAL_INTEGRAL_ADD THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_INTEGRABLE_INTEGRAL THEN
      MATCH_MP_TAC REAL_INTEGRABLE_SUBINTERVAL THEN
      MAP_EVERY EXISTS_TAC [`--(&1)`; `&1`] THEN ASM_REWRITE_TAC[SUBSET_REAL_INTERVAL] THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(ISPECL [`fq:real->real`; `real_integral (real_interval[--(&1),&0]) fq`; `--(&1)`; `&0`]
           HAS_REAL_INTEGRAL_REFLECT) THEN REWRITE_TAC[REAL_NEG_0; REAL_NEG_NEG] THEN
    DISCH_THEN SUBST1_TAC THEN
    MATCH_MP_TAC REAL_INTEGRABLE_INTEGRAL THEN
    MATCH_MP_TAC REAL_INTEGRABLE_SUBINTERVAL THEN
    MAP_EVERY EXISTS_TAC [`--(&1)`; `&1`] THEN ASM_REWRITE_TAC[SUBSET_REAL_INTERVAL] THEN
    REAL_ARITH_TAC;
    ALL_TAC]) THEN
  (MP_TAC(ISPECL [`\x:real. --(log(&1 - x) + log(&1 + x)) / (x * sqrt(&1 - x pow 2))`;
                  `\w:real. &2 * w / (&1 + w pow 2)`;
                  `\w:real. &2 * (&1 - w pow 2) / (&1 + w pow 2) pow 2`;
                  `&0`; `&1`; `kk:real`] RAT_C_SUBST) THEN
   ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL [REAL_ARITH_TAC; CONV_TAC REAL_RAT_REDUCE_CONV;
      CONV_TAC REAL_RAT_REDUCE_CONV; ALL_TAC; ALL_TAC] THEN
    X_GEN_TAC `x:real` THEN STRIP_TAC THEN
    (SUBGOAL_THEN `&0 < &1 + x pow 2` ASSUME_TAC THENL
     [MP_TAC(SPEC `x:real` REAL_LE_POW_2) THEN REAL_ARITH_TAC; ALL_TAC]) THENL
     [CONJ_TAC THENL [ALL_TAC; CONJ_TAC] THENL
       [REAL_DIFF_TAC THEN UNDISCH_TAC `&0 < &1 + x pow 2` THEN CONV_TAC REAL_FIELD;
        MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
         [REAL_ARITH_TAC; MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC];
        REWRITE_TAC[GSYM real_div; REAL_ARITH `&2 * x / y = (&2 * x) / y`] THEN
        ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
        MP_TAC(SPEC `(x:real) - &1` REAL_LE_POW_2) THEN REWRITE_TAC[REAL_POW_2] THEN REAL_ARITH_TAC];
      ALL_TAC] THEN
    ABBREV_TAC `u = &2 * x / (&1 + x pow 2)` THEN
    SUBGOAL_THEN `&0 < u /\ u < &1` STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "u" THEN REWRITE_TAC[REAL_ARITH `&2 * x / y = (&2 * x) / y`] THEN
      ASM_SIMP_TAC[REAL_LT_RDIV_EQ; REAL_LT_LDIV_EQ] THEN
      MP_TAC(SPECL [`&1 - x:real`; `2`] REAL_POW_LT) THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[REAL_POW_2] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&0 < &1 - u pow 2` ASSUME_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `u pow 2 < &1 ==> &0 < &1 - u pow 2`) THEN
      MATCH_MP_TAC REAL_POW_1_LT THEN REWRITE_TAC[ARITH_EQ] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_DIFFERENTIABLE_IMP_CONTINUOUS_ATREAL THEN
    REAL_DIFFERENTIABLE_TAC THEN ASM_SIMP_TAC[SQRT_POS_LT; REAL_LT_IMP_NZ; REAL_ENTIRE] THEN
    ASM_REAL_ARITH_TAC;
    DISCH_TAC]) THEN
  (SUBGOAL_THEN `((\v. --log(&1 - v) / v + log(&1 + v) / v) has_real_integral iq + jq)
                 (real_interval[&0,&1])` ASSUME_TAC THENL
   [MATCH_MP_TAC RAT_C_SPIKE THEN EXISTS_TAC `\v:real. rat_g 0 v + rat_g 0 (--v)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC HAS_REAL_INTEGRAL_ADD THEN MAP_EVERY EXPAND_TAC ["iq"; "jq"] THEN CONJ_TAC THEN
      MATCH_MP_TAC REAL_INTEGRABLE_INTEGRAL THEN ASM_REWRITE_TAC[RAT_C_G0NEG_INT];
      REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
      SUBGOAL_THEN `rat_g 0 x = --log(&1 - x) / x /\ rat_g 0 (--x) = --log(&1 - --x) / --x`
       (CONJUNCTS_THEN SUBST1_TAC) THENL
       [CONJ_TAC THEN MATCH_MP_TAC RAT_C_G0 THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[REAL_ARITH `&1 - --u = &1 + u`; real_div; REAL_INV_NEG] THEN REAL_ARITH_TAC];
    ALL_TAC]) THEN
  (MP_TAC(ISPECL [`\v:real. --log(&1 - v) / v + log(&1 + v) / v`;
                  `\w:real. w pow 2`; `\w:real. &2 * w`;
                  `&0`; `&1`; `iq + jq:real`] RAT_C_SUBST) THEN
   ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL [REAL_ARITH_TAC; CONV_TAC REAL_RAT_REDUCE_CONV;
      CONV_TAC REAL_RAT_REDUCE_CONV; ALL_TAC; ALL_TAC] THEN
    X_GEN_TAC `x:real` THEN STRIP_TAC THENL
     [REPEAT CONJ_TAC THENL
       [REAL_DIFF_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[REAL_POW_1] THEN REAL_ARITH_TAC;
        REWRITE_TAC[REAL_LE_POW_2];
        MATCH_MP_TAC REAL_POW_1_LE THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 < x pow 2 /\ x pow 2 < &1` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL [MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_POW_1_LT THEN REWRITE_TAC[ARITH_EQ] THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_DIFFERENTIABLE_IMP_CONTINUOUS_ATREAL THEN
    REAL_DIFFERENTIABLE_TAC THEN ASM_REAL_ARITH_TAC;
    DISCH_TAC]) THEN
  (SUBGOAL_THEN `((\x. --(log(&1 - &2 * x / (&1 + x pow 2)) + log(&1 + &2 * x / (&1 + x pow 2))) /
        ((&2 * x / (&1 + x pow 2)) * sqrt(&1 - (&2 * x / (&1 + x pow 2)) pow 2)) *
        (&2 * (&1 - x pow 2) / (&1 + x pow 2) pow 2)) has_real_integral iq + jq)
       (real_interval[&0,&1])` ASSUME_TAC THENL
   [MATCH_MP_TAC RAT_C_SPIKE THEN
    FIRST_X_ASSUM(fun th -> EXISTS_TAC(rand(rator(rator(concl th)))) THEN REWRITE_TAC[th]) THEN
    REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC RAT_C_K1PT THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
   SUBGOAL_THEN `kk = iq + jq:real` ASSUME_TAC THENL
   [FIRST_X_ASSUM(fun th10 -> FIRST_X_ASSUM(fun th7 ->
      ACCEPT_TAC(MATCH_MP HAS_REAL_INTEGRAL_UNIQUE (CONJ th7 th10)))); ALL_TAC]) THEN
  (SUBGOAL_THEN `((\y. --log(&1 - y) / y) has_real_integral iq) (real_interval[&0,&1])`
   ASSUME_TAC THENL
   [MATCH_MP_TAC RAT_C_SPIKE THEN EXISTS_TAC `\t:real. rat_g 0 t` THEN CONJ_TAC THENL
     [EXPAND_TAC "iq" THEN MATCH_MP_TAC REAL_INTEGRABLE_INTEGRAL THEN ASM_REWRITE_TAC[];
      REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN CONV_TAC SYM_CONV THEN
      MATCH_MP_TAC RAT_C_G0 THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
   MP_TAC(ISPECL [`\y:real. --log(&1 - y) / y`;
                  `\w:real. w pow 2`; `\w:real. &2 * w`;
                  `&0`; `&1`; `iq:real`] RAT_C_SUBST) THEN
   ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL [REAL_ARITH_TAC; CONV_TAC REAL_RAT_REDUCE_CONV;
      CONV_TAC REAL_RAT_REDUCE_CONV; ALL_TAC; ALL_TAC] THEN
    X_GEN_TAC `x:real` THEN STRIP_TAC THENL
     [REPEAT CONJ_TAC THENL
       [REAL_DIFF_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[REAL_POW_1] THEN
        REAL_ARITH_TAC;
        REWRITE_TAC[REAL_LE_POW_2];
        MATCH_MP_TAC REAL_POW_1_LE THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 < x pow 2 /\ x pow 2 < &1` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL [MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_POW_1_LT THEN REWRITE_TAC[ARITH_EQ] THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_DIFFERENTIABLE_IMP_CONTINUOUS_ATREAL THEN
    REAL_DIFFERENTIABLE_TAC THEN ASM_REAL_ARITH_TAC;
    DISCH_TAC]) THEN
  (SUBGOAL_THEN `((\v. &2 * (rat_g 0 v - rat_g 0 (--v))) has_real_integral iq)
                 (real_interval[&0,&1])` ASSUME_TAC THENL
   [MATCH_MP_TAC RAT_C_SPIKE THEN
    FIRST_X_ASSUM(fun th -> EXISTS_TAC(rand(rator(rator(concl th)))) THEN REWRITE_TAC[th]) THEN
    REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
    SUBGOAL_THEN `rat_g 0 x = --log(&1 - x) / x /\ rat_g 0 (--x) = --log(&1 - --x) / --x`
     (CONJUNCTS_THEN SUBST1_TAC) THENL
     [CONJ_TAC THEN MATCH_MP_TAC RAT_C_G0 THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[RAT_C_FDPT] THEN
    REWRITE_TAC[REAL_ARITH `&1 - --u = &1 + u`; real_div; REAL_INV_NEG] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
   SUBGOAL_THEN `((\v. &2 * (rat_g 0 v - rat_g 0 (--v))) has_real_integral &2 * (iq - jq))
                 (real_interval[&0,&1])` ASSUME_TAC THENL
   [MATCH_MP_TAC HAS_REAL_INTEGRAL_LMUL THEN MATCH_MP_TAC HAS_REAL_INTEGRAL_SUB THEN
    MAP_EVERY EXPAND_TAC ["iq"; "jq"] THEN CONJ_TAC THEN
    MATCH_MP_TAC REAL_INTEGRABLE_INTEGRAL THEN ASM_REWRITE_TAC[RAT_C_G0NEG_INT];
    ALL_TAC] THEN
   SUBGOAL_THEN `iq = &2 * (iq - jq):real` MP_TAC THENL
   [FIRST_X_ASSUM(fun th10 -> FIRST_X_ASSUM(fun th7 ->
      ACCEPT_TAC(MATCH_MP HAS_REAL_INTEGRAL_UNIQUE (CONJ th7 th10)))); ALL_TAC] THEN
   ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC));;
