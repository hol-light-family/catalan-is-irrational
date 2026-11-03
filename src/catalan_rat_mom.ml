(* ========================================================================= *)
(* CAT_RATIONALITY: monomial moments M(i,j), Z(i,j) (prefix rat).            *)
(* ========================================================================= *)

needs "src/catalan_rat_base.ml";;


(* ------------------------------------------------------------------------- *)
(* The one-variable moments J_k = int_0^1 t^(k+1)/sqrt(1-t^2) dt.           *)
(* ------------------------------------------------------------------------- *)

let RAT_CONT_SQRT = prove
 (`forall f s. f real_continuous_on s ==> (\x. sqrt(f x)) real_continuous_on s`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\x. sqrt(f x)) = sqrt o (f:real->real)` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_CONTINUOUS_ON_COMPOSE THEN
  ASM_REWRITE_TAC[REAL_CONTINUOUS_ON_SQRT]);;

let RAT_SQRT_CONT = prove
 (`forall s. (\t. sqrt(&1 - t pow 2)) real_continuous_on s`,
  GEN_TAC THEN MATCH_MP_TAC RAT_CONT_SQRT THEN
  SIMP_TAC[REAL_CONTINUOUS_ON_SUB; REAL_CONTINUOUS_ON_CONST;
           REAL_CONTINUOUS_ON_POW; REAL_CONTINUOUS_ON_ID]);;

let RAT_J0 = prove
 (`((\t. t / sqrt(&1 - t pow 2)) has_real_integral &1) (real_interval[&0,&1])`,
  MP_TAC(ISPECL [`\t. --sqrt(&1 - t pow 2)`; `\t. t / sqrt(&1 - t pow 2)`;
                 `&0`; `&1`] REAL_FUNDAMENTAL_THEOREM_OF_CALCULUS_INTERIOR) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [REWRITE_TAC[REAL_POS] THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_CONTINUOUS_ON_NEG THEN REWRITE_TAC[RAT_SQRT_CONT];
      ALL_TAC] THEN
    X_GEN_TAC `x:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
    SUBGOAL_THEN `&0 < &1 - x pow 2` ASSUME_TAC THENL
     [REWRITE_TAC[REAL_SUB_LT] THEN MATCH_MP_TAC REAL_POW_1_LT THEN
      CONV_TAC NUM_REDUCE_CONV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REAL_DIFF_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `&0 < sqrt(&1 - x pow 2)` MP_TAC THENL
     [ASM_SIMP_TAC[SQRT_POS_LT]; ALL_TAC] THEN
    CONV_TAC REAL_FIELD;
    REWRITE_TAC[] THEN CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
    REWRITE_TAC[SQRT_0; SQRT_1] THEN CONV_TAC REAL_RAT_REDUCE_CONV]);;

let RAT_J0_INT = prove
 (`(\t. t / sqrt(&1 - t pow 2)) real_integrable_on real_interval[&0,&1]`,
  MESON_TAC[RAT_J0; real_integrable_on]);;

let RAT_ONE_SUB_SQ_POS = prove
 (`forall t. abs t <= &1 ==> &0 <= &1 - t pow 2`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[REAL_SUB_LE] THEN
  ONCE_REWRITE_TAC[GSYM REAL_POW2_ABS] THEN
  MATCH_MP_TAC REAL_POW_1_LE THEN ASM_REAL_ARITH_TAC);;

let RAT_ONE_SUB_SQ_LT = prove
 (`forall t. abs t < &1 ==> &0 < &1 - t pow 2`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[REAL_SUB_LT] THEN
  ONCE_REWRITE_TAC[GSYM REAL_POW2_ABS] THEN
  MATCH_MP_TAC REAL_POW_1_LT THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_REAL_ARITH_TAC);;

let RAT_SQRT_POS = prove
 (`forall t. abs t <= &1 ==> &0 <= sqrt(&1 - t pow 2)`,
  SIMP_TAC[SQRT_POS_LE; RAT_ONE_SUB_SQ_POS]);;

let RAT_SQRT_LT = prove
 (`forall t. abs t < &1 ==> &0 < sqrt(&1 - t pow 2)`,
  SIMP_TAC[SQRT_POS_LT; RAT_ONE_SUB_SQ_LT]);;

let RAT_SQRT_SQ = prove
 (`forall t. abs t <= &1 ==> sqrt(&1 - t pow 2) pow 2 = &1 - t pow 2`,
  SIMP_TAC[SQRT_POW_2; RAT_ONE_SUB_SQ_POS]);;

let RAT_FDIV_POS = prove
 (`forall t. &0 <= t /\ t <= &1 ==> &0 <= t / sqrt(&1 - t pow 2)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_DIV THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC RAT_SQRT_POS THEN ASM_REAL_ARITH_TAC);;

let rat_J = new_definition
 `rat_J k = real_integral (real_interval[&0,&1])
              (\t. t pow (k + 1) / sqrt(&1 - t pow 2))`;;

let RAT_LE_MUL1 = prove
 (`forall a b. a <= &1 /\ &0 <= b ==> a * b <= b:real`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(REAL_ARITH `&0 <= (&1 - a) * b ==> a * b <= b`) THEN
  MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC);;

let RAT_POW_SPLIT = prove
 (`forall t k f. (t:real) pow (k + 1) / f = t pow k * (t / f)`,
  REWRITE_TAC[REAL_POW_ADD; REAL_POW_1; real_div] THEN REAL_ARITH_TAC);;

let RAT_J_INT = prove
 (`forall k. (\t. t pow (k + 1) / sqrt(&1 - t pow 2)) real_integrable_on
       real_interval[&0,&1]`,
  GEN_TAC THEN
  MATCH_MP_TAC REAL_MEASURABLE_BOUNDED_BY_INTEGRABLE_IMP_INTEGRABLE THEN
  EXISTS_TAC `\t. t / sqrt(&1 - t pow 2)` THEN REWRITE_TAC[RAT_J0_INT] THEN
  REWRITE_TAC[RAT_POW_SPLIT] THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_MEASURABLE_ON_MUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_IMP_REAL_MEASURABLE_ON_CLOSED_SUBSET THEN
      SIMP_TAC[REAL_CLOSED_REAL_INTERVAL; REAL_CONTINUOUS_ON_POW;
               REAL_CONTINUOUS_ON_ID];
      MATCH_MP_TAC INTEGRABLE_IMP_REAL_MEASURABLE THEN
      REWRITE_TAC[RAT_J0_INT]];
    X_GEN_TAC `t:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
    REWRITE_TAC[REAL_ABS_MUL] THEN
    ASM_SIMP_TAC[REAL_ABS_POW; RAT_FDIV_POS;
                 REAL_ARITH `&0 <= x ==> abs x = x`] THEN
    MATCH_MP_TAC RAT_LE_MUL1 THEN ASM_SIMP_TAC[RAT_FDIV_POS] THEN
    MATCH_MP_TAC REAL_POW_1_LE THEN ASM_REAL_ARITH_TAC]);;
let RAT_C_POS = prove
 (`forall l. &0 < cat_c l`,
  GEN_TAC THEN REWRITE_TAC[cat_c] THEN MATCH_MP_TAC REAL_LT_DIV THEN
  SIMP_TAC[REAL_POW_LT; REAL_ARITH `&0 < &4`; REAL_OF_NUM_LT] THEN
  REWRITE_TAC[ARITH_RULE `0 < n <=> ~(n = 0)`; BINOM_EQ_0] THEN ARITH_TAC);;

let RAT_C_0 = prove
 (`cat_c 0 = &1`,
  REWRITE_TAC[cat_c; MULT_CLAUSES; binom; real_pow] THEN REAL_ARITH_TAC);;

let RAT_C_STEP = prove
 (`forall l. &(2 * l + 2) * cat_c (l + 1) = &(2 * l + 1) * cat_c l`,
  GEN_TAC THEN REWRITE_TAC[cat_c] THEN
  REWRITE_TAC[ARITH_RULE `2 * (l + 1) = (2 * l + 1) + 1`] THEN
  REWRITE_TAC[BINOM_BOTH_STEP_REAL] THEN
  REWRITE_TAC[ARITH_RULE `2 * l + 1 = (2 * l) + 1`; BINOM_TOP_STEP_REAL] THEN
  REWRITE_TAC[ARITH_RULE `~(l = 2 * l + 1)`; real_pow; REAL_POW_ADD] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_ADD; GSYM REAL_OF_NUM_MUL] THEN
  MP_TAC(SPEC `l:num` RAT_C_POS) THEN REWRITE_TAC[cat_c] THEN
  SUBGOAL_THEN `&0 < &4 pow l` MP_TAC THENL
   [SIMP_TAC[REAL_POW_LT; REAL_ARITH `&0 < &4`]; ALL_TAC] THEN
  REWRITE_TAC[REAL_POW_1] THEN CONV_TAC REAL_FIELD);;
let RAT_JREC_DERIV = prove(`forall n x. &0 < x /\ x < &1 ==>
   ((\t. --(t pow (n + 2) * sqrt(&1 - t pow 2))) has_real_derivative
    ((&(n + 3) * x pow (n + 3) - &(n + 2) * x pow (n + 1)) / sqrt(&1 - x pow 2)))
   (atreal x)`,
REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `abs x < &1` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP RAT_ONE_SUB_SQ_LT) THEN
  REAL_DIFF_TAC THEN ASM_REWRITE_TAC[] THEN
MP_TAC(SPEC `x:real` RAT_SQRT_LT) THEN MP_TAC(SPEC `x:real` RAT_SQRT_SQ) THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
  SUBGOAL_THEN `(x:real) pow (n + 2) = x pow (n + 1) * x /\
                x pow (n + 3) = x pow (n + 1) * x pow 2 /\
                x pow (2 - 1) = x /\ (n + 2) - 1 = n + 1` 
   (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[ARITH_RULE `n + 2 = SUC(n + 1) /\ n + 3 = SUC(SUC(n + 1))`] THEN
    REWRITE_TAC[real_pow; REAL_POW_2] THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[REAL_POW_1] THEN REPEAT CONJ_TAC THEN (ARITH_TAC ORELSE REAL_ARITH_TAC); ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN
  SPEC_TAC(`(x:real) pow (n + 1)`,`y:real`) THEN SPEC_TAC(`sqrt(&1 - x pow 2)`,`s:real`) THEN
  CONV_TAC REAL_FIELD);;

let RAT_HRI = prove
 (`forall f s. f real_integrable_on s ==> (f has_real_integral real_integral s f) s`,
  SIMP_TAC[HAS_REAL_INTEGRAL_INTEGRAL]);;

let RAT_J_REC = prove
 (`forall n. &(n + 3) * rat_J (n + 2) = &(n + 2) * rat_J n`,
  GEN_TAC THEN
  MP_TAC(ISPECL [`\t. --(t pow (n + 2) * sqrt(&1 - t pow 2))`;
                 `\x. (&(n + 3) * x pow (n + 3) - &(n + 2) * x pow (n + 1)) /
                      sqrt(&1 - x pow 2)`;
                 `&0`; `&1`] REAL_FUNDAMENTAL_THEOREM_OF_CALCULUS_INTERIOR) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [REWRITE_TAC[REAL_POS; IN_REAL_INTERVAL] THEN
    SIMP_TAC[RAT_JREC_DERIV] THEN
    MATCH_MP_TAC REAL_CONTINUOUS_ON_NEG THEN
    MATCH_MP_TAC REAL_CONTINUOUS_ON_MUL THEN
    SIMP_TAC[RAT_SQRT_CONT; REAL_CONTINUOUS_ON_POW; REAL_CONTINUOUS_ON_ID];
    ALL_TAC] THEN
  CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
  REWRITE_TAC[REAL_POW_ONE; REAL_POW_ZERO; ADD_EQ_0; ARITH_EQ] THEN
  CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
  REWRITE_TAC[SQRT_0; SQRT_1] THEN CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
  SUBGOAL_THEN
   `((\x. &(n + 3) * (x pow ((n + 2) + 1) / sqrt(&1 - x pow 2)) -
          &(n + 2) * (x pow (n + 1) / sqrt(&1 - x pow 2))) has_real_integral
     (&(n + 3) * rat_J (n + 2) - &(n + 2) * rat_J n)) (real_interval[&0,&1])`
  MP_TAC THENL
   [MATCH_MP_TAC HAS_REAL_INTEGRAL_SUB THEN CONJ_TAC THEN
    MATCH_MP_TAC HAS_REAL_INTEGRAL_LMUL THEN REWRITE_TAC[rat_J] THEN
    MATCH_MP_TAC RAT_HRI THEN REWRITE_TAC[RAT_J_INT];
    ALL_TAC] THEN
  REWRITE_TAC[ARITH_RULE `(n + 2) + 1 = n + 3`] THEN
  REWRITE_TAC[real_div; REAL_MUL_ASSOC; GSYM REAL_SUB_RDISTRIB] THEN
  REWRITE_TAC[IMP_IMP] THEN
  DISCH_THEN(MP_TAC o MATCH_MP HAS_REAL_INTEGRAL_UNIQUE) THEN
  REAL_ARITH_TAC);;
let RAT_J_0 = prove
 (`rat_J 0 = &1`,
  REWRITE_TAC[rat_J; ADD_CLAUSES; REAL_POW_1] THEN
  MATCH_MP_TAC REAL_INTEGRAL_UNIQUE THEN REWRITE_TAC[RAT_J0]);;

let RAT_J_EVEN = prove
 (`forall l. rat_J (2 * l) = &1 / (&(2 * l + 1) * cat_c l)`,
  INDUCT_TAC THENL
   [REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; RAT_J_0; RAT_C_0] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV;
    ALL_TAC] THEN
  MP_TAC(SPEC `2 * l` RAT_J_REC) THEN
  REWRITE_TAC[ARITH_RULE `2 * SUC l = 2 * l + 2`; ADD1] THEN
  MP_TAC(SPEC `l:num` RAT_C_STEP) THEN MP_TAC(SPEC `l:num` RAT_C_POS) THEN
  MP_TAC(SPEC `l + 1` RAT_C_POS) THEN
  ASM_REWRITE_TAC[ARITH_RULE `2 * (l + 1) + 1 = 2 * l + 3`] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_ADD; GSYM REAL_OF_NUM_MUL] THEN
  MP_TAC(SPEC `l:num` REAL_POS) THEN
  CONV_TAC REAL_FIELD);;

let RAT_JF_POS = prove
 (`forall k t. t IN real_interval[&0,&1] ==> &0 <= t pow k / sqrt(&1 - t pow 2)`,
  REWRITE_TAC[IN_REAL_INTERVAL] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC REAL_LE_DIV THEN ASM_SIMP_TAC[REAL_POW_LE] THEN
  MATCH_MP_TAC RAT_SQRT_POS THEN ASM_REAL_ARITH_TAC);;

let RAT_J_POS = prove
 (`forall k. &0 <= rat_J k`,
  GEN_TAC THEN REWRITE_TAC[rat_J] THEN MATCH_MP_TAC REAL_INTEGRAL_POS THEN
  SIMP_TAC[RAT_J_INT; RAT_JF_POS]);;

let RAT_J_MONO = prove
 (`forall k. rat_J (k + 1) <= rat_J k`,
  GEN_TAC THEN REWRITE_TAC[rat_J] THEN MATCH_MP_TAC REAL_INTEGRAL_LE THEN
  REWRITE_TAC[RAT_J_INT] THEN X_GEN_TAC `t:real` THEN
  REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
  REWRITE_TAC[real_div] THEN MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_POW_MONO_INV THEN ASM_REWRITE_TAC[] THEN ARITH_TAC;
    MATCH_MP_TAC REAL_LE_INV THEN MATCH_MP_TAC RAT_SQRT_POS THEN
    ASM_REAL_ARITH_TAC]);;
let RAT_MK_HALF = prove
 (`forall k. ((\t. abs t / sqrt(&1 - t pow 2) * t pow k) has_real_integral rat_J k)
       (real_interval[&0,&1])`,
  GEN_TAC THEN MATCH_MP_TAC HAS_REAL_INTEGRAL_EQ THEN
  EXISTS_TAC `\t. t pow (k + 1) / sqrt(&1 - t pow 2)` THEN
  SIMP_TAC[rat_J; RAT_HRI; RAT_J_INT] THEN
  REWRITE_TAC[IN_REAL_INTERVAL] THEN REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 <= x ==> abs x = x`] THEN
  REWRITE_TAC[RAT_POW_SPLIT] THEN REAL_ARITH_TAC);;

let RAT_MK = prove
 (`forall k. ((\t. abs t / sqrt(&1 - t pow 2) * t pow k) has_real_integral cat_m k)
       (real_interval[--(&1),&1])`,
  GEN_TAC THEN
  SUBGOAL_THEN `((\t. abs t / sqrt(&1 - t pow 2) * t pow k) has_real_integral
                 (--(&1) pow k * rat_J k)) (real_interval[--(&1),&0])`
  ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[GSYM HAS_REAL_INTEGRAL_REFLECT] THEN
    REWRITE_TAC[REAL_NEG_0; REAL_NEG_NEG] THEN
    MATCH_MP_TAC HAS_REAL_INTEGRAL_EQ THEN
    EXISTS_TAC `\t. --(&1) pow k * (abs t / sqrt(&1 - t pow 2) * t pow k)` THEN
    SIMP_TAC[HAS_REAL_INTEGRAL_LMUL; RAT_MK_HALF] THEN
    REWRITE_TAC[REAL_ABS_NEG; REAL_POW_NEG; REAL_POW_ONE] THEN
    REWRITE_TAC[ARITH_RULE `EVEN 2`] THEN
    REPEAT STRIP_TAC THEN COND_CASES_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\t. abs t / sqrt(&1 - t pow 2) * t pow k`;
    `--(&1) pow k * rat_J k`; `rat_J k`; `--(&1)`; `&1`; `&0`]
    HAS_REAL_INTEGRAL_COMBINE) THEN
  ASM_REWRITE_TAC[RAT_MK_HALF] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  MATCH_MP_TAC(MESON[] `a = b ==> ((f has_real_integral a) s ==> (f has_real_integral b) s)`) THEN
  REWRITE_TAC[cat_m; REAL_POW_NEG; REAL_POW_ONE] THEN
  COND_CASES_TAC THEN REWRITE_TAC[REAL_ARITH `--(&1) * x + x = &0`] THEN
  FIRST_X_ASSUM(CHOOSE_THEN SUBST1_TAC o REWRITE_RULE[EVEN_EXISTS]) THEN
  REWRITE_TAC[RAT_J_EVEN; ARITH_RULE `(2 * m) DIV 2 = m`] THEN
  MP_TAC(SPEC `m:num` RAT_C_POS) THEN MP_TAC(SPEC `m:num` REAL_POS) THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_ADD; GSYM REAL_OF_NUM_MUL] THEN
  CONV_TAC REAL_FIELD);;
let RAT_POW_INTEGRAL = prove
 (`forall n. ((\s. s pow n) has_real_integral (&1 / &(n + 1))) (real_interval[&0,&1])`,
  GEN_TAC THEN
  MP_TAC(ISPECL [`\s. s pow (n + 1) / &(n + 1)`; `\s:real. s pow n`; `&0`; `&1`]
    REAL_FUNDAMENTAL_THEOREM_OF_CALCULUS) THEN
  REWRITE_TAC[REAL_POS] THEN ANTS_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC HAS_REAL_DERIVATIVE_ATREAL_WITHIN THEN
    REAL_DIFF_TAC THEN REWRITE_TAC[ADD_SUB] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN
    MP_TAC(SPEC `n:num` REAL_POS) THEN CONV_TAC REAL_FIELD;
    REWRITE_TAC[REAL_POW_ONE; REAL_POW_ZERO; ADD_EQ_0; ARITH_EQ] THEN
    REWRITE_TAC[REAL_ARITH `x / y - &0 / y = x / y`]]);;

let RAT_DEN_POS = prove
 (`forall t s. abs t < &1 /\ s IN real_interval[&0,&1] ==> &0 < &1 - t * s`,
  REWRITE_TAC[IN_REAL_INTERVAL] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(REAL_ARITH `abs(t * s) < &1 ==> &0 < &1 - t * s`) THEN
  REWRITE_TAC[REAL_ABS_MUL] THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `abs t * &1` THEN
  CONJ_TAC THENL [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
                  ASM_REAL_ARITH_TAC]);;

let RAT_CONT_DEN = prove
 (`forall t p. abs t < &1 /\ p real_continuous_on real_interval[&0,&1]
         ==> (\s. p s / (&1 - t * s)) real_continuous_on real_interval[&0,&1]`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_CONTINUOUS_ON_DIV THEN
  ASM_SIMP_TAC[REAL_CONTINUOUS_ON_SUB; REAL_CONTINUOUS_ON_CONST;
               REAL_CONTINUOUS_ON_LMUL; REAL_CONTINUOUS_ON_ID] THEN
  ASM_MESON_TAC[RAT_DEN_POS; REAL_LT_IMP_NZ]);;

let RAT_G_INT = prove
 (`forall j t. abs t < &1
         ==> (\s. s pow j / (&1 - t * s)) real_integrable_on real_interval[&0,&1]`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_INTEGRABLE_CONTINUOUS THEN
  MATCH_MP_TAC(REWRITE_RULE[] (ISPECL [`t:real`; `\s:real. s pow j`] RAT_CONT_DEN)) THEN
  ASM_SIMP_TAC[REAL_CONTINUOUS_ON_POW; REAL_CONTINUOUS_ON_ID]);;

let RAT_GEOM = prove
 (`forall j t s n. abs t < &1 /\ s IN real_interval[&0,&1]
             ==> s pow j / (&1 - t * s) =
                 sum(0..n) (\u. t pow u * s pow (j + u)) +
                 t pow (n + 1) * s pow (j + n + 1) / (&1 - t * s)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`t * s:real`; `n:num`] SUM_GP_BASIC) THEN
  SUBGOAL_THEN `&0 < &1 - t * s` MP_TAC THENL [ASM_MESON_TAC[RAT_DEN_POS]; ALL_TAC] THEN
  SUBGOAL_THEN `sum(0..n) (\u. t pow u * s pow (j + u)) =
                s pow j * sum(0..n) (\u. (t * s) pow u)` SUBST1_TAC THENL
   [REWRITE_TAC[GSYM SUM_LMUL; REAL_POW_MUL; REAL_POW_ADD] THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[ADD1; GSYM ADD_ASSOC] THEN
  SPEC_TAC(`sum(0..n) (\u. (t * s) pow u)`,`q:real`) THEN
  REWRITE_TAC[REAL_POW_MUL; REAL_POW_ADD] THEN CONV_TAC REAL_FIELD);;
let RAT_POWMUL_INTEGRAL = prove
 (`forall c n. real_integral (real_interval[&0,&1]) (\s. c * s pow n) = c / &(n + 1)`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC REAL_INTEGRAL_UNIQUE THEN
  REWRITE_TAC[real_div] THEN
  ONCE_REWRITE_TAC[REAL_ARITH `c * inv x = c * (&1 / x)`] THEN
  MATCH_MP_TAC HAS_REAL_INTEGRAL_LMUL THEN REWRITE_TAC[RAT_POW_INTEGRAL]);;

let RAT_REM_CONT = prove
 (`forall j t n. abs t < &1
     ==> (\s. t pow (n + 1) * s pow (j + n + 1) / (&1 - t * s))
         real_continuous_on real_interval[&0,&1]`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`t:real`; `\s:real. t pow (n + 1) * s pow (j + n + 1)`]
    RAT_CONT_DEN) THEN
  ASM_SIMP_TAC[REAL_CONTINUOUS_ON_POW; REAL_CONTINUOUS_ON_ID;
               REAL_CONTINUOUS_ON_LMUL; real_div; REAL_MUL_ASSOC]);;

let RAT_G_DECOMP = prove
 (`forall j t n. abs t < &1
     ==> rat_g j t = sum(0..n) (\u. t pow u / &(j + u + 1)) +
           real_integral (real_interval[&0,&1])
             (\s. t pow (n + 1) * s pow (j + n + 1) / (&1 - t * s))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[rat_g] THEN
  TRANS_TAC EQ_TRANS
   `real_integral (real_interval[&0,&1])
      (\s. sum(0..n) (\u. t pow u * s pow (j + u)) +
           t pow (n + 1) * s pow (j + n + 1) / (&1 - t * s))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_INTEGRAL_EQ THEN REPEAT STRIP_TAC THEN
    REWRITE_TAC[] THEN MATCH_MP_TAC RAT_GEOM THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) REAL_INTEGRAL_ADD o lhand o snd) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_INTEGRABLE_SUM THEN REWRITE_TAC[FINITE_NUMSEG] THEN
      REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_INTEGRABLE_CONTINUOUS THEN
      SIMP_TAC[REAL_CONTINUOUS_ON_POW; REAL_CONTINUOUS_ON_ID;
               REAL_CONTINUOUS_ON_LMUL];
      MATCH_MP_TAC REAL_INTEGRABLE_CONTINUOUS THEN ASM_SIMP_TAC[RAT_REM_CONT]];
    DISCH_THEN SUBST1_TAC] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  W(MP_TAC o PART_MATCH (lhand o rand) REAL_INTEGRAL_SUM o lhand o snd) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[FINITE_NUMSEG] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_INTEGRABLE_CONTINUOUS THEN
    SIMP_TAC[REAL_CONTINUOUS_ON_POW; REAL_CONTINUOUS_ON_ID;
             REAL_CONTINUOUS_ON_LMUL];
    DISCH_THEN SUBST1_TAC] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN
  REWRITE_TAC[RAT_POWMUL_INTEGRAL; ADD_ASSOC]);;

let RAT_DIV_BOUND = prove
 (`forall x y c d. &0 <= x /\ x <= y /\ &0 < d /\ d <= c ==> x / c <= y / d:real`,
  REPEAT STRIP_TAC THEN TRANS_TAC REAL_LE_TRANS `(y:real) / c` THEN
  SUBGOAL_THEN `&0 < c:real` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_DIV2_EQ] THEN REWRITE_TAC[real_div] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REWRITE_TAC[]);;

let RAT_REM_PT = prove
 (`forall t s n m. abs t < &1 /\ &0 <= s /\ s <= &1
     ==> abs(t pow n * s pow m / (&1 - t * s)) <= abs t pow n / (&1 - abs t)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < &1 - t * s` ASSUME_TAC THENL
   [MATCH_MP_TAC RAT_DEN_POS THEN ASM_REWRITE_TAC[IN_REAL_INTERVAL]; ALL_TAC] THEN
  SUBGOAL_THEN `abs(t pow n * s pow m / (&1 - t * s)) =
                (abs t pow n * s pow m) / (&1 - t * s)` SUBST1_TAC THENL
   [REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_DIV; REAL_ABS_POW] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < x ==> abs x = x`;
                 REAL_ARITH `&0 <= x ==> abs x = x`] THEN
    REWRITE_TAC[real_div; REAL_MUL_ASSOC]; ALL_TAC] THEN
  MATCH_MP_TAC RAT_DIV_BOUND THEN
  ASM_SIMP_TAC[REAL_POW_LE; REAL_LE_MUL; REAL_ABS_POS] THEN
  REPEAT CONJ_TAC THENL
   [ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN MATCH_MP_TAC RAT_LE_MUL1 THEN
    ASM_SIMP_TAC[REAL_POW_LE; REAL_ABS_POS] THEN
    MATCH_MP_TAC REAL_POW_1_LE THEN ASM_REWRITE_TAC[];
    ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC(REAL_ARITH `abs(t * s) <= abs t ==> &1 - abs t <= &1 - t * s`) THEN
    REWRITE_TAC[REAL_ABS_MUL] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 <= x ==> abs x = x`] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= a * (&1 - s) ==> a * s <= a`) THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC]);;

let RAT_REM_BOUND = prove
 (`forall j t n. abs t < &1
     ==> abs(real_integral (real_interval[&0,&1])
               (\s. t pow (n + 1) * s pow (j + n + 1) / (&1 - t * s)))
         <= abs t pow (n + 1) / (&1 - abs t)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\s. t pow (n + 1) * s pow (j + n + 1) / (&1 - t * s)`;
                 `\s:real. abs t pow (n + 1) / (&1 - abs t)`;
                 `real_interval[&0,&1]`] REAL_INTEGRAL_ABS_BOUND_INTEGRAL) THEN
  SIMP_TAC[REAL_INTEGRAL_CONST; REAL_POS; REAL_INTEGRABLE_CONST] THEN
  REWRITE_TAC[REAL_SUB_RZERO; REAL_MUL_RID] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_SIMP_TAC[REAL_INTEGRABLE_CONTINUOUS; RAT_REM_CONT; RAT_REM_PT;
               IN_REAL_INTERVAL]);;

let RAT_G_SUMS = prove
 (`forall j t. abs t < &1
         ==> ((\u. t pow u / &(j + u + 1)) real_sums rat_g j t) (from 0)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[real_sums; FROM_INTER_NUMSEG] THEN
  ONCE_REWRITE_TAC[REALLIM_NULL] THEN
  MATCH_MP_TAC REALLIM_NULL_COMPARISON THEN
  EXISTS_TAC `\n. abs t pow (n + 1) / (&1 - abs t)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC ALWAYS_EVENTUALLY THEN X_GEN_TAC `n:num` THEN
    REWRITE_TAC[] THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP RAT_G_DECOMP
       (SPEC `n:num` (GENL [`n:num`] th))]) THEN
    ASM_SIMP_TAC[REAL_ARITH `abs(a - (a + b)) = abs b`; RAT_REM_BOUND];
    REWRITE_TAC[REAL_POW_ADD; REAL_POW_1; real_div] THEN
    ONCE_REWRITE_TAC[REAL_ARITH `(a * b) * c = (b * c) * a:real`] THEN
    MATCH_MP_TAC REALLIM_NULL_LMUL THEN MATCH_MP_TAC REALLIM_POWN THEN
    ASM_REWRITE_TAC[REAL_ABS_ABS]]);;

let RAT_G_LOWER = prove
 (`forall x n. &0 <= x /\ x < &1
         ==> sum(0..n) (\u. x pow u / &(u + 1)) <= rat_g 0 x`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `abs x < &1` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP RAT_G_DECOMP th]) THEN
  REWRITE_TAC[ADD_CLAUSES; REAL_LE_ADDR] THEN
  MATCH_MP_TAC REAL_INTEGRAL_POS THEN
  ASM_SIMP_TAC[REAL_INTEGRABLE_CONTINUOUS; REWRITE_RULE[ADD_CLAUSES]
     (SPEC `0` RAT_REM_CONT)] THEN
  X_GEN_TAC `s:real` THEN DISCH_TAC THEN
  MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_POW_LE] THEN
  MATCH_MP_TAC REAL_LE_DIV THEN
  FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[IN_REAL_INTERVAL]) THEN
  STRIP_TAC THEN ASM_SIMP_TAC[REAL_POW_LE] THEN
  MATCH_MP_TAC REAL_LT_IMP_LE THEN MATCH_MP_TAC RAT_DEN_POS THEN
  ASM_REWRITE_TAC[IN_REAL_INTERVAL]);;
let RAT_JSUM_STEP = prove
 (`forall k. rat_J (k + 2) / &(k + 3) + rat_J (k + 2) <= rat_J k`,
  GEN_TAC THEN MP_TAC(SPEC `k:num` RAT_J_REC) THEN
  MP_TAC(SPEC `k + 2` RAT_J_POS) THEN
  SPEC_TAC(`rat_J k`,`a:real`) THEN SPEC_TAC(`rat_J (k + 2)`,`b:real`) THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `a - b = b / &(k + 2)` ASSUME_TAC THENL
   [MP_TAC(SPEC `k:num` REAL_POS) THEN POP_ASSUM MP_TAC THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `x <= a - b ==> x + b <= a`) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC RAT_DIV_BOUND THEN
  ASM_REWRITE_TAC[REAL_LE_REFL; REAL_OF_NUM_LT; REAL_OF_NUM_LE] THEN ARITH_TAC);;

let RAT_JSUM_BOUND = prove
 (`forall k. &0 <= sum(0..k) (\u. rat_J u / &(u + 1)) /\
       sum(0..k) (\u. rat_J u / &(u + 1)) <= &4`,
  SUBGOAL_THEN `forall k. sum(0..k+1) (\u. rat_J u / &(u + 1)) + rat_J k + rat_J (k + 1)
                    <= &4` ASSUME_TAC THENL
   [INDUCT_TAC THENL
     [REWRITE_TAC[num_CONV `1`; SUM_CLAUSES_NUMSEG; ADD_CLAUSES; LE_0] THEN
      REWRITE_TAC[GSYM(num_CONV `1`); RAT_J_0] THEN
      MP_TAC(SPEC `0` RAT_J_MONO) THEN MP_TAC(SPEC `1` RAT_J_POS) THEN
      REWRITE_TAC[ADD_CLAUSES; RAT_J_0] THEN CONV_TAC NUM_REDUCE_CONV THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[ARITH_RULE `SUC k + 1 = SUC(k + 1)`; SUM_CLAUSES_NUMSEG; LE_0] THEN
    REWRITE_TAC[ARITH_RULE `SUC(k + 1) = k + 2 /\ SUC k = k + 1 /\
                            (k + 2) + 1 = k + 3 /\ (k + 1) + 2 = k + 3`] THEN
    MP_TAC(SPEC `k:num` RAT_JSUM_STEP) THEN POP_ASSUM MP_TAC THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  GEN_TAC THEN CONJ_TAC THENL
   [MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN REPEAT STRIP_TAC THEN
    REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_DIV THEN
    REWRITE_TAC[RAT_J_POS; REAL_POS];
    ALL_TAC] THEN
  STRUCT_CASES_TAC(SPEC `k:num` num_CASES) THENL
   [REWRITE_TAC[SUM_SING_NUMSEG; RAT_J_0; ADD_CLAUSES] THEN REAL_ARITH_TAC;
    FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN REWRITE_TAC[ADD1] THEN
    MP_TAC(SPEC `n:num` RAT_J_POS) THEN MP_TAC(SPEC `n + 1` RAT_J_POS) THEN
    REAL_ARITH_TAC]);;
let RAT_SQRT1 = prove
 (`sqrt(&1 - &1 pow 2) = &0`,
  REWRITE_TAC[REAL_POW_ONE; REAL_SUB_REFL; SQRT_0]);;

let RAT_DOM_INT = prove
 (`(\t. t / sqrt(&1 - t pow 2) * rat_g 0 t) real_integrable_on
   real_interval[&0,&1]`,
  MP_TAC(ISPECL
   [`\k t. sum(0..k) (\u. inv(&(u + 1)) * (t pow (u + 1) / sqrt(&1 - t pow 2)))`;
    `\t. t / sqrt(&1 - t pow 2) * rat_g 0 t`; `real_interval[&0,&1]`]
   REAL_MONOTONE_CONVERGENCE_INCREASING) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
  REPEAT CONJ_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC REAL_INTEGRABLE_SUM THEN
    REWRITE_TAC[FINITE_NUMSEG] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC REAL_INTEGRABLE_LMUL THEN REWRITE_TAC[RAT_J_INT];
    REPEAT STRIP_TAC THEN REWRITE_TAC[SUM_CLAUSES_NUMSEG; LE_0] THEN
    REWRITE_TAC[REAL_LE_ADDR] THEN MATCH_MP_TAC REAL_LE_MUL THEN
    ASM_SIMP_TAC[RAT_JF_POS; REAL_LE_INV_EQ; REAL_POS];
    X_GEN_TAC `t:real` THEN DISCH_TAC THEN
    ASM_CASES_TAC `t = &1` THENL
     [ASM_REWRITE_TAC[RAT_SQRT1; real_div; REAL_INV_0; REAL_MUL_RZERO;
                      REAL_MUL_LZERO; SUM_0; REALLIM_CONST];
      ALL_TAC] THEN
    SUBGOAL_THEN `abs t < &1` ASSUME_TAC THENL
     [POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN
      REWRITE_TAC[IN_REAL_INTERVAL] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN
     `forall k. sum(0..k) (\u. inv(&(u + 1)) * (t pow (u + 1) / sqrt(&1 - t pow 2))) =
          t / sqrt(&1 - t pow 2) * sum(0..k) (\u. t pow u / &(0 + u + 1))`
     (fun th -> REWRITE_TAC[th]) THENL
     [GEN_TAC THEN REWRITE_TAC[GSYM SUM_LMUL] THEN
      MATCH_MP_TAC SUM_EQ_NUMSEG THEN REPEAT STRIP_TAC THEN
      REWRITE_TAC[ADD_CLAUSES; REAL_POW_ADD; REAL_POW_1; real_div] THEN
      REWRITE_TAC[GSYM ADD1; real_pow] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC REALLIM_LMUL THEN
    FIRST_ASSUM(MP_TAC o SPEC `0` o MATCH_MP (ONCE_REWRITE_RULE[IMP_CONJ_ALT]
      (REWRITE_RULE[IMP_CONJ] RAT_G_SUMS))) THEN
    REWRITE_TAC[real_sums; FROM_INTER_NUMSEG];
    REWRITE_TAC[real_bounded; FORALL_IN_GSPEC; IN_UNIV] THEN
    EXISTS_TAC `&4` THEN GEN_TAC THEN
    W(MP_TAC o PART_MATCH (lhand o rand) REAL_INTEGRAL_SUM o rand o lhand o snd) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[FINITE_NUMSEG] THEN REPEAT STRIP_TAC THEN
      MATCH_MP_TAC REAL_INTEGRABLE_LMUL THEN REWRITE_TAC[RAT_J_INT];
      DISCH_THEN SUBST1_TAC] THEN
    SIMP_TAC[REAL_INTEGRAL_LMUL; RAT_J_INT; GSYM rat_J] THEN
    MP_TAC(SPEC `k:num` RAT_JSUM_BOUND) THEN
    REWRITE_TAC[real_div; REAL_MUL_SYM] THEN REAL_ARITH_TAC]);;
let RAT_DOM2_INT = prove
 (`(\t. abs t / sqrt(&1 - t pow 2) * rat_g 0 (abs t)) real_integrable_on
   real_interval[--(&1),&1]`,
  MATCH_MP_TAC REAL_INTEGRABLE_COMBINE THEN EXISTS_TAC `&0` THEN
  REWRITE_TAC[REAL_ARITH `--(&1) <= &0 /\ &0 <= &1`] THEN
  SUBGOAL_THEN `(\t. abs t / sqrt(&1 - t pow 2) * rat_g 0 (abs t))
                real_integrable_on real_interval[&0,&1]` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_INTEGRABLE_EQ THEN
    EXISTS_TAC `\t. t / sqrt(&1 - t pow 2) * rat_g 0 t` THEN
    REWRITE_TAC[RAT_DOM_INT; IN_REAL_INTERVAL] THEN
    SIMP_TAC[REAL_ARITH `&0 <= t ==> abs t = t`];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  ONCE_REWRITE_TAC[GSYM REAL_INTEGRABLE_REFLECT] THEN
  REWRITE_TAC[REAL_NEG_0; REAL_NEG_NEG; REAL_ABS_NEG; REAL_POW_NEG] THEN
  ASM_REWRITE_TAC[ARITH_RULE `EVEN 2`]);;

let RAT_ABS1_CASES = prove
 (`forall t. t IN real_interval[--(&1),&1] ==> abs t < &1 \/ t = &1 \/ t = --(&1)`,
  REWRITE_TAC[IN_REAL_INTERVAL] THEN REAL_ARITH_TAC);;

let RAT_SQRT1N = prove
 (`sqrt(&1 - (--(&1)) pow 2) = &0`,
  REWRITE_TAC[REAL_POW_NEG; ARITH_RULE `EVEN 2`; RAT_SQRT1]);;

let RAT_PARTIAL_BOUND = prove
 (`forall i j t k. abs t < &1
     ==> abs(sum(0..k) (\u. t pow (i + u) / &(j + u + 1)))
         <= rat_g 0 (abs t)`,
  REPEAT STRIP_TAC THEN TRANS_TAC REAL_LE_TRANS
   `sum(0..k) (\u. abs t pow u / &(u + 1))` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC RAT_G_LOWER THEN ASM_REWRITE_TAC[REAL_ABS_POS]] THEN
  MATCH_MP_TAC SUM_ABS_LE THEN REWRITE_TAC[FINITE_NUMSEG] THEN
  X_GEN_TAC `u:num` THEN DISCH_TAC THEN REWRITE_TAC[REAL_ABS_DIV; REAL_ABS_NUM] THEN
  MATCH_MP_TAC RAT_DIV_BOUND THEN
  REWRITE_TAC[REAL_ABS_POS; REAL_OF_NUM_LT; REAL_OF_NUM_LE] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[REAL_POW_ADD; REAL_ABS_MUL; REAL_ABS_POW] THEN
    MATCH_MP_TAC RAT_LE_MUL1 THEN SIMP_TAC[REAL_POW_LE; REAL_ABS_POS] THEN
    MATCH_MP_TAC REAL_POW_1_LE THEN ASM_SIMP_TAC[REAL_ABS_POS; REAL_LT_IMP_LE];
    ARITH_TAC; ARITH_TAC]);;

let RAT_MIX_SERIES = prove
 (`forall i j. (\t. abs t / sqrt(&1 - t pow 2) * t pow i * rat_g j t)
           real_integrable_on real_interval[--(&1),&1] /\
         ((\u. cat_m (i + u) / &(j + u + 1)) real_sums
          real_integral (real_interval[--(&1),&1])
            (\t. abs t / sqrt(&1 - t pow 2) * t pow i * rat_g j t)) (from 0)`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL
   [`\k t. sum(0..k) (\u. inv(&(j + u + 1)) *
                         (abs t / sqrt(&1 - t pow 2) * t pow (i + u)))`;
    `\t. abs t / sqrt(&1 - t pow 2) * t pow i * rat_g j t`;
    `\t. abs t / sqrt(&1 - t pow 2) * rat_g 0 (abs t)`;
    `real_interval[--(&1),&1]`]
   REAL_DOMINATED_CONVERGENCE) THEN
  REWRITE_TAC[RAT_DOM2_INT] THEN
  SUBGOAL_THEN
   `forall k. ((\t. sum(0..k) (\u. inv(&(j + u + 1)) *
                         (abs t / sqrt(&1 - t pow 2) * t pow (i + u))))
         has_real_integral (sum(0..k) (\u. cat_m (i + u) / &(j + u + 1))))
        (real_interval[--(&1),&1])`
  ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC HAS_REAL_INTEGRAL_SUM THEN
    REWRITE_TAC[FINITE_NUMSEG] THEN X_GEN_TAC `u:num` THEN DISCH_TAC THEN
    REWRITE_TAC[] THEN
    SUBGOAL_THEN `cat_m (i + u) / &(j + u + 1) = inv(&(j + u + 1)) * cat_m (i + u)`
    SUBST1_TAC THENL [REWRITE_TAC[real_div] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC HAS_REAL_INTEGRAL_LMUL THEN REWRITE_TAC[RAT_MK];
    ALL_TAC] THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[real_integrable_on];
      MAP_EVERY X_GEN_TAC [`k:num`; `t:real`] THEN
      DISCH_THEN(DISJ_CASES_TAC o MATCH_MP RAT_ABS1_CASES) THENL
       [ALL_TAC;
        FIRST_X_ASSUM(DISJ_CASES_THEN SUBST1_TAC) THEN
        REWRITE_TAC[RAT_SQRT1; RAT_SQRT1N; real_div; REAL_INV_0;
          REAL_MUL_RZERO; REAL_MUL_LZERO; SUM_0; REAL_ABS_0; REAL_LE_REFL]] THEN
      REWRITE_TAC[GSYM SUM_LMUL] THEN
      SUBGOAL_THEN
       `sum(0..k) (\u. inv(&(j + u + 1)) *
                        (abs t / sqrt(&1 - t pow 2) * t pow (i + u))) =
        abs t / sqrt(&1 - t pow 2) * sum(0..k) (\u. t pow (i + u) / &(j + u + 1))`
      SUBST1_TAC THENL
       [REWRITE_TAC[GSYM SUM_LMUL] THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN
        REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN REAL_ARITH_TAC;
        ALL_TAC] THEN
      REWRITE_TAC[REAL_ABS_MUL] THEN
      SUBGOAL_THEN `abs(abs t / sqrt(&1 - t pow 2)) = abs t / sqrt(&1 - t pow 2)`
      SUBST1_TAC THENL
       [REWRITE_TAC[REAL_ABS_REFL] THEN MATCH_MP_TAC REAL_LE_DIV THEN
        ASM_SIMP_TAC[REAL_ABS_POS; RAT_SQRT_POS; REAL_LT_IMP_LE]; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN
      ASM_SIMP_TAC[RAT_PARTIAL_BOUND] THEN MATCH_MP_TAC REAL_LE_DIV THEN
      ASM_SIMP_TAC[REAL_ABS_POS; RAT_SQRT_POS; REAL_LT_IMP_LE];
      X_GEN_TAC `t:real` THEN
      DISCH_THEN(DISJ_CASES_TAC o MATCH_MP RAT_ABS1_CASES) THENL
       [ALL_TAC;
        FIRST_X_ASSUM(DISJ_CASES_THEN SUBST1_TAC) THEN
        REWRITE_TAC[RAT_SQRT1; RAT_SQRT1N; real_div; REAL_INV_0;
          REAL_MUL_RZERO; REAL_MUL_LZERO; SUM_0; REALLIM_CONST]] THEN
      SUBGOAL_THEN
       `forall k. sum(0..k) (\u. inv(&(j + u + 1)) *
                        (abs t / sqrt(&1 - t pow 2) * t pow (i + u))) =
        (abs t / sqrt(&1 - t pow 2) * t pow i) *
        sum(0..k) (\u. t pow u / &(j + u + 1))`
      (fun th -> REWRITE_TAC[th]) THENL
       [GEN_TAC THEN REWRITE_TAC[GSYM SUM_LMUL] THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN
        REPEAT STRIP_TAC THEN REWRITE_TAC[REAL_POW_ADD] THEN REAL_ARITH_TAC;
        ALL_TAC] THEN
      REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REALLIM_LMUL THEN
      FIRST_ASSUM(MP_TAC o SPEC `j:num` o MATCH_MP (ONCE_REWRITE_RULE[IMP_CONJ_ALT]
        (REWRITE_RULE[IMP_CONJ] RAT_G_SUMS))) THEN
      REWRITE_TAC[real_sums; FROM_INTER_NUMSEG]];
    ALL_TAC] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[real_sums; FROM_INTER_NUMSEG] THEN
  FIRST_X_ASSUM(MP_TAC o check (is_comb o rator o concl)) THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN
  MATCH_MP_TAC REAL_INTEGRAL_UNIQUE THEN ASM_REWRITE_TAC[]);;
let RAT_INVSQ_BOUND = prove
 (`forall k. sum(0..k) (\u. &1 / &(u + 1) pow 2) <= &2 - &1 / &(k + 1)`,
  INDUCT_TAC THENL
   [REWRITE_TAC[SUM_SING_NUMSEG; ADD_CLAUSES] THEN CONV_TAC REAL_RAT_REDUCE_CONV; ALL_TAC] THEN
  REWRITE_TAC[SUM_CLAUSES_NUMSEG; LE_0] THEN POP_ASSUM MP_TAC THEN
  MATCH_MP_TAC(REAL_ARITH `a / x <= b - c ==> s <= &2 - b ==> s + a / x <= &2 - c`) THEN
  REWRITE_TAC[ADD1; GSYM REAL_OF_NUM_ADD] THEN
  MP_TAC(SPEC `k:num` REAL_POS) THEN SPEC_TAC(`&k`,`x:real`) THEN
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `&1 / (x + &1) - &1 / ((x + &1) + &1) = &1 / ((x + &1) * (x + &2))`
  SUBST1_TAC THENL [POP_ASSUM MP_TAC THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  REWRITE_TAC[REAL_POW_2] THEN MATCH_MP_TAC RAT_DIV_BOUND THEN
  REPEAT CONJ_TAC THEN TRY REAL_ARITH_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REAL_ARITH_TAC]);;

let RAT_ZETA_SERIES = prove
 (`forall i j. (\t. t pow i * rat_g j t) real_integrable_on real_interval[&0,&1] /\
         ((\u. &1 / (&(i + u + 1) * &(j + u + 1))) real_sums
          real_integral (real_interval[&0,&1]) (\t. t pow i * rat_g j t)) (from 0)`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL
   [`\k t. if t = &1 then &0 else
           sum(0..k) (\u. inv(&(j + u + 1)) * t pow (i + u))`;
    `\t. if t = &1 then &0 else t pow i * rat_g j t`;
    `real_interval[&0,&1]`]
   REAL_MONOTONE_CONVERGENCE_INCREASING) THEN
  SUBGOAL_THEN
   `forall k. ((\t. if t = &1 then &0 else
              sum(0..k) (\u. inv(&(j + u + 1)) * t pow (i + u)))
         has_real_integral (sum(0..k) (\u. &1 / (&(i + u + 1) * &(j + u + 1)))))
        (real_interval[&0,&1])`
  ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC HAS_REAL_INTEGRAL_SPIKE THEN
    MAP_EVERY EXISTS_TAC
     [`\t. sum(0..k) (\u. inv(&(j + u + 1)) * t pow (i + u))`; `{&1}`] THEN
    SIMP_TAC[REAL_NEGLIGIBLE_SING; IN_DIFF; IN_SING] THEN
    MATCH_MP_TAC HAS_REAL_INTEGRAL_SUM THEN
    REWRITE_TAC[FINITE_NUMSEG] THEN X_GEN_TAC `u:num` THEN DISCH_TAC THEN
    REWRITE_TAC[] THEN
    SUBGOAL_THEN `&1 / (&(i + u + 1) * &(j + u + 1)) =
                  inv(&(j + u + 1)) * (&1 / &((i + u) + 1))` SUBST1_TAC THENL
     [REWRITE_TAC[ADD_ASSOC; real_div; REAL_INV_MUL] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC HAS_REAL_INTEGRAL_LMUL THEN REWRITE_TAC[RAT_POW_INTEGRAL];
    ALL_TAC] THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[real_integrable_on];
      MAP_EVERY X_GEN_TAC [`k:num`; `t:real`] THEN
      REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
      COND_CASES_TAC THEN REWRITE_TAC[REAL_LE_REFL] THEN
      REWRITE_TAC[SUM_CLAUSES_NUMSEG; LE_0; REAL_LE_ADDR] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_POW_LE; REAL_LE_INV_EQ; REAL_POS];
      X_GEN_TAC `t:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
      COND_CASES_TAC THEN REWRITE_TAC[REALLIM_CONST] THEN
      SUBGOAL_THEN `abs t < &1` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN
       `forall k. sum(0..k) (\u. inv(&(j + u + 1)) * t pow (i + u)) =
            t pow i * sum(0..k) (\u. t pow u / &(j + u + 1))`
      (fun th -> REWRITE_TAC[th]) THENL
       [GEN_TAC THEN REWRITE_TAC[GSYM SUM_LMUL] THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN
        REPEAT STRIP_TAC THEN REWRITE_TAC[REAL_POW_ADD; real_div] THEN
        REAL_ARITH_TAC;
        ALL_TAC] THEN
      MATCH_MP_TAC REALLIM_LMUL THEN
      FIRST_ASSUM(MP_TAC o SPEC `j:num` o MATCH_MP (ONCE_REWRITE_RULE[IMP_CONJ_ALT]
        (REWRITE_RULE[IMP_CONJ] RAT_G_SUMS))) THEN
      REWRITE_TAC[real_sums; FROM_INTER_NUMSEG];
      REWRITE_TAC[real_bounded; FORALL_IN_GSPEC; IN_UNIV] THEN
      EXISTS_TAC `&2` THEN X_GEN_TAC `k:num` THEN
      FIRST_X_ASSUM(SUBST1_TAC o MATCH_MP REAL_INTEGRAL_UNIQUE o SPEC `k:num`) THEN
      MATCH_MP_TAC(REAL_ARITH `&0 <= x /\ x <= &2 ==> abs x <= &2`) THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN
        SIMP_TAC[REAL_LE_DIV; REAL_POS; REAL_LE_MUL];
        ALL_TAC] THEN
      TRANS_TAC REAL_LE_TRANS `sum(0..k) (\u. &1 / &(u + 1) pow 2)` THEN
      CONJ_TAC THENL
       [ALL_TAC;
        MP_TAC(SPEC `k:num` RAT_INVSQ_BOUND) THEN
        MP_TAC(SPECL [`&1`; `&(k + 1)`] REAL_LE_DIV) THEN
        REWRITE_TAC[REAL_POS] THEN REAL_ARITH_TAC] THEN
        MATCH_MP_TAC SUM_LE_NUMSEG THEN REPEAT STRIP_TAC THEN
        REWRITE_TAC[REAL_POW_2] THEN MATCH_MP_TAC RAT_DIV_BOUND THEN
        REWRITE_TAC[REAL_POS; REAL_LE_REFL] THEN
        SIMP_TAC[REAL_LT_MUL; REAL_OF_NUM_LT; ARITH_RULE `0 < u + 1`] THEN
        MATCH_MP_TAC REAL_LE_MUL2 THEN
        REWRITE_TAC[REAL_POS; REAL_OF_NUM_LE] THEN ARITH_TAC];
    ALL_TAC] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `forall h. real_integral (real_interval[&0,&1])
                      (\t. if t = &1 then &0 else h t) =
                    real_integral (real_interval[&0,&1]) h /\
                    ((\t. if t = &1 then &0 else h t) real_integrable_on
                       real_interval[&0,&1] <=> h real_integrable_on real_interval[&0,&1])`
  (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
   [GEN_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_INTEGRAL_SPIKE THEN EXISTS_TAC `{&1}`;
      MATCH_MP_TAC REAL_INTEGRABLE_SPIKE_EQ THEN EXISTS_TAC `{&1}`] THEN
    SIMP_TAC[REAL_NEGLIGIBLE_SING; IN_DIFF; IN_SING];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[real_sums; FROM_INTER_NUMSEG] THEN
  FIRST_X_ASSUM(MP_TAC o check (is_comb o rator o concl)) THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `k:num` THEN
  MATCH_MP_TAC REAL_INTEGRAL_UNIQUE THEN MATCH_MP_TAC HAS_REAL_INTEGRAL_SPIKE THEN
  MAP_EVERY EXISTS_TAC
   [`\t. if t = &1 then &0 else sum(0..k) (\u. inv(&(j + u + 1)) * t pow (i + u))`;
    `{&1}`] THEN
  ASM_SIMP_TAC[REAL_NEGLIGIBLE_SING; IN_DIFF; IN_SING]);;
let RAT_MIXED_INNER = prove
 (`forall i j t. t IN real_interval[--(&1),&1]
    ==> (\s. abs t / sqrt(&1 - t pow 2) * (t pow i * s pow j) / (&1 - t * s))
          real_integrable_on real_interval[&0,&1] /\
        real_integral (real_interval[&0,&1])
          (\s. abs t / sqrt(&1 - t pow 2) * (t pow i * s pow j) / (&1 - t * s)) =
        abs t / sqrt(&1 - t pow 2) * t pow i * rat_g j t`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(DISJ_CASES_TAC o MATCH_MP RAT_ABS1_CASES) THENL
   [ALL_TAC;
    FIRST_X_ASSUM(DISJ_CASES_THEN SUBST1_TAC) THEN
    REWRITE_TAC[RAT_SQRT1; RAT_SQRT1N; real_div; REAL_INV_0;
      REAL_MUL_RZERO; REAL_MUL_LZERO; REAL_INTEGRAL_0; REAL_INTEGRABLE_0]] THEN
  SUBGOAL_THEN
   `(\s. abs t / sqrt(&1 - t pow 2) * (t pow i * s pow j) / (&1 - t * s)) =
    (\s. (abs t / sqrt(&1 - t pow 2) * t pow i) * (s pow j / (&1 - t * s)))`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; real_div] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_INTEGRABLE_LMUL; REAL_INTEGRAL_LMUL; RAT_G_INT] THEN
  REWRITE_TAC[rat_g; REAL_MUL_ASSOC]);;

let RAT_ZETA_INNER = prove
 (`forall i j t. t IN real_interval[&0,&1] /\ ~(t = &1)
    ==> (\s. (t pow i * s pow j) / (&1 - t * s))
          real_integrable_on real_interval[&0,&1] /\
        real_integral (real_interval[&0,&1])
          (\s. (t pow i * s pow j) / (&1 - t * s)) = t pow i * rat_g j t`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
  SUBGOAL_THEN `abs t < &1` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `(\s. (t pow i * s pow j) / (&1 - t * s)) =
    (\s. t pow i * (s pow j / (&1 - t * s)))`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; real_div] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_INTEGRABLE_LMUL; REAL_INTEGRAL_LMUL; RAT_G_INT] THEN
  REWRITE_TAC[rat_g]);;

let RAT_M_INTEGRAL = prove
 (`forall i j. rat_M i j = real_integral (real_interval[--(&1),&1])
            (\t. abs t / sqrt(&1 - t pow 2) * t pow i * rat_g j t)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[rat_M; cat_mixed] THEN
  MATCH_MP_TAC REAL_INTEGRAL_EQ THEN SIMP_TAC[RAT_MIXED_INNER]);;

let RAT_Z_INTEGRAL = prove
 (`forall i j. rat_Z i j = real_integral (real_interval[&0,&1])
            (\t. t pow i * rat_g j t)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[rat_Z; cat_zeta] THEN
  MATCH_MP_TAC REAL_INTEGRAL_SPIKE THEN EXISTS_TAC `{&1}` THEN
  SIMP_TAC[REAL_NEGLIGIBLE_SING; IN_DIFF; IN_SING; RAT_ZETA_INNER]);;

let RAT_M_SUMS = prove
 (`forall i j. ((\u. cat_m (i + u) / &(j + u + 1)) real_sums rat_M i j) (from 0)`,
  REWRITE_TAC[RAT_M_INTEGRAL; RAT_MIX_SERIES]);;

let RAT_Z_SUMS = prove
 (`forall i j. ((\u. &1 / (&(i + u + 1) * &(j + u + 1))) real_sums rat_Z i j) (from 0)`,
  REWRITE_TAC[RAT_Z_INTEGRAL; RAT_ZETA_SERIES]);;
let RAT_SUMPROD = prove
 (`forall a d H p J w e x y.
     a * (sum(0..H) (\i. p i * x pow i) * sum(0..J) (\v. w v * y pow (e v))) / d =
     sum(0..H) (\i. sum(0..J) (\v. (p i * w v) * (a * (x pow i * y pow (e v)) / d)))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[real_div; GSYM SUM_LMUL; GSYM SUM_RMUL] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
  REAL_ARITH_TAC);;

let RAT_INT_DSUM = prove
 (`forall f:num->num->real->real s H J.
     (forall i v. i IN 0..H /\ v IN 0..J ==> f i v real_integrable_on s)
     ==> (\x. sum(0..H) (\i. sum(0..J) (\v. f i v x))) real_integrable_on s /\
         real_integral s (\x. sum(0..H) (\i. sum(0..J) (\v. f i v x))) =
         sum(0..H) (\i. sum(0..J) (\v. real_integral s (f i v)))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `forall i. i IN 0..H ==>
     (\x. sum(0..J) (\v. f i v x)) real_integrable_on s /\
     real_integral s (\x. sum(0..J) (\v. (f:num->num->real->real) i v x)) =
     sum(0..J) (\v. real_integral s (f i v))` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THENL
     [MATCH_MP_TAC REAL_INTEGRABLE_SUM;
      MATCH_MP_TAC REAL_INTEGRAL_SUM] THEN
    ASM_SIMP_TAC[FINITE_NUMSEG; ETA_AX];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_INTEGRABLE_SUM THEN ASM_SIMP_TAC[FINITE_NUMSEG];
    W(MP_TAC o PART_MATCH (lhand o rand) REAL_INTEGRAL_SUM o lhand o snd) THEN
    ASM_SIMP_TAC[FINITE_NUMSEG] THEN DISCH_THEN(K ALL_TAC) THEN
    MATCH_MP_TAC SUM_EQ THEN ASM_SIMP_TAC[]]);;

let RAT_MIXED_LIN = prove
 (`forall H p J w e.
     cat_mixed (\t. sum(0..H) (\i. p i * t pow i))
               (\s. sum(0..J) (\v. w v * s pow (e v))) =
     sum(0..H) (\i. sum(0..J) (\v. (p i * w v) * rat_M i (e v)))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[cat_mixed; RAT_SUMPROD] THEN
  TRANS_TAC EQ_TRANS
   `real_integral (real_interval[--(&1),&1])
     (\t. sum(0..H) (\i. sum(0..J) (\v. (\(i:num) (v:num) (t:real). (p i * w v) *
           (abs t / sqrt(&1 - t pow 2) * t pow i * rat_g (e v) t)) i v t)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_INTEGRAL_EQ THEN X_GEN_TAC `t:real` THEN DISCH_TAC THEN
    MP_TAC(ISPECL
     [`\(i:num) (v:num) (s:real). (p i * w v) *
         (abs t / sqrt(&1 - t pow 2) * (t pow i * s pow (e v)) / (&1 - t * s))`;
      `real_interval[&0,&1]`; `H:num`; `J:num`] RAT_INT_DSUM) THEN
    ASM_SIMP_TAC[REAL_INTEGRABLE_LMUL; REAL_INTEGRAL_LMUL; RAT_MIXED_INNER] THEN
    DISCH_THEN(K ALL_TAC) THEN REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL
     [`\(i:num) (v:num) (t:real). (p i * w v) *
         (abs t / sqrt(&1 - t pow 2) * t pow i * rat_g (e v) t)`;
      `real_interval[--(&1),&1]`; `H:num`; `J:num`] RAT_INT_DSUM) THEN
  SIMP_TAC[REAL_INTEGRABLE_LMUL; REAL_INTEGRAL_LMUL; RAT_MIX_SERIES] THEN
  DISCH_THEN(K ALL_TAC) THEN REWRITE_TAC[RAT_M_INTEGRAL]);;

let RAT_ZETA_LIN = prove
 (`forall H p J w e.
     cat_zeta (\t. sum(0..H) (\i. p i * t pow i))
              (\s. sum(0..J) (\v. w v * s pow (e v))) =
     sum(0..H) (\i. sum(0..J) (\v. (p i * w v) * rat_Z i (e v)))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[cat_zeta] THEN
  ONCE_REWRITE_TAC[REAL_ARITH `x / d = &1 * x / d`] THEN
  REWRITE_TAC[RAT_SUMPROD] THEN
  TRANS_TAC EQ_TRANS
   `real_integral (real_interval[&0,&1])
     (\t. sum(0..H) (\i. sum(0..J) (\v. (\(i:num) (v:num) (t:real). (p i * w v) *
           (t pow i * rat_g (e v) t)) i v t)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_INTEGRAL_SPIKE THEN EXISTS_TAC `{&1}` THEN
    REWRITE_TAC[REAL_NEGLIGIBLE_SING; IN_DIFF; IN_SING] THEN
    X_GEN_TAC `t:real` THEN STRIP_TAC THEN
    MP_TAC(ISPECL
     [`\(i:num) (v:num) (s:real). (p i * w v) * (&1 * (t pow i * s pow (e v)) / (&1 - t * s))`;
      `real_interval[&0,&1]`; `H:num`; `J:num`] RAT_INT_DSUM) THEN
    ASM_SIMP_TAC[REAL_INTEGRABLE_LMUL; REAL_INTEGRAL_LMUL; RAT_ZETA_INNER;
                 REAL_MUL_LID] THEN
    DISCH_THEN(K ALL_TAC) THEN REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL
     [`\(i:num) (v:num) (t:real). (p i * w v) * (t pow i * rat_g (e v) t)`;
      `real_interval[&0,&1]`; `H:num`; `J:num`] RAT_INT_DSUM) THEN
  SIMP_TAC[REAL_INTEGRABLE_LMUL; REAL_INTEGRAL_LMUL; RAT_ZETA_SERIES] THEN
  DISCH_THEN(K ALL_TAC) THEN REWRITE_TAC[RAT_Z_INTEGRAL]);;
