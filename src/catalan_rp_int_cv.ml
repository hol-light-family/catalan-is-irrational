needs "src/catalan_rp_defs.ml";;

(* ========================================================================= *)
(* Change of variables t = rp_t x for the one-variable integrals of rp_int. *)
(* Inverse map X(t) = t / (1 + sqrt(1 - t^2)).                               *)
(* ========================================================================= *)

let rp_int_cv_X = new_definition
 `rp_int_cv_X t = t / (&1 + sqrt(&1 - t pow 2))`;;

let RP_INT_CV_X_ALT = prove
 (`rp_int_cv_X = \t. t / (&1 + sqrt(&1 - t pow 2))`,
  REWRITE_TAC[FUN_EQ_THM; rp_int_cv_X]);;

let RP_INT_CV_SQ_POS = prove
 (`forall t. abs t < &1 ==> &0 < &1 - t pow 2`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[REAL_SUB_LT] THEN
  ONCE_REWRITE_TAC[GSYM REAL_POW2_ABS] THEN
  MATCH_MP_TAC REAL_POW_1_LT THEN ASM_REWRITE_TAC[REAL_ABS_POS] THEN ARITH_TAC);;

let RP_INT_CV_SQ_LE = prove
 (`forall t. abs t <= &1 ==> &0 <= &1 - t pow 2`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[REAL_SUB_LE] THEN
  ONCE_REWRITE_TAC[GSYM REAL_POW2_ABS] THEN
  MATCH_MP_TAC REAL_POW_1_LE THEN ASM_REWRITE_TAC[REAL_ABS_POS]);;

let RP_INT_CV_ALG1 = prove
 (`forall s t. s pow 2 = &1 - t pow 2 /\ &0 <= s
         ==> &1 + (t / (&1 + s)) pow 2 = &2 / (&1 + s)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(&1 + s = &0)` MP_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN CONV_TAC REAL_FIELD);;

let RP_INT_CV_ALG2 = prove
 (`forall s t. s pow 2 = &1 - t pow 2 /\ &0 <= s
         ==> &1 - (t / (&1 + s)) pow 2 = &2 * s / (&1 + s)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(&1 + s = &0)` MP_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN CONV_TAC REAL_FIELD);;

let RP_INT_CV_SQRT_FACTS = prove
 (`forall t. abs t <= &1
       ==> sqrt(&1 - t pow 2) pow 2 = &1 - t pow 2 /\
           &0 <= sqrt(&1 - t pow 2)`,
  MESON_TAC[RP_INT_CV_SQ_LE; SQRT_POW_2; SQRT_POS_LE]);;

let RP_INT_CV_RP_T_X = prove
 (`forall t. abs t <= &1 ==> rp_t(rp_int_cv_X t) = t`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[rp_t; rp_int_cv_X] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP RP_INT_CV_SQRT_FACTS) THEN
  SPEC_TAC(`sqrt(&1 - t pow 2)`,`s:real`) THEN REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[RP_INT_CV_ALG1] THEN
  SUBGOAL_THEN `~(&1 + s = &0)` MP_TAC THENL
   [ASM_REAL_ARITH_TAC; CONV_TAC REAL_FIELD]);;

let RP_INT_CV_DERIV = prove
 (`forall t. abs t < &1
       ==> (rp_int_cv_X has_real_derivative
            inv(sqrt(&1 - t pow 2) * (&1 + sqrt(&1 - t pow 2)))) (atreal t)`,
  REPEAT STRIP_TAC THEN FIRST_ASSUM(ASSUME_TAC o MATCH_MP RP_INT_CV_SQ_POS) THEN
  REWRITE_TAC[RP_INT_CV_X_ALT] THEN REAL_DIFF_TAC THEN
  MP_TAC(SPEC `&1 - t pow 2` SQRT_POS_LT) THEN
  MP_TAC(SPEC `&1 - t pow 2` SQRT_POW_2) THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
  SPEC_TAC(`sqrt(&1 - t pow 2)`,`s:real`) THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[REAL_POW_1] THEN
  REPEAT STRIP_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `~(&1 + s = &0) /\ ~(s = &0)` MP_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  UNDISCH_TAC `s pow 2 = &1 - t pow 2` THEN CONV_TAC REAL_FIELD);;

let RP_INT_CV_ID_MIXED = prove
 (`forall t. abs t < &1
       ==> &4 * abs(rp_int_cv_X t) / (&1 + rp_int_cv_X t pow 2) pow 2 *
           inv(sqrt(&1 - t pow 2) * (&1 + sqrt(&1 - t pow 2))) =
           abs t / sqrt(&1 - t pow 2)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[rp_int_cv_X] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP RP_INT_CV_SQ_POS) THEN
  MP_TAC(SPEC `&1 - t pow 2` SQRT_POS_LT) THEN
  MP_TAC(SPEC `&1 - t pow 2` SQRT_POW_2) THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
  SPEC_TAC(`sqrt(&1 - t pow 2)`,`s:real`) THEN REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[RP_INT_CV_ALG1; REAL_LT_IMP_LE] THEN
  SUBGOAL_THEN `abs(t / (&1 + s)) = abs t / (&1 + s)` SUBST1_TAC THENL
   [REWRITE_TAC[REAL_ABS_DIV] THEN AP_TERM_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `~(&1 + s = &0) /\ ~(s = &0)` MP_TAC THENL
   [ASM_REAL_ARITH_TAC; CONV_TAC REAL_FIELD]);;

let RP_INT_CV_ID_ZETA = prove
 (`forall t. abs t < &1
       ==> &2 * (&1 - rp_int_cv_X t pow 2) / (&1 + rp_int_cv_X t pow 2) pow 2 *
           inv(sqrt(&1 - t pow 2) * (&1 + sqrt(&1 - t pow 2))) = &1`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[rp_int_cv_X] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP RP_INT_CV_SQ_POS) THEN
  MP_TAC(SPEC `&1 - t pow 2` SQRT_POS_LT) THEN
  MP_TAC(SPEC `&1 - t pow 2` SQRT_POW_2) THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
  SPEC_TAC(`sqrt(&1 - t pow 2)`,`s:real`) THEN REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[RP_INT_CV_ALG1; RP_INT_CV_ALG2; REAL_LT_IMP_LE] THEN
  SUBGOAL_THEN `~(&1 + s = &0) /\ ~(s = &0)` MP_TAC THENL
   [ASM_REAL_ARITH_TAC; CONV_TAC REAL_FIELD]);;

let RP_INT_CV_X_ABS = prove
 (`forall t. abs t <= &1 ==> abs(rp_int_cv_X t) <= abs t`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[rp_int_cv_X] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP RP_INT_CV_SQRT_FACTS) THEN
  SPEC_TAC(`sqrt(&1 - t pow 2)`,`s:real`) THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[REAL_ABS_DIV] THEN
  SUBGOAL_THEN `abs(&1 + s) = &1 + s /\ &0 < &1 + s` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ASM_SIMP_TAC[REAL_LE_LDIV_EQ]] THEN
  MP_TAC(SPECL [`abs t`; `s:real`] REAL_LE_MUL) THEN
  ASM_REWRITE_TAC[REAL_ABS_POS] THEN REAL_ARITH_TAC);;

let RP_INT_CV_X_POS = prove
 (`forall t. abs t <= &1 /\ &0 <= t ==> &0 <= rp_int_cv_X t`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[rp_int_cv_X] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP RP_INT_CV_SQRT_FACTS) THEN
  SPEC_TAC(`sqrt(&1 - t pow 2)`,`s:real`) THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC);;

let RP_INT_CV_X_VALS = prove
 (`rp_int_cv_X(--(&1)) = --(&1) /\ rp_int_cv_X(&1) = &1 /\
   rp_int_cv_X(&0) = &0`,
  REWRITE_TAC[rp_int_cv_X] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  REWRITE_TAC[SQRT_0; SQRT_1] THEN CONV_TAC REAL_RAT_REDUCE_CONV);;

let RP_INT_CV_RP_T_ABS = prove
 (`forall x. abs(rp_t x) <= &1`,
  GEN_TAC THEN REWRITE_TAC[rp_t; real_div; REAL_MUL_ASSOC] THEN
  REWRITE_TAC[GSYM real_div; REAL_ABS_DIV] THEN
  SUBGOAL_THEN `abs(&1 + x pow 2) = &1 + x pow 2 /\ &0 < &1 + x pow 2`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(SPEC `x:real` REAL_LE_POW_2) THEN REAL_ARITH_TAC;
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ]] THEN
  ONCE_REWRITE_TAC[GSYM REAL_POW2_ABS] THEN
  MP_TAC(SPEC `abs x - &1` REAL_LE_POW_2) THEN
  REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_NUM] THEN REAL_ARITH_TAC);;

let RP_INT_CV_RP_T_POS = prove
 (`forall x. &0 <= x ==> &0 <= rp_t x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[rp_t] THEN
  MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_DIV THEN
  MP_TAC(SPEC `x:real` REAL_LE_POW_2) THEN ASM_REAL_ARITH_TAC);;

let RP_INT_CV_DEN = prove
 (`forall x. ~(&1 + x pow 2 = &0) /\ ~((&1 + x pow 2) pow 2 = &0)`,
  GEN_TAC THEN REWRITE_TAC[REAL_POW_EQ_0] THEN
  MP_TAC(SPEC `x:real` REAL_LE_POW_2) THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Continuity.                                                               *)
(* ------------------------------------------------------------------------- *)

let RP_INT_CV_CONT_SQRT = prove
 (`forall f s. f real_continuous_on s ==> (\x. sqrt(f x)) real_continuous_on s`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`f:real->real`; `sqrt`; `s:real->bool`]
    REAL_CONTINUOUS_ON_COMPOSE) THEN
  ASM_REWRITE_TAC[o_DEF; REAL_CONTINUOUS_ON_SQRT]);;

let RP_INT_CV_CONT_ABS = prove
 (`forall s. abs real_continuous_on s`,
  GEN_TAC THEN
  MP_TAC(ISPECL [`\x:real. x`; `s:real->bool`] REAL_CONTINUOUS_ON_ABS) THEN
  REWRITE_TAC[REAL_CONTINUOUS_ON_ID; ETA_AX]);;

let RP_INT_CV_CONT_TAC =
  REPEAT((FIRST_ASSUM MATCH_ACCEPT_TAC) ORELSE CONJ_TAC ORELSE
         MATCH_ACCEPT_TAC RP_INT_CV_CONT_ABS ORELSE
         MATCH_ACCEPT_TAC REAL_CONTINUOUS_ON_CONST ORELSE
         MATCH_ACCEPT_TAC REAL_CONTINUOUS_ON_ID ORELSE
         MATCH_MP_TAC REAL_CONTINUOUS_ON_MUL ORELSE
         MATCH_MP_TAC REAL_CONTINUOUS_ON_DIV ORELSE
         MATCH_MP_TAC REAL_CONTINUOUS_ON_ADD ORELSE
         MATCH_MP_TAC REAL_CONTINUOUS_ON_SUB ORELSE
         MATCH_MP_TAC REAL_CONTINUOUS_ON_POW ORELSE
         MATCH_MP_TAC REAL_CONTINUOUS_ON_ABS ORELSE
         MATCH_MP_TAC RP_INT_CV_CONT_SQRT);;

let RP_INT_CV_RP_T_CONT = prove
 (`forall s. rp_t real_continuous_on s`,
  GEN_TAC THEN
  SUBGOAL_THEN `rp_t = \x. &2 * x / (&1 + x pow 2)` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; rp_t]; ALL_TAC] THEN
  RP_INT_CV_CONT_TAC THEN REWRITE_TAC[RP_INT_CV_DEN]);;

let RP_INT_CV_X_CONT = prove
 (`rp_int_cv_X real_continuous_on real_interval[--(&1),&1]`,
  REWRITE_TAC[RP_INT_CV_X_ALT] THEN RP_INT_CV_CONT_TAC THEN
  REWRITE_TAC[IN_REAL_INTERVAL] THEN GEN_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC(REAL_ARITH `&0 <= s ==> ~(&1 + s = &0)`) THEN
  MATCH_MP_TAC SQRT_POS_LE THEN MATCH_MP_TAC RP_INT_CV_SQ_LE THEN
  ASM_REAL_ARITH_TAC);;

let RP_INT_CV_COMP_CONT = prove
 (`forall H s. H real_continuous_on s /\ IMAGE rp_t s SUBSET s
         ==> (\x. H(rp_t x)) real_continuous_on s`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`rp_t`; `H:real->real`; `s:real->bool`]
    REAL_CONTINUOUS_ON_COMPOSE) THEN
  REWRITE_TAC[o_DEF; RP_INT_CV_RP_T_CONT] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_MESON_TAC[REAL_CONTINUOUS_ON_SUBSET]);;

let RP_INT_CV_IMAGES = prove
 (`IMAGE rp_t (real_interval[--(&1),&1]) SUBSET real_interval[--(&1),&1] /\
   IMAGE rp_t (real_interval[&0,&1]) SUBSET real_interval[&0,&1] /\
   IMAGE rp_int_cv_X (real_interval[--(&1),&1]) SUBSET
     real_interval[--(&1),&1] /\
   IMAGE rp_int_cv_X (real_interval[&0,&1]) SUBSET real_interval[&0,&1]`,
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_REAL_INTERVAL] THEN
  REPEAT CONJ_TAC THEN X_GEN_TAC `x:real` THEN STRIP_TAC THENL
   [MP_TAC(SPEC `x:real` RP_INT_CV_RP_T_ABS) THEN REAL_ARITH_TAC;
    MP_TAC(SPEC `x:real` RP_INT_CV_RP_T_ABS) THEN
    MP_TAC(SPEC `x:real` RP_INT_CV_RP_T_POS) THEN ASM_REAL_ARITH_TAC;
    MP_TAC(SPEC `x:real` RP_INT_CV_X_ABS) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
    SUBGOAL_THEN `abs x <= &1` ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(SPEC `x:real` RP_INT_CV_X_ABS) THEN
    MP_TAC(SPEC `x:real` RP_INT_CV_X_POS) THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Main theorems.                                                            *)
(* ------------------------------------------------------------------------- *)

let RP_INT_CV_SPIKE = prove
 (`forall f g s t y. (f has_real_integral y) t
               ==> FINITE s /\ (forall x. x IN (t DIFF s) ==> g x = f x)
               ==> (g has_real_integral y) t`,
  MESON_TAC[HAS_REAL_INTEGRAL_SPIKE_FINITE]);;

let RP_INT_CV_MIXED = prove
 (`forall H. H real_continuous_on real_interval[--(&1),&1]
      ==> ((\t. abs t / sqrt(&1 - t pow 2) * H t) has_real_integral
           real_integral (real_interval[--(&1),&1])
             (\x. &4 * abs x / (&1 + x pow 2) pow 2 * H (rp_t x)))
          (real_interval[--(&1),&1])`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`H:real->real`; `real_interval[--(&1),&1]`]
    RP_INT_CV_COMP_CONT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[RP_INT_CV_IMAGES]; DISCH_TAC] THEN
  MP_TAC(ISPECL
   [`\x. &4 * abs x / (&1 + x pow 2) pow 2 * H (rp_t x)`;
    `rp_int_cv_X`;
    `\t. inv(sqrt(&1 - t pow 2) * (&1 + sqrt(&1 - t pow 2)))`;
    `--(&1)`; `&1`; `--(&1)`; `&1`; `{--(&1), &1}`]
   HAS_REAL_INTEGRAL_SUBSTITUTION) THEN
  REWRITE_TAC[RP_INT_CV_X_VALS; RP_INT_CV_IMAGES; RP_INT_CV_X_CONT] THEN
  ANTS_TAC THENL
   [CONV_TAC REAL_RAT_REDUCE_CONV THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_IMP_COUNTABLE THEN
      REWRITE_TAC[FINITE_INSERT; FINITE_EMPTY];
      RP_INT_CV_CONT_TAC THEN REWRITE_TAC[RP_INT_CV_DEN];
      REWRITE_TAC[IN_DIFF; IN_INSERT; NOT_IN_EMPTY; IN_REAL_INTERVAL] THEN
      REPEAT STRIP_TAC THEN MATCH_MP_TAC RP_INT_CV_DERIV THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(MATCH_MP_TAC o MATCH_MP RP_INT_CV_SPIKE) THEN
  EXISTS_TAC `{--(&1), &1}` THEN
  REWRITE_TAC[FINITE_INSERT; FINITE_EMPTY] THEN
  REWRITE_TAC[IN_DIFF; IN_INSERT; NOT_IN_EMPTY; IN_REAL_INTERVAL] THEN
  X_GEN_TAC `t:real` THEN DISCH_TAC THEN
  SUBGOAL_THEN `abs t < &1` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[RP_INT_CV_RP_T_X; REAL_LT_IMP_LE] THEN
  ASM_SIMP_TAC[GSYM RP_INT_CV_ID_MIXED] THEN REAL_ARITH_TAC);;

let RP_INT_CV_ZETA = prove
 (`forall H. H real_continuous_on real_interval[&0,&1]
      ==> (H has_real_integral
           real_integral (real_interval[&0,&1])
             (\x. &2 * (&1 - x pow 2) / (&1 + x pow 2) pow 2 * H (rp_t x)))
          (real_interval[&0,&1])`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`H:real->real`; `real_interval[&0,&1]`]
    RP_INT_CV_COMP_CONT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[RP_INT_CV_IMAGES]; DISCH_TAC] THEN
  SUBGOAL_THEN `rp_int_cv_X real_continuous_on real_interval[&0,&1]`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC `real_interval[--(&1),&1]` THEN
    REWRITE_TAC[RP_INT_CV_X_CONT; SUBSET_REAL_INTERVAL] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV;
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`\x. &2 * (&1 - x pow 2) / (&1 + x pow 2) pow 2 * H (rp_t x)`;
    `rp_int_cv_X`;
    `\t. inv(sqrt(&1 - t pow 2) * (&1 + sqrt(&1 - t pow 2)))`;
    `&0`; `&1`; `&0`; `&1`; `{&1}`]
   HAS_REAL_INTEGRAL_SUBSTITUTION) THEN
  ASM_REWRITE_TAC[RP_INT_CV_X_VALS; RP_INT_CV_IMAGES] THEN
  ANTS_TAC THENL
   [CONV_TAC REAL_RAT_REDUCE_CONV THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_IMP_COUNTABLE THEN
      REWRITE_TAC[FINITE_INSERT; FINITE_EMPTY];
      RP_INT_CV_CONT_TAC THEN REWRITE_TAC[RP_INT_CV_DEN];
      REWRITE_TAC[IN_DIFF; IN_INSERT; NOT_IN_EMPTY; IN_REAL_INTERVAL] THEN
      REPEAT STRIP_TAC THEN MATCH_MP_TAC RP_INT_CV_DERIV THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(MATCH_MP_TAC o MATCH_MP RP_INT_CV_SPIKE) THEN
  EXISTS_TAC `{&1}` THEN
  REWRITE_TAC[FINITE_INSERT; FINITE_EMPTY] THEN
  REWRITE_TAC[IN_DIFF; IN_INSERT; NOT_IN_EMPTY; IN_REAL_INTERVAL] THEN
  X_GEN_TAC `t:real` THEN DISCH_TAC THEN
  SUBGOAL_THEN `abs t < &1` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[RP_INT_CV_RP_T_X; REAL_LT_IMP_LE] THEN
  MATCH_MP_TAC(REAL_RING
   `forall a q b h:real. a * (q * b) = &1 ==> h = (a * (q * h)) * b`) THEN
  ASM_SIMP_TAC[RP_INT_CV_ID_ZETA]);;
