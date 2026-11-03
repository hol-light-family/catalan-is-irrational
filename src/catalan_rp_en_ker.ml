(* ========================================================================= *)
(* EN kernel series: Chebyshev values and the logarithmic cosine series.    *)
(* ========================================================================= *)

needs "src/catalan_rp_en_defs.ml";;

let RP_EN_KER_RE_TERM = prove
 (`forall z th n. Re(--Cx(&1) pow (n + 1) * (--(Cx z * cexp(ii * Cx th))) pow n / Cx(&n)) =
             --(z pow n * cos(&n * th) / &n)`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `--Cx(&1) pow (n + 1) * (--(Cx z * cexp(ii * Cx th))) pow n / Cx(&n) =
                Cx(--(&1) pow (n + 1) * (--(&1)) pow n * z pow n / &n) *
                cexp(ii * Cx(&n * th))` SUBST1_TAC THENL
   [REWRITE_TAC[CX_MUL; CX_DIV; CX_POW; CX_NEG] THEN
    REWRITE_TAC[COMPLEX_RING `--(a * b:complex) = (--Cx(&1) * a) * b`] THEN
    REWRITE_TAC[COMPLEX_POW_MUL; GSYM CEXP_N] THEN
    REWRITE_TAC[COMPLEX_RING `Cx(&n) * ii * Cx th = ii * Cx(&n) * Cx th`] THEN
    REWRITE_TAC[complex_div] THEN CONV_TAC COMPLEX_RING;
    REWRITE_TAC[RE_MUL_CX; RE_CEXP; RE_MUL_II; IM_MUL_II; RE_CX; IM_CX] THEN
    REWRITE_TAC[REAL_NEG_0; REAL_EXP_0; REAL_POW_ADD; REAL_MUL_RID] THEN
    REWRITE_TAC[REAL_ARITH `(a * b) * a * c:real = (a * a) * b * c`] THEN
    REWRITE_TAC[GSYM REAL_POW_MUL] THEN
    REWRITE_TAC[REAL_ARITH `--(&1) * --(&1) = &1`; REAL_POW_ONE] THEN
    REAL_ARITH_TAC]);;

let RP_EN_KER_QPOS = prove
 (`forall z th. abs z < &1 ==> &0 < &1 - &2 * z * cos th + z pow 2`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `abs(z * cos th) <= abs z` MP_TAC THENL
   [REWRITE_TAC[REAL_ABS_MUL] THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_ABS_POS] THEN
    MP_TAC(SPEC `th:real` COS_BOUNDS) THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ONCE_REWRITE_TAC[GSYM REAL_POW2_ABS] THEN
  SUBGOAL_THEN `&0 < (&1 - abs z) pow 2` MP_TAC THENL
   [MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REAL_ARITH_TAC);;

let RP_EN_KER_CORE = prove
 (`forall z th. abs z < &1
     ==> ((\k. z pow k * cos(&k * th) / &k) real_sums
          (--(log(&1 - &2 * z * cos th + z pow 2)) / &2)) (from 1)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `norm(--(Cx z * cexp(ii * Cx th))) < &1` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[NORM_NEG; COMPLEX_NORM_MUL; COMPLEX_NORM_CX; NORM_CEXP_II;
                    REAL_MUL_RID];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP REAL_SUMS_RE o MATCH_MP CLOG_CONVERGES) THEN
  DISCH_THEN(MP_TAC o MATCH_MP REAL_SERIES_NEG) THEN
  REWRITE_TAC[o_DEF] THEN
  REWRITE_TAC[RP_EN_KER_RE_TERM; REAL_NEG_NEG; ETA_AX] THEN
  MATCH_MP_TAC(MESON[] `a = b ==> (f real_sums a) s ==> (f real_sums b) s`) THEN
  SUBGOAL_THEN `~(Cx(&1) + --(Cx z * cexp(ii * Cx th)) = Cx(&0))` ASSUME_TAC THENL
   [DISCH_THEN(MP_TAC o MATCH_MP (COMPLEX_RING
      `a + --w = Cx(&0) ==> --w = --a`)) THEN
    DISCH_THEN(MP_TAC o AP_TERM `norm:complex->real`) THEN
    UNDISCH_TAC `norm(--(Cx z * cexp(ii * Cx th))) < &1` THEN
    SIMP_TAC[NORM_NEG; COMPLEX_NORM_CX] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[RE_CLOG; complex_norm] THEN
  REWRITE_TAC[RE_ADD; RE_NEG; IM_ADD; IM_NEG; RE_CX; IM_CX; RE_MUL_CX; IM_MUL_CX;
              RE_CEXP; IM_CEXP; RE_MUL_II; IM_MUL_II] THEN
  REWRITE_TAC[REAL_NEG_0; REAL_EXP_0; REAL_MUL_LID] THEN
  SUBGOAL_THEN `(&1 + --(z * cos th)) pow 2 + (&0 + --(z * sin th)) pow 2 =
                &1 - &2 * z * cos th + z pow 2` SUBST1_TAC THENL
   [MP_TAC(SPEC `th:real` SIN_CIRCLE) THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  ASM_SIMP_TAC[LOG_SQRT; RP_EN_KER_QPOS] THEN REAL_ARITH_TAC);;


let RP_EN_KER_CHEB_COS = prove
 (`forall k t. rp_cheb k (cos t) = cos(&k * t)`,
  GEN_TAC THEN GEN_TAC THEN
  SUBGOAL_THEN `forall k. rp_cheb k (cos t) = cos(&k * t) /\
                    rp_cheb (k + 1) (cos t) = cos(&(k + 1) * t)`
   (fun th -> REWRITE_TAC[th]) THEN
  INDUCT_TAC THENL
   [REWRITE_TAC[ADD_CLAUSES; rp_cheb; REAL_MUL_LZERO; COS_0; REAL_MUL_LID];
    ASM_REWRITE_TAC[ADD1; ARITH_RULE `(k + 1) + 1 = k + 2`; rp_cheb] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN
    SUBGOAL_THEN `(&k + &2) * t = (&k + &1) * t + t /\ &k * t = (&k + &1) * t - t`
     (fun th -> ONCE_REWRITE_TAC[th]) THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[COS_ADD; COS_SUB] THEN REAL_ARITH_TAC]);;


let RP_EN_KER_CHEB_BOUND = prove
 (`forall k u. abs u <= &1 ==> abs(rp_cheb k u) <= &1`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `u = cos(acs u)` SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC COS_ACS THEN ASM_REAL_ARITH_TAC;
    REWRITE_TAC[RP_EN_KER_CHEB_COS; COS_BOUND]]);;

let RP_EN_KER_CROSS_SERIES = prove
 (`forall z s. abs z < &1 /\ abs s <= &1
         ==> ((\k. z pow k * rp_cheb k s / &k) real_sums
              (--(log(&1 - &2 * z * s + z pow 2)) / &2)) (from 1)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `s = cos(acs s)` SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC COS_ACS THEN ASM_REAL_ARITH_TAC;
    ASM_SIMP_TAC[RP_EN_KER_CHEB_COS; RP_EN_KER_CORE]]);;

let RP_EN_KER_POW_SERIES = prove
 (`forall w. abs w < &1
       ==> ((\k. w pow k / &k) real_sums (--(log(&1 - w)))) (from 1)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `&0` o MATCH_MP RP_EN_KER_CORE) THEN
  REWRITE_TAC[REAL_MUL_RZERO; COS_0; REAL_MUL_RID] THEN
  SUBGOAL_THEN `&1 - &2 * w + w pow 2 = (&1 - w) pow 2` SUBST1_TAC THENL
   [REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &1 - w` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[LOG_POW] THEN
  MATCH_MP_TAC(MESON[] `f = g /\ a = b ==> (f real_sums a) s ==> (g real_sums b) s`) THEN
  REWRITE_TAC[FUN_EQ_THM; real_div] THEN REAL_ARITH_TAC);;

let RP_EN_KER_PROD = prove
 (`forall r a b. (&1 - &2 * r * cos(a + b) + r pow 2) *
           (&1 - &2 * r * cos(a - b) + r pow 2) =
           rp_en_P r (cos a) (cos b)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[rp_en_P; COS_ADD; COS_SUB] THEN
  MP_TAC(SPEC `a:real` SIN_CIRCLE) THEN MP_TAC(SPEC `b:real` SIN_CIRCLE) THEN
  CONV_TAC REAL_RING);;

let RP_EN_KER_COS_SERIES = prove
 (`forall r u v. &0 <= r /\ r < &1 /\ abs u <= &1 /\ abs v <= &1
         ==> ((\k. r pow k * rp_cheb k u * rp_cheb k v / &k) real_sums
              (--(log(rp_en_P r u v)) / &4)) (from 1)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `u = cos(acs u) /\ v = cos(acs v)`
   (CONJUNCTS_THEN SUBST1_TAC) THENL
   [CONJ_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC COS_ACS THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[RP_EN_KER_CHEB_COS] THEN
  SPEC_TAC(`acs v`,`b:real`) THEN SPEC_TAC(`acs u`,`a:real`) THEN
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `abs r < &1` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`r:real`; `a + b:real`] RP_EN_KER_CORE) THEN
  MP_TAC(SPECL [`r:real`; `a - b:real`] RP_EN_KER_CORE) THEN
  ASM_REWRITE_TAC[IMP_IMP] THEN
  DISCH_THEN(MP_TAC o MATCH_MP REAL_SERIES_ADD) THEN
  DISCH_THEN(MP_TAC o SPEC `&1 / &2` o MATCH_MP REAL_SERIES_LMUL) THEN
  REWRITE_TAC[GSYM RP_EN_KER_PROD] THEN
  ASM_SIMP_TAC[LOG_MUL; RP_EN_KER_QPOS] THEN
  MATCH_MP_TAC(MESON[] `f = g /\ a = b ==> (f real_sums a) s ==> (g real_sums b) s`) THEN
  CONJ_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN
    REWRITE_TAC[REAL_ADD_LDISTRIB; REAL_SUB_LDISTRIB; COS_ADD; COS_SUB] THEN
    REWRITE_TAC[real_div] THEN REAL_ARITH_TAC;
    REAL_ARITH_TAC]);;

let RP_EN_KER_CHECK =
  concl RP_EN_KER_CHEB_COS = `forall k t. rp_cheb k (cos t) = cos(&k * t)` &&
  concl RP_EN_KER_CHEB_BOUND = `forall k u. abs u <= &1 ==> abs(rp_cheb k u) <= &1` &&
  concl RP_EN_KER_COS_SERIES = `forall r u v. &0 <= r /\ r < &1 /\ abs u <= &1 /\ abs v <= &1
         ==> ((\k. r pow k * rp_cheb k u * rp_cheb k v / &k) real_sums
              (--(log(rp_en_P r u v)) / &4)) (from 1)` &&
  concl RP_EN_KER_CROSS_SERIES = `forall z s. abs z < &1 /\ abs s <= &1
         ==> ((\k. z pow k * rp_cheb k s / &k) real_sums
              (--(log(&1 - &2 * z * s + z pow 2)) / &2)) (from 1)` &&
  concl RP_EN_KER_POW_SERIES = `forall w. abs w < &1
         ==> ((\k. w pow k / &k) real_sums (--(log(&1 - w)))) (from 1)`;;
if not RP_EN_KER_CHECK then failwith "RP_EN_KER_CHECK";;
