(* ========================================================================= *)
(* CERT / SER: the series T(u,x), S(u,x), ||u||^2 of the trial sequences:   *)
(* closed forms (Equation (90)) and term-by-term derivatives (92).          *)
(* ========================================================================= *)

needs "src/catalan_rp_cert_base.ml";;

(* ------------------------------------------------------------------------- *)
(* Chebyshev polynomials.                                                    *)
(* ------------------------------------------------------------------------- *)

let RP_CERT_SER_CHEB_COS = prove
 (`forall n t. rp_cheb n (cos t) = cos(&n * t)`,
  GEN_TAC THEN GEN_TAC THEN
  SUBGOAL_THEN `forall n. rp_cheb n (cos t) = cos(&n * t) /\
                    rp_cheb (n + 1) (cos t) = cos(&(n + 1) * t)`
    (fun th -> REWRITE_TAC[th]) THEN
  INDUCT_TAC THENL
   [REWRITE_TAC[rp_cheb; ARITH; REAL_MUL_LZERO; REAL_MUL_LID; COS_0] THEN
    MP_TAC(INST [`cos t`,`x:real`] (CONJUNCT1(CONJUNCT2 rp_cheb))) THEN
    REWRITE_TAC[ARITH];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[ADD1] THEN
  REWRITE_TAC[ARITH_RULE `(n + 1) + 1 = n + 2`; rp_cheb] THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_ADD; REAL_ADD_RDISTRIB; REAL_MUL_LID] THEN
  MP_TAC(SPECL [`&n * t + t`; `t:real`] COS_ADD) THEN
  MP_TAC(SPECL [`&n * t + t`; `t:real`] COS_SUB) THEN
  REWRITE_TAC[REAL_ARITH `(a + t) - t:real = a`; REAL_ARITH `&n * t + &2 * t = (&n * t + t) + t:real`] THEN
  CONV_TAC REAL_RING);;

let RP_CERT_SER_CHEB_BOUND = prove
 (`forall n x. abs x <= &1 ==> abs(rp_cheb n x) <= &1`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `x:real` COS_ACS) THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[RP_CERT_SER_CHEB_COS] THEN
  MP_TAC(SPEC `&n * acs x` COS_BOUNDS) THEN REAL_ARITH_TAC);;

(* recurrences in convenient instantiated form *)
let RP_CERT_SER_CHEB_REC = prove
 (`forall n x. rp_cheb (n + 2) x = &2 * x * rp_cheb (n + 1) x - rp_cheb n x /\
         rp_cert_chebu (n + 2) x = &2 * x * rp_cert_chebu (n + 1) x - rp_cert_chebu n x`,
  REWRITE_TAC[rp_cheb; rp_cert_chebu]);;

let RP_CERT_SER_CHEB_TU = prove
 (`forall n x. rp_cert_chebu (n + 1) x = x * rp_cert_chebu n x + rp_cheb (n + 1) x /\
         rp_cheb (n + 2) x = x * rp_cert_chebu (n + 1) x - rp_cert_chebu n x`,
  GEN_TAC THEN GEN_TAC THEN SPEC_TAC(`n:num`,`n:num`) THEN INDUCT_TAC THENL
   [MP_TAC(SPECL [`0`; `x:real`] RP_CERT_SER_CHEB_REC) THEN
    REWRITE_TAC[ARITH; rp_cheb; rp_cert_chebu] THEN CONV_TAC REAL_RING;
    ALL_TAC] THEN
  MP_TAC(SPECL [`n:num`; `x:real`] RP_CERT_SER_CHEB_REC) THEN
  MP_TAC(SPECL [`n + 1`; `x:real`] RP_CERT_SER_CHEB_REC) THEN
  REWRITE_TAC[ADD1; ARITH_RULE `(n + 1) + 1 = n + 2 /\ (n + 1) + 2 = n + 3`] THEN
  POP_ASSUM MP_TAC THEN CONV_TAC REAL_RING);;

let RP_CERT_SER_CHEBU_BOUND = prove
 (`forall n x. abs x <= &1 ==> abs(rp_cert_chebu n x) <= &(n + 1)`,
  INDUCT_TAC THEN REWRITE_TAC[rp_cert_chebu] THEN REPEAT STRIP_TAC THENL
   [CONV_TAC NUM_REDUCE_CONV THEN REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[ADD1; CONJUNCT1(SPEC_ALL RP_CERT_SER_CHEB_TU)] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x:real`) THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`n + 1`; `x:real`] RP_CERT_SER_CHEB_BOUND) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN
  MP_TAC(SPECL [`x:real`; `rp_cert_chebu n x`] REAL_ABS_MUL) THEN
  MP_TAC(SPECL [`abs x`; `&1`; `abs(rp_cert_chebu n x)`] REAL_LE_RMUL) THEN
  ASM_REWRITE_TAC[REAL_ABS_POS] THEN REAL_ARITH_TAC);;

let rp_cert_ser_chebd = define
 `(rp_cert_ser_chebd 0 (x:real) = &0) /\
  (rp_cert_ser_chebd (SUC n) x = &(SUC n) * rp_cert_chebu n x)`;;

let RP_CERT_SER_CHEB_DERIV = prove
 (`forall n x. ((\x. rp_cheb n x) has_real_derivative rp_cert_ser_chebd n x) (atreal x)`,
  GEN_TAC THEN GEN_TAC THEN
  SUBGOAL_THEN `forall n. ((\x. rp_cheb n x) has_real_derivative rp_cert_ser_chebd n x) (atreal x) /\
                    ((\x. rp_cheb (n + 1) x) has_real_derivative rp_cert_ser_chebd (n + 1) x)
                    (atreal x)` (fun th -> REWRITE_TAC[th]) THEN
  INDUCT_TAC THENL
   [REWRITE_TAC[ARITH; rp_cheb; rp_cert_ser_chebd; HAS_REAL_DERIVATIVE_CONST] THEN
    SUBGOAL_THEN `rp_cert_ser_chebd 1 x = &1` SUBST1_TAC THENL
     [REWRITE_TAC[ONE; rp_cert_ser_chebd; rp_cert_chebu] THEN
      CONV_TAC NUM_REDUCE_CONV THEN REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[ETA_AX; HAS_REAL_DERIVATIVE_ID];
    ALL_TAC] THEN
  POP_ASSUM STRIP_ASSUME_TAC THEN ASM_REWRITE_TAC[ADD1] THEN
  REWRITE_TAC[ARITH_RULE `(n + 1) + 1 = n + 2`] THEN
  SUBGOAL_THEN `(\x. rp_cheb (n + 2) x) =
                (\x. &2 * x * rp_cheb (n + 1) x - rp_cheb n x)` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; RP_CERT_SER_CHEB_REC]; ALL_TAC] THEN
  SUBGOAL_THEN `rp_cert_ser_chebd (n + 2) x =
                (&2 * x * rp_cert_ser_chebd (n + 1) x + &2 * rp_cheb (n + 1) x) -
                rp_cert_ser_chebd n x` SUBST1_TAC THENL
   [REWRITE_TAC[ARITH_RULE `n + 2 = SUC(n + 1)`; GSYM ADD1; rp_cert_ser_chebd] THEN
    STRUCT_CASES_TAC(SPEC `n:num` num_CASES) THEN
    REWRITE_TAC[rp_cert_ser_chebd; ARITH; rp_cheb; rp_cert_chebu] THENL
     [CONV_TAC REAL_RING; ALL_TAC] THEN
    REWRITE_TAC[ARITH_RULE `SUC(SUC n) = n + 2`; ADD1] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN
    MP_TAC(SPECL [`n':num`; `x:real`] RP_CERT_SER_CHEB_REC) THEN
    MP_TAC(SPECL [`n':num`; `x:real`] RP_CERT_SER_CHEB_TU) THEN
    CONV_TAC REAL_RING;
    ALL_TAC] THEN
  MATCH_MP_TAC HAS_REAL_DERIVATIVE_SUB THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[REAL_MUL_ASSOC] THEN
  SUBGOAL_THEN `(&2 * x) * rp_cert_ser_chebd (n + 1) x + &2 * rp_cheb (n + 1) x =
                (&2 * x) * rp_cert_ser_chebd (n + 1) x + (&2 * &1) * rp_cheb (n + 1) x`
    SUBST1_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`\x:real. &2 * x`; `&2 * &1`; `\x. rp_cheb (n + 1) x`;
                 `rp_cert_ser_chebd (n + 1) x`; `x:real`] HAS_REAL_DERIVATIVE_MUL_ATREAL) THEN
  ASM_SIMP_TAC[HAS_REAL_DERIVATIVE_LMUL_ATREAL; HAS_REAL_DERIVATIVE_ID]);;

(* ------------------------------------------------------------------------- *)
(* Logarithmic series.                                                       *)
(* ------------------------------------------------------------------------- *)

let RP_CERT_SER_LOGSER = prove
 (`forall w. norm w < &1
       ==> ((\n. w pow n / Cx(&n)) sums --clog(Cx(&1) - w)) (from 1)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `--w:complex` CLOG_CONVERGES) THEN ASM_REWRITE_TAC[NORM_NEG] THEN
  DISCH_THEN(MP_TAC o MATCH_MP SERIES_NEG) THEN
  REWRITE_TAC[COMPLEX_NEG_NEG; GSYM complex_sub] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `n:num` THEN
  REWRITE_TAC[COMPLEX_POW_NEG; GSYM ADD1; complex_pow; EVEN] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[COMPLEX_POW_ONE] THEN
  REWRITE_TAC[complex_div] THEN CONV_TAC COMPLEX_RING);;

let RP_CERT_SER_RELOG = prove
 (`forall c w. norm w < &1
         ==> ((\n. Re(c * w pow n) / &n) real_sums Re(c * --clog(Cx(&1) - w))) (from 1)`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP RP_CERT_SER_LOGSER) THEN
  DISCH_THEN(MP_TAC o SPEC `c:complex` o MATCH_MP SERIES_COMPLEX_LMUL) THEN
  DISCH_THEN(MP_TAC o MATCH_MP REAL_SUMS_RE) THEN
  REWRITE_TAC[o_DEF] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM; complex_div; COMPLEX_MUL_ASSOC; GSYM CX_INV; RE_MUL_CX] THEN
  REWRITE_TAC[real_div; REAL_MUL_AC]);;


let RP_CERT_SER_COSEXP = prove
 (`forall k t. Cx(cos(&k * t)) =
         (cexp(ii * Cx t) pow k + cexp(--ii * Cx t) pow k) / Cx(&2)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[CX_COS; ccos; GSYM CEXP_N] THEN
  REWRITE_TAC[CX_MUL] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  BINOP_TAC THEN AP_TERM_TAC THEN CONV_TAC COMPLEX_RING);;
let RP_CERT_SER_EXPPROD = prove
 (`forall t. cexp(ii * Cx t) * cexp(--ii * Cx t) = Cx(&1) /\
       cexp(ii * Cx t) + cexp(--ii * Cx t) = Cx(&2 * cos t)`,
  GEN_TAC THEN REWRITE_TAC[GSYM CEXP_ADD; COMPLEX_RING `ii * x + --ii * x = Cx(&0)`; CEXP_0] THEN
  REWRITE_TAC[CX_MUL; CX_COS; ccos] THEN CONV_TAC COMPLEX_FIELD);;
let RP_CERT_SER_RE_LT1 = prove
 (`forall w. norm w < &1 ==> &0 < Re(Cx(&1) - w) /\ ~(Cx(&1) - w = Cx(&0))`,
  GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(SPEC `w:complex` COMPLEX_NORM_GE_RE_IM) THEN
  REWRITE_TAC[RE_SUB; RE_CX] THEN STRIP_TAC THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o AP_TERM `Re`) THEN REWRITE_TAC[RE_SUB; RE_CX] THEN
  ASM_REAL_ARITH_TAC);;
let RP_CERT_SER_CLOG_PAIR = prove
 (`forall w1 w2. norm w1 < &1 /\ norm w2 < &1
           ==> clog(Cx(&1) - w1) + clog(Cx(&1) - w2) = clog((Cx(&1) - w1) * (Cx(&1) - w2))`,
  REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC CLOG_MUL_SIMPLE THEN
  MP_TAC(SPEC `w1:complex` RP_CERT_SER_RE_LT1) THEN
  MP_TAC(SPEC `w2:complex` RP_CERT_SER_RE_LT1) THEN ASM_REWRITE_TAC[] THEN
  REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `abs(Im(clog(Cx(&1) - w1))) < pi / &2 /\ abs(Im(clog(Cx(&1) - w2))) < pi / &2`
  MP_TAC THENL [ASM_SIMP_TAC[RE_CLOG_POS_LT]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN MP_TAC PI_POS THEN REAL_ARITH_TAC);;
let RP_CERT_SER_NEGII = prove(`forall t. --ii * Cx t = ii * Cx(--t)`, REWRITE_TAC[CX_NEG] THEN CONV_TAC COMPLEX_RING);;
let RP_CERT_SER_RECOS = prove
 (`forall c z t n. Re(c * z pow n) * cos(&n * t) =
             inv(&2) * (Re(c * (z * cexp(--ii * Cx t)) pow n) +
                        Re(c * (z * cexp(ii * Cx t)) pow n))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM RE_MUL_CX; RP_CERT_SER_COSEXP] THEN
  REWRITE_TAC[GSYM RE_ADD] THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  REWRITE_TAC[GSYM RE_MUL_CX] THEN AP_TERM_TAC THEN
  REWRITE_TAC[COMPLEX_POW_MUL; CX_INV] THEN CONV_TAC COMPLEX_FIELD);;

let RP_CERT_SER_TTERM = rp_cert_steps
 `forall c z x. norm z < &1 /\ --(&1) <= x /\ x <= &1
     ==> ((\k. Re(c * z pow k) * rp_cheb k x / &k) real_sums
          (--(Re(c * clog(Cx(&1) - Cx(&2 * x) * z + z pow 2))) / &2)) (from 1)`
 [(REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `x = cos(acs x)` SUBST1_TAC THENL [ASM_SIMP_TAC[COS_ACS]; ALL_TAC] THEN
  SPEC_TAC(`acs x`,`t:real`) THEN GEN_TAC THEN
  REWRITE_TAC[RP_CERT_SER_CHEB_COS]);
  (MP_TAC(SPECL [`c:complex`; `z * cexp(ii * Cx t)`] RP_CERT_SER_RELOG) THEN
  MP_TAC(SPECL [`c:complex`; `z * cexp(--ii * Cx t)`] RP_CERT_SER_RELOG) THEN
  REWRITE_TAC[COMPLEX_NORM_MUL; RP_CERT_SER_NEGII; NORM_CEXP_II] THEN
  ASM_REWRITE_TAC[REAL_MUL_RID] THEN
  REWRITE_TAC[IMP_IMP] THEN DISCH_THEN(MP_TAC o MATCH_MP REAL_SERIES_ADD) THEN
  DISCH_THEN(MP_TAC o SPEC `inv(&2)` o MATCH_MP REAL_SERIES_LMUL));
  (REWRITE_TAC[GSYM RP_CERT_SER_NEGII] THEN MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN BINOP_TAC);
  (REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `n:num` THEN REWRITE_TAC[]);
  (REWRITE_TAC[real_div; REAL_MUL_ASSOC; RP_CERT_SER_RECOS] THEN CONV_TAC REAL_RING);
  (SUBGOAL_THEN `Cx(&1) - Cx(&2 * cos t) * z + z pow 2 =
                (Cx(&1) - z * cexp(--ii * Cx t)) * (Cx(&1) - z * cexp(ii * Cx t))`
  SUBST1_TAC THENL
   [MP_TAC(SPEC `t:real` RP_CERT_SER_EXPPROD) THEN CONV_TAC COMPLEX_RING; ALL_TAC] THEN
  MP_TAC(SPECL [`z * cexp(--ii * Cx t)`; `z * cexp(ii * Cx t)`] RP_CERT_SER_CLOG_PAIR) THEN
  REWRITE_TAC[COMPLEX_NORM_MUL; RP_CERT_SER_NEGII; NORM_CEXP_II] THEN
  ASM_REWRITE_TAC[REAL_MUL_RID] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[COMPLEX_MUL_RNEG; RE_NEG; COMPLEX_ADD_LDISTRIB; RE_ADD] THEN
  REAL_ARITH_TAC)];;

let RP_CERT_SER_STERM = prove
 (`forall c z x. norm z < &1 /\ abs x <= &1
     ==> ((\k. Re(c * z pow k) * x pow k / &k) real_sums
          --(Re(c * clog(Cx(&1) - Cx x * z)))) (from 1)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`c:complex`; `Cx x * z`] RP_CERT_SER_RELOG) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[COMPLEX_NORM_MUL; COMPLEX_NORM_CX] THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `&1 * norm(z:complex)` THEN
    CONJ_TAC THENL [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[NORM_POS_LE];
                    ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[COMPLEX_MUL_RNEG; RE_NEG] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `n:num` THEN
  REWRITE_TAC[COMPLEX_POW_MUL; GSYM CX_POW] THEN
  REWRITE_TAC[COMPLEX_RING `c * Cx a * b = (c * b) * Cx a`; RE_MUL_CX] THEN
  REWRITE_TAC[real_div; REAL_MUL_ASSOC]);;

let RP_CERT_SER_REPROD = prove
 (`forall a b. Re a * Re b = inv(&2) * (Re(a * b) + Re(a * cnj b))`,
  REWRITE_TAC[complex_mul; RE; cnj; IM] THEN REAL_ARITH_TAC);;

let RP_CERT_SER_NTERM = prove
 (`forall c z c' w. norm z < &1 /\ norm w < &1
     ==> ((\k. Re(c * z pow k) * Re(c' * w pow k) / &k) real_sums
          --(Re(c * c' * clog(Cx(&1) - z * w)) +
             Re(c * cnj(c') * clog(Cx(&1) - z * cnj(w)))) / &2) (from 1)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`c * c':complex`; `z * w:complex`] RP_CERT_SER_RELOG) THEN
  MP_TAC(SPECL [`c * cnj c'`; `z * cnj w`] RP_CERT_SER_RELOG) THEN
  REWRITE_TAC[COMPLEX_NORM_MUL; COMPLEX_NORM_CNJ] THEN
  SUBGOAL_THEN `norm(z:complex) * norm(w:complex) < &1` (fun th -> REWRITE_TAC[th]) THENL
   [MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `&1 * norm(w:complex)` THEN
    CONJ_TAC THENL [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[NORM_POS_LE; REAL_LT_IMP_LE];
                    ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[IMP_IMP] THEN DISCH_THEN(MP_TAC o MATCH_MP REAL_SERIES_ADD) THEN
  DISCH_THEN(MP_TAC o SPEC `inv(&2)` o MATCH_MP REAL_SERIES_LMUL) THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN BINOP_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `n:num` THEN
    REWRITE_TAC[real_div; REAL_MUL_ASSOC; RP_CERT_SER_REPROD] THEN
    REWRITE_TAC[CNJ_MUL; CNJ_POW; COMPLEX_POW_MUL] THEN
    REWRITE_TAC[COMPLEX_RING `(c * z) * (c' * w):complex = (c * c') * z * w`] THEN
    CONV_TAC REAL_RING;
    REWRITE_TAC[COMPLEX_MUL_RNEG; RE_NEG; COMPLEX_MUL_ASSOC] THEN REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Finite support and the list-level series.                                 *)
(* ------------------------------------------------------------------------- *)




let RP_CERT_SER_FINSUMS = rp_cert_steps
 `forall f n. (forall k. n < k ==> f k = &0) ==> (f real_sums sum(1..n) f) (from 1)`
 [(REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\k. if k = 0 then &0 else (f:num->real) k`; `1..n`; `from 1`]
    REAL_SERIES_FINITE_SUPPORT));
  (REWRITE_TAC[IN_INTER; IN_NUMSEG; IN_FROM]);
  (SUBGOAL_THEN `(1..n) INTER from 1 = 1..n` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_INTER; IN_NUMSEG; IN_FROM] THEN ARITH_TAC; ALL_TAC]);
  (REWRITE_TAC[FINITE_NUMSEG] THEN ANTS_TAC THENL
   [X_GEN_TAC `k:num` THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    ALL_TAC]);
  (SUBGOAL_THEN `sum(1..n) (\k. if k = 0 then &0 else (f:num->real) k) = sum(1..n) f`
    SUBST1_TAC THENL
   [MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `k:num` THEN STRIP_TAC THEN
    REWRITE_TAC[] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC]);
  (DISCH_TAC THEN MATCH_MP_TAC REAL_SUMS_EQ THEN
  EXISTS_TAC `\k. if k = 0 then &0 else (f:num->real) k` THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[IN_FROM] THEN X_GEN_TAC `k:num` THEN DISCH_TAC THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC)];;

let RP_CERT_SER_OK_CONS = prove
 (`(rp_cert_ok [] <=> true) /\
   (forall cz t. rp_cert_ok (CONS cz t) <=> norm(SND cz) < &1 /\ rp_cert_ok t)`,
  REWRITE_TAC[rp_cert_ok; ALL]);;

let RP_CERT_SER_TAIL_T = prove
 (`forall t x. rp_cert_ok t /\ --(&1) <= x /\ x <= &1
     ==> ((\k. rp_cert_tail t k * rp_cheb k x / &k) real_sums rp_cert_ttail t x) (from 1)`,
  LIST_INDUCT_TAC THEN
  REWRITE_TAC[rp_cert_tail; rp_cert_ttail; REAL_MUL_LZERO; REAL_SERIES_0;
              RP_CERT_SER_OK_CONS] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[REAL_ADD_RDISTRIB] THEN
  MATCH_MP_TAC REAL_SERIES_ADD THEN ASM_SIMP_TAC[RP_CERT_SER_TTERM]);;

let RP_CERT_SER_TAIL_S = prove
 (`forall t x. rp_cert_ok t /\ abs x <= &1
     ==> ((\k. rp_cert_tail t k * x pow k / &k) real_sums rp_cert_stail t x) (from 1)`,
  LIST_INDUCT_TAC THEN
  REWRITE_TAC[rp_cert_tail; rp_cert_stail; REAL_MUL_LZERO; REAL_SERIES_0;
              RP_CERT_SER_OK_CONS] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[REAL_ADD_RDISTRIB] THEN
  MATCH_MP_TAC REAL_SERIES_ADD THEN ASM_SIMP_TAC[RP_CERT_SER_STERM]);;

let RP_CERT_SER_NTAIL1 = prove
 (`forall t2 cz. norm(SND cz) < &1 /\ rp_cert_ok t2
     ==> ((\k. Re(FST cz * SND cz pow k) * rp_cert_tail t2 k / &k) real_sums
          rp_cert_ntail1 cz t2) (from 1)`,
  LIST_INDUCT_TAC THEN
  REWRITE_TAC[rp_cert_tail; rp_cert_ntail1; REAL_MUL_LZERO; REAL_MUL_RZERO; real_div;
              REAL_SERIES_0; RP_CERT_SER_OK_CONS] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[REAL_ADD_LDISTRIB; REAL_ADD_RDISTRIB] THEN
  MATCH_MP_TAC REAL_SERIES_ADD THEN CONJ_TAC THENL
   [MP_TAC(SPECL [`FST(cz:complex#complex)`; `SND(cz:complex#complex)`;
                  `FST(h:complex#complex)`; `SND(h:complex#complex)`] RP_CERT_SER_NTERM) THEN
    ASM_REWRITE_TAC[real_div];
    FIRST_X_ASSUM(MP_TAC o SPEC `cz:complex#complex`) THEN ASM_REWRITE_TAC[real_div]]);;

let RP_CERT_SER_NTAIL = prove
 (`forall t1 t2. rp_cert_ok t1 /\ rp_cert_ok t2
     ==> ((\k. rp_cert_tail t1 k * rp_cert_tail t2 k / &k) real_sums
          rp_cert_ntail t1 t2) (from 1)`,
  LIST_INDUCT_TAC THEN
  REWRITE_TAC[rp_cert_tail; rp_cert_ntail; REAL_MUL_LZERO; REAL_SERIES_0;
              RP_CERT_SER_OK_CONS] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[REAL_ADD_RDISTRIB] THEN
  MATCH_MP_TAC REAL_SERIES_ADD THEN ASM_SIMP_TAC[RP_CERT_SER_NTAIL1]);;

let RP_CERT_SER_FIN_ZERO = prove
 (`forall l k. LENGTH l < k ==> rp_cert_fin l k = &0`,
  REWRITE_TAC[rp_cert_fin] THEN REPEAT STRIP_TAC THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

let RP_CERT_SER_FIN_EL = prove
 (`forall l k. 1 <= k /\ k <= LENGTH l ==> rp_cert_fin l k = EL (k - 1) l`,
  SIMP_TAC[rp_cert_fin]);;

let RP_CERT_SER_FIN_PART = prove
 (`forall l g. ((\k. rp_cert_fin l k * g k) real_sums
          sum (1..LENGTH l) (\k. EL (k - 1) l * g k)) (from 1)`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`\k. rp_cert_fin l k * g k`; `LENGTH(l:real list)`] RP_CERT_SER_FINSUMS) THEN
  SIMP_TAC[RP_CERT_SER_FIN_ZERO; REAL_MUL_LZERO] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN SIMP_TAC[RP_CERT_SER_FIN_EL]);;

let RP_CERT_ST_CLOSED = prove
 (`forall l t x. rp_cert_ok t /\ --(&1) <= x /\ x <= &1
     ==> rp_Tser (rp_cert_seq l t) x =
         sum (1..LENGTH l) (\k. EL (k - 1) l * rp_cheb k x / &k) +
         rp_cert_ttail t x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[rp_Tser; rp_cert_seq; REAL_ADD_RDISTRIB] THEN
  MATCH_MP_TAC REAL_INFSUM_UNIQUE THEN MATCH_MP_TAC REAL_SERIES_ADD THEN
  ASM_SIMP_TAC[RP_CERT_SER_TAIL_T] THEN
  MP_TAC(ISPECL [`l:real list`; `\k. rp_cheb k x / &k`] RP_CERT_SER_FIN_PART) THEN
  REWRITE_TAC[]);;

let RP_CERT_SS_CLOSED = prove
 (`forall l t x. rp_cert_ok t /\ --(&1) <= x /\ x <= &1
     ==> rp_Sser (rp_cert_seq l t) x =
         sum (1..LENGTH l) (\k. EL (k - 1) l * x pow k / &k) +
         rp_cert_stail t x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[rp_Sser; rp_cert_seq; REAL_ADD_RDISTRIB] THEN
  MATCH_MP_TAC REAL_INFSUM_UNIQUE THEN MATCH_MP_TAC REAL_SERIES_ADD THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`l:real list`; `\k. x pow k / &k`] RP_CERT_SER_FIN_PART) THEN
    REWRITE_TAC[];
    MATCH_MP_TAC RP_CERT_SER_TAIL_S THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]);;




let RP_CERT_SS_NSQ = rp_cert_steps
 `forall l t. rp_cert_ok t
     ==> rp_nsq (rp_cert_seq l t) =
         sum (1..LENGTH l)
           (\k. (EL (k - 1) l pow 2 + &2 * EL (k - 1) l * rp_cert_tail t k) / &k) +
         rp_cert_ntail t t`
 [(REPEAT STRIP_TAC THEN REWRITE_TAC[rp_nsq; rp_cert_seq] THEN
  MATCH_MP_TAC REAL_INFSUM_UNIQUE THEN
  SUBGOAL_THEN
   `(\k. (rp_cert_fin l k + rp_cert_tail t k) pow 2 / &k) =
    (\k. (rp_cert_fin l k pow 2 + &2 * rp_cert_fin l k * rp_cert_tail t k) / &k +
         rp_cert_tail t k * rp_cert_tail t k / &k)` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; real_div] THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  MATCH_MP_TAC REAL_SERIES_ADD THEN ASM_SIMP_TAC[RP_CERT_SER_NTAIL]);
  (MP_TAC(ISPECL [`\k. (rp_cert_fin l k pow 2 + &2 * rp_cert_fin l k * rp_cert_tail t k) / &k`;
                 `LENGTH(l:real list)`] RP_CERT_SER_FINSUMS));
  (SIMP_TAC[RP_CERT_SER_FIN_ZERO]);
  (REWRITE_TAC[REAL_POW_ZERO; ARITH; REAL_MUL_LZERO; REAL_MUL_RZERO; REAL_ADD_LID; real_div]);
  (MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN SIMP_TAC[RP_CERT_SER_FIN_EL])];;
(* summability *)
let rp_cert_ser_tb = define
 `(rp_cert_ser_tb [] (k:num) = &0) /\
  (rp_cert_ser_tb (CONS (cz:complex#complex) t) k =
     norm(FST cz) * norm(SND cz) pow k + rp_cert_ser_tb t k)`;;

let RP_CERT_SER_TB = prove
 (`forall t k. abs(rp_cert_tail t k) <= rp_cert_ser_tb t k`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[rp_cert_tail; rp_cert_ser_tb; REAL_ABS_0; REAL_LE_REFL] THEN
  GEN_TAC THEN MATCH_MP_TAC(REAL_ARITH `abs a <= c /\ abs b <= d ==> abs(a + b) <= c + d`) THEN
  ASM_REWRITE_TAC[GSYM COMPLEX_NORM_POW; GSYM COMPLEX_NORM_MUL] THEN
  REWRITE_TAC[COMPLEX_NORM_GE_RE_IM]);;

let RP_CERT_SER_TB_SUMMABLE = prove
 (`forall t. rp_cert_ok t ==> real_summable (from 1) (\k. rp_cert_ser_tb t k)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[rp_cert_ser_tb; REAL_SUMMABLE_0; RP_CERT_SER_OK_CONS] THEN
  STRIP_TAC THEN MATCH_MP_TAC REAL_SUMMABLE_ADD THEN ASM_SIMP_TAC[] THEN
  MATCH_MP_TAC REAL_SUMMABLE_LMUL THEN MATCH_MP_TAC REAL_SUMMABLE_GP THEN
  ASM_REWRITE_TAC[REAL_ABS_NORM]);;

let RP_CERT_SS_SUMMABLE = prove
 (`forall l t. rp_cert_ok t ==> rp_summable (rp_cert_seq l t)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[rp_summable; rp_cert_seq] THEN
  MATCH_MP_TAC REAL_SUMMABLE_COMPARISON THEN
  EXISTS_TAC `\k. abs(rp_cert_fin l k) + rp_cert_ser_tb t k` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_SUMMABLE_ADD THEN ASM_SIMP_TAC[RP_CERT_SER_TB_SUMMABLE] THEN
    REWRITE_TAC[real_summable] THEN
    EXISTS_TAC `sum(1..LENGTH(l:real list)) (\k. abs(rp_cert_fin l k))` THEN
    MATCH_MP_TAC RP_CERT_SER_FINSUMS THEN SIMP_TAC[RP_CERT_SER_FIN_ZERO; REAL_ABS_0];
    EXISTS_TAC `0` THEN REPEAT STRIP_TAC THEN REWRITE_TAC[REAL_ABS_ABS] THEN
    MP_TAC(SPECL [`t:(complex#complex)list`; `n:num`] RP_CERT_SER_TB) THEN
    REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Derivatives of the closed forms.                                          *)
(* ------------------------------------------------------------------------- *)

let RP_CERT_SER_RE_DERIV = prove
 (`forall f f' x. (f has_complex_derivative f') (at (Cx x))
            ==> ((Re o f o Cx) has_real_derivative (Re f')) (atreal x)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[HAS_COMPLEX_DERIVATIVE_AT; HAS_REAL_DERIVATIVE_ATREAL] THEN
  REWRITE_TAC[LIM_AT; REALLIM_ATREAL; o_THM] THEN
  MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `e:real` THEN
  ASM_CASES_TAC `&0 < e` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `d:real` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN X_GEN_TAC `y:real` THEN
  STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `Cx y`) THEN
  ASM_REWRITE_TAC[DIST_CX; dist] THEN
  REWRITE_TAC[GSYM RE_SUB; GSYM IM_SUB; CX_SUB;
              GSYM RE_DIV_CX; GSYM IM_SUB; GSYM IM_DIV_CX] THEN
  MESON_TAC[COMPLEX_NORM_GE_RE_IM; REAL_LET_TRANS]);;




let RP_CERT_SER_W_POS = rp_cert_steps
 `forall z x. norm z < &1 /\ --(&1) < x /\ x < &1
         ==> (Im(Cx(&1) - Cx(&2) * Cx x * z + z pow 2) = &0
              ==> &0 < Re(Cx(&1) - Cx(&2) * Cx x * z + z pow 2))`
 [(REPEAT GEN_TAC THEN
  REWRITE_TAC[COMPLEX_POW_2; RE_ADD; RE_SUB; IM_ADD; IM_SUB; RE_CX; IM_CX;
              RE_MUL_CX; IM_MUL_CX] THEN
  REWRITE_TAC[complex_mul; RE; IM; RE_CX; IM_CX] THEN
  STRIP_TAC);
  (SUBGOAL_THEN `Re z pow 2 + Im z pow 2 < &1` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM COMPLEX_SQNORM] THEN
    MP_TAC(SPECL [`2`; `norm(z:complex)`; `&1`] REAL_POW_LT2) THEN
    ASM_REWRITE_TAC[NORM_POS_LE; REAL_POW_ONE; ARITH];
    ALL_TAC] THEN DISCH_TAC);
  (SUBGOAL_THEN `Im z * (Re z - x) = &0` MP_TAC THENL
   [POP_ASSUM MP_TAC THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  REWRITE_TAC[REAL_ENTIRE; REAL_SUB_0] THEN STRIP_TAC);
  (ASM_REWRITE_TAC[] THEN
    MP_TAC(SPEC `Re z - x` REAL_LE_POW_2) THEN
    SUBGOAL_THEN `&0 < (&1 - x) * (&1 + x)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REAL_ARITH_TAC);
  (UNDISCH_TAC `Re z pow 2 + Im z pow 2 < &1` THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC)];;

let RP_CERT_SER_TTERM_DERIV = prove
 (`forall c z x. norm z < &1 /\ --(&1) < x /\ x < &1
     ==> ((\x. --(Re(c * clog(Cx(&1) - Cx(&2 * x) * z + z pow 2))) / &2)
          has_real_derivative
          Re(c * z / (Cx(&1) - Cx(&2 * x) * z + z pow 2))) (atreal x)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`\w. c * clog(Cx(&1) - Cx(&2) * w * z + z pow 2)`;
                `c * (--(Cx(&2) * z)) / (Cx(&1) - Cx(&2) * Cx x * z + z pow 2)`;
                `x:real`] RP_CERT_SER_RE_DERIV) THEN
  ANTS_TAC THENL
   [MP_TAC(SPECL [`z:complex`; `x:real`] RP_CERT_SER_W_POS) THEN ASM_REWRITE_TAC[] THEN
    DISCH_TAC THEN COMPLEX_DIFF_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[complex_div] THEN CONV_TAC COMPLEX_RING;
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `--inv(&2)` o MATCH_MP HAS_REAL_DERIVATIVE_LMUL_ATREAL) THEN
  REWRITE_TAC[o_DEF; CX_MUL] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN BINOP_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; COMPLEX_MUL_ASSOC] THEN REAL_ARITH_TAC;
    REWRITE_TAC[complex_div; COMPLEX_RING `c * --(Cx(&2) * z) * w = Cx(--(&2)) * (c * z * w)`] THEN
    REWRITE_TAC[RE_MUL_CX; COMPLEX_MUL_ASSOC] THEN REAL_ARITH_TAC]);;

let RP_CERT_SER_STERM_DERIV = prove
 (`forall c z x. norm z < &1 /\ abs x <= &1
     ==> ((\x. --(Re(c * clog(Cx(&1) - Cx x * z)))) has_real_derivative
          Re(c * z / (Cx(&1) - Cx x * z))) (atreal x)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `norm(Cx x * z) < &1` ASSUME_TAC THENL
   [REWRITE_TAC[COMPLEX_NORM_MUL; COMPLEX_NORM_CX] THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `&1 * norm(z:complex)` THEN
    CONJ_TAC THENL [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[NORM_POS_LE];
                    ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(SPECL [`\w. c * clog(Cx(&1) - w * z)`;
                `c * (--z) / (Cx(&1) - Cx x * z)`; `x:real`] RP_CERT_SER_RE_DERIV) THEN
  ANTS_TAC THENL
   [MP_TAC(SPEC `Cx x * z` RP_CERT_SER_RE_LT1) THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN COMPLEX_DIFF_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[complex_div] THEN CONV_TAC COMPLEX_RING;
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP HAS_REAL_DERIVATIVE_NEG) THEN
  REWRITE_TAC[o_DEF] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[complex_div; COMPLEX_MUL_RNEG; COMPLEX_MUL_LNEG; RE_NEG; REAL_NEG_NEG]);;

let RP_CERT_SER_TTAIL_DERIV = prove
 (`forall t x. rp_cert_ok t /\ --(&1) < x /\ x < &1
     ==> ((\x. rp_cert_ttail t x) has_real_derivative rp_cert_dttail t x) (atreal x)`,
  LIST_INDUCT_TAC THEN
  REWRITE_TAC[rp_cert_ttail; rp_cert_dttail; HAS_REAL_DERIVATIVE_CONST; RP_CERT_SER_OK_CONS] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HAS_REAL_DERIVATIVE_ADD THEN
  ASM_SIMP_TAC[RP_CERT_SER_TTERM_DERIV]);;

let RP_CERT_SER_STAIL_DERIV = prove
 (`forall t x. rp_cert_ok t /\ abs x <= &1
     ==> ((\x. rp_cert_stail t x) has_real_derivative rp_cert_dstail t x) (atreal x)`,
  LIST_INDUCT_TAC THEN
  REWRITE_TAC[rp_cert_stail; rp_cert_dstail; HAS_REAL_DERIVATIVE_CONST; RP_CERT_SER_OK_CONS] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HAS_REAL_DERIVATIVE_ADD THEN
  ASM_SIMP_TAC[RP_CERT_SER_STERM_DERIV]);;

let RP_CERT_SER_CHEBD_EQ = prove
 (`forall k x. 1 <= k ==> rp_cert_ser_chebd k x = &k * rp_cert_chebu (k - 1) x`,
  INDUCT_TAC THEN REWRITE_TAC[ARITH; rp_cert_ser_chebd; SUC_SUB1]);;




let RP_CERT_SER_TFIN_DERIV = rp_cert_steps
 `forall l x. ((\x. sum (1..LENGTH l) (\k. EL (k - 1) l * rp_cheb k x / &k)) has_real_derivative
          sum (1..LENGTH l) (\k. EL (k - 1) l * rp_cert_chebu (k - 1) x)) (atreal x)`
 [(REPEAT GEN_TAC THEN
  SUBGOAL_THEN `sum (1..LENGTH l) (\k. EL (k - 1) l * rp_cert_chebu (k - 1) x) =
                sum (1..LENGTH l) (\k. EL (k - 1) l * rp_cert_ser_chebd k x * inv(&k))`
    SUBST1_TAC);
  (MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `k:num` THEN STRIP_TAC THEN
    ASM_SIMP_TAC[RP_CERT_SER_CHEBD_EQ]);
  (SUBGOAL_THEN `~(&k = &0)` MP_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_EQ] THEN ASM_ARITH_TAC; CONV_TAC REAL_FIELD]);
  (MATCH_MP_TAC HAS_REAL_DERIVATIVE_SUM THEN REWRITE_TAC[FINITE_NUMSEG] THEN
  X_GEN_TAC `k:num` THEN DISCH_TAC THEN REWRITE_TAC[real_div; REAL_MUL_ASSOC]);
  (MATCH_MP_TAC HAS_REAL_DERIVATIVE_RMUL_ATREAL);
  (MATCH_MP_TAC HAS_REAL_DERIVATIVE_LMUL_ATREAL);
  (REWRITE_TAC[RP_CERT_SER_CHEB_DERIV])];;

let RP_CERT_SER_SFIN_DERIV = prove
 (`forall l x. ((\x. sum (1..LENGTH l) (\k. EL (k - 1) l * x pow k / &k)) has_real_derivative
          sum (1..LENGTH l) (\k. EL (k - 1) l * x pow (k - 1))) (atreal x)`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `sum (1..LENGTH l) (\k. EL (k - 1) l * x pow (k - 1)) =
                sum (1..LENGTH l) (\k. EL (k - 1) l * (&k * x pow (k - 1) * &1) * inv(&k))`
    SUBST1_TAC THENL
   [MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `k:num` THEN STRIP_TAC THEN
    SUBGOAL_THEN `~(&k = &0)` MP_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_EQ] THEN ASM_ARITH_TAC; CONV_TAC REAL_FIELD];
    ALL_TAC] THEN
  MATCH_MP_TAC HAS_REAL_DERIVATIVE_SUM THEN REWRITE_TAC[FINITE_NUMSEG] THEN
  X_GEN_TAC `k:num` THEN DISCH_TAC THEN REWRITE_TAC[real_div; REAL_MUL_ASSOC] THEN
  MATCH_MP_TAC HAS_REAL_DERIVATIVE_RMUL_ATREAL THEN
  REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN
  MATCH_MP_TAC HAS_REAL_DERIVATIVE_LMUL_ATREAL THEN
  MATCH_MP_TAC HAS_REAL_DERIVATIVE_POW_ATREAL THEN REWRITE_TAC[HAS_REAL_DERIVATIVE_ID]);;

let RP_CERT_ST_DERIV_AT = prove
 (`forall l t x. rp_cert_ok t /\ --(&1) < x /\ x < &1
     ==> (rp_Tser (rp_cert_seq l t) has_real_derivative
          (sum (1..LENGTH l) (\k. EL (k - 1) l * rp_cert_chebu (k - 1) x) +
           rp_cert_dttail t x)) (atreal x)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HAS_REAL_DERIVATIVE_TRANSFORM_ATREAL THEN
  EXISTS_TAC `\x. sum (1..LENGTH l) (\k. EL (k - 1) l * rp_cheb k x / &k) +
                  rp_cert_ttail t x` THEN
  EXISTS_TAC `min (&1 - x) (&1 + x)` THEN REPEAT CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC;
    X_GEN_TAC `y:real` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC RP_CERT_ST_CLOSED THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC HAS_REAL_DERIVATIVE_ADD THEN
    ASM_SIMP_TAC[RP_CERT_SER_TFIN_DERIV; RP_CERT_SER_TTAIL_DERIV]]);;

let RP_CERT_SS_DERIV_AT = prove
 (`forall l t x. rp_cert_ok t /\ --(&1) < x /\ x < &1
     ==> (rp_Sser (rp_cert_seq l t) has_real_derivative
          (sum (1..LENGTH l) (\k. EL (k - 1) l * x pow (k - 1)) +
           rp_cert_dstail t x)) (atreal x)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HAS_REAL_DERIVATIVE_TRANSFORM_ATREAL THEN
  EXISTS_TAC `\x. sum (1..LENGTH l) (\k. EL (k - 1) l * x pow k / &k) +
                  rp_cert_stail t x` THEN
  EXISTS_TAC `min (&1 - x) (&1 + x)` THEN REPEAT CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC;
    X_GEN_TAC `y:real` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC RP_CERT_SS_CLOSED THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC HAS_REAL_DERIVATIVE_ADD THEN
    REWRITE_TAC[RP_CERT_SER_SFIN_DERIV] THEN
    MATCH_MP_TAC RP_CERT_SER_STAIL_DERIV THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]);;
