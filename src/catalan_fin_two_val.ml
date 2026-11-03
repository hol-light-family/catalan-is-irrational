(* ========================================================================= *)
(* fin_two_: elementary 2-adic valuation bounds (flog, c_l, m_i, Chebyshev,  *)
(* harmonic sums, Z').                                                       *)
(* ========================================================================= *)

needs "src/catalan_fin_base.ml";;
needs "src/catalan_fin_bdry.ml";;

(* ------------------------------------------------------------------------- *)
(* floor(log_2 n).                                                           *)
(* ------------------------------------------------------------------------- *)

let FIN_TWO_FLOG_FIN = prove
 (`forall n. FINITE {e | 1 <= e /\ 2 EXP e <= n}`,
  GEN_TAC THEN MATCH_MP_TAC FINITE_EXP_LE THEN ARITH_TAC);;

let FIN_TWO_FLOG_GE = prove
 (`forall n e. 2 EXP e <= n ==> e <= fin_flog 2 n`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[fin_flog] THEN
  TRANS_TAC LE_TRANS `CARD(1..e)` THEN CONJ_TAC THENL
   [REWRITE_TAC[CARD_NUMSEG_1; LE_REFL]; ALL_TAC] THEN
  MATCH_MP_TAC CARD_SUBSET THEN REWRITE_TAC[FIN_TWO_FLOG_FIN] THEN
  REWRITE_TAC[SUBSET; IN_NUMSEG; IN_ELIM_THM] THEN
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  TRANS_TAC LE_TRANS `2 EXP e` THEN ASM_REWRITE_TAC[LE_EXP] THEN
  ASM_ARITH_TAC);;

let FIN_TWO_FLOG_UB = prove
 (`forall n e. n < 2 EXP (e + 1) ==> fin_flog 2 n <= e`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[fin_flog] THEN
  TRANS_TAC LE_TRANS `CARD(1..e)` THEN CONJ_TAC THENL
   [ALL_TAC; REWRITE_TAC[CARD_NUMSEG_1; LE_REFL]] THEN
  MATCH_MP_TAC CARD_SUBSET THEN REWRITE_TAC[FINITE_NUMSEG] THEN
  REWRITE_TAC[SUBSET; IN_NUMSEG; IN_ELIM_THM] THEN
  X_GEN_TAC `j:num` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `2 EXP j < 2 EXP (e + 1)` MP_TAC THENL
   [ASM_ARITH_TAC; REWRITE_TAC[LT_EXP] THEN ARITH_TAC]);;

let FIN_TWO_FLOG_LT = prove
 (`forall n. n < 2 EXP (fin_flog 2 n + 1)`,
  GEN_TAC THEN REWRITE_TAC[GSYM NOT_LE] THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP FIN_TWO_FLOG_GE) THEN ARITH_TAC);;

let FIN_TWO_FLOG_EXP = prove
 (`forall n. 1 <= n ==> 2 EXP (fin_flog 2 n) <= n`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `\e. 2 EXP e <= n` num_MAX) THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC(TAUT `a /\ (b ==> c) ==> (a <=> b) ==> c`) THEN CONJ_TAC THENL
   [CONJ_TAC THENL
     [EXISTS_TAC `0` THEN ASM_REWRITE_TAC[EXP];
      EXISTS_TAC `n:num` THEN X_GEN_TAC `e:num` THEN DISCH_TAC THEN
      MP_TAC(SPEC `e:num` LT_POW2_REFL) THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:num` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `fin_flog 2 n = k` (fun th -> ASM_REWRITE_TAC[th]) THEN
  REWRITE_TAC[GSYM LE_ANTISYM] THEN CONJ_TAC THENL
   [MATCH_MP_TAC FIN_TWO_FLOG_UB THEN REWRITE_TAC[GSYM NOT_LE] THEN
    DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `k + 1`) THEN
    ASM_REWRITE_TAC[] THEN ARITH_TAC;
    MATCH_MP_TAC FIN_TWO_FLOG_GE THEN ASM_REWRITE_TAC[]]);;

let FIN_TWO_FLOG_MONO = prove
 (`forall m n. m <= n ==> fin_flog 2 m <= fin_flog 2 n`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[fin_flog] THEN
  MATCH_MP_TAC CARD_SUBSET THEN REWRITE_TAC[FIN_TWO_FLOG_FIN] THEN
  REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN ASM_MESON_TAC[LE_TRANS]);;

let FIN_TWO_FLOG_MUL = prove
 (`forall a b. fin_flog 2 (a * b) <= fin_flog 2 a + fin_flog 2 b + 1`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC FIN_TWO_FLOG_UB THEN
  SUBGOAL_THEN `2 EXP ((fin_flog 2 a + fin_flog 2 b + 1) + 1) =
                2 EXP (fin_flog 2 a + 1) * 2 EXP (fin_flog 2 b + 1)` SUBST1_TAC THENL
   [REWRITE_TAC[GSYM EXP_ADD] THEN AP_TERM_TAC THEN ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC LT_MULT2 THEN REWRITE_TAC[FIN_TWO_FLOG_LT]);;

let FIN_TWO_TWICE_LE_EXP = prove
 (`forall f. 2 * f <= 2 EXP f`,
  INDUCT_TAC THEN REWRITE_TAC[EXP; ARITH] THEN
  MP_TAC(SPEC `f:num` LT_POW2_REFL) THEN ARITH_TAC);;

let FIN_TWO_FLOG_HALF = prove
 (`forall n. 2 * fin_flog 2 n <= n`,
  GEN_TAC THEN ASM_CASES_TAC `n = 0` THENL
   [ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `fin_flog 2 0 <= 0` MP_TAC THENL
     [MATCH_MP_TAC FIN_TWO_FLOG_UB THEN REWRITE_TAC[EXP_LT_0] THEN ARITH_TAC;
      ARITH_TAC];
    ALL_TAC] THEN
  TRANS_TAC LE_TRANS `2 EXP (fin_flog 2 n)` THEN
  REWRITE_TAC[FIN_TWO_TWICE_LE_EXP] THEN MATCH_MP_TAC FIN_TWO_FLOG_EXP THEN
  ASM_ARITH_TAC);;

let FIN_TWO_FLOG_ADD = prove
 (`forall H k. 1 <= H ==> fin_flog 2 (H + k) <= fin_flog 2 H + fin_flog 2 (k + 1) + 1`,
  REPEAT STRIP_TAC THEN TRANS_TAC LE_TRANS `fin_flog 2 (H * (k + 1))` THEN
  REWRITE_TAC[FIN_TWO_FLOG_MUL] THEN MATCH_MP_TAC FIN_TWO_FLOG_MONO THEN
  REWRITE_TAC[LEFT_ADD_DISTRIB; MULT_CLAUSES] THEN
  SUBGOAL_THEN `k:num <= H * k` MP_TAC THENL
   [MATCH_MP_TAC(ARITH_RULE `1 * k <= H * k ==> k:num <= H * k`) THEN
    REWRITE_TAC[LE_MULT_RCANCEL] THEN ASM_ARITH_TAC;
    ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Valuations of 1/n, c_l, ckern, m_i.                                       *)
(* ------------------------------------------------------------------------- *)

let FIN_TWO_PRIME = prove
 (`prime 2`,
  REWRITE_TAC[PRIME_2]);;

let FIN_TWO_INV_VAL = prove
 (`forall n H. 1 <= n /\ n <= H ==> fin_vge 2 (--(&(fin_flog 2 H))) (inv(&n))`,
  MESON_TAC[FIN_BDRY_NUM_VAL; FIN_TWO_PRIME]);;

let FIN_TWO_DIV_VAL = prove
 (`forall k x n H. fin_vge 2 k x /\ 1 <= n /\ n <= H
             ==> fin_vge 2 (k - &(fin_flog 2 H)) (x / &n)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[real_div; real_sub] THEN
  MATCH_MP_TAC FIN_VGE_MUL THEN ASM_SIMP_TAC[FIN_TWO_PRIME; FIN_TWO_INV_VAL]);;

let FIN_TWO_C_VAL = prove
 (`forall l. fin_vge 2 (--(&(2 * l))) (cat_c l)`,
  GEN_TAC THEN SIMP_TAC[FIN_VGE_NEGPOW; FIN_TWO_PRIME] THEN
  REWRITE_TAC[cat_c; GSYM REAL_POW_POW] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN
  SUBGOAL_THEN `&(binom(2 * l,l)) / &4 pow l * &4 pow l = &(binom(2 * l,l))`
  SUBST1_TAC THENL
   [MATCH_MP_TAC REAL_DIV_RMUL THEN REWRITE_TAC[REAL_POW_EQ_0] THEN REAL_ARITH_TAC;
    SIMP_TAC[FIN_ZP_NUM; FIN_TWO_PRIME]]);;

let FIN_TWO_CKERN_VAL = prove
 (`forall i j. fin_vge 2 (&j - &i) (cat_ckern i j)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[cat_ckern] THEN COND_CASES_TAC THENL
   [ALL_TAC; SIMP_TAC[FIN_VGE_0; FIN_TWO_PRIME]] THEN
  MATCH_MP_TAC FIN_VGE_MONO THEN
  EXISTS_TAC `--(&(2 * ((i - j) DIV 2)))` THEN REWRITE_TAC[FIN_TWO_C_VAL] THEN
  FIRST_X_ASSUM(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  REWRITE_TAC[EVEN_EXISTS] THEN DISCH_THEN(X_CHOOSE_TAC `q:num`) THEN
  ASM_REWRITE_TAC[] THEN SIMP_TAC[DIV_MULT; ARITH_EQ] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN ASM_SIMP_TAC[GSYM REAL_OF_NUM_SUB] THEN
  REAL_ARITH_TAC);;

let FIN_TWO_M_VAL = prove
 (`forall n. fin_vge 2 (&n + &1 - &(fin_flog 2 n)) (cat_m n)`,
  GEN_TAC THEN REWRITE_TAC[cat_m] THEN COND_CASES_TAC THENL
   [ALL_TAC; SIMP_TAC[FIN_VGE_0; FIN_TWO_PRIME]] THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `a:num` SUBST1_TAC o REWRITE_RULE[EVEN_EXISTS]) THEN
  SIMP_TAC[DIV_MULT; ARITH_EQ] THEN
  SUBGOAL_THEN `&2 / (&(2 * a + 1) * cat_c a) =
                (&2 pow (2 * a + 1) * inv(&(binom(2 * a,a)))) * inv(&(2 * a + 1))`
  SUBST1_TAC THENL
   [REWRITE_TAC[cat_c; GSYM REAL_POW_POW; REAL_POW_ADD] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN
    SUBGOAL_THEN `~(&(binom(2 * a,a)) = &0) /\ ~(&(2 * a + 1) = &0)` MP_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_EQ; BINOM_EQ_0] THEN ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `~(&4 pow a = &0)` MP_TAC THENL
     [REWRITE_TAC[REAL_POW_EQ_0] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  MATCH_MP_TAC FIN_VGE_MONO THEN
  EXISTS_TAC `(&(2 * a + 1) + --(&(fin_flog 2 (2 * a)))) + &0` THEN CONJ_TAC THENL
   [REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC FIN_VGE_MUL THEN REWRITE_TAC[FIN_TWO_PRIME] THEN CONJ_TAC THENL
   [MATCH_MP_TAC FIN_VGE_MUL THEN
    SIMP_TAC[FIN_TWO_PRIME; FIN_VGE_PPOW; FIN_BDRY_BINOM_VAL; LE_REFL];
    SIMP_TAC[FIN_VGE_ZP; FIN_TWO_PRIME] THEN MATCH_MP_TAC FIN_ZP_INV_NUM THEN
    REWRITE_TAC[FIN_TWO_PRIME; DIVIDES_2; EVEN_ADD; EVEN_MULT; ARITH]]);;

(* ------------------------------------------------------------------------- *)
(* Chebyshev coefficients: v_2(T_d[k]) >= k - 1, v_2(U_d[k]) >= k.           *)
(* ------------------------------------------------------------------------- *)

let FIN_TWO_VGE_ONE = prove
 (`forall k. k <= &0 ==> fin_vge 2 k (&1)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC FIN_VGE_MONO THEN EXISTS_TAC `&0` THEN
  ASM_SIMP_TAC[FIN_VGE_NUM; FIN_TWO_PRIME]);;

let FIN_TWO_VGE_TWICE = prove
 (`forall k x. fin_vge 2 (k - &1) x ==> fin_vge 2 k (&2 * x)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`2`; `k - &1`; `x:real`] FIN_VGE_PMUL) THEN
  REWRITE_TAC[FIN_TWO_PRIME; REAL_ARITH `k - &1 + &1 = k`] THEN
  ASM_MESON_TAC[]);;

let FIN_TWO_CHEBT_VAL = prove
 (`forall d k. fin_vge 2 (&k - &1) (cheb_T d k)`,
  SUBGOAL_THEN `forall d. (forall k. fin_vge 2 (&k - &1) (cheb_T d k)) /\
                    (forall k. fin_vge 2 (&k - &1) (cheb_T (SUC d) k))`
   (fun th -> MESON_TAC[th]) THEN
  INDUCT_TAC THENL
   [REWRITE_TAC[cheb_T] THEN CONJ_TAC THEN GEN_TAC THEN COND_CASES_TAC THEN
    ASM_SIMP_TAC[FIN_VGE_0; FIN_TWO_PRIME] THEN
    MATCH_MP_TAC FIN_TWO_VGE_ONE THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN GEN_TAC THEN REWRITE_TAC[cheb_T] THEN
  MATCH_MP_TAC FIN_VGE_SUB THEN ASM_REWRITE_TAC[FIN_TWO_PRIME] THEN
  COND_CASES_TAC THEN SIMP_TAC[FIN_VGE_0; FIN_TWO_PRIME] THEN
  MATCH_MP_TAC FIN_TWO_VGE_TWICE THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `k - 1` o CONJUNCT2) THEN
  ASM_SIMP_TAC[GSYM REAL_OF_NUM_SUB; ARITH_RULE `~(k = 0) ==> 1 <= k`]);;

let FIN_TWO_CHEBU_VAL = prove
 (`forall d k. fin_vge 2 (&k) (cheb_U d k)`,
  SUBGOAL_THEN `forall d. (forall k. fin_vge 2 (&k) (cheb_U d k)) /\
                    (forall k. fin_vge 2 (&k) (cheb_U (SUC d) k))`
   (fun th -> MESON_TAC[th]) THEN
  INDUCT_TAC THENL
   [REWRITE_TAC[cheb_U] THEN CONJ_TAC THEN GEN_TAC THEN COND_CASES_TAC THEN
    ASM_SIMP_TAC[FIN_VGE_0; FIN_TWO_PRIME] THENL
     [MATCH_MP_TAC FIN_TWO_VGE_ONE THEN REAL_ARITH_TAC;
      SIMP_TAC[FIN_VGE_1_NUM; FIN_TWO_PRIME; DIVIDES_REFL]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN GEN_TAC THEN REWRITE_TAC[cheb_U] THEN
  MATCH_MP_TAC FIN_VGE_SUB THEN ASM_REWRITE_TAC[FIN_TWO_PRIME] THEN
  COND_CASES_TAC THEN SIMP_TAC[FIN_VGE_0; FIN_TWO_PRIME] THEN
  MATCH_MP_TAC FIN_TWO_VGE_TWICE THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `k - 1` o CONJUNCT2) THEN
  ASM_SIMP_TAC[GSYM REAL_OF_NUM_SUB; ARITH_RULE `~(k = 0) ==> 1 <= k`]);;

(* ------------------------------------------------------------------------- *)
(* Harmonic sums and Z'.                                                     *)
(* ------------------------------------------------------------------------- *)

let FIN_TWO_HARM1_VAL = prove
 (`forall i H. i <= H ==> fin_vge 2 (--(&(fin_flog 2 H))) (cat_harm 1 i)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[cat_harm; REAL_POW_1; real_div; REAL_MUL_LID] THEN
  MATCH_MP_TAC FIN_VGE_SUM THEN REWRITE_TAC[FIN_TWO_PRIME; FINITE_NUMSEG; IN_NUMSEG] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC FIN_TWO_INV_VAL THEN ASM_ARITH_TAC);;

let FIN_TWO_HARM2_VAL = prove
 (`forall i H. i <= H ==> fin_vge 2 (--(&2 * &(fin_flog 2 H))) (cat_harm 2 i)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[cat_harm; REAL_POW_2; real_div; REAL_MUL_LID] THEN
  MATCH_MP_TAC FIN_VGE_SUM THEN REWRITE_TAC[FIN_TWO_PRIME; FINITE_NUMSEG; IN_NUMSEG] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[REAL_INV_MUL] THEN
  REWRITE_TAC[REAL_ARITH `--(&2 * x) = --x + --x`] THEN
  MATCH_MP_TAC FIN_VGE_MUL THEN REWRITE_TAC[FIN_TWO_PRIME] THEN
  REPEAT CONJ_TAC THEN MATCH_MP_TAC FIN_TWO_INV_VAL THEN ASM_ARITH_TAC);;

let FIN_TWO_Z0_VAL = prove
 (`forall i j H. i <= H /\ j <= H ==> fin_vge 2 (--(&2 * &(fin_flog 2 H))) (cat_Z0 i j)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[cat_Z0] THEN COND_CASES_TAC THENL
   [ASM_SIMP_TAC[FIN_VGE_NEG_EQ; FIN_TWO_HARM2_VAL]; ALL_TAC] THEN
  REWRITE_TAC[real_div; REAL_ARITH `--(&2 * x) = --x + --x`] THEN
  MATCH_MP_TAC FIN_VGE_MUL THEN REWRITE_TAC[FIN_TWO_PRIME] THEN CONJ_TAC THENL
   [MATCH_MP_TAC FIN_VGE_SUB THEN ASM_SIMP_TAC[FIN_TWO_PRIME; FIN_TWO_HARM1_VAL];
    ALL_TAC] THEN
  SUBGOAL_THEN `j:num < i \/ i < j` DISJ_CASES_TAC THENL
   [ASM_ARITH_TAC;
    ASM_SIMP_TAC[REAL_OF_NUM_SUB; LT_IMP_LE] THEN
    MATCH_MP_TAC FIN_TWO_INV_VAL THEN ASM_ARITH_TAC;
    ONCE_REWRITE_TAC[GSYM REAL_NEG_SUB] THEN REWRITE_TAC[REAL_INV_NEG] THEN
    REWRITE_TAC[FIN_VGE_NEG_EQ] THEN ASM_SIMP_TAC[REAL_OF_NUM_SUB; LT_IMP_LE] THEN
    MATCH_MP_TAC FIN_TWO_INV_VAL THEN ASM_ARITH_TAC]);;
