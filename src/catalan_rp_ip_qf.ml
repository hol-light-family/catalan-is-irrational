(* ========================================================================= *)
(* rp_ip: quadratic forms on num-indexed vectors; positivity of the Gram    *)
(* matrix 1/(1 - x_i x_j) of the kernels k_i(z) = 1/(1 - x_i z).            *)
(* ========================================================================= *)

needs "src/catalan_rp_ip_base.ml";;

let rp_ip_qf = new_definition
 `rp_ip_qf n (G:num->num->real) (a:num->real) =
    sum {i | i < n} (\i. sum {j | j < n} (\j. a i * G i j * a j))`;;

let rp_ip_bil = new_definition
 `rp_ip_bil n (G:num->num->real) (a:num->real) (b:num->real) =
    sum {i | i < n} (\i. sum {j | j < n} (\j. a i * G i j * b j))`;;

let RP_IP_BIL_SYM = prove
 (`forall n G a b. (forall i j. i < n /\ j < n ==> G i j = G j i)
     ==> rp_ip_bil n G b a = rp_ip_bil n G a b`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[rp_ip_bil] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) SUM_SWAP o lhand o snd) THEN
  REWRITE_TAC[FINITE_NUMSEG_LT] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `p:num` THEN
  REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN
  MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `q:num` THEN
  REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`q:num`; `p:num`]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REAL_ARITH_TAC);;

let RP_IP_QF_LIN = prove
 (`forall n G a b u v. (forall i j. i < n /\ j < n ==> G i j = G j i)
     ==> rp_ip_qf n G (\i. u * a i + v * b i) =
         u pow 2 * rp_ip_qf n G a + &2 * u * v * rp_ip_bil n G a b +
         v pow 2 * rp_ip_qf n G b`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o SPECL [`a:num->real`; `b:num->real`] o
    MATCH_MP RP_IP_BIL_SYM) THEN
  TRANS_TAC EQ_TRANS
   `u pow 2 * rp_ip_qf n G a + u * v * rp_ip_bil n G a b +
    u * v * rp_ip_bil n G b a + v pow 2 * rp_ip_qf n G b` THEN
  CONJ_TAC THENL [ALL_TAC; ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC] THEN
  REWRITE_TAC[rp_ip_qf; rp_ip_bil] THEN
  SIMP_TAC[GSYM SUM_LMUL; GSYM SUM_ADD; FINITE_NUMSEG_LT] THEN
  MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `p:num` THEN DISCH_TAC THEN
  REWRITE_TAC[] THEN
  MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `q:num` THEN DISCH_TAC THEN
  REWRITE_TAC[] THEN CONV_TAC REAL_RING);;

(* triangle inequality in squared form, without square roots *)
let RP_IP_QF_TRIANGLE = prove
 (`forall n G a b c.
     (forall i j. i < n /\ j < n ==> G i j = G j i) /\
     (forall a. &0 <= rp_ip_qf n G a) /\ &0 < c /\
     rp_ip_qf n G b <= c pow 2 * rp_ip_qf n G a
     ==> rp_ip_qf n G (\i. a i + b i) <= (&1 + c) pow 2 * rp_ip_qf n G a`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`n:num`; `G:num->num->real`; `a:num->real`; `b:num->real`;
                 `&1`; `&1`] RP_IP_QF_LIN) THEN
  MP_TAC(ISPECL [`n:num`; `G:num->num->real`; `a:num->real`; `b:num->real`;
                 `c:real`; `--(&1)`] RP_IP_QF_LIN) THEN
  ASM_REWRITE_TAC[REAL_MUL_LID] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `\i. c * (a:num->real) i + --(&1) * b i`) THEN
  ABBREV_TAC `qa = rp_ip_qf n G a` THEN ABBREV_TAC `qb = rp_ip_qf n G b` THEN
  ABBREV_TAC `B = rp_ip_bil n G a b` THEN
  DISCH_TAC THEN DISCH_THEN SUBST_ALL_TAC THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN `B <= c * qa` ASSUME_TAC THENL
   [SUBGOAL_THEN `c * B <= c * (c * qa)` MP_TAC THENL
     [ASM_REAL_ARITH_TAC; ASM_SIMP_TAC[REAL_LE_LMUL_EQ]];
    ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

let RP_IP_SERIES_FINSUM = prove
 (`forall k (f:num->num->real) l s.
      FINITE k /\ (forall j. j IN k ==> ((f j) real_sums (l j)) s)
      ==> ((\m. sum k (\j. f j m)) real_sums (sum k l)) s`,
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[SUM_CLAUSES; REAL_SERIES_0; FORALL_IN_INSERT] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_SERIES_ADD THEN
  ASM_SIMP_TAC[ETA_AX]);;

let RP_IP_GRAM_GE = prove
 (`forall n x a. (forall i. i < n ==> abs(x i) < &1)
     ==> sum {m | m < n} (\m. sum {i | i < n} (\i. a i * x i pow m) pow 2)
         <= rp_ip_qf n (\i j. inv(&1 - x i * x j)) a`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `f = \m. sum {i:num | i < n} (\i. (a:num->real) i * (x:num->real) i pow m) pow 2` THEN
  SUBGOAL_THEN
   `((f:num->real) real_sums
      rp_ip_qf n (\i j. inv(&1 - (x:num->real) i * x j)) a) (from 0)`
  ASSUME_TAC THENL
   [EXPAND_TAC "f" THEN
    SUBGOAL_THEN
     `forall m. sum {i:num | i < n} (\i. (a:num->real) i * (x:num->real) i pow m) pow 2 =
          sum {i | i < n}
            (\i. sum {j | j < n} (\j. a i * a j * (x i * x j) pow m))`
    (fun th -> REWRITE_TAC[th]) THENL
     [GEN_TAC THEN REWRITE_TAC[REAL_POW_2; GSYM SUM_RMUL; GSYM SUM_LMUL] THEN
      MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `p:num` THEN DISCH_TAC THEN
      REWRITE_TAC[] THEN
      MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `q:num` THEN DISCH_TAC THEN
      REWRITE_TAC[REAL_POW_MUL] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[rp_ip_qf] THEN
    MP_TAC(ISPECL
     [`{i:num | i < n}`;
      `\i m. sum {j | j < n} (\j. (a:num->real) i * a j * (x i * x j) pow m)`;
      `\i. sum {j | j < n} (\j. (a:num->real) i * inv(&1 - x i * x j) * a j)`;
      `from 0`] RP_IP_SERIES_FINSUM) THEN
    REWRITE_TAC[FINITE_NUMSEG_LT] THEN ANTS_TAC THENL
     [ALL_TAC; SIMP_TAC[]] THEN
    X_GEN_TAC `i:num` THEN REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN
    MP_TAC(ISPECL
     [`{j:num | j < n}`;
      `\j m. (a:num->real) i * a j * (x i * x j) pow m`;
      `\j. (a:num->real) i * inv(&1 - x i * x j) * a j`;
      `from 0`] RP_IP_SERIES_FINSUM) THEN
    REWRITE_TAC[FINITE_NUMSEG_LT] THEN ANTS_TAC THENL
     [ALL_TAC; SIMP_TAC[]] THEN
    X_GEN_TAC `j:num` THEN REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN
    SUBGOAL_THEN `abs((x:num->real) i * x j) < &1` ASSUME_TAC THENL
     [MP_TAC(SPECL [`abs(x(i:num))`; `&1`; `abs(x(j:num))`; `&1`]
        REAL_LT_MUL2) THEN
      ASM_SIMP_TAC[REAL_ABS_POS; REAL_ABS_MUL; REAL_MUL_LID];
      ALL_TAC] THEN
    FIRST_ASSUM(MP_TAC o SPEC `(a:num->real) i * a j` o
      MATCH_MP REAL_SERIES_LMUL o MATCH_MP (SPEC `0` REAL_SUMS_GP)) THEN
    MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN BINOP_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM] THEN REAL_ARITH_TAC;
      REWRITE_TAC[real_pow; real_div] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `sum (0..n) f` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_SUBSET_SIMPLE THEN EXPAND_TAC "f" THEN BETA_TAC THEN
    REWRITE_TAC[FINITE_NUMSEG; REAL_LE_POW_2] THEN
    REWRITE_TAC[SUBSET; IN_NUMSEG; IN_ELIM_THM] THEN ARITH_TAC;
    FIRST_ASSUM(SUBST1_TAC o SYM o MATCH_MP REAL_INFSUM_UNIQUE) THEN
    MP_TAC(ISPECL [`f:num->real`; `from 0`; `n:num`]
      REAL_PARTIAL_SUMS_LE_INFSUM) THEN
    REWRITE_TAC[FROM_0; INTER_UNIV] THEN DISCH_THEN MATCH_MP_TAC THEN
    CONJ_TAC THENL
     [EXPAND_TAC "f" THEN REWRITE_TAC[REAL_LE_POW_2];
      REWRITE_TAC[GSYM FROM_0] THEN ASM_MESON_TAC[real_summable]]]);;

let RP_IP_GRAM_POS = prove
 (`forall n x a. (forall i. i < n ==> abs(x i) < &1) /\
           (forall i j. i < n /\ j < n /\ x i = x j ==> i = j) /\
           ~(forall i. i < n ==> a i = &0)
           ==> &0 < rp_ip_qf n (\i j. inv(&1 - x i * x j)) a`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LTE_TRANS THEN
  EXISTS_TAC
   `sum {m:num | m < n}
      (\m. sum {i:num | i < n} (\i. (a:num->real) i * (x:num->real) i pow m) pow 2)` THEN
  ASM_SIMP_TAC[RP_IP_GRAM_GE] THEN REWRITE_TAC[REAL_LT_LE] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_POS_LE THEN REWRITE_TAC[FINITE_NUMSEG_LT; REAL_LE_POW_2];
    ALL_TAC] THEN
  DISCH_THEN(ASSUME_TAC o SYM) THEN
  UNDISCH_TAC `~(forall i. i < n ==> (a:num->real) i = &0)` THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC RP_IP_VDM_KERNEL THEN EXISTS_TAC `x:num->real` THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL
   [`\m. sum {i | i < n} (\i. (a:num->real) i * x i pow m) pow 2`;
    `{m:num | m < n}`] SUM_POS_EQ_0) THEN
  ASM_REWRITE_TAC[FINITE_NUMSEG_LT; REAL_LE_POW_2; IN_ELIM_THM;
                  REAL_POW_EQ_0; ARITH_EQ]);;
