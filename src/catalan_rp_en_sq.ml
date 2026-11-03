(* ========================================================================= *)
(* EN part: negative-square identities (86), (87) in series form, trial     *)
(* completion -a^2 <= b^2 - 2ab, damped trial series.                        *)
(* ========================================================================= *)

needs "src/catalan_rp_en_base.ml";;
needs "src/catalan_rp_en_ker.ml";;
needs "src/catalan_rp_en_dmp.ml";;

(* damped trial series T_eps(p,x), S_eps(v,x), T_eps(v,s) *)
let rp_en_Te = new_definition
 `rp_en_Te (p:num->real) e x =
    real_infsum (from 1) (\k. p k * ((&1 - e) pow k * rp_cheb k x) / &k)`;;

let rp_en_Se = new_definition
 `rp_en_Se (v:num->real) e x =
    real_infsum (from 1) (\k. v k * (rp_en_rho e x * x) pow k / &k)`;;

let rp_en_Ts = new_definition
 `rp_en_Ts (v:num->real) e s =
    real_infsum (from 1) (\k. v k * (rp_en_sig e s pow k * rp_cheb k s) / &k)`;;

(* ------------------------------------------------------------------------- *)
(* Generic square / product series over finite families.                     *)
(* ------------------------------------------------------------------------- *)

let RP_EN_SUM_SQ = prove
 (`forall (a:num->real) n.
     sum {i | i < n} a pow 2 =
     sum {i | i < n} (\i. sum {j | j < n} (\j. a i * a j))`,
  REWRITE_TAC[REAL_POW_2; GSYM SUM_LMUL; GSYM SUM_RMUL]);;

let RP_EN_SUM_PROD = prove
 (`forall (a:num->real) (b:num->real) n.
     sum {i | i < n} a * sum {j | j < n} b =
     sum {i | i < n} (\i. sum {j | j < n} (\j. a i * b j))`,
  REWRITE_TAC[GSYM SUM_LMUL; GSYM SUM_RMUL]);;

let RP_EN_GEN_SQ = prove
 (`forall (a:num->num->real) K n.
     (forall i j. i < n /\ j < n ==> ((\k. a i k * a j k / &k) real_sums K i j) (from 1))
     ==> ((\k. sum {i | i < n} (\i. a i k) pow 2 / &k) real_sums
          sum {i | i < n} (\i. sum {j | j < n} (\j. K i j))) (from 1)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `forall k. sum {i | i < n} (\i. (a:num->num->real) i k) pow 2 / &k =
        sum {i | i < n} (\i. sum {j | j < n} (\j. a i k * a j k / &k))`
   (fun th -> REWRITE_TAC[th])
  THENL
   [GEN_TAC THEN REWRITE_TAC[RP_EN_SUM_SQ; real_div; GSYM SUM_RMUL; REAL_MUL_ASSOC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\i m. sum {j | j < n} (\j. (a:num->num->real) i m * a j m / &m)`;
                 `\i. sum {j | j < n} (\j. (K:num->num->real) i j)`; `from 1`; `n:num`]
         RP_EN_SERIES_FINSUM_LT) THEN
  REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\j m. (a:num->num->real) i m * a j m / &m`;
                 `\j. (K:num->num->real) i j`; `from 1`; `n:num`]
         RP_EN_SERIES_FINSUM_LT) THEN
  REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC[ETA_AX]);;

let RP_EN_GEN_CROSS = prove
 (`forall (b:num->num->real) (c:num->num->real) K n.
     (forall i j. i < n /\ j < n ==> ((\k. b i k * c j k / &k) real_sums K i j) (from 1))
     ==> ((\k. sum {i | i < n} (\i. b i k) * sum {j | j < n} (\j. c j k) / &k)
          real_sums
          sum {i | i < n} (\i. sum {j | j < n} (\j. K i j))) (from 1)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `forall k. sum {i | i < n} (\i. (b:num->num->real) i k) *
        sum {j | j < n} (\j. (c:num->num->real) j k) / &k =
        sum {i | i < n} (\i. sum {j | j < n} (\j. b i k * c j k / &k))`
   (fun th -> REWRITE_TAC[th])
  THENL
   [GEN_TAC THEN REWRITE_TAC[real_div; REAL_MUL_ASSOC] THEN
    REWRITE_TAC[RP_EN_SUM_PROD] THEN REWRITE_TAC[GSYM SUM_RMUL];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\i m. sum {j | j < n} (\j. (b:num->num->real) i m * (c:num->num->real) j m / &m)`;
                 `\i. sum {j | j < n} (\j. (K:num->num->real) i j)`; `from 1`; `n:num`]
         RP_EN_SERIES_FINSUM_LT) THEN
  REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\j m. (b:num->num->real) i m * (c:num->num->real) j m / &m`;
                 `\j. (K:num->num->real) i j`; `from 1`; `n:num`]
         RP_EN_SERIES_FINSUM_LT) THEN
  REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC[ETA_AX]);;

(* ------------------------------------------------------------------------- *)
(* Trial sequences.                                                          *)
(* ------------------------------------------------------------------------- *)

let RP_EN_NSQ_SUMMABLE = prove
 (`forall u. rp_summable u ==> real_summable (from 1) (\k. u k pow 2 / &k)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`u:num->real`; `u:num->real`;
                 `real_infsum (from 1) (\k. abs((u:num->real) k))`] RP_EN_WSERIES) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[RP_EN_ABS_LE_INFSUM]; ALL_TAC] THEN
  SIMP_TAC[REAL_POW_2; real_div; REAL_MUL_ASSOC]);;

let RP_EN_NSQ_SUMS = prove
 (`forall u. rp_summable u ==> ((\k. u k pow 2 / &k) real_sums rp_nsq u) (from 1)`,
  SIMP_TAC[rp_nsq; REAL_SUMS_INFSUM; RP_EN_NSQ_SUMMABLE]);;

let RP_EN_WSUMS = prove
 (`forall u c. rp_summable u /\ (forall k. 1 <= k ==> abs(c k) <= &1)
         ==> ((\k. u k * c k / &k) real_sums
              real_infsum (from 1) (\k. u k * c k / &k)) (from 1)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[REAL_SUMS_INFSUM] THEN
  MP_TAC(ISPECL [`u:num->real`; `c:num->real`; `&1`] RP_EN_WSERIES) THEN
  ASM_SIMP_TAC[]);;

let RP_EN_TRIALSUM = prove
 (`forall (u:num->real) (c:num->num->real) n.
     rp_summable u /\ (forall i k. i < n /\ 1 <= k ==> abs(c i k) <= &1)
     ==> ((\k. u k * sum {i | i < n} (\i. c i k) / &k) real_sums
          sum {i | i < n} (\i. real_infsum (from 1) (\k. u k * c i k / &k))) (from 1)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `forall k. (u:num->real) k * sum {i | i < n} (\i. (c:num->num->real) i k) / &k =
        sum {i | i < n} (\i. u k * c i k / &k)`
   (fun th -> REWRITE_TAC[th])
  THENL
   [GEN_TAC THEN REWRITE_TAC[real_div; GSYM SUM_LMUL; GSYM SUM_RMUL] THEN
    MATCH_MP_TAC SUM_EQ THEN REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\i k. (u:num->real) k * (c:num->num->real) i k / &k`;
                 `\i. real_infsum (from 1) (\k. (u:num->real) k * (c:num->num->real) i k / &k)`;
                 `from 1`; `n:num`]
         RP_EN_SERIES_FINSUM_LT) THEN
  REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`u:num->real`; `\k. (c:num->num->real) i k`] RP_EN_WSUMS) THEN
  ASM_SIMP_TAC[]);;

(* -a^2 <= b^2 - 2ab in series form *)
let RP_EN_TRIAL1 = prove
 (`forall (a:num->real) p Q R m.
     ((\k. a k pow 2 / &k) real_sums Q) (from 1) /\
     ((\k. p k * a k / &k) real_sums R) (from 1) /\
     rp_summable p
     ==> --Q <= m pow 2 * rp_nsq p - &2 * m * R`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(REAL_ARITH `&0 <= m pow 2 * N - &2 * m * R + Q ==> --Q <= m pow 2 * N - &2 * m * R`) THEN
  MATCH_MP_TAC REAL_SERIES_POS THEN
  EXISTS_TAC `\k. (a k - m * (p:num->real) k) pow 2 / &k` THEN
  EXISTS_TAC `from 1` THEN CONJ_TAC THENL
   [SUBGOAL_THEN `forall k. (a k - m * (p:num->real) k) pow 2 / &k =
                      (m pow 2 * (p k pow 2 / &k) - &2 * m * (p k * a k / &k)) + a k pow 2 / &k`
     (fun th -> REWRITE_TAC[th]) THENL
     [GEN_TAC THEN REWRITE_TAC[real_div] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_SERIES_ADD THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_SERIES_SUB THEN CONJ_TAC THEN
    REPEAT(MATCH_MP_TAC REAL_SERIES_LMUL) THEN ASM_SIMP_TAC[RP_EN_NSQ_SUMS];
    REWRITE_TAC[IN_FROM] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC REAL_LE_DIV THEN REWRITE_TAC[REAL_POS; REAL_LE_POW_2]]);;

(* -(1/2)(b - 2c)^2 <= (1/2) v^2 - v (b - 2c) in series form *)
let RP_EN_TRIAL2 = prove
 (`forall (b:num->real) (c:num->real) v Qb Qc Qbc Rb Rc m.
     ((\k. b k pow 2 / &k) real_sums Qb) (from 1) /\
     ((\k. c k pow 2 / &k) real_sums Qc) (from 1) /\
     ((\k. b k * c k / &k) real_sums Qbc) (from 1) /\
     ((\k. v k * b k / &k) real_sums Rb) (from 1) /\
     ((\k. v k * c k / &k) real_sums Rc) (from 1) /\
     rp_summable v
     ==> --(Qb / &2) - &2 * Qc + &2 * Qbc <=
         m pow 2 * rp_nsq v / &2 - m * Rb + &2 * m * Rc`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(REAL_ARITH
   `&0 <= ((m pow 2 * N - &2 * m * Rb + &4 * m * Rc) + Qb + &4 * Qc - &4 * Qbc) / &2
    ==> --(Qb / &2) - &2 * Qc + &2 * Qbc <= m pow 2 * N / &2 - m * Rb + &2 * m * Rc`) THEN
  MATCH_MP_TAC REAL_SERIES_POS THEN
  EXISTS_TAC `\k. ((b k - &2 * c k) - m * (v:num->real) k) pow 2 / &k / &2` THEN
  EXISTS_TAC `from 1` THEN CONJ_TAC THENL
   [SUBGOAL_THEN `forall k. ((b k - &2 * c k) - m * (v:num->real) k) pow 2 / &k / &2 =
          (((m pow 2 * (v k pow 2 / &k) - &2 * m * (v k * b k / &k)) +
            &4 * m * (v k * c k / &k)) + b k pow 2 / &k + &4 * (c k pow 2 / &k) -
           &4 * (b k * c k / &k)) / &2`
     (fun th -> REWRITE_TAC[th]) THENL
     [GEN_TAC THEN REWRITE_TAC[real_div] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[real_div] THEN MATCH_MP_TAC REAL_SERIES_RMUL THEN
    REWRITE_TAC[GSYM real_div] THEN
    REPEAT((MATCH_MP_TAC REAL_SERIES_ADD ORELSE MATCH_MP_TAC REAL_SERIES_SUB) THEN
           CONJ_TAC) THEN
    REPEAT(MATCH_MP_TAC REAL_SERIES_LMUL) THEN ASM_SIMP_TAC[RP_EN_NSQ_SUMS];
    REWRITE_TAC[IN_FROM] THEN REPEAT STRIP_TAC THEN
    REPEAT(MATCH_MP_TAC REAL_LE_DIV THEN CONJ_TAC) THEN
    REWRITE_TAC[REAL_POS; REAL_LE_POW_2]]);;

(* ------------------------------------------------------------------------- *)
(* Damped versus undamped trial series.                                      *)
(* ------------------------------------------------------------------------- *)

let RP_EN_MUL_LE1 = prove
 (`forall a b. &0 <= a /\ a <= &1 /\ &0 <= b /\ b <= &1 ==> a * b <= &1`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(REAL_ARITH `a * b <= &1 * &1 ==> a * b <= &1`) THEN
  MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[]);;

let RP_EN_BERN = prove
 (`forall r k. &0 <= r /\ r <= &1
         ==> &0 <= r pow k /\ r pow k <= &1 /\ &1 - r pow k <= &k * (&1 - r)`,
  GEN_TAC THEN REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN DISCH_TAC THEN
  INDUCT_TAC THEN REWRITE_TAC[real_pow; GSYM REAL_OF_NUM_SUC] THENL
   [REAL_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM STRIP_ASSUME_TAC THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC RP_EN_MUL_LE1 THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC(REAL_ARITH
     `r * q <= q /\ &1 - q <= k * (&1 - r) /\ q - r * q <= &1 - r
      ==> &1 - r * q <= (k + &1) * (&1 - r)`) THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[REAL_ARITH `q - r * q = (&1 - r) * q`] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `&0 <= (&1 - r) * q ==> r * q <= q`) THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC(REAL_ARITH `x * q <= x * &1 ==> x * q <= x`) THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC]]);;

let RP_EN_DIV_SUB = prove
 (`forall u d c k:real. u * d / k - u * c / k = u * (d - c) / k`,
  REWRITE_TAC[real_div] THEN REAL_ARITH_TAC);;

let RP_EN_DAMP_GEN = prove
 (`forall (u:num->real) c d D.
     rp_summable u /\ (forall k. 1 <= k ==> abs(c k) <= &1) /\
     (forall k. 1 <= k ==> abs(d k) <= &1) /\
     (forall k. 1 <= k ==> abs(d k - c k) <= &k * D)
     ==> abs(real_infsum (from 1) (\k. u k * d k / &k) -
             real_infsum (from 1) (\k. u k * c k / &k)) <=
         D * real_infsum (from 1) (\k. abs(u k))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`u:num->real`; `c:num->real`] RP_EN_WSUMS) THEN
  MP_TAC(ISPECL [`u:num->real`; `d:num->real`] RP_EN_WSUMS) THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
  MATCH_MP_TAC REAL_SERIES_BOUND THEN
  EXISTS_TAC `\k. (u:num->real) k * d k / &k - u k * c k / &k` THEN
  EXISTS_TAC `\k. D * abs((u:num->real) k)` THEN EXISTS_TAC `from 1` THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC REAL_SERIES_SUB THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC REAL_SERIES_LMUL THEN
    RULE_ASSUM_TAC(REWRITE_RULE[rp_summable]) THEN
    ASM_SIMP_TAC[REAL_SUMS_INFSUM];
    REWRITE_TAC[IN_FROM] THEN X_GEN_TAC `k:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `&0 < &k` ASSUME_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[RP_EN_DIV_SUB] THEN
    REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_DIV; REAL_ABS_NUM] THEN
    MATCH_MP_TAC(REAL_ARITH `a * b <= a * D ==> a * b <= D * a:real`) THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_ABS_POS] THEN
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
    ASM_SIMP_TAC[]]);;

let RP_EN_TSER_BOUND = prove
 (`forall u x. rp_summable u /\ abs x <= &1
         ==> abs(rp_Tser u x) <= real_infsum (from 1) (\k. abs(u k))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[rp_Tser] THEN
  MP_TAC(ISPECL [`u:num->real`; `\k. rp_cheb k x`; `&1`] RP_EN_WSERIES) THEN
  ASM_SIMP_TAC[RP_EN_KER_CHEB_BOUND; REAL_MUL_LID]);;

let RP_EN_SSER_BOUND = prove
 (`forall u x. rp_summable u /\ abs x <= &1
         ==> abs(rp_Sser u x) <= real_infsum (from 1) (\k. abs(u k))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[rp_Sser] THEN
  MP_TAC(ISPECL [`u:num->real`; `\k. (x:real) pow k`; `&1`] RP_EN_WSERIES) THEN
  ASM_SIMP_TAC[REAL_ABS_POW; REAL_POW_1_LE; REAL_ABS_POS; REAL_MUL_LID]);;

let RP_EN_TE_CLOSE = prove
 (`forall p e x. rp_summable p /\ &0 < e /\ e < &1 /\ abs x <= &1
           ==> abs(rp_en_Te p e x - rp_Tser p x) <=
               e * real_infsum (from 1) (\k. abs(p k))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[rp_en_Te; rp_Tser] THEN
  SUBGOAL_THEN `forall k. 1 <= k ==> abs((&1 - e) pow k * rp_cheb k x) <= &1 /\
                   abs((&1 - e) pow k * rp_cheb k x - rp_cheb k x) <= &k * e`
  MP_TAC THENL [ALL_TAC;
    DISCH_TAC THEN MATCH_MP_TAC RP_EN_DAMP_GEN THEN
    ASM_SIMP_TAC[RP_EN_KER_CHEB_BOUND]] THEN
  X_GEN_TAC `k:num` THEN DISCH_TAC THEN
  MP_TAC(SPECL [`&1 - e`; `k:num`] RP_EN_BERN) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  MP_TAC(SPECL [`k:num`; `x:real`] RP_EN_KER_CHEB_BOUND) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN CONJ_TAC THENL
   [REWRITE_TAC[REAL_ABS_MUL] THEN MATCH_MP_TAC RP_EN_MUL_LE1 THEN
    ASM_REWRITE_TAC[REAL_ABS_POS] THEN ASM_REAL_ARITH_TAC;
    REWRITE_TAC[REAL_ARITH `q * c - c = --((&1 - q) * c)`; REAL_ABS_NEG] THEN
    REWRITE_TAC[REAL_ABS_MUL] THEN
    MATCH_MP_TAC(REAL_ARITH `a * b <= a * &1 /\ a <= c ==> a * b <= c`) THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_ABS_POS];
      ASM_REAL_ARITH_TAC]]);;

let RP_EN_TS_CLOSE = prove
 (`forall v e s. rp_summable v /\ &0 < e /\ e < &1 / &8 /\ &0 < s /\ s < &1
           ==> abs(rp_en_Ts v e s - rp_Tser v s) <=
               e * real_infsum (from 1) (\k. abs(v k))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[rp_en_Ts; rp_Tser] THEN
  MP_TAC(SPEC `s:real` RP_EN_DMP_SQRT_ONE_SUB) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `abs s <= &1` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `forall k. 1 <= k ==> abs(rp_en_sig e s pow k * rp_cheb k s) <= &1 /\
                   abs(rp_en_sig e s pow k * rp_cheb k s - rp_cheb k s) <= &k * e`
  MP_TAC THENL [ALL_TAC;
    DISCH_TAC THEN MATCH_MP_TAC RP_EN_DAMP_GEN THEN
    ASM_SIMP_TAC[RP_EN_KER_CHEB_BOUND]] THEN
  X_GEN_TAC `k:num` THEN DISCH_TAC THEN
  MP_TAC(SPECL [`rp_en_sig e s`; `k:num`] RP_EN_BERN) THEN
  REWRITE_TAC[rp_en_sig] THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `e * q <= e * &1 /\ e < &1 ==> &0 <= &1 - e * q`) THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
      MATCH_MP_TAC(REAL_ARITH `&0 <= e * q ==> &1 - e * q <= &1`) THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC];
    STRIP_TAC] THEN
  MP_TAC(SPECL [`k:num`; `s:real`] RP_EN_KER_CHEB_BOUND) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN CONJ_TAC THENL
   [REWRITE_TAC[REAL_ABS_MUL] THEN MATCH_MP_TAC RP_EN_MUL_LE1 THEN
    ASM_REWRITE_TAC[REAL_ABS_POS] THEN ASM_REAL_ARITH_TAC;
    REWRITE_TAC[REAL_ARITH `q * c - c = --((&1 - q) * c)`; REAL_ABS_NEG] THEN
    REWRITE_TAC[REAL_ABS_MUL] THEN
    MATCH_MP_TAC(REAL_ARITH `a * b <= a * &1 /\ a <= c ==> a * b <= c`) THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_ABS_POS];
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `&k * (&1 - (&1 - e * sqrt(&1 - s)))` THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[REAL_ARITH `&1 - (&1 - e * q) = e * q`] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
      MATCH_MP_TAC(REAL_ARITH `e * q <= e * &1 ==> e * q <= e`) THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC]]);;

let RP_EN_SE_CLOSE = prove
 (`forall v e x. rp_summable v /\ &0 < e /\ e < &1 / &8 /\ --(&1) < x /\ x < &1
           ==> abs(rp_en_Se v e x - rp_Sser v x) <=
               (&2 * e) * real_infsum (from 1) (\k. abs(v k))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[rp_en_Se; rp_Sser] THEN
  MP_TAC(SPECL [`e:real`; `x:real`] RP_EN_DMP_RHO_BOUNDS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `abs x <= &1` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `forall k. 1 <= k ==> abs((x:real) pow k) <= &1 /\
                   abs((rp_en_rho e x * x) pow k) <= &1 /\
                   abs((rp_en_rho e x * x) pow k - x pow k) <= &k * (&2 * e)`
  MP_TAC THENL [ALL_TAC;
    DISCH_TAC THEN MATCH_MP_TAC RP_EN_DAMP_GEN THEN ASM_SIMP_TAC[]] THEN
  X_GEN_TAC `k:num` THEN DISCH_TAC THEN
  MP_TAC(SPECL [`rp_en_rho e x`; `k:num`] RP_EN_BERN) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  SUBGOAL_THEN `abs((x:real) pow k) <= &1` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_ABS_POW; REAL_POW_1_LE; REAL_ABS_POS]; ALL_TAC] THEN
  REWRITE_TAC[REAL_POW_MUL] THEN REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    REWRITE_TAC[REAL_ABS_MUL] THEN MATCH_MP_TAC RP_EN_MUL_LE1 THEN
    ASM_REWRITE_TAC[REAL_ABS_POS] THEN ASM_REAL_ARITH_TAC;
    REWRITE_TAC[REAL_ARITH `q * c - c = --((&1 - q) * c)`; REAL_ABS_NEG] THEN
    REWRITE_TAC[REAL_ABS_MUL] THEN
    MATCH_MP_TAC(REAL_ARITH `a * b <= a * &1 /\ a <= c ==> a * b <= c`) THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_ABS_POS];
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `&k * (&1 - rp_en_rho e x)` THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
      ASM_REAL_ARITH_TAC]]);;
