(* ========================================================================= *)
(* CAT_NONVANISHING, part C: structural lemmas for the certificate.          *)
(* ========================================================================= *)

needs "src/catalan_nv_cert_base.ml";;
needs "src/catalan_nv_det.ml";;

(* ------------------------------------------------------------------------- *)
(* Sums over numeral segments.                                               *)
(* ------------------------------------------------------------------------- *)

let NV_CERT_SUM_STEP = prove
 (`forall a n f. a <= n + 1 ==> sum(a..n + 1) f = sum(a..n) f + f(n + 1)`,
  SIMP_TAC[GSYM ADD1; SUM_CLAUSES_NUMSEG]);;

let NV_CERT_SUM_SKIP = prove
 (`forall f a n. (forall i. i < a ==> f i = &0) ==> sum(0..n) f = sum(a..n) f`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUM_SUPERSET THEN
  REWRITE_TAC[SUBSET; IN_NUMSEG] THEN CONJ_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC);;

(* numeral instances: |- !a f. a <= N ==> sum(a..N) f = sum(a..N-1) f + f N *)
let nv_cert_step_tab =
  Array.init 70 (fun n ->
    if n = 0 then TRUTH else
    CONV_RULE NUM_REDUCE_CONV (SPEC (nv_cert_mk_num (n - 1))
      (ONCE_REWRITE_RULE[SWAP_FORALL_THM] NV_CERT_SUM_STEP)));;

(* |- sum(0..n) f = f 0 + ... + f n (left associated, beta reduced) *)
let nv_cert_sum_expand n f =
  let rec go k =
    if k = 0 then
      CONV_RULE (RAND_CONV (TRY_CONV BETA_CONV))
        (ISPECL [f; `0`] SUM_SING_NUMSEG)
    else
      let th = ISPECL [`0`; f] nv_cert_step_tab.(k) in
      let th = MP th (nv_cert_arith (lhand(concl th))) in
      let th = CONV_RULE (RAND_CONV (RAND_CONV (TRY_CONV BETA_CONV))) th in
      TRANS th (AP_THM (AP_TERM `(+):real->real->real` (go (k - 1)))
                       (rand(rand(concl th)))) in
  go n;;

let NV_CERT_SUM4 = prove
 (`forall f. sum(0..4) f = f 0 + f 1 + f 2 + f 3 + f 4`,
  GEN_TAC THEN REWRITE_TAC[nv_cert_sum_expand 4 `f:num->real`] THEN
  REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Chebyshev coefficients.                                                   *)
(* ------------------------------------------------------------------------- *)

let NV_CERT_CHEB_T_ZERO = prove
 (`forall d k. d < k ==> cheb_T d k = &0`,
  SUBGOAL_THEN
   `forall d. (forall k. d < k ==> cheb_T d k = &0) /\ (forall k. SUC d < k ==> cheb_T (SUC d) k = &0)`
   (fun th -> MESON_TAC[th]) THEN
  INDUCT_TAC THENL
   [CONJ_TAC THEN REPEAT STRIP_TAC THEN REWRITE_TAC[cheb_T] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[LT_REFL; ARITH_RULE `~(SUC 0 < 1)`];
    POP_ASSUM STRIP_ASSUME_TAC THEN CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    X_GEN_TAC `k:num` THEN DISCH_TAC THEN REWRITE_TAC[cheb_T] THEN
    COND_CASES_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `SUC d < k - 1 /\ d < k` STRIP_ASSUME_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[] THEN REAL_ARITH_TAC]);;

let NV_CERT_CHEB_U_ZERO = prove
 (`forall d k. d < k ==> cheb_U d k = &0`,
  SUBGOAL_THEN
   `forall d. (forall k. d < k ==> cheb_U d k = &0) /\ (forall k. SUC d < k ==> cheb_U (SUC d) k = &0)`
   (fun th -> MESON_TAC[th]) THEN
  INDUCT_TAC THENL
   [CONJ_TAC THEN REPEAT STRIP_TAC THEN REWRITE_TAC[cheb_U] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[LT_REFL; ARITH_RULE `~(SUC 0 < 1)`];
    POP_ASSUM STRIP_ASSUME_TAC THEN CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    X_GEN_TAC `k:num` THEN DISCH_TAC THEN REWRITE_TAC[cheb_U] THEN
    COND_CASES_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `SUC d < k - 1 /\ d < k` STRIP_ASSUME_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[] THEN REAL_ARITH_TAC]);;

let NV_CERT_CHEB_T_STEP = prove
 (`forall d k. cheb_T (d + 2) k =
         (if k = 0 then &0 else &2 * cheb_T (d + 1) (k - 1)) - cheb_T d k`,
  REWRITE_TAC[ARITH_RULE `d + 2 = SUC(SUC d) /\ d + 1 = SUC d`; cheb_T]);;

let NV_CERT_CHEB_U_STEP = prove
 (`forall d k. cheb_U (d + 2) k =
         (if k = 0 then &0 else &2 * cheb_U (d + 1) (k - 1)) - cheb_U d k`,
  REWRITE_TAC[ARITH_RULE `d + 2 = SUC(SUC d) /\ d + 1 = SUC d`; cheb_U]);;

let NV_CERT_CHEB_T_01 = prove
 (`(forall k. cheb_T 0 k = if k = 0 then &1 else &0) /\
   (forall k. cheb_T 1 k = if k = 1 then &1 else &0)`,
  REWRITE_TAC[cheb_T; ONE]);;

let NV_CERT_CHEB_U_01 = prove
 (`(forall k. cheb_U 0 k = if k = 0 then &1 else &0) /\
   (forall k. cheb_U 1 k = if k = 1 then &2 else &0)`,
  REWRITE_TAC[cheb_U; ONE]);;

(* ------------------------------------------------------------------------- *)
(* Row coefficients at N = 1.                                                *)
(* ------------------------------------------------------------------------- *)

let NV_CERT_MULFAC2 = prove
 (`forall c i. cat_mulfac 2 c i =
         c i - (if i = 0 then &0 else &2 * c (i - 1)) +
         (if i <= 1 then &0 else c (i - 2))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[cat_mulfac] THEN
  REWRITE_TAC[nv_cert_sum_expand 2
    `\v. if v <= i then --(&1) pow v * &(binom(2,v)) * c(i - v) else &0`] THEN
  CONV_TAC(DEPTH_CONV NUM_BINOM_CONV) THEN REWRITE_TAC[LE_0; SUB_0] THEN
  ASM_CASES_TAC `i = 0` THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THENL
   [REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[ARITH_RULE `~(i = 0) ==> 1 <= i`] THEN
  ASM_CASES_TAC `i = 1` THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THENL
   [REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[ARITH_RULE `~(i = 0) /\ ~(i = 1) ==> 2 <= i /\ ~(i <= 1)`] THEN
  REAL_ARITH_TAC);;

let NV_CERT_REVC63 = prove
 (`forall c m. cat_revc 63 c m = if m < 63 then c (62 - m) else &0`,
  REWRITE_TAC[cat_revc; ARITH_RULE `63 - 1 - m = 62 - m`]);;

let NV_CERT_PCOEF = prove
 (`forall r i. cat_pcoef 1 r i = cat_mulfac 2 (cat_revc 63 (cheb_T (cat_dist 1 r))) i`,
  REWRITE_TAC[cat_pcoef] THEN CONV_TAC NUM_REDUCE_CONV);;

let NV_CERT_DCOEF = prove
 (`forall r i. cat_dcoef 1 r i =
         cat_sgn 1 r * cat_mulfac 2 (cat_revc 63 (cheb_U (cat_dist 1 r - 1))) i`,
  REWRITE_TAC[cat_dcoef] THEN CONV_TAC NUM_REDUCE_CONV);;

let NV_CERT_PVAN = prove
 (`forall r i. i + cat_dist 1 r < 62 ==> cat_pcoef 1 r i = &0`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[cat_pcoef; cat_mulfac] THEN
  MATCH_MP_TAC SUM_EQ_0_NUMSEG THEN X_GEN_TAC `v:num` THEN STRIP_TAC THEN
  REWRITE_TAC[] THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN
  REWRITE_TAC[cat_revc] THEN COND_CASES_TAC THEN REWRITE_TAC[REAL_MUL_RZERO] THEN
  SUBGOAL_THEN `cheb_T (cat_dist 1 r) (63 * 1 - 1 - (i - v)) = &0`
   (fun th -> REWRITE_TAC[th; REAL_MUL_RZERO]) THEN
  MATCH_MP_TAC NV_CERT_CHEB_T_ZERO THEN ASM_ARITH_TAC);;

let NV_CERT_DVAN = prove
 (`forall r i. i + cat_dist 1 r < 62 ==> cat_dcoef 1 r i = &0`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[cat_dcoef; cat_mulfac] THEN
  MATCH_MP_TAC(MESON[REAL_MUL_RZERO] `x = &0 ==> s * x = &0`) THEN
  MATCH_MP_TAC SUM_EQ_0_NUMSEG THEN X_GEN_TAC `v:num` THEN STRIP_TAC THEN
  REWRITE_TAC[] THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN
  REWRITE_TAC[cat_revc] THEN COND_CASES_TAC THEN REWRITE_TAC[REAL_MUL_RZERO] THEN
  SUBGOAL_THEN `cheb_U (cat_dist 1 r - 1) (63 * 1 - 1 - (i - v)) = &0`
   (fun th -> REWRITE_TAC[th; REAL_MUL_RZERO]) THEN
  MATCH_MP_TAC NV_CERT_CHEB_U_ZERO THEN ASM_ARITH_TAC);;

let NV_CERT_PSKIP = prove
 (`forall r a g. a + cat_dist 1 r <= 62
           ==> sum(0..65) (\i. cat_pcoef 1 r i * g i) =
               sum(a..65) (\i. cat_pcoef 1 r i * g i)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC NV_CERT_SUM_SKIP THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
  SUBGOAL_THEN `cat_pcoef 1 r i = &0` (fun th -> REWRITE_TAC[th; REAL_MUL_LZERO]) THEN
  MATCH_MP_TAC NV_CERT_PVAN THEN ASM_ARITH_TAC);;

let NV_CERT_DSKIP = prove
 (`forall r a g. a + cat_dist 1 r <= 62
           ==> sum(0..65) (\i. cat_dcoef 1 r i * g i) =
               sum(a..65) (\i. cat_dcoef 1 r i * g i)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC NV_CERT_SUM_SKIP THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
  SUBGOAL_THEN `cat_dcoef 1 r i = &0` (fun th -> REWRITE_TAC[th; REAL_MUL_LZERO]) THEN
  MATCH_MP_TAC NV_CERT_DVAN THEN ASM_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The filtered entries at N = 1, z = 0, as sums against filtered columns.   *)
(* ------------------------------------------------------------------------- *)

let nv_cert_mt = new_definition
 `nv_cert_mt k i =
    sum (0..4) (\v. (--(&1)) pow v * &(binom(4,v)) * cat_M0 i (7 + k + v))`;;

let nv_cert_zt = new_definition
 `nv_cert_zt k i =
    sum (0..4) (\v. (--(&1)) pow v * &(binom(4,v)) * cat_Z0 i (7 + k + v))`;;

let NV_CERT_SWAP = prove
 (`forall w P M. sum(0..4) (\v. w v * sum(0..65) (\i. P i * M i v)) =
           sum(0..65) (\i. P i * sum(0..4) (\v. w v * M i v))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM SUM_LMUL] THEN
  GEN_REWRITE_TAC LAND_CONV [SUM_SWAP_NUMSEG] THEN
  REWRITE_TAC[] THEN REWRITE_TAC[REAL_MUL_AC]);;

let NV_CERT_ENTRY = prove
 (`forall r k. cat_entryq (&0) 1 r k =
         sum(0..65) (\i. cat_pcoef 1 r i * nv_cert_mt k i) -
         &3 / &2 * sum(0..65) (\i. cat_dcoef 1 r i * nv_cert_zt k i)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[cat_entryq; cat_rawq] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[REAL_MUL_LZERO; REAL_MUL_RZERO; REAL_ADD_RID] THEN
  REWRITE_TAC[REAL_SUB_LDISTRIB; SUM_SUB_NUMSEG] THEN
  REWRITE_TAC[REAL_ARITH `a * b * (c * d:real) = c * (a * b) * d`; SUM_LMUL] THEN
  REWRITE_TAC[REAL_MUL_ASSOC] THEN
  MP_TAC(ISPECL [`\v. (--(&1)) pow v * &(binom(4,v))`; `cat_pcoef 1 r`;
                 `\i v. cat_M0 i (7 + k + v)`] NV_CERT_SWAP) THEN
  MP_TAC(ISPECL [`\v. (--(&1)) pow v * &(binom(4,v))`; `cat_dcoef 1 r`;
                 `\i v. cat_Z0 i (7 + k + v)`] NV_CERT_SWAP) THEN
  REWRITE_TAC[nv_cert_mt; nv_cert_zt; REAL_MUL_ASSOC] THEN
  REPEAT(DISCH_THEN SUBST1_TAC) THEN REFL_TAC);;

let NV_CERT_MT_EXP = prove
 (`forall k i. nv_cert_mt k i =
         cat_M0 i (k + 7) - &4 * cat_M0 i (k + 8) + &6 * cat_M0 i (k + 9) -
         &4 * cat_M0 i (k + 10) + cat_M0 i (k + 11)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[nv_cert_mt; NV_CERT_SUM4] THEN
  CONV_TAC(DEPTH_CONV NUM_BINOM_CONV) THEN
  REWRITE_TAC[ARITH_RULE `7 + k + 0 = k + 7 /\ 7 + k + 1 = k + 8 /\
    7 + k + 2 = k + 9 /\ 7 + k + 3 = k + 10 /\ 7 + k + 4 = k + 11`] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN REAL_ARITH_TAC);;

let NV_CERT_ZT_EXP = prove
 (`forall k i. nv_cert_zt k i =
         cat_Z0 i (k + 7) - &4 * cat_Z0 i (k + 8) + &6 * cat_Z0 i (k + 9) -
         &4 * cat_Z0 i (k + 10) + cat_Z0 i (k + 11)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[nv_cert_zt; NV_CERT_SUM4] THEN
  CONV_TAC(DEPTH_CONV NUM_BINOM_CONV) THEN
  REWRITE_TAC[ARITH_RULE `7 + k + 0 = k + 7 /\ 7 + k + 1 = k + 8 /\
    7 + k + 2 = k + 9 /\ 7 + k + 3 = k + 10 /\ 7 + k + 4 = k + 11`] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Recurrences for the moment arrays.                                        *)
(* ------------------------------------------------------------------------- *)

let NV_CERT_M0_I0 = prove
 (`forall i. cat_M0 i 0 = cat_kminus i`,
  REWRITE_TAC[cat_M0; LE_0; SUB_0; SUM_CLAUSES_NUMSEG; ARITH; REAL_SUB_RZERO]);;

let NV_CERT_M0_0J = prove
 (`forall j. cat_M0 0 j = cat_kplus j`,
  GEN_TAC THEN REWRITE_TAC[cat_M0; LE; SUB_0; SUM_CLAUSES_NUMSEG; ARITH; REAL_SUB_RZERO] THEN
  COND_CASES_TAC THEN
  ASM_REWRITE_TAC[cat_kminus; cat_kplus; SUB_0; SUM_CLAUSES_NUMSEG; ARITH; REAL_SUB_RZERO]);;

let NV_CERT_M0_REC = prove
 (`forall i j. cat_M0 (i + 1) (j + 1) = cat_M0 i j - cat_m i * inv(&(j + 1))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[cat_M0; LE_ADD_RCANCEL; ARITH_RULE `(i + 1) - (j + 1) = i - j`] THEN
  COND_CASES_TAC THEN REWRITE_TAC[ARITH_RULE `(j + 1) - (i + 1) = j - i`] THEN
  REWRITE_TAC[GSYM ADD1; SUM_CLAUSES_NUMSEG; ARITH_RULE `1 <= SUC n`] THENL
   [SUBGOAL_THEN `i - j + SUC j - 1 = i` SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC];
    SUBGOAL_THEN `j - i + SUC i = SUC j` SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[SUC_SUB1]] THEN
  REWRITE_TAC[real_div] THEN REAL_ARITH_TAC);;

let NV_CERT_KM_STEP = prove
 (`forall d. cat_kminus (d + 2) =
       (&(d + 1) * cat_kminus d + cat_m d + cat_m (d + 1)) * inv(&(d + 2))`,
  REWRITE_TAC[ARITH_RULE `d + 2 = SUC(SUC d)`; cat_kminus; real_div]);;

let NV_CERT_KP_STEP = prove
 (`forall d. cat_kplus (d + 2) =
       (&d * cat_kplus d + &2 * inv(&(d + 1))) * inv(&(d + 1))`,
  REWRITE_TAC[ARITH_RULE `d + 2 = SUC(SUC d)`; cat_kplus; real_div]);;

let NV_CERT_K01 = prove
 (`cat_kminus 0 = &0 /\ cat_kminus 1 = &2 /\ cat_kplus 0 = &0 /\ cat_kplus 1 = &0`,
  REWRITE_TAC[cat_kminus; cat_kplus; ONE]);;

let NV_CERT_HARM_0 = prove
 (`forall d. cat_harm d 0 = &0`,
  REWRITE_TAC[cat_harm; SUM_CLAUSES_NUMSEG; ARITH]);;

let NV_CERT_HARM_STEP = prove
 (`forall d n. cat_harm d (n + 1) = cat_harm d n + inv(&(n + 1) pow d)`,
  REWRITE_TAC[cat_harm; GSYM ADD1; SUM_CLAUSES_NUMSEG; ARITH_RULE `1 <= SUC n`;
              real_div; REAL_MUL_LID]);;

let NV_CERT_Z0_EQ = prove
 (`forall i. cat_Z0 i i = --(cat_harm 2 i)`,
  REWRITE_TAC[cat_Z0]);;

let NV_CERT_Z0_NE = prove
 (`forall i j. ~(i = j) ==> cat_Z0 i j = (cat_harm 1 i - cat_harm 1 j) * inv(&i - &j)`,
  SIMP_TAC[cat_Z0; real_div]);;

let NV_CERT_M_EVEN = prove
 (`forall i. cat_m i = if EVEN i then &2 * inv(&(i + 1) * (&(binom(2 * (i DIV 2),i DIV 2)) / &4 pow (i DIV 2)))
                 else &0`,
  REWRITE_TAC[cat_m; cat_c; real_div]);;

(* ------------------------------------------------------------------------- *)
(* The final determinant argument.                                           *)
(* ------------------------------------------------------------------------- *)

let NV_CERT_NOT_CONG_01 = prove
 (`~(nv_cong 101 (&0) (&1))`,
  REWRITE_TAC[nv_cong] THEN
  SUBGOAL_THEN `(&0 - &1) / &101 = --(inv(&101))` SUBST1_TAC THENL
   [CONV_TAC REAL_FIELD; ALL_TAC] THEN
  REWRITE_TAC[NV_PINT_NEG_EQ] THEN
  MATCH_ACCEPT_TAC(MATCH_MP NV_PINT_INV_P NV_CERT_PRIME));;

let NV_CERT_FINAL = prove
 (`forall A (X:num->num->num).
     (forall i. i <= 47 ==> forall j. j <= 47 ==>
            nv_cong 101 (sum (0..47) (\k. &(X i k) * A k j)) (&(if i = j then 1 else 0)))
     ==> ~(ndet (0..47) A = &0)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`101`; `0..47`;
     `\i j. sum (0..47) (\k. &((X:num->num->num) i k) * (A:num->num->real) k j)`;
     `\i j. if (i:num) = j then &1 else &0`] NV_NDET_CONG) THEN
  REWRITE_TAC[NV_CERT_PRIME; FINITE_NUMSEG; IN_NUMSEG; LE_0] THEN
  MATCH_MP_TAC(TAUT `p /\ (q ==> false) ==> ~(p ==> q)`) THEN CONJ_TAC THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPEC `j:num`) THEN ASM_REWRITE_TAC[] THEN
    COND_CASES_TAC THEN REWRITE_TAC[NV_CERT_PINT_NUM];
    ALL_TAC] THEN
  REWRITE_TAC[NV_DET_NDET] THEN
  MP_TAC(ISPECL [`0..47`; `\i k. &((X:num->num->num) i k)`; `A:num->num->real`]
    NV_DET_MUL) THEN
  REWRITE_TAC[FINITE_NUMSEG] THEN DISCH_THEN SUBST1_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[NV_DET_NDET]) THEN ASM_REWRITE_TAC[REAL_MUL_RZERO] THEN
  SIMP_TAC[NV_DET_ID; FINITE_NUMSEG; NV_CERT_NOT_CONG_01]);;

(* forall over 0..n built from instances *)
let NV_CERT_FA0 = prove
 (`forall P. P 0 ==> forall i. i <= 0 ==> P i`,
  REWRITE_TAC[LE] THEN MESON_TAC[]);;

let NV_CERT_FAS = prove
 (`forall P n. (forall i. i <= n ==> P i) ==> P (n + 1) ==> forall i. i <= n + 1 ==> P i`,
  REWRITE_TAC[GSYM ADD1; LE] THEN MESON_TAC[]);;

let nv_cert_fas_tab =
  Array.init 70 (fun n ->
    if n = 0 then SPEC_ALL NV_CERT_FA0 else
    CONV_RULE NUM_REDUCE_CONV (INST [nv_cert_mk_num (n - 1),`n:num`]
      (SPEC_ALL NV_CERT_FAS)));;

(* given lambda p = \i. body and ths.(k) : |- body[k/i] for k = 0..n,
   produce |- !i. i <= n ==> body *)
let nv_cert_forall p ths =
  let n = Array.length ths - 1 in
  let pv = `P:num->bool` in
  let rec go k =
    let th = BETA_RULE (INST [p,pv] nv_cert_fas_tab.(k)) in
    if k = 0 then MP th ths.(0)
    else MP (MP th (go (k - 1))) ths.(k) in
  go n;;
