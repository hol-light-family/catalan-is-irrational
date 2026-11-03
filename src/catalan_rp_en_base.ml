(* ========================================================================= *)
(* EN part: basic finite-sum and series helpers.                             *)
(* ========================================================================= *)

needs "src/catalan_rp_en_defs.ml";;

(* canonical name for {i | i < n}, used to normalise set abstractions      *)
(* (alpha-variants of GSPEC terms confuse REAL_ARITH)                       *)
let rp_en_lt = new_definition
 `rp_en_lt n = {i:num | i < n}`;;

let RP_EN_NUMSEG_LT_SUC = prove
 (`forall n. {i | i < SUC n} = n INSERT {i | i < n}`,
  REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_INSERT] THEN ARITH_TAC);;

let RP_EN_SUM_LT_SUC = prove
 (`forall f n. sum {i | i < SUC n} f = sum {i | i < n} f + f n`,
  REPEAT GEN_TAC THEN REWRITE_TAC[RP_EN_NUMSEG_LT_SUC] THEN
  SIMP_TAC[SUM_CLAUSES; FINITE_NUMSEG_LT; IN_ELIM_THM; LT_REFL] THEN
  MATCH_ACCEPT_TAC REAL_ADD_SYM);;

let RP_EN_SUM_LT_0 = prove
 (`forall f. sum {i | i < 0} f = &0`,
  REWRITE_TAC[LT; EMPTY_GSPEC; SUM_CLAUSES]);;

let RP_EN_PSUM_0 = prove
 (`forall f. rp_en_psum 0 f = &0`,
  REWRITE_TAC[rp_en_psum; RP_EN_SUM_LT_0]);;

let RP_EN_PSUM_SUC = prove
 (`forall f n. rp_en_psum (SUC n) f = rp_en_psum n f + sum {i | i < n} (\i. f i n)`,
  REWRITE_TAC[rp_en_psum; RP_EN_SUM_LT_SUC]);;

let RP_EN_PSUM_SYM = prove
 (`forall f n. (forall i j. f i j = f j i)
         ==> sum {i | i < n} (\i. sum {j | j < n} (\j. f i j)) =
             &2 * rp_en_psum n f + sum {i | i < n} (\i. f i i)`,
  GEN_TAC THEN REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN DISCH_TAC THEN
  INDUCT_TAC THEN
  REWRITE_TAC[RP_EN_SUM_LT_0; RP_EN_PSUM_0; RP_EN_PSUM_SUC; RP_EN_SUM_LT_SUC] THENL
   [REAL_ARITH_TAC; ALL_TAC] THEN
  SIMP_TAC[SUM_ADD; FINITE_NUMSEG_LT] THEN
  SUBGOAL_THEN `sum {i | i < n} (\j. (f:num->num->real) n j) =
                sum {i | i < n} (\i. f i n)` SUBST1_TAC THENL
   [MATCH_MP_TAC SUM_EQ THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[GSYM rp_en_lt] THEN
  FIRST_X_ASSUM(MP_TAC o check (is_eq o concl)) THEN
  REWRITE_TAC[GSYM rp_en_lt] THEN REAL_ARITH_TAC);;

let RP_EN_PSUM_ADD = prove
 (`forall f g n. rp_en_psum n (\i j. f i j + g i j) =
           rp_en_psum n f + rp_en_psum n g`,
  REWRITE_TAC[rp_en_psum] THEN
  SIMP_TAC[SUM_ADD; FINITE_NUMSEG_LT] THEN REWRITE_TAC[ETA_AX]);;

let RP_EN_PSUM_SUB = prove
 (`forall f g n. rp_en_psum n (\i j. f i j - g i j) =
           rp_en_psum n f - rp_en_psum n g`,
  REWRITE_TAC[rp_en_psum] THEN
  SIMP_TAC[SUM_SUB; FINITE_NUMSEG_LT] THEN REWRITE_TAC[ETA_AX]);;

let RP_EN_PSUM_LMUL = prove
 (`forall c f n. rp_en_psum n (\i j. c * f i j) = c * rp_en_psum n f`,
  REWRITE_TAC[rp_en_psum; SUM_LMUL] THEN REWRITE_TAC[ETA_AX]);;

let RP_EN_PSUM_LE = prove
 (`forall f g n. (forall i j. i < j /\ j < n ==> f i j <= g i j)
           ==> rp_en_psum n f <= rp_en_psum n g`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[rp_en_psum] THEN
  MATCH_MP_TAC SUM_LE THEN REWRITE_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUM_LE THEN
  REWRITE_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM] THEN ASM_MESON_TAC[]);;

let RP_EN_PSUM_CONST = prove
 (`forall c n. rp_en_psum n (\i j. c) = &n * (&n - &1) / &2 * c`,
  GEN_TAC THEN INDUCT_TAC THEN
  REWRITE_TAC[RP_EN_PSUM_0; RP_EN_PSUM_SUC] THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[SUM_CONST; FINITE_NUMSEG_LT; CARD_NUMSEG_LT; GSYM REAL_OF_NUM_SUC] THEN
  REAL_ARITH_TAC);;

(* finite sums of series *)
let RP_EN_SERIES_FINSUM = prove
 (`forall (f:A->num->real) l k s.
      FINITE s /\ (forall i. i IN s ==> ((f i) real_sums (l i)) k)
      ==> ((\n. sum s (\i. f i n)) real_sums (sum s l)) k`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[SUM_CLAUSES; REAL_SERIES_0; IN_INSERT] THEN
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC REAL_SERIES_ADD THEN REWRITE_TAC[ETA_AX] THEN ASM_MESON_TAC[]);;

let RP_EN_SERIES_FINSUM_LT = prove
 (`forall (f:num->num->real) l k n.
      (forall i. i < n ==> ((f i) real_sums (l i)) k)
      ==> ((\m. sum {i | i < n} (\i. f i m)) real_sums (sum {i | i < n} l)) k`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC RP_EN_SERIES_FINSUM THEN
  ASM_REWRITE_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM]);;

(* single term of an absolutely summable sequence *)
let RP_EN_ABS_LE_INFSUM = prove
 (`forall u k. rp_summable u /\ 1 <= k
         ==> abs(u k) <= real_infsum (from 1) (\k. abs(u k))`,
  REWRITE_TAC[rp_summable] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\k. abs((u:num->real) k)`; `from 1`; `{k:num}`]
    REAL_PARTIAL_SUMS_LE_INFSUM_GEN) THEN
  ASM_REWRITE_TAC[FINITE_SING; SING_SUBSET; IN_FROM; REAL_ABS_POS; SUM_SING]);;

let RP_EN_INFSUM_ABS_POS = prove
 (`forall u. rp_summable u ==> &0 <= real_infsum (from 1) (\k. abs(u k))`,
  REWRITE_TAC[rp_summable] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC REAL_SERIES_POS THEN
  EXISTS_TAC `\k. abs((u:num->real) k)` THEN EXISTS_TAC `from 1` THEN
  ASM_SIMP_TAC[REAL_SUMS_INFSUM; REAL_ABS_POS]);;

let RP_EN_LE_MUL_GE1 = prove
 (`forall a k. &0 <= a /\ &1 <= k ==> a <= a * k`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(REAL_ARITH `a * &1 <= a * k ==> a <= a * k`) THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]);;

(* weighted series sum u_k c_k / k with |c_k| <= B *)
let RP_EN_WSERIES = prove
 (`forall u c B. rp_summable u /\ (forall k. 1 <= k ==> abs(c k) <= B)
           ==> real_summable (from 1) (\k. u k * c k / &k) /\
               abs(real_infsum (from 1) (\k. u k * c k / &k)) <=
               B * real_infsum (from 1) (\k. abs(u k))`,
  REWRITE_TAC[rp_summable] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `forall k. k IN from 1 ==> abs(u k * c k / &k) <= B * abs((u:num->real) k)`
  ASSUME_TAC THENL
   [REWRITE_TAC[IN_FROM] THEN REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `&1 <= &k` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[REAL_OF_NUM_LE]; ALL_TAC] THEN
    SUBGOAL_THEN `abs((c:num->real) k) / &k <= B` ASSUME_TAC THENL
     [ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_ARITH `&1 <= x ==> &0 < x`] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `B:real` THEN
      ASM_SIMP_TAC[] THEN MATCH_MP_TAC RP_EN_LE_MUL_GE1 THEN
      ASM_MESON_TAC[REAL_ABS_POS; REAL_LE_TRANS; LE_REFL];
      ALL_TAC] THEN
    REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_DIV; REAL_ABS_NUM] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `abs((u:num->real) k) * B` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[real_div; GSYM REAL_MUL_ASSOC] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_ABS_POS; GSYM real_div];
      REWRITE_TAC[REAL_MUL_SYM; REAL_LE_REFL]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\k. (u:num->real) k * c k / &k`; `\k. B * abs((u:num->real) k)`;
                 `from 1`; `B * real_infsum (from 1) (\k. abs((u:num->real) k))`]
         REAL_SERIES_COMPARISON_BOUND) THEN
  ASM_SIMP_TAC[REAL_SERIES_LMUL; REAL_SUMS_INFSUM] THEN
  STRIP_TAC THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP REAL_INFSUM_UNIQUE th]) THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[real_summable]);;
