(* ========================================================================= *)
(* rp_ip: basic determinant / polynomial facts for Proposition 5.2.          *)
(* ========================================================================= *)

needs "src/catalan_rp_defs.ml";;
needs "Library/ring_det.ml";;

let RP_IP_NDET_RING = prove
 (`forall s a. ndet s a = ring_det real_ring s a`,
  REWRITE_TAC[ndet; ring_det; ring_sign; REAL_RING_SUM; REAL_RING_PRODUCT;
              REAL_RING_CLAUSES; sign] THEN
  REPEAT GEN_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN
  GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[]);;

let RP_IP_NDET_TRANSP = prove
 (`forall s a. FINITE s ==> ndet s (\i j. a j i) = ndet s a`,
  SIMP_TAC[RP_IP_NDET_RING; RING_DET_TRANSP]);;

let RP_IP_NDET_EQ = prove
 (`forall s a b. (forall i j. i IN s /\ j IN s ==> a i j = b i j)
           ==> ndet s a = ndet s b`,
  REWRITE_TAC[RP_IP_NDET_RING] THEN MESON_TAC[RING_DET_EQ]);;

let RP_IP_NDET_ROWS_MUL = prove
 (`forall s c a. FINITE s
           ==> ndet s (\i j. c i * a i j) = product s c * ndet s a`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[RP_IP_NDET_RING] THEN
  MP_TAC(ISPECL [`real_ring`; `s:num->bool`; `c:num->real`;
                 `a:num->num->real`] RING_DET_ROWS_MUL) THEN
  ASM_REWRITE_TAC[REAL_RING_CLAUSES; IN_UNIV; REAL_RING_PRODUCT]);;

let RP_IP_NDET_COLUMNS_MUL = prove
 (`forall s c a. FINITE s
           ==> ndet s (\i j. a i j * c j) = ndet s a * product s c`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[RP_IP_NDET_RING] THEN
  MP_TAC(ISPECL [`real_ring`; `s:num->bool`; `c:num->real`;
                 `a:num->num->real`] RING_DET_COLUMNS_MUL) THEN
  ASM_REWRITE_TAC[REAL_RING_CLAUSES; IN_UNIV; REAL_RING_PRODUCT]);;

let RP_IP_NDET_MUL = prove
 (`forall s a b. FINITE s
           ==> ndet s (\i j. sum s (\k. a i k * b k j)) =
               ndet s a * ndet s b`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[RP_IP_NDET_RING] THEN
  MP_TAC(ISPECL [`real_ring`; `s:num->bool`; `a:num->num->real`;
                 `b:num->num->real`] RING_DET_MUL) THEN
  ASM_REWRITE_TAC[REAL_RING_CLAUSES; IN_UNIV; REAL_RING_SUM]);;

let RP_IP_NDET_DIAGONAL = prove
 (`forall s a. FINITE s /\ (forall i j. i IN s /\ j IN s /\ ~(i = j) ==> a i j = &0)
         ==> ndet s a = product s (\i. a i i)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[RP_IP_NDET_RING] THEN
  MP_TAC(ISPECL [`real_ring`; `s:num->bool`; `a:num->num->real`]
    RING_DET_DIAGONAL) THEN
  ASM_REWRITE_TAC[REAL_RING_CLAUSES; REAL_RING_PRODUCT]);;

let RP_IP_NDET_KERNEL = prove
 (`forall s a c. FINITE s /\ ~(ndet s a = &0) /\
           (forall i. i IN s ==> sum s (\j. a i j * c j) = &0)
           ==> forall j. j IN s ==> c j = &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`real_ring`; `s:num->bool`; `a:num->num->real`;
                 `c:num->real`] RING_DET_DEPENDENT_COLUMNS) THEN
  ASM_REWRITE_TAC[INTEGRAL_DOMAIN_REAL_RING; REAL_RING_CLAUSES; IN_UNIV;
                  REAL_RING_SUM; GSYM RP_IP_NDET_RING] THEN
  MESON_TAC[]);;

let RP_IP_VDM_NDET = prove
 (`forall n x. ndet {i | i < n} (\i j. x i pow j) = rp_vdm n x`,
  REPEAT GEN_TAC THEN REWRITE_TAC[RP_IP_NDET_RING; rp_vdm] THEN
  MP_TAC(ISPECL [`real_ring`; `n:num`; `x:num->real`] RING_DET_VANDERMONDE) THEN
  REWRITE_TAC[REAL_FIELD_CLAUSES; IN_UNIV; REAL_RING_PRODUCT]);;

let RP_IP_VDM_NZ = prove
 (`forall n x. (forall i j. i < n /\ j < n /\ x i = x j ==> i = j)
         ==> ~(rp_vdm n x = &0)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SIMP_TAC[rp_vdm; PRODUCT_EQ_0; FINITE_NUMSEG_LT; IN_ELIM_THM;
           REAL_SUB_0] THEN
  ASM_MESON_TAC[LT_TRANS; LT_REFL]);;

(* Vandermonde kernel: sum_i a_i x_i^m = 0 for all m < n forces a = 0 *)
let RP_IP_VDM_KERNEL = prove
 (`forall n x a. (forall i j. i < n /\ j < n /\ x i = x j ==> i = j) /\
           (forall m. m < n ==> sum {i | i < n} (\i. a i * x i pow m) = &0)
           ==> forall i. i < n ==> a i = &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`{i:num | i < n}`; `\m i. (x:num->real) i pow m`;
                 `a:num->real`] RP_IP_NDET_KERNEL) THEN
  MP_TAC(ISPECL [`{i:num | i < n}`; `\i m. (x:num->real) i pow m`]
    RP_IP_NDET_TRANSP) THEN
  REWRITE_TAC[FINITE_NUMSEG_LT; RP_IP_VDM_NDET] THEN
  DISCH_THEN SUBST1_TAC THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP RP_IP_VDM_NZ th]) THEN
  REWRITE_TAC[IN_ELIM_THM] THEN
  ANTS_TAC THENL [ALL_TAC; MESON_TAC[]] THEN
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN ASM_SIMP_TAC[]);;

let RP_IP_SUM_REFLECT = prove
 (`forall n f. sum {m:num | m < n} (\m. (f:num->real) (n - 1 - m)) =
         sum {m | m < n} f`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `n = 0` THENL
   [ASM_REWRITE_TAC[LT; EMPTY_GSPEC; SUM_CLAUSES]; ALL_TAC] THEN
  SUBGOAL_THEN `{m | m < n} = 0..n-1` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_NUMSEG; IN_ELIM_THM] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  GEN_REWRITE_TAC RAND_CONV [SUM_REFLECT] THEN
  REWRITE_TAC[ARITH_RULE `~(n - 1 < 0)`; SUB_0]);;

let RP_IP_SUM_SHIFT = prove
 (`forall g k. sum(0..SUC k) g = g 0 + sum(0..k) (\i. g(i + 1))`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`g:num->real`; `0`; `SUC k`] SUM_CLAUSES_LEFT) THEN
  REWRITE_TAC[LE_0; ADD_CLAUSES] THEN DISCH_THEN SUBST1_TAC THEN
  AP_TERM_TAC THEN
  MP_TAC(ISPECL [`g:num->real`; `1`; `SUC k`] SUM_OFFSET_0) THEN
  REWRITE_TAC[ARITH_RULE `1 <= SUC k`; ARITH_RULE `SUC k - 1 = k`]);;

(* coefficients of the homogeneous product prod_{l in s} (w - x_l y) *)
let RP_IP_HOMPOLY = prove
 (`forall (x:num->real) s. FINITE s
     ==> exists c. forall y w. product s (\l. w - x l * y) =
                   sum (0..CARD s) (\m. c m * y pow m * w pow (CARD s - m))`,
  GEN_TAC THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN CONJ_TAC THENL
   [EXISTS_TAC `\m:num. &1` THEN
    REWRITE_TAC[PRODUCT_CLAUSES; CARD_CLAUSES; SUM_SING_NUMSEG] THEN
    REWRITE_TAC[SUB_REFL; real_pow] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`a:num`; `s:num->bool`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC `c:num->real`)
    STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `\m. (if m <= CARD(s:num->bool) then c m else &0) -
                  (if m = 0 then &0 else x(a:num) * c(m - 1))` THEN
  ASM_SIMP_TAC[PRODUCT_CLAUSES; CARD_CLAUSES] THEN
  MAP_EVERY X_GEN_TAC [`y:real`; `w:real`] THEN
  ABBREV_TAC `k = CARD(s:num->bool)` THEN
  REWRITE_TAC[REAL_SUB_RDISTRIB; SUM_SUB_NUMSEG] THEN
  BINOP_TAC THENL
   [REWRITE_TAC[SUM_CLAUSES_NUMSEG; LE_0; ARITH_RULE `~(SUC k <= k)`] THEN
    REWRITE_TAC[REAL_MUL_LZERO; REAL_ADD_RID; GSYM SUM_LMUL] THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `m:num` THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[ARITH_RULE `m <= k ==> SUC k - m = SUC(k - m)`] THEN
    REWRITE_TAC[real_pow] THEN REAL_ARITH_TAC;
    GEN_REWRITE_TAC RAND_CONV [RP_IP_SUM_SHIFT] THEN
    REWRITE_TAC[ADD_EQ_0; ARITH_EQ; ADD_SUB; REAL_MUL_LZERO; REAL_ADD_LID;
                GSYM SUM_LMUL] THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `m:num` THEN STRIP_TAC THEN
    REWRITE_TAC[ARITH_RULE `SUC k - (m + 1) = k - m`] THEN
    REWRITE_TAC[GSYM ADD1; real_pow] THEN REAL_ARITH_TAC]);;
