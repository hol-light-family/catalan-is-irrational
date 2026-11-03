(* ========================================================================= *)
(* rp_la_: RP_LA_THM : |- RP_LA_STMT  (|det A| <= c^n for a G-contraction). *)
(* Route: Schur complement induction, det monotone in the Loewner order.    *)
(* ========================================================================= *)

needs "src/catalan_rp_la_base.ml";;
let RP_LA_SCHUR_DET = prove
 (`forall n (M:num->num->real).
        ~(M n n = &0)
        ==> ndet {i | i < SUC n} M =
            M n n * ndet {i | i < n} (\i j. M i j - M i n * M n j / M n n)`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `U = \i j. if i = j then &1 else if j = n then (M:num->num->real) i n / M n n else &0` THEN
  ABBREV_TAC `L = \i j. if i = n then (M:num->num->real) n j else if j = n then &0 else M i j - M i n * M n j / M n n` THEN
  SUBGOAL_THEN `ndet {i | i < SUC n} M =
                ndet {i | i < SUC n} (\i j. sum {k | k < SUC n} (\k. (U:num->num->real) i k * (L:num->num->real) k j))`
  SUBST1_TAC THENL
   [MATCH_MP_TAC RP_LA_NDET_EQ THEN REWRITE_TAC[IN_ELIM_THM] THEN
    MAP_EVERY X_GEN_TAC [`i:num`; `j:num`] THEN STRIP_TAC THEN
    SIMP_TAC[NUMSEG_CLAUSES_LT; SUM_CLAUSES; FINITE_NUMSEG_LT; IN_ELIM_THM; LT_REFL] THEN
    SUBGOAL_THEN `sum {k | k < n} (\k. (U:num->num->real) i k * (L:num->num->real) k j) =
                  sum {k | k < n} (\k. if k = i then (if i = n then &0 else L i j) else &0)`
    SUBST1_TAC THENL
     [MATCH_MP_TAC SUM_EQ THEN REWRITE_TAC[IN_ELIM_THM] THEN
      X_GEN_TAC `k:num` THEN DISCH_TAC THEN
      SUBGOAL_THEN `~(k:num = n)` ASSUME_TAC THENL [RP_LA_ARITH_TAC; ALL_TAC] THEN
      MAP_EVERY EXPAND_TAC ["U"; "L"] THEN ASM_REWRITE_TAC[] THEN
      ASM_CASES_TAC `i:num = k` THENL
       [FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN ASM_REWRITE_TAC[REAL_MUL_LID];
        ASM_REWRITE_TAC[REAL_MUL_LZERO] THEN
        COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN RP_LA_CONTR_TAC];
      ALL_TAC] THEN
    REWRITE_TAC[SUM_DELTA; IN_ELIM_THM] THEN
    MAP_EVERY EXPAND_TAC ["U"; "L"] THEN
    ASM_CASES_TAC `i:num = n` THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC THEN REWRITE_TAC[LT_REFL] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `i:num < n` ASSUME_TAC THENL [RP_LA_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `j:num = n` THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `~((M:num->num->real) n n = &0)` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  SIMP_TAC[RP_LA_NDET_MUL; FINITE_NUMSEG_LT] THEN
  SUBGOAL_THEN `ndet {i | i < SUC n} U = &1` SUBST1_TAC THENL
   [MP_TAC(ISPECL [`{i | i < SUC n}`; `U:num->num->real`] RP_LA_NDET_UPPER) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM] THEN EXPAND_TAC "U" THEN
      MAP_EVERY X_GEN_TAC [`i:num`; `j:num`] THEN STRIP_TAC THEN
      ASM_SIMP_TAC[ARITH_RULE `j:num < i ==> ~(i = j)`] THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN RP_LA_CONTR_TAC;
      DISCH_THEN SUBST1_TAC THEN EXPAND_TAC "U" THEN REWRITE_TAC[PRODUCT_ONE]];
    ALL_TAC] THEN
  SUBGOAL_THEN `{i | i < SUC n} = {i | i < n} UNION {n}` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_UNION; IN_SING] THEN ARITH_TAC;
    ALL_TAC] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) RP_LA_NDET_BLOCK o rand o lhand o snd) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[FINITE_NUMSEG_LT; FINITE_SING; IN_ELIM_THM; IN_SING; DISJOINT;
      EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN
    EXPAND_TAC "L" THEN CONJ_TAC THENL [ARITH_TAC; SIMP_TAC[LT_IMP_NE]];
    DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[RP_LA_NDET_SING; REAL_MUL_LID] THEN
  EXPAND_TAC "L" THEN REWRITE_TAC[] THEN
  GEN_REWRITE_TAC LAND_CONV [REAL_MUL_SYM] THEN AP_TERM_TAC THEN
  MATCH_MP_TAC RP_LA_NDET_EQ THEN SIMP_TAC[IN_ELIM_THM; LT_IMP_NE]);;


let rp_la_qf = new_definition
 `rp_la_qf n (M:num->num->real) (a:num->real) =
    sum {i | i < n} (\i. sum {j | j < n} (\j. a i * M i j * a j))`;;

let RP_LA_QF_SUC = prove
 (`forall n M a. rp_la_qf (SUC n) M a =
           (a n * M n n * a n + sum {j | j < n} (\j. a n * M n j * a j)) +
           (sum {i | i < n} (\i. a i * M i n * a n) + rp_la_qf n M a)`,
  REWRITE_TAC[rp_la_qf; NUMSEG_CLAUSES_LT] THEN
  SIMP_TAC[SUM_CLAUSES; FINITE_NUMSEG_LT; IN_ELIM_THM; LT_REFL; SUM_ADD]);;

let RP_LA_QF_EQ = prove
 (`forall n M a b. (forall i. i < n ==> a i = b i) ==> rp_la_qf n M a = rp_la_qf n M b`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[rp_la_qf] THEN
  MATCH_MP_TAC SUM_EQ THEN REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC SUM_EQ THEN ASM_SIMP_TAC[IN_ELIM_THM]);;

let RP_LA_QF_0 = prove
 (`forall n M. rp_la_qf n M (\i. &0) = &0`,
  REWRITE_TAC[rp_la_qf; REAL_MUL_LZERO; SUM_0]);;

let RP_LA_QF_DELTA = prove
 (`forall n M k. k < n ==> rp_la_qf n M (\i. if i = k then &1 else &0) = M k k`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[rp_la_qf] THEN
  SUBGOAL_THEN `forall i j. (if i = k then &1 else &0) * M i j * (if j = k then &1 else &0) =
    if j = k then (if i = k then (M:num->num->real) k k else &0) else &0`
  (fun th -> REWRITE_TAC[th]) THENL
   [REPEAT GEN_TAC THEN ASM_CASES_TAC `i:num = k` THEN
    ASM_CASES_TAC `j:num = k` THEN ASM_REWRITE_TAC[] THEN
    REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[SUM_DELTA; IN_ELIM_THM]);;

let RP_LA_SCHUR_FORM = prove
 (`forall n (M:num->num->real) x t.
        (forall i j. i <= n /\ j <= n ==> M i j = M j i) /\ ~(M n n = &0)
        ==> rp_la_qf (SUC n) M (\i. if i = n then t else x i) =
            rp_la_qf n (\i j. M i j - M i n * M n j / M n n) x +
            M n n * (t + sum {j | j < n} (\j. M n j * x j) / M n n) pow 2`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[RP_LA_QF_SUC] THEN BETA_TAC THEN REWRITE_TAC[] THEN
  SUBGOAL_THEN `rp_la_qf n M (\i. if i = n then t else x i) = rp_la_qf n M x`
  SUBST1_TAC THENL
   [MATCH_MP_TAC RP_LA_QF_EQ THEN SIMP_TAC[LT_IMP_NE]; ALL_TAC] THEN
  ABBREV_TAC `b = sum {j | j < n} (\j. (M:num->num->real) n j * x j)` THEN
  SUBGOAL_THEN `sum {j | j < n} (\j. t * M n j *
                   (if j = n then t else (x:num->real) j)) = t * b`
  SUBST1_TAC THENL
   [EXPAND_TAC "b" THEN REWRITE_TAC[GSYM SUM_LMUL] THEN
    MATCH_MP_TAC SUM_EQ THEN SIMP_TAC[IN_ELIM_THM; LT_IMP_NE]; ALL_TAC] THEN
  SUBGOAL_THEN `sum {i | i < n} (\i. (if i = n then t else (x:num->real) i) *
                   M i n * t) = b * t`
  SUBST1_TAC THENL
   [EXPAND_TAC "b" THEN REWRITE_TAC[GSYM SUM_RMUL] THEN
    MATCH_MP_TAC SUM_EQ THEN SIMP_TAC[IN_ELIM_THM; LT_IMP_NE] THEN
    REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`x':num`; `n:num`]) THEN
    ANTS_TAC THENL [RP_LA_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `rp_la_qf n (\i j. M i j - M i n * M n j / M n n) x =
                rp_la_qf n M x - b * b / M n n`
  SUBST1_TAC THENL
   [REWRITE_TAC[rp_la_qf] THEN
    TRANS_TAC EQ_TRANS
     `sum {i | i < n} (\i. sum {j | j < n} (\j. (x:num->real) i * M i j * x j) -
                          ((M:num->num->real) n i * x i) * (b * inv(M n n)))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SUM_EQ THEN REWRITE_TAC[IN_ELIM_THM] THEN
      X_GEN_TAC `i:num` THEN DISCH_TAC THEN BETA_TAC THEN EXPAND_TAC "b" THEN
      REWRITE_TAC[GSYM SUM_RMUL; GSYM SUM_LMUL] THEN
      SIMP_TAC[GSYM SUM_SUB; FINITE_NUMSEG_LT] THEN
      MATCH_MP_TAC SUM_EQ THEN REWRITE_TAC[IN_ELIM_THM] THEN
      X_GEN_TAC `j:num` THEN DISCH_TAC THEN BETA_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`i:num`; `n:num`]) THEN
      ANTS_TAC THENL [RP_LA_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
      UNDISCH_TAC `~((M:num->num->real) n n = &0)` THEN CONV_TAC REAL_FIELD;
      ALL_TAC] THEN
    SIMP_TAC[SUM_SUB; FINITE_NUMSEG_LT; SUM_RMUL] THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[real_div] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[] THEN
  SUBGOAL_THEN `forall i. i < n ==> (M:num->num->real) i n = M n i` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN RP_LA_ARITH_TAC;
    ALL_TAC] THEN
  UNDISCH_TAC `~((M:num->num->real) n n = &0)` THEN CONV_TAC REAL_FIELD);;

let RP_LA_NDET_ZERO_ROW = prove
 (`forall s (f:num->num->real) k.
        FINITE s /\ k IN s /\ (forall j. j IN s ==> f k j = &0) ==> ndet s f = &0`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[ndet] THEN MATCH_MP_TAC SUM_EQ_0 THEN
  X_GEN_TAC `p:num->num` THEN REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN
  REWRITE_TAC[REAL_ENTIRE] THEN DISJ2_TAC THEN
  ASM_SIMP_TAC[PRODUCT_EQ_0] THEN EXISTS_TAC `k:num` THEN
  ASM_MESON_TAC[PERMUTES_IN_IMAGE]);;

let RP_LA_QF_TWO = prove
 (`forall n (M:num->num->real) j t.
        (forall i j. i <= n /\ j <= n ==> M i j = M j i) /\ j < n
        ==> rp_la_qf (SUC n) M (\i. if i = n then t else if i = j then &1 else &0) =
            M j j + &2 * t * M n j + t * M n n * t`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[RP_LA_QF_SUC] THEN
  SUBGOAL_THEN `rp_la_qf n M (\i. if i = n then t else if i = j then &1 else &0) =
                (M:num->num->real) j j` SUBST1_TAC THENL
   [TRANS_TAC EQ_TRANS `rp_la_qf n M (\i. if i = j then &1 else &0)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC RP_LA_QF_EQ THEN SIMP_TAC[LT_IMP_NE];
      ASM_SIMP_TAC[RP_LA_QF_DELTA]];
    ALL_TAC] THEN
  SUBGOAL_THEN `sum {k | k < n} (\k. t * (M:num->num->real) n k *
                    (if k = n then t else if k = j then &1 else &0)) =
                t * M n j` SUBST1_TAC THENL
   [TRANS_TAC EQ_TRANS `sum {k | k < n} (\k. if k = j then t * (M:num->num->real) n j else &0)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SUM_EQ THEN REWRITE_TAC[IN_ELIM_THM] THEN
      X_GEN_TAC `k:num` THEN DISCH_TAC THEN BETA_TAC THEN
      ASM_SIMP_TAC[LT_IMP_NE] THEN
      ASM_CASES_TAC `k:num = j` THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
      ASM_REWRITE_TAC[SUM_DELTA; IN_ELIM_THM]];
    ALL_TAC] THEN
  SUBGOAL_THEN `sum {k | k < n} (\k. (if k = n then t else if k = j then &1 else &0) *
                    (M:num->num->real) k n * t) =
                t * M n j` SUBST1_TAC THENL
   [TRANS_TAC EQ_TRANS `sum {k | k < n} (\k. if k = j then t * (M:num->num->real) n j else &0)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SUM_EQ THEN REWRITE_TAC[IN_ELIM_THM] THEN
      X_GEN_TAC `k:num` THEN DISCH_TAC THEN BETA_TAC THEN
      ASM_SIMP_TAC[LT_IMP_NE] THEN
      ASM_CASES_TAC `k:num = j` THEN ASM_REWRITE_TAC[] THENL
       [FIRST_X_ASSUM(MP_TAC o SPECL [`j:num`; `n:num`]) THEN
        ANTS_TAC THENL [RP_LA_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
        REAL_ARITH_TAC;
        REAL_ARITH_TAC];
      ASM_REWRITE_TAC[SUM_DELTA; IN_ELIM_THM]];
    ALL_TAC] THEN
  REAL_ARITH_TAC);;

let RP_LA_PSD_ZERO_DIAG = prove
 (`forall n (M:num->num->real).
        (forall i j. i <= n /\ j <= n ==> M i j = M j i) /\
        (forall a. &0 <= rp_la_qf (SUC n) M a) /\ M n n = &0
        ==> forall j. j < SUC n ==> M n j = &0`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `j:num = n` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `j:num < n` ASSUME_TAC THENL [RP_LA_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `forall t. &0 <= M j j + &2 * t * (M:num->num->real) n j` MP_TAC THENL
   [X_GEN_TAC `t:real` THEN
    FIRST_X_ASSUM(MP_TAC o SPEC
      `\i:num. if i = n then t else if i = j then &1 else &0`) THEN
    ASM_SIMP_TAC[RP_LA_QF_TWO] THEN REAL_ARITH_TAC;
    DISCH_THEN(MP_TAC o SPEC `--(M j j + &1) / (&2 * (M:num->num->real) n j)`) THEN
    ASM_CASES_TAC `(M:num->num->real) n j = &0` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `M j j + &2 * (--(M j j + &1) / (&2 * M n j)) * (M:num->num->real) n j = -- &1`
    SUBST1_TAC THENL
     [POP_ASSUM MP_TAC THEN CONV_TAC REAL_FIELD; REAL_ARITH_TAC]]);;

let RP_LA_PD_PSD = prove
 (`forall n M. (forall a. ~(forall i. i < n ==> a i = &0) ==> &0 < rp_la_qf n M a)
         ==> forall a. &0 <= rp_la_qf n M a`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `forall i. i < n ==> (a:num->real) i = &0` THENL
   [SUBGOAL_THEN `rp_la_qf n M a = rp_la_qf n M (\i. &0)` SUBST1_TAC THENL
     [MATCH_MP_TAC RP_LA_QF_EQ THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[RP_LA_QF_0; REAL_LE_REFL]];
    ASM_SIMP_TAC[REAL_LT_IMP_LE]]);;

let RP_LA_SCHUR_SYM = prove
 (`forall n (M:num->num->real).
        (forall i j. i <= n /\ j <= n ==> M i j = M j i)
        ==> forall i j. i < n /\ j < n
                  ==> M i j - M i n * M n j / M n n =
                      M j i - M j n * M n i / M n n`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
  FIRST_ASSUM(MP_TAC o SPECL [`i:num`; `j:num`]) THEN
  FIRST_ASSUM(MP_TAC o SPECL [`i:num`; `n:num`]) THEN
  FIRST_ASSUM(MP_TAC o SPECL [`j:num`; `n:num`]) THEN
  ASM_SIMP_TAC[LT_IMP_LE; LE_REFL] THEN REAL_ARITH_TAC);;

let RP_LA_SCHUR_FORM_OPT = prove
 (`forall n (M:num->num->real) x.
        (forall i j. i <= n /\ j <= n ==> M i j = M j i) /\ ~(M n n = &0)
        ==> rp_la_qf n (\i j. M i j - M i n * M n j / M n n) x =
            rp_la_qf (SUC n) M
              (\i. if i = n then --(sum {j | j < n} (\j. M n j * x j)) / M n n
                   else x i)`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[RP_LA_SCHUR_FORM] THEN
  REWRITE_TAC[real_div; REAL_MUL_LNEG; REAL_ADD_LINV; REAL_POW_2;
              REAL_MUL_LZERO; REAL_MUL_RZERO; REAL_ADD_RID]);;

let RP_LA_SCHUR_FORM_LE = prove
 (`forall n (M:num->num->real) x t.
        (forall i j. i <= n /\ j <= n ==> M i j = M j i) /\ &0 < M n n
        ==> rp_la_qf n (\i j. M i j - M i n * M n j / M n n) x <=
            rp_la_qf (SUC n) M (\i. if i = n then t else x i)`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[RP_LA_SCHUR_FORM; REAL_LT_IMP_NZ] THEN
  MATCH_MP_TAC(REAL_ARITH `&0 <= y ==> x <= x + y`) THEN
  ASM_SIMP_TAC[REAL_LE_MUL; REAL_LT_IMP_LE; REAL_LE_POW_2]);;

let RP_LA_MONO = prove
 (`forall n (G:num->num->real) H.
        (forall i j. i < n /\ j < n ==> G i j = G j i) /\
        (forall i j. i < n /\ j < n ==> H i j = H j i) /\
        (forall a. ~(forall i. i < n ==> a i = &0) ==> &0 < rp_la_qf n G a) /\
        (forall a. &0 <= rp_la_qf n H a) /\
        (forall a. rp_la_qf n H a <= rp_la_qf n G a)
        ==> &0 < ndet {i | i < n} G /\ &0 <= ndet {i | i < n} H /\
            ndet {i | i < n} H <= ndet {i | i < n} G`,
  INDUCT_TAC THENL
   [REWRITE_TAC[NUMSEG_CLAUSES_LT; RP_LA_NDET_EMPTY] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "pd") (CONJUNCTS_THEN2 (LABEL_TAC "psd")
       (LABEL_TAC "le"))))) THEN
  SUBGOAL_THEN `forall i j. i <= n /\ j <= n ==> (G:num->num->real) i j = G j i /\
                                          (H:num->num->real) i j = H j i`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN RP_LA_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `forall i j. i <= n /\ j <= n ==> (G:num->num->real) i j = G j i`
  ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `forall i j. i <= n /\ j <= n ==> (H:num->num->real) i j = H j i`
  ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < (G:num->num->real) n n` ASSUME_TAC THENL
   [USE_THEN "pd" (MP_TAC o SPEC `\i:num. if i = n then &1 else &0`) THEN
    SIMP_TAC[RP_LA_QF_DELTA; LT] THEN
    DISCH_THEN MATCH_MP_TAC THEN DISCH_THEN(MP_TAC o SPEC `n:num`) THEN
    REWRITE_TAC[LT] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= (H:num->num->real) n n /\ H n n <= (G:num->num->real) n n`
  STRIP_ASSUME_TAC THENL
   [USE_THEN "psd" (MP_TAC o SPEC `\i:num. if i = n then &1 else &0`) THEN
    USE_THEN "le" (MP_TAC o SPEC `\i:num. if i = n then &1 else &0`) THEN
    SIMP_TAC[RP_LA_QF_DELTA; LT]; ALL_TAC] THEN
  ABBREV_TAC `SG = \i j. (G:num->num->real) i j - G i n * G n j / G n n` THEN
  SUBGOAL_THEN `forall x. ~(forall i. i < n ==> x i = &0) ==> &0 < rp_la_qf n SG x`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "SG" THEN
    ASM_SIMP_TAC[RP_LA_SCHUR_FORM_OPT; REAL_LT_IMP_NZ] THEN
    USE_THEN "pd" MATCH_MP_TAC THEN
    UNDISCH_TAC `~(forall i. i < n ==> (x:num->real) i = &0)` THEN
    REWRITE_TAC[NOT_FORALL_THM; NOT_IMP] THEN MATCH_MP_TAC MONO_EXISTS THEN
    SIMP_TAC[LT_IMP_NE] THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `forall i j. i < n /\ j < n ==> (SG:num->num->real) i j = SG j i`
  ASSUME_TAC THENL
   [EXPAND_TAC "SG" THEN MATCH_MP_TAC RP_LA_SCHUR_SYM THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < ndet {i | i < SUC n} G` ASSUME_TAC THENL
   [ASM_SIMP_TAC[RP_LA_SCHUR_DET; REAL_LT_IMP_NZ] THEN
    MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `forall a. &0 <= rp_la_qf n SG a` ASSUME_TAC THENL
     [MATCH_MP_TAC RP_LA_PD_PSD THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    FIRST_ASSUM(MP_TAC o SPECL [`SG:num->num->real`; `SG:num->num->real`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_LE_REFL]; SIMP_TAC[]]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `(H:num->num->real) n n = &0` THENL
   [SUBGOAL_THEN `ndet {i | i < SUC n} H = &0` SUBST1_TAC THENL
     [MATCH_MP_TAC RP_LA_NDET_ZERO_ROW THEN EXISTS_TAC `n:num` THEN
      REWRITE_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM; LT] THEN
      MP_TAC(SPECL [`n:num`; `H:num->num->real`] RP_LA_PSD_ZERO_DIAG) THEN
      ASM_REWRITE_TAC[LT];
      ASM_SIMP_TAC[REAL_LE_REFL; REAL_LT_IMP_LE]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < (H:num->num->real) n n` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `SH = \i j. (H:num->num->real) i j - H i n * H n j / H n n` THEN
  SUBGOAL_THEN `forall i j. i < n /\ j < n ==> (SH:num->num->real) i j = SH j i`
  ASSUME_TAC THENL
   [EXPAND_TAC "SH" THEN MATCH_MP_TAC RP_LA_SCHUR_SYM THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `forall x. &0 <= rp_la_qf n SH x` ASSUME_TAC THENL
   [GEN_TAC THEN EXPAND_TAC "SH" THEN
    ASM_SIMP_TAC[RP_LA_SCHUR_FORM_OPT; REAL_LT_IMP_NZ]; ALL_TAC] THEN
  SUBGOAL_THEN `forall x. rp_la_qf n SH x <= rp_la_qf n SG x` ASSUME_TAC THENL
   [X_GEN_TAC `x:num->real` THEN MAP_EVERY EXPAND_TAC ["SH"; "SG"] THEN
    MP_TAC(ISPECL [`n:num`; `G:num->num->real`; `x:num->real`]
      RP_LA_SCHUR_FORM_OPT) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[REAL_LT_IMP_NZ]; DISCH_TAC] THEN
    MP_TAC(ISPECL [`n:num`; `H:num->num->real`; `x:num->real`;
      `--(sum {j | j < n} (\j. (G:num->num->real) n j * x j)) / G n n`]
      RP_LA_SCHUR_FORM_LE) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[]; DISCH_TAC] THEN
    USE_THEN "le" (MP_TAC o SPEC `\i. if i = n then
       --(sum {j | j < n} (\j. (G:num->num->real) n j * x j)) / G n n
       else (x:num->real) i`) THEN
    POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN
    MATCH_ACCEPT_TAC(REAL_ARITH
      `forall a b c d:real. a = b ==> c <= d ==> d <= b ==> c <= a`);
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`SG:num->num->real`; `SH:num->num->real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  ASM_SIMP_TAC[RP_LA_SCHUR_DET; REAL_LT_IMP_NZ] THEN
  MAP_EVERY EXPAND_TAC ["SH"; "SG"] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM(ASSUME `(\i j. (G:num->num->real) i j - G i n * G n j / G n n) = SG`);
     GSYM(ASSUME `(\i j. (H:num->num->real) i j - H i n * H n j / H n n) = SH`)]) THEN
  ASM_SIMP_TAC[REAL_LE_MUL; REAL_LT_IMP_LE] THEN
  MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]);;

let RP_LA_SUM_SWAP4 = prove
 (`forall n (f:num->num->num->num->real).
        sum {i | i < n} (\i. sum {j | j < n} (\j. sum {k | k < n} (\k.
          sum {l | l < n} (\l. f i j k l)))) =
        sum {k | k < n} (\k. sum {l | l < n} (\l. sum {i | i < n} (\i.
          sum {j | j < n} (\j. f i j k l))))`,
  REPEAT GEN_TAC THEN
  CONV_TAC(LAND_CONV(BINDER_CONV RP_LA_SWAP_CONV)) THEN
  CONV_TAC(LAND_CONV RP_LA_SWAP_CONV) THEN
  CONV_TAC(LAND_CONV(BINDER_CONV(BINDER_CONV RP_LA_SWAP_CONV))) THEN
  CONV_TAC(LAND_CONV(BINDER_CONV RP_LA_SWAP_CONV)) THEN
  REFL_TAC);;

let RP_LA_SUM_SWAP_LT = prove
 (`forall (f:num->num->real) n m.
        sum {i | i < n} (\i. sum {j | j < m} (f i)) =
        sum {j | j < m} (\j. sum {i | i < n} (\i. f i j))`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`f:num->num->real`; `{i:num | i < n}`; `{j:num | j < m}`]
    SUM_SWAP) THEN REWRITE_TAC[FINITE_NUMSEG_LT]);;

let RP_LA_QF_CMUL = prove
 (`forall n M c a. rp_la_qf n (\i j. c * M i j) a = c * rp_la_qf n M a`,
  REPEAT GEN_TAC THEN REWRITE_TAC[rp_la_qf; GSYM SUM_LMUL] THEN
  MATCH_MP_TAC SUM_EQ THEN REPEAT STRIP_TAC THEN BETA_TAC THEN
  MATCH_MP_TAC SUM_EQ THEN REPEAT STRIP_TAC THEN BETA_TAC THEN
  CONV_TAC REAL_RING);;

let RP_LA_QF_GRAM = prove
 (`forall n (G:num->num->real) A a.
     rp_la_qf n (\i j. sum {k | k < n} (\k. A k i * sum {l | l < n} (\l. G k l * A l j))) a =
     rp_la_qf n G (\i. sum {k | k < n} (\k. A i k * a k))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[rp_la_qf; GSYM SUM_LMUL; GSYM SUM_RMUL] THEN
  GEN_REWRITE_TAC LAND_CONV [RP_LA_SUM_SWAP4] THEN
  REPEAT(MATCH_MP_TAC SUM_EQ THEN GEN_TAC THEN DISCH_TAC THEN BETA_TAC) THEN
  CONV_TAC REAL_RING);;

let RP_LA_GRAM_SYM = prove
 (`forall n (G:num->num->real) A.
     (forall i j. i < n /\ j < n ==> G i j = G j i)
     ==> forall i j. i < n /\ j < n ==>
          sum {k | k < n} (\k. A k i * sum {l | l < n} (\l. G k l * A l j)) =
          sum {k | k < n} (\k. A k j * sum {l | l < n} (\l. G k l * A l i))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM SUM_LMUL] THEN
  GEN_REWRITE_TAC RAND_CONV [RP_LA_SUM_SWAP_LT] THEN
  MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `l:num` THEN REWRITE_TAC[IN_ELIM_THM] THEN
  DISCH_TAC THEN MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `k:num` THEN
  REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN BETA_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`k:num`; `l:num`]) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN SUBST1_TAC THEN REAL_ARITH_TAC);;

let RP_LA_MAIN_POS = prove
 (`forall n (G:num->num->real) A d.
        (forall i j. i < n /\ j < n ==> G i j = G j i) /\
        (forall a. ~(forall i. i < n ==> a i = &0) ==> &0 < rp_la_qf n G a) /\ &0 < d /\
        (forall a. rp_la_qf n G (\i. sum {k | k < n} (\k. A i k * a k)) <=
             d pow 2 * rp_la_qf n G a)
        ==> abs(ndet {i | i < n} A) <= d pow n`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "sym") (CONJUNCTS_THEN2 (LABEL_TAC "pd")
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "le")))) THEN
  MP_TAC(ISPECL [`n:num`; `\i j. d pow 2 * (G:num->num->real) i j`;
     `\i j. sum {k | k < n} (\k. (A:num->num->real) k i *
                 sum {l | l < n} (\l. (G:num->num->real) k l * A l j))`]
     RP_LA_MONO) THEN
  REWRITE_TAC[RP_LA_QF_CMUL; RP_LA_QF_GRAM] THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN FIRST
     [USE_THEN "le" ACCEPT_TAC;
      GEN_TAC THEN USE_THEN "pd" (fun th -> REWRITE_TAC[MATCH_MP RP_LA_PD_PSD th])
      THEN NO_TAC;
      MATCH_MP_TAC RP_LA_GRAM_SYM THEN USE_THEN "sym" ACCEPT_TAC;
      REPEAT GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC REAL_LT_MUL THEN
      ASM_SIMP_TAC[REAL_POW_LT] THEN NO_TAC;
      REPEAT STRIP_TAC THEN AP_TERM_TAC THEN USE_THEN "sym" MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SIMP_TAC[RP_LA_NDET_CMUL; FINITE_NUMSEG_LT; CARD_NUMSEG_LT] THEN
  SUBGOAL_THEN
   `ndet {i | i < n} (\i j. sum {k | k < n} (\k. (A:num->num->real) k i *
                 sum {l | l < n} (\l. (G:num->num->real) k l * A l j))) =
    ndet {i | i < n} A * (ndet {i | i < n} G * ndet {i | i < n} A)`
  SUBST1_TAC THENL
   [SIMP_TAC[RP_LA_NDET_MUL; FINITE_NUMSEG_LT] THEN
    SIMP_TAC[RP_LA_NDET_TRANSP; FINITE_NUMSEG_LT]; ALL_TAC] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `&0 < ndet {i | i < n} G` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_RCANCEL_IMP THEN
    EXISTS_TAC `((d:real) pow 2) pow n` THEN ASM_SIMP_TAC[REAL_POW_LT; REAL_MUL_LZERO] THEN
    ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `ndet {i | i < n} A pow 2 <= ((d:real) pow 2) pow n` MP_TAC THENL
   [SUBGOAL_THEN `ndet {i | i < n} A pow 2 * ndet {i | i < n} G <=
                  ((d:real) pow 2) pow n * ndet {i | i < n} G` MP_TAC THENL
     [SUBGOAL_THEN `ndet {i | i < n} A pow 2 * ndet {i | i < n} G =
                    ndet {i | i < n} A * (ndet {i | i < n} G * ndet {i | i < n} A)`
      SUBST1_TAC THENL
       [MATCH_ACCEPT_TAC(REAL_RING `forall x g:real. x pow 2 * g = x * (g * x)`);
        ASM_REWRITE_TAC[]];
      ASM_SIMP_TAC[REAL_LE_RMUL_EQ]];
    ALL_TAC] THEN
  REWRITE_TAC[REAL_POW_POW] THEN ONCE_REWRITE_TAC[ARITH_RULE `2 * n = n * 2`] THEN
  REWRITE_TAC[GSYM REAL_POW_POW; GSYM REAL_LE_SQUARE_ABS] THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 <= y ==> abs y = y`; REAL_POW_LE; REAL_LT_IMP_LE]);;

let RP_LA_POW_LE_SELF = prove
 (`forall x n. &0 <= x /\ x <= &1 /\ ~(n = 0) ==> x pow n <= x`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `n:num` num_CASES) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `m:num` SUBST1_TAC) THEN
  REWRITE_TAC[real_pow] THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_POW_1_LE]);;

let RP_LA_ZERO_LIM = prove
 (`forall D n. (forall d. &0 < d ==> abs D <= d pow n) ==> abs D <= &0 pow n`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `n = 0` THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `&1`) THEN
    ASM_REWRITE_TAC[real_pow; REAL_LT_01];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[REAL_POW_ZERO] THEN
  ASM_CASES_TAC `abs D = &0` THENL [ASM_REWRITE_TAC[REAL_LE_REFL]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `min (&1) (abs D / &2)`) THEN
  MP_TAC(SPECL [`min (&1) (abs D / &2)`; `n:num`] RP_LA_POW_LE_SELF) THEN
  ASM_REWRITE_TAC[] THEN POP_ASSUM MP_TAC THEN REAL_ARITH_TAC);;

let RP_LA_MAIN = prove
 (`forall n (G:num->num->real) A c.
        (forall i j. i < n /\ j < n ==> G i j = G j i) /\
        (forall a. ~(forall i. i < n ==> a i = &0) ==> &0 < rp_la_qf n G a) /\ &0 <= c /\
        (forall a. rp_la_qf n G (\i. sum {k | k < n} (\k. A i k * a k)) <=
             c pow 2 * rp_la_qf n G a)
        ==> abs(ndet {i | i < n} A) <= c pow n`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "sym") (CONJUNCTS_THEN2 (LABEL_TAC "pd")
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "le")))) THEN
  ASM_CASES_TAC `c = &0` THENL
   [ALL_TAC;
    MATCH_MP_TAC RP_LA_MAIN_POS THEN EXISTS_TAC `G:num->num->real` THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC] THEN
  SUBGOAL_THEN `forall d. &0 < d ==> abs(ndet {i | i < n} A) <= d pow n`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC RP_LA_MAIN_POS THEN
    EXISTS_TAC `G:num->num->real` THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `a:num->real` THEN
    USE_THEN "le" (MP_TAC o SPEC `a:num->real`) THEN
    USE_THEN "pd" (MP_TAC o SPEC `a:num->real` o MATCH_MP RP_LA_PD_PSD) THEN
    REWRITE_TAC[ASSUME `c = &0`] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    REWRITE_TAC[REAL_MUL_LZERO] THEN
    MP_TAC(SPEC `d:real` REAL_LE_POW_2) THEN
    SPEC_TAC(`rp_la_qf n G a`,`q:real`) THEN
    SPEC_TAC(`rp_la_qf n G (\i. sum {k | k < n} (\k. (A:num->num->real) i k * a k))`,
             `p:real`) THEN
    SPEC_TAC(`(d:real) pow 2`,`e:real`) THEN
    REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
    TRANS_TAC REAL_LE_TRANS `&0` THEN ASM_SIMP_TAC[REAL_LE_MUL];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC RP_LA_ZERO_LIM THEN ASM_REWRITE_TAC[]);;

let RP_LA_THM = prove
 (`RP_LA_STMT`,
  REWRITE_TAC[RP_LA_STMT; GSYM rp_la_qf] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC RP_LA_MAIN THEN EXISTS_TAC `G:num->num->real` THEN
  ASM_REWRITE_TAC[]);;

