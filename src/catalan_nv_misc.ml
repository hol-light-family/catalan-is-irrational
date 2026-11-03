(* ========================================================================= *)
(* CAT_NONVANISHING: integrality, degree and rationality facts for the rows  *)
(* and the rational arrays.                                                  *)
(* ========================================================================= *)

needs "src/catalan_nv_base.ml";;

let NV_CHEB_INT = prove
 (`forall n k. integer(cheb_T n k) /\ integer(cheb_U n k)`,
  SUBGOAL_THEN `forall n. (forall k. integer(cheb_T n k) /\ integer(cheb_U n k)) /\
                    (forall k. integer(cheb_T (SUC n) k) /\ integer(cheb_U (SUC n) k))`
   (fun th -> MESON_TAC[th]) THEN
  INDUCT_TAC THEN ASM_REWRITE_TAC[cheb_T; cheb_U] THENL
   [REPEAT STRIP_TAC THEN REPEAT COND_CASES_TAC THEN REWRITE_TAC[INTEGER_CLOSED];
    GEN_TAC THEN CONJ_TAC THEN
    COND_CASES_TAC THEN ASM_SIMP_TAC[INTEGER_CLOSED]]);;

let NV_CHEB_DEG = prove
 (`forall n k. n < k ==> cheb_T n k = &0 /\ cheb_U n k = &0`,
  SUBGOAL_THEN `forall n. (forall k. n < k ==> cheb_T n k = &0 /\ cheb_U n k = &0) /\
                    (forall k. SUC n < k ==> cheb_T (SUC n) k = &0 /\ cheb_U (SUC n) k = &0)`
   (fun th -> MESON_TAC[th]) THEN
  INDUCT_TAC THEN ASM_REWRITE_TAC[cheb_T; cheb_U] THENL
   [CONJ_TAC THEN GEN_TAC THEN DISCH_TAC THENL
     [SUBGOAL_THEN `~(k = 0)` (fun th -> REWRITE_TAC[th]);
      SUBGOAL_THEN `~(k = 0) /\ ~(k = 1)` (fun th -> REWRITE_TAC[th])] THEN
    POP_ASSUM MP_TAC THEN ARITH_TAC;
    GEN_TAC THEN DISCH_TAC THEN
    SUBGOAL_THEN `~(k = 0) /\ SUC n < k - 1 /\ n < k` STRIP_ASSUME_TAC THENL
     [POP_ASSUM MP_TAC THEN ARITH_TAC; ASM_SIMP_TAC[]] THEN
    REAL_ARITH_TAC]);;

let NV_CHEB_T_DEG = prove
 (`forall n k. n < k ==> cheb_T n k = &0`, SIMP_TAC[NV_CHEB_DEG]);;

let NV_CHEB_U_DEG = prove
 (`forall n k. n < k ==> cheb_U n k = &0`, SIMP_TAC[NV_CHEB_DEG]);;

let NV_CHEB_U_LEAD = prove
 (`forall n. cheb_U n n = &2 pow n`,
  SUBGOAL_THEN `forall n. cheb_U n n = &2 pow n /\ cheb_U (SUC n) (SUC n) = &2 pow (SUC n)`
   (fun th -> MESON_TAC[th]) THEN
  INDUCT_TAC THENL
   [REWRITE_TAC[cheb_U; real_pow] THEN CONV_TAC(NUM_REDUCE_CONV THENC REAL_RAT_REDUCE_CONV);
    ASM_REWRITE_TAC[cheb_U; real_pow; NOT_SUC; SUC_SUB1] THEN
    SIMP_TAC[NV_CHEB_DEG; ARITH_RULE `n < SUC(SUC n)`] THEN REAL_ARITH_TAC]);;

(* Row coefficients are integers. *)

let NV_INT_TAC =
  REPEAT(FIRST [MATCH_ACCEPT_TAC(CONJUNCT1(SPEC_ALL NV_CHEB_INT)); MATCH_ACCEPT_TAC(CONJUNCT2(SPEC_ALL NV_CHEB_INT)); MATCH_ACCEPT_TAC(CONJUNCT1 INTEGER_CLOSED);
                MATCH_MP_TAC INTEGER_SUM THEN REPEAT STRIP_TAC THEN BETA_TAC;
                COND_CASES_TAC; MATCH_MP_TAC INTEGER_MUL THEN CONJ_TAC;
                MATCH_MP_TAC INTEGER_ADD THEN CONJ_TAC; MATCH_MP_TAC INTEGER_SUB THEN CONJ_TAC;
                REWRITE_TAC[INTEGER_NEG] THEN NO_TAC; MATCH_MP_TAC INTEGER_POW;
                CHANGED_TAC(REWRITE_TAC[INTEGER_NEG])]);;

let NV_PCOEF_INT = prove
 (`forall N r i. integer(cat_pcoef N r i) /\ integer(cat_dcoef N r i)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[cat_pcoef; cat_dcoef; cat_mulfac; cat_revc; cat_sgn] THEN
  CONJ_TAC THEN NV_INT_TAC);;

let NV_DIST_LE = prove
 (`forall N r. r < 48 * N ==> cat_dist N r <= 44 * N`,
  REWRITE_TAC[cat_dist] THEN ARITH_TAC);;

let NV_PCOEF_LOW = prove
 (`forall N r i. r < 48 * N /\ i < N ==> cat_pcoef N r i = &0 /\ cat_dcoef N r i = &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP NV_DIST_LE) THEN
  REWRITE_TAC[cat_pcoef; cat_dcoef; cat_mulfac; cat_revc; REAL_ENTIRE] THEN
  CONJ_TAC THEN TRY DISJ2_TAC THEN MATCH_MP_TAC SUM_EQ_0 THEN
  X_GEN_TAC `v:num` THEN REWRITE_TAC[IN_NUMSEG] THEN STRIP_TAC THEN
  REPEAT(COND_CASES_TAC THEN REWRITE_TAC[REAL_MUL_RZERO]) THEN
  REWRITE_TAC[REAL_ENTIRE] THEN REPEAT DISJ2_TAC THEN
  (MATCH_MP_TAC NV_CHEB_T_DEG ORELSE MATCH_MP_TAC NV_CHEB_U_DEG) THEN ASM_ARITH_TAC);;

let NV_PCOEF_HIGH = prove
 (`forall N r i. 65 * N <= i ==> cat_pcoef N r i = &0 /\ cat_dcoef N r i = &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[cat_pcoef; cat_dcoef; cat_mulfac; cat_revc; REAL_ENTIRE] THEN
  CONJ_TAC THEN TRY DISJ2_TAC THEN MATCH_MP_TAC SUM_EQ_0 THEN
  X_GEN_TAC `v:num` THEN REWRITE_TAC[IN_NUMSEG] THEN STRIP_TAC THEN
  REPEAT(COND_CASES_TAC THEN REWRITE_TAC[REAL_MUL_RZERO]) THEN ASM_ARITH_TAC);;

(* Rationality of the arrays. *)

let NV_RAT_TAC ths =
  REPEAT GEN_TAC THEN REPEAT(FIRST (map MATCH_ACCEPT_TAC ths @
               [MATCH_ACCEPT_TAC RATIONAL_NUM; FIRST_ASSUM MATCH_ACCEPT_TAC; CONJ_TAC;
                MATCH_MP_TAC RATIONAL_SUM THEN REPEAT STRIP_TAC THEN BETA_TAC;
                COND_CASES_TAC;
                MATCH_MP_TAC RATIONAL_MUL THEN CONJ_TAC;
                MATCH_MP_TAC RATIONAL_DIV THEN CONJ_TAC;
                MATCH_MP_TAC RATIONAL_ADD THEN CONJ_TAC;
                MATCH_MP_TAC RATIONAL_SUB THEN CONJ_TAC;
                MATCH_MP_TAC RATIONAL_NEG; MATCH_MP_TAC RATIONAL_POW;
                MATCH_MP_TAC RATIONAL_INV]));;

let NV_RAT_C = prove
 (`forall l. rational(cat_c l)`,
  REWRITE_TAC[cat_c] THEN NV_RAT_TAC[]);;

let NV_RAT_M = prove
 (`forall i. rational(cat_m i)`,
  REWRITE_TAC[cat_m] THEN NV_RAT_TAC[NV_RAT_C]);;

let NV_RAT_KMINUS = prove
 (`forall d. rational(cat_kminus d)`,
  SUBGOAL_THEN `forall d. rational(cat_kminus d) /\ rational(cat_kminus(SUC d))`
   (fun th -> MESON_TAC[th]) THEN
  INDUCT_TAC THEN REWRITE_TAC[cat_kminus] THEN TRY(POP_ASSUM STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[] THEN NV_RAT_TAC[NV_RAT_M]);;

let NV_RAT_KPLUS = prove
 (`forall d. rational(cat_kplus d)`,
  SUBGOAL_THEN `forall d. rational(cat_kplus d) /\ rational(cat_kplus(SUC d))`
   (fun th -> MESON_TAC[th]) THEN
  INDUCT_TAC THEN REWRITE_TAC[cat_kplus] THEN TRY(POP_ASSUM STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[] THEN NV_RAT_TAC[NV_RAT_M]);;

let NV_RAT_M0 = prove
 (`forall i j. rational(cat_M0 i j)`,
  REWRITE_TAC[cat_M0] THEN NV_RAT_TAC[NV_RAT_M; NV_RAT_KMINUS; NV_RAT_KPLUS]);;

let NV_RAT_Z0 = prove
 (`forall i j. rational(cat_Z0 i j)`,
  REWRITE_TAC[cat_Z0; cat_harm] THEN NV_RAT_TAC[]);;

let NV_RAT_CKERN = prove
 (`forall i j. rational(cat_ckern i j)`,
  REWRITE_TAC[cat_ckern] THEN NV_RAT_TAC[NV_RAT_C]);;

let NV_RAT_PCOEF = prove
 (`forall N r i. rational(cat_pcoef N r i) /\ rational(cat_dcoef N r i)`,
  MESON_TAC[NV_PCOEF_INT; RATIONAL_INTEGER]);;

let NV_RAT_RAWQ = prove
 (`forall z N r j. rational z ==> rational(cat_rawq z N r j)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[cat_rawq] THEN
  NV_RAT_TAC[NV_RAT_M0; NV_RAT_Z0; NV_RAT_CKERN; CONJUNCT1(SPEC_ALL NV_RAT_PCOEF);
             CONJUNCT2(SPEC_ALL NV_RAT_PCOEF)] THEN ASM_REWRITE_TAC[]);;

let NV_RAT_ENTRYQ = prove
 (`forall z N r k. rational z ==> rational(cat_entryq z N r k)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[cat_entryq] THEN
  NV_RAT_TAC[] THEN ASM_SIMP_TAC[NV_RAT_RAWQ]);;

let NV_RAT_NDET = prove
 (`forall s a. FINITE s /\ (forall i j. i IN s /\ j IN s ==> rational(a i j)) ==> rational(ndet s a)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[ndet] THEN
  MATCH_MP_TAC RATIONAL_SUM THEN REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
  BETA_TAC THEN MATCH_MP_TAC RATIONAL_MUL THEN CONJ_TAC THENL
   [REWRITE_TAC[sign] THEN COND_CASES_TAC THEN NV_RAT_TAC[];
    MATCH_MP_TAC PRODUCT_CLOSED THEN ASM_SIMP_TAC[RATIONAL_CLOSED] THEN
    ASM_MESON_TAC[PERMUTES_IN_IMAGE]]);;
