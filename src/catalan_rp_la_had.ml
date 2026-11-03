(* ========================================================================= *)
(* rp_la_: RP_HAD_THM : |- RP_HAD_STMT (Proposition 5.3, Hadamard estimate). *)
(* Real PSD Hadamard (Schur induction); complex projective Vandermonde with  *)
(* real Gram matrix gives |V(z)| <= sqrt(m)^m 2^-C(m,2) prod sqrt(1+z^2)^(m-1) *)
(* (RP_LA_WVDM); multilinear expansion of rp_R by sheets (RP_LA_SHEET).     *)
(* ========================================================================= *)

needs "src/catalan_rp_la_det.ml";;
let RP_LA_SQ_DIV_POS = prove
 (`forall x y. &0 < y ==> &0 <= x * x / y`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[real_div; REAL_MUL_ASSOC] THEN
  MATCH_MP_TAC REAL_LE_MUL THEN
  ASM_SIMP_TAC[REAL_LE_SQUARE; REAL_LE_INV_EQ; REAL_LT_IMP_LE]);;

let RP_LA_HADAMARD_PSD = prove
 (`forall n (G:num->num->real).
        (forall i j. i < n /\ j < n ==> G i j = G j i) /\
        (forall a. &0 <= rp_la_qf n G a)
        ==> &0 <= ndet {i | i < n} G /\
            ndet {i | i < n} G <= product {i | i < n} (\i. G i i)`,
  INDUCT_TAC THENL
   [REWRITE_TAC[NUMSEG_CLAUSES_LT; RP_LA_NDET_EMPTY; PRODUCT_CLAUSES] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `forall i j. i <= n /\ j <= n ==> (G:num->num->real) i j = G j i`
  (LABEL_TAC "symle") THENL
   [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN RP_LA_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `forall i. i < SUC n ==> &0 <= (G:num->num->real) i i` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `\j:num. if j = i then &1 else &0`) THEN
    ASM_SIMP_TAC[RP_LA_QF_DELTA]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= product {i | i < SUC n} (\i. (G:num->num->real) i i)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC PRODUCT_POS_LE THEN ASM_SIMP_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM];
    ALL_TAC] THEN
  ASM_CASES_TAC `(G:num->num->real) n n = &0` THENL
   [SUBGOAL_THEN `ndet {i | i < SUC n} G = &0` SUBST1_TAC THENL
     [MATCH_MP_TAC RP_LA_NDET_ZERO_ROW THEN EXISTS_TAC `n:num` THEN
      REWRITE_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM; LT] THEN
      MP_TAC(SPECL [`n:num`; `G:num->num->real`] RP_LA_PSD_ZERO_DIAG) THEN
      ASM_REWRITE_TAC[LT];
      ASM_REWRITE_TAC[REAL_LE_REFL]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < (G:num->num->real) n n` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN REWRITE_TAC[LT] THEN
    ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `S = \i j. (G:num->num->real) i j - G i n * G n j / G n n` THEN
  SUBGOAL_THEN `forall i j. i < n /\ j < n ==> (S:num->num->real) i j = S j i`
  ASSUME_TAC THENL
   [EXPAND_TAC "S" THEN MATCH_MP_TAC RP_LA_SCHUR_SYM THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `forall x. &0 <= rp_la_qf n S x` ASSUME_TAC THENL
   [GEN_TAC THEN EXPAND_TAC "S" THEN
    ASM_SIMP_TAC[RP_LA_SCHUR_FORM_OPT]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `S:num->num->real`) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[RP_LA_SCHUR_DET] THEN
  SIMP_TAC[NUMSEG_CLAUSES_LT; PRODUCT_CLAUSES; FINITE_NUMSEG_LT; IN_ELIM_THM;
           LT_REFL] THEN
  CONJ_TAC THENL [ASM_SIMP_TAC[REAL_LE_MUL; REAL_LT_IMP_LE]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
  TRANS_TAC REAL_LE_TRANS `product {i | i < n} (\i. (S:num->num->real) i i)` THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC PRODUCT_LE THEN
  REWRITE_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM] THEN X_GEN_TAC `i:num` THEN
  DISCH_TAC THEN CONJ_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `\j:num. if j = i then &1 else &0`) THEN
    ASM_SIMP_TAC[RP_LA_QF_DELTA];
    EXPAND_TAC "S" THEN
    USE_THEN "symle" (MP_TAC o SPECL [`i:num`; `n:num`]) THEN
    ANTS_TAC THENL [RP_LA_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
    REWRITE_TAC[REAL_ARITH `a - b <= a <=> &0 <= b`] THEN
    MATCH_MP_TAC RP_LA_SQ_DIV_POS THEN ASM_REWRITE_TAC[]]);;

let rp_la_cring = new_definition
 `rp_la_cring = ring((:complex),Cx(&0),Cx(&1),( -- ),( + ),( * ))`;;

let RP_LA_CRING_CLAUSES = prove
 (`ring_carrier rp_la_cring = (:complex) /\
   ring_0 rp_la_cring = Cx(&0) /\
   ring_1 rp_la_cring = Cx(&1) /\
   ring_neg rp_la_cring = ( -- ) /\
   ring_add rp_la_cring = ( + ) /\
   ring_mul rp_la_cring = ( * )`,
  PURE_REWRITE_TAC
   [GSYM PAIR_EQ; ring_carrier; ring_0; ring_1; ring_neg; ring_add; ring_mul;
    BETA_THM; PAIR] THEN
  PURE_REWRITE_TAC[rp_la_cring; GSYM(CONJUNCT2 ring_tybij)] THEN
  REWRITE_TAC[IN_UNIV] THEN CONV_TAC COMPLEX_RING);;

let RP_LA_CRING_POW = prove
 (`ring_pow rp_la_cring = (pow)`,
  REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN INDUCT_TAC THEN
  ASM_REWRITE_TAC[ring_pow; complex_pow; RP_LA_CRING_CLAUSES]);;

let RP_LA_CRING_SUB = prove
 (`ring_sub rp_la_cring = (-)`,
  REWRITE_TAC[FUN_EQ_THM; ring_sub; RP_LA_CRING_CLAUSES; complex_sub]);;

let RP_LA_CRING_SUM = prove
 (`forall s (f:A->complex). FINITE s ==> ring_sum rp_la_cring s f = vsum s f`,
  REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[RING_SUM_CLAUSES; VSUM_CLAUSES; RP_LA_CRING_CLAUSES; IN_UNIV;
           COMPLEX_VEC_0]);;

let RP_LA_CRING_PRODUCT = prove
 (`forall s (f:A->complex). FINITE s ==> ring_product rp_la_cring s f = cproduct s f`,
  REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[RING_PRODUCT_CLAUSES; CPRODUCT_CLAUSES; RP_LA_CRING_CLAUSES; IN_UNIV]);;

let RP_LA_CX_HOM = prove
 (`ring_homomorphism(real_ring,rp_la_cring) Cx`,
  REWRITE_TAC[ring_homomorphism; REAL_RING_CLAUSES; RP_LA_CRING_CLAUSES;
              SUBSET_UNIV; CX_ADD; CX_MUL; CX_NEG]);;

let RP_LA_CNJ_HOM = prove
 (`ring_homomorphism(rp_la_cring,rp_la_cring) cnj`,
  REWRITE_TAC[ring_homomorphism; RP_LA_CRING_CLAUSES;
              SUBSET_UNIV; CNJ_ADD; CNJ_MUL; CNJ_NEG; CNJ_CX]);;

let RP_LA_CX_NDET = prove
 (`forall s (a:num->num->real).
        FINITE s
        ==> Cx(ndet s a) = ring_det rp_la_cring s (\i j. Cx(a i j))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[RP_LA_NDET_RING] THEN
  MATCH_MP_TAC(ISPECL [`real_ring`; `rp_la_cring`; `Cx`] RING_DET_HOMOMORPHISM) THEN
  ASM_REWRITE_TAC[RP_LA_CX_HOM; REAL_RING_CLAUSES; IN_UNIV]);;

let RP_LA_CNJ_CDET = prove
 (`forall s (a:num->num->complex).
        FINITE s
        ==> cnj(ring_det rp_la_cring s a) =
            ring_det rp_la_cring s (\i j. cnj(a i j))`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(ISPECL [`rp_la_cring`; `rp_la_cring`; `cnj`] RING_DET_HOMOMORPHISM) THEN
  ASM_REWRITE_TAC[RP_LA_CNJ_HOM; RP_LA_CRING_CLAUSES; IN_UNIV]);;

let RP_LA_CDET_MUL = prove
 (`forall s (a:num->num->complex) b.
        FINITE s
        ==> ring_det rp_la_cring s (\i j. vsum s (\k. a i k * b k j)) =
            ring_det rp_la_cring s a * ring_det rp_la_cring s b`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`rp_la_cring`; `s:num->bool`; `a:num->num->complex`;
                 `b:num->num->complex`] RING_DET_MUL) THEN
  ASM_SIMP_TAC[RP_LA_CRING_CLAUSES; IN_UNIV; RP_LA_CRING_SUM]);;

let RP_LA_CDET_TRANSP = prove
 (`forall s (a:num->num->complex).
        FINITE s
        ==> ring_det rp_la_cring s (\i j. a j i) = ring_det rp_la_cring s a`,
  SIMP_TAC[RING_DET_TRANSP]);;

let RP_LA_CDET_ROWS_MUL = prove
 (`forall s c (f:num->num->complex).
        FINITE s
        ==> ring_det rp_la_cring s (\i j. c i * f i j) =
            cproduct s c * ring_det rp_la_cring s f`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`rp_la_cring`; `s:num->bool`; `c:num->complex`;
                 `f:num->num->complex`] RING_DET_ROWS_MUL) THEN
  ASM_SIMP_TAC[RP_LA_CRING_CLAUSES; IN_UNIV; RP_LA_CRING_PRODUCT]);;

let RP_LA_CDET_VANDERMONDE = prove
 (`forall n (x:num->complex).
        ring_det rp_la_cring {i | i < n} (\i j. x i pow j) =
        cproduct {j | j < n} (\j. cproduct {i | i < j} (\i. x j - x i))`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`rp_la_cring`; `n:num`; `x:num->complex`]
    RING_DET_VANDERMONDE) THEN
  SIMP_TAC[RP_LA_CRING_CLAUSES; IN_UNIV; RP_LA_CRING_PRODUCT; RP_LA_CRING_POW;
           RP_LA_CRING_SUB; FINITE_NUMSEG_LT]);;

let RP_LA_PROD_PAIRS = prove
 (`forall m (a:num->real).
        product {j | j < m} (\j. product {i | i < j} (\i. a i * a j)) =
        product {i | i < m} (\i. a i pow (m - 1))`,
  INDUCT_TAC THEN GEN_TAC THENL
   [REWRITE_TAC[NUMSEG_CLAUSES_LT; PRODUCT_CLAUSES]; ALL_TAC] THEN
  SIMP_TAC[NUMSEG_CLAUSES_LT; PRODUCT_CLAUSES; FINITE_NUMSEG_LT; IN_ELIM_THM;
           LT_REFL] THEN
  ASM_REWRITE_TAC[] THEN
  SIMP_TAC[PRODUCT_MUL; FINITE_NUMSEG_LT; PRODUCT_CONST; CARD_NUMSEG_LT] THEN
  REWRITE_TAC[SUC_SUB1] THEN
  SUBGOAL_THEN `product {i | i < m} (\i. (a:num->real) i pow m) =
                product {i | i < m} a * product {i | i < m} (\i. a i pow (m - 1))`
  SUBST1_TAC THENL
   [SIMP_TAC[GSYM PRODUCT_MUL; FINITE_NUMSEG_LT] THEN
    MATCH_MP_TAC PRODUCT_EQ THEN REWRITE_TAC[IN_ELIM_THM] THEN
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN BETA_TAC THEN
    GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [MATCH_MP (ARITH_RULE `i < m ==> m = SUC(m - 1)`) (ASSUME `i:num < m`)] THEN
    REWRITE_TAC[real_pow];
    MATCH_ACCEPT_TAC(REAL_RING `forall x y z:real. (x * y) * z = y * x * z`)]);;

let RP_LA_TRIANGLE_DIV = prove
 (`forall m. (SUC m * (SUC m - 1)) DIV 2 = m + (m * (m - 1)) DIV 2`,
  GEN_TAC THEN REWRITE_TAC[SUC_SUB1] THEN
  SUBGOAL_THEN `SUC m * m = m * 2 + m * (m - 1)` SUBST1_TAC THENL
   [STRUCT_CASES_TAC(SPEC `m:num` num_CASES) THEN
    REWRITE_TAC[SUC_SUB1; MULT_CLAUSES] THEN ARITH_TAC;
    SIMP_TAC[DIV_MULT_ADD; ARITH_EQ]]);;

let RP_LA_PROD_TWO = prove
 (`forall m c. product {j | j < m} (\j. product {i | i < j} (\i. c)) =
         c pow ((m * (m - 1)) DIV 2)`,
  INDUCT_TAC THEN GEN_TAC THENL
   [REWRITE_TAC[NUMSEG_CLAUSES_LT; PRODUCT_CLAUSES] THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[real_pow];
    ALL_TAC] THEN
  SIMP_TAC[NUMSEG_CLAUSES_LT; PRODUCT_CLAUSES; FINITE_NUMSEG_LT; IN_ELIM_THM;
           LT_REFL] THEN
  ASM_REWRITE_TAC[RP_LA_TRIANGLE_DIV; REAL_POW_ADD] THEN
  SIMP_TAC[PRODUCT_CONST; FINITE_NUMSEG_LT; CARD_NUMSEG_LT]);;

let RP_LA_NORM_ZPI = prove
 (`forall x. norm(Cx x + ii) = sqrt(&1 + x pow 2) /\
       norm(Cx x - ii) = sqrt(&1 + x pow 2)`,
  REWRITE_TAC[complex_norm; RE_ADD; IM_ADD; RE_SUB; IM_SUB; RE_CX; IM_CX;
              RE_II; IM_II] THEN
  GEN_TAC THEN CONJ_TAC THEN AP_TERM_TAC THEN REAL_ARITH_TAC);;

let RP_LA_ZMI_NZ = prove
 (`forall x. ~(Cx x - ii = Cx(&0))`,
  REWRITE_TAC[COMPLEX_EQ; IM_SUB; IM_CX; IM_II] THEN REAL_ARITH_TAC);;

let RP_LA_SQRT1_POS = prove
 (`forall x. &0 < sqrt(&1 + x pow 2)`,
  GEN_TAC THEN MATCH_MP_TAC SQRT_POS_LT THEN
  MP_TAC(SPEC `x:real` REAL_LE_POW_2) THEN REAL_ARITH_TAC);;

let RP_LA_PROJ_DET_NORM = prove
 (`forall m (z:num->real).
     norm(ring_det rp_la_cring {i | i < m}
            (\i j. (Cx(z i) + ii) pow j * (Cx(z i) - ii) pow (m - 1 - j))) =
     &2 pow ((m * (m - 1)) DIV 2) * abs(rp_vdm m z)`,
  REPEAT GEN_TAC THEN
  ABBREV_TAC `y = \i. (Cx((z:num->real) i) + ii) / (Cx(z i) - ii)` THEN
  SUBGOAL_THEN
   `ring_det rp_la_cring {i | i < m}
      (\i j. (Cx(z i) + ii) pow j * (Cx(z i) - ii) pow (m - 1 - j)) =
    ring_det rp_la_cring {i | i < m}
      (\i j. (Cx((z:num->real) i) - ii) pow (m - 1) * (y:num->complex) i pow j)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC RING_DET_EQ THEN REWRITE_TAC[IN_ELIM_THM] THEN
    MAP_EVERY X_GEN_TAC [`i:num`; `j:num`] THEN STRIP_TAC THEN
    EXPAND_TAC "y" THEN REWRITE_TAC[COMPLEX_POW_DIV] THEN
    SUBGOAL_THEN `m - 1 = (m - 1 - j) + j:num` SUBST1_TAC THENL
     [RP_LA_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[ARITH_RULE `(a + j) - j = a:num`; COMPLEX_POW_ADD] THEN
    SUBGOAL_THEN `~((Cx((z:num->real) i) - ii) pow j = Cx(&0))` MP_TAC THENL
     [REWRITE_TAC[COMPLEX_POW_EQ_0; RP_LA_ZMI_NZ]; ALL_TAC] THEN
    CONV_TAC COMPLEX_FIELD;
    ALL_TAC] THEN
  SIMP_TAC[RP_LA_CDET_ROWS_MUL; FINITE_NUMSEG_LT; RP_LA_CDET_VANDERMONDE] THEN
  SIMP_TAC[COMPLEX_NORM_MUL; NORM_CPRODUCT; FINITE_NUMSEG_LT; COMPLEX_NORM_POW;
           RP_LA_NORM_ZPI] THEN
  SUBGOAL_THEN
   `forall i j. norm((y:num->complex) j - y i) =
          &2 * abs((z:num->real) j - z i) *
          inv(sqrt(&1 + z i pow 2) * sqrt(&1 + z j pow 2))`
  (fun th -> REWRITE_TAC[th]) THENL
   [REPEAT GEN_TAC THEN EXPAND_TAC "y" THEN
    SUBGOAL_THEN
     `(Cx((z:num->real) j) + ii) / (Cx(z j) - ii) - (Cx(z i) + ii) / (Cx(z i) - ii) =
      --(Cx(&2) * ii * Cx(z j - z i) / ((Cx(z i) - ii) * (Cx(z j) - ii)))`
    SUBST1_TAC THENL
     [MP_TAC(SPEC `(z:num->real) i` RP_LA_ZMI_NZ) THEN
      MP_TAC(SPEC `(z:num->real) j` RP_LA_ZMI_NZ) THEN
      REWRITE_TAC[CX_SUB] THEN CONV_TAC COMPLEX_FIELD;
      ALL_TAC] THEN
    REWRITE_TAC[NORM_NEG; COMPLEX_NORM_MUL; COMPLEX_NORM_DIV; COMPLEX_NORM_CX;
                COMPLEX_NORM_II; RP_LA_NORM_ZPI] THEN
    REWRITE_TAC[real_div; REAL_ABS_NUM; REAL_MUL_LID];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM RP_LA_PROD_PAIRS] THEN
  SIMP_TAC[GSYM PRODUCT_MUL; FINITE_NUMSEG_LT] THEN
  REWRITE_TAC[GSYM(SPECL [`m:num`; `&2`] RP_LA_PROD_TWO); rp_vdm] THEN
  SIMP_TAC[GSYM PRODUCT_ABS; FINITE_NUMSEG_LT] THEN
  SIMP_TAC[GSYM PRODUCT_MUL; FINITE_NUMSEG_LT] THEN
  MATCH_MP_TAC PRODUCT_EQ THEN X_GEN_TAC `j:num` THEN DISCH_TAC THEN
  BETA_TAC THEN
  MATCH_MP_TAC PRODUCT_EQ THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  BETA_TAC THEN
  MATCH_MP_TAC(REAL_FIELD `~(p = &0) ==> p * (t * v * inv p) = t * v`) THEN
  MATCH_MP_TAC(REAL_ARITH `&0 < x ==> ~(x = &0)`) THEN
  MATCH_MP_TAC REAL_LT_MUL THEN REWRITE_TAC[RP_LA_SQRT1_POS]);;

let RP_LA_VSUM_REFLECT_LT = prove
 (`forall m (f:num->complex).
        vsum {j | j < m} f = vsum {j | j < m} (\j. f (m - 1 - j))`,
  GEN_TAC THEN ASM_CASES_TAC `m = 0` THENL
   [ASM_REWRITE_TAC[NUMSEG_CLAUSES_LT; VSUM_CLAUSES]; ALL_TAC] THEN
  ASM_SIMP_TAC[GSYM RP_NUMSEG_LT; LE_1] THEN GEN_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [VSUM_REFLECT] THEN
  REWRITE_TAC[ARITH_RULE `~(m - 1 < 0)`; SUB_0]);;

let RP_LA_GRAM_REAL = prove
 (`forall m a. real(vsum {j | j < m} (\j. a pow j * cnj a pow (m - 1 - j)))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[REAL_CNJ] THEN
  SIMP_TAC[CNJ_VSUM; FINITE_NUMSEG_LT; CNJ_MUL; CNJ_POW; CNJ_CNJ] THEN
  GEN_REWRITE_TAC LAND_CONV [RP_LA_VSUM_REFLECT_LT] THEN
  MATCH_MP_TAC VSUM_EQ THEN REWRITE_TAC[IN_ELIM_THM] THEN
  X_GEN_TAC `j:num` THEN DISCH_TAC THEN BETA_TAC THEN
  SUBGOAL_THEN `m - 1 - (m - 1 - j) = j:num` SUBST1_TAC THENL
   [RP_LA_ARITH_TAC; REWRITE_TAC[COMPLEX_MUL_SYM]]);;

let RP_LA_CNJ_ZPI = prove
 (`forall x. cnj(Cx x + ii) = Cx x - ii /\ cnj(Cx x - ii) = Cx x + ii`,
  REWRITE_TAC[CNJ_ADD; CNJ_SUB; CNJ_CX; CNJ_II] THEN
  CONV_TAC COMPLEX_RING);;

let RP_LA_PROJ_TERM = prove
 (`forall x y j m.
     ((Cx x + ii) pow j * (Cx x - ii) pow (m - 1 - j)) *
     cnj((Cx y + ii) pow j * (Cx y - ii) pow (m - 1 - j)) =
     ((Cx x + ii) * (Cx y - ii)) pow j *
     cnj((Cx x + ii) * (Cx y - ii)) pow (m - 1 - j)`,
  REWRITE_TAC[CNJ_MUL; CNJ_POW; RP_LA_CNJ_ZPI; COMPLEX_POW_MUL] THEN
  CONV_TAC COMPLEX_RING);;

let RP_LA_RE_MUL_CNJ = prove
 (`forall p q. Re(p * cnj q) = Re p * Re q + Im p * Im q`,
  REWRITE_TAC[cnj; complex_mul; RE; IM] THEN REAL_ARITH_TAC);;

let RP_LA_SUM_GRAM_PSD = prove
 (`forall s (a:num->real) X Y.
        FINITE s
        ==> sum s (\i. sum s (\k. a i * (X i * X k + Y i * Y k) * a k)) =
            sum s (\i. a i * X i) pow 2 + sum s (\i. a i * Y i) pow 2`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[REAL_POW_2] THEN ASM_SIMP_TAC[GSYM SUM_LMUL; GSYM SUM_RMUL] THEN
  ASM_SIMP_TAC[GSYM SUM_ADD] THEN
  MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN BETA_TAC THEN
  ASM_SIMP_TAC[GSYM SUM_ADD] THEN
  MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `k:num` THEN DISCH_TAC THEN BETA_TAC THEN
  REAL_ARITH_TAC);;

let rp_la_proj = new_definition
 `rp_la_proj m (z:num->real) i j =
    (Cx(z i) + ii) pow j * (Cx(z i) - ii) pow (m - 1 - j)`;;

let rp_la_gram = new_definition
 `rp_la_gram m (z:num->real) i k =
    Re(vsum {j | j < m} (\j. rp_la_proj m z i j * cnj(rp_la_proj m z k j)))`;;

let RP_LA_GRAM_CX = prove
 (`forall m z i k. Cx(rp_la_gram m z i k) =
             vsum {j | j < m} (\j. rp_la_proj m z i j * cnj(rp_la_proj m z k j))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[rp_la_gram; GSYM REAL] THEN
  REWRITE_TAC[rp_la_proj; RP_LA_PROJ_TERM; RP_LA_GRAM_REAL]);;

let RP_LA_GRAM_DET = prove
 (`forall m z. ndet {i | i < m} (rp_la_gram m z) =
         norm(ring_det rp_la_cring {i | i < m} (rp_la_proj m z)) pow 2`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM CX_INJ; CX_POW] THEN
  SIMP_TAC[RP_LA_CX_NDET; FINITE_NUMSEG_LT; RP_LA_GRAM_CX] THEN
  MP_TAC(ISPECL [`{i:num | i < m}`; `rp_la_proj m z`;
                 `\k j. cnj(rp_la_proj m z j k)`] RP_LA_CDET_MUL) THEN
  REWRITE_TAC[FINITE_NUMSEG_LT] THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN
   `ring_det rp_la_cring {i:num | i < m} (\k j. cnj(rp_la_proj m z j k)) =
    cnj(ring_det rp_la_cring {i:num | i < m} (rp_la_proj m z))`
  SUBST1_TAC THENL
   [SIMP_TAC[RP_LA_CNJ_CDET; FINITE_NUMSEG_LT] THEN
    MP_TAC(ISPECL [`{i:num | i < m}`; `\i j. cnj(rp_la_proj m z i j)`]
      RP_LA_CDET_TRANSP) THEN
    REWRITE_TAC[FINITE_NUMSEG_LT] THEN DISCH_THEN ACCEPT_TAC;
    REWRITE_TAC[COMPLEX_MUL_CNJ]]);;

let RP_LA_GRAMC_SYM = prove
 (`forall m z i k. rp_la_gram m z i k = rp_la_gram m z k i`,
  REPEAT GEN_TAC THEN REWRITE_TAC[rp_la_gram] THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM RE_CNJ] THEN
  SIMP_TAC[CNJ_VSUM; FINITE_NUMSEG_LT; CNJ_MUL; CNJ_CNJ] THEN
  REWRITE_TAC[COMPLEX_MUL_SYM]);;

let RP_LA_GRAM_PSD = prove
 (`forall m z a. &0 <= rp_la_qf m (rp_la_gram m z) a`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[rp_la_qf; rp_la_gram] THEN
  SIMP_TAC[RE_VSUM; FINITE_NUMSEG_LT; RP_LA_RE_MUL_CNJ] THEN
  REWRITE_TAC[GSYM SUM_LMUL; GSYM SUM_RMUL] THEN
  CONV_TAC(RAND_CONV(BINDER_CONV RP_LA_SWAP_CONV)) THEN
  CONV_TAC(RAND_CONV RP_LA_SWAP_CONV) THEN
  MATCH_MP_TAC SUM_POS_LE THEN REWRITE_TAC[FINITE_NUMSEG_LT] THEN
  X_GEN_TAC `j:num` THEN DISCH_TAC THEN BETA_TAC THEN
  MP_TAC(ISPECL [`{i:num | i < m}`; `a:num->real`;
     `\i. Re(rp_la_proj m z i j)`; `\i. Im(rp_la_proj m z i j)`]
     RP_LA_SUM_GRAM_PSD) THEN
  REWRITE_TAC[FINITE_NUMSEG_LT] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC REAL_LE_ADD THEN REWRITE_TAC[REAL_LE_POW_2]);;

let RP_LA_GRAM_DIAG = prove
 (`forall m z i. rp_la_gram m z i i = &m * (sqrt(&1 + z i pow 2) pow (m - 1)) pow 2`,
  REPEAT GEN_TAC THEN REWRITE_TAC[rp_la_gram; COMPLEX_MUL_CNJ] THEN
  SIMP_TAC[RE_VSUM; FINITE_NUMSEG_LT; GSYM CX_POW; RE_CX] THEN
  REWRITE_TAC[rp_la_proj; COMPLEX_NORM_MUL; COMPLEX_NORM_POW; RP_LA_NORM_ZPI] THEN
  REWRITE_TAC[GSYM REAL_POW_ADD] THEN
  TRANS_TAC EQ_TRANS
   `sum {j | j < m} (\j. (sqrt(&1 + (z:num->real) i pow 2) pow (m - 1)) pow 2)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_EQ THEN REWRITE_TAC[IN_ELIM_THM] THEN
    REPEAT STRIP_TAC THEN BETA_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    AP_TERM_TAC THEN RP_LA_ARITH_TAC;
    SIMP_TAC[SUM_CONST; FINITE_NUMSEG_LT; CARD_NUMSEG_LT]]);;

let RP_LA_PRODUCT_SQ = prove
 (`forall s (f:num->real). FINITE s ==> product s (\i. f i pow 2) = product s f pow 2`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[REAL_POW_2] THEN
  ASM_SIMP_TAC[PRODUCT_MUL]);;

let RP_LA_SQRT_POW = prove
 (`forall m. &m pow m = (sqrt(&m) pow m) pow 2`,
  GEN_TAC THEN REWRITE_TAC[REAL_POW_POW] THEN ONCE_REWRITE_TAC[MULT_SYM] THEN
  REWRITE_TAC[GSYM REAL_POW_POW] THEN SIMP_TAC[SQRT_POW_2; REAL_POS]);;

let RP_LA_FIN = prove
 (`forall t v s q. &0 < t /\ &0 <= v /\ &0 <= s /\ &0 <= q /\
             (t * v) pow 2 <= (s * q) pow 2 ==> v <= s * inv t * q`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `t * v <= s * q` ASSUME_TAC THENL
   [MP_TAC(SPECL [`t * v:real`; `s * q:real`] REAL_LE_SQUARE_ABS) THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 <= x ==> abs x = x`; REAL_LE_MUL;
                 REAL_LT_IMP_LE];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_LCANCEL_IMP THEN EXISTS_TAC `t:real` THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(t:real) * s * inv t * q = s * q` SUBST1_TAC THENL
   [MATCH_MP_TAC(REAL_FIELD `&0 < t ==> t * s * inv t * q = s * q`) THEN
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[]]);;

let RP_LA_WVDM = prove
 (`forall m (z:num->real).
      abs(rp_vdm m z) <=
      sqrt(&m) pow m * inv(&2) pow ((m * (m - 1)) DIV 2) *
      product {i | i < m} (\i. sqrt(&1 + z i pow 2) pow (m - 1))`,
  REPEAT GEN_TAC THEN
  MP_TAC(SPECL [`m:num`; `z:num->real`] RP_LA_PROJ_DET_NORM) THEN
  REWRITE_TAC[GSYM rp_la_proj] THEN REWRITE_TAC[ETA_AX] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`m:num`; `rp_la_gram m z`] RP_LA_HADAMARD_PSD) THEN
  REWRITE_TAC[RP_LA_GRAM_PSD; RP_LA_GRAM_DIAG; RP_LA_GRAM_DET] THEN
  ANTS_TAC THENL [MESON_TAC[RP_LA_GRAMC_SYM]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SIMP_TAC[PRODUCT_MUL; FINITE_NUMSEG_LT; PRODUCT_CONST; CARD_NUMSEG_LT;
           RP_LA_PRODUCT_SQ] THEN
  REWRITE_TAC[RP_LA_SQRT_POW; GSYM REAL_POW_MUL; REAL_POW_INV] THEN
  STRIP_TAC THEN MATCH_MP_TAC RP_LA_FIN THEN ASM_REWRITE_TAC[REAL_ABS_POS] THEN
  SIMP_TAC[REAL_POW_LT; REAL_ARITH `&0 < &2`; REAL_POW_LE; SQRT_POS_LE;
           REAL_POS] THEN
  MATCH_MP_TAC PRODUCT_POS_LE THEN
  SIMP_TAC[FINITE_NUMSEG_LT; REAL_POW_LE; RP_LA_SQRT1_POS; REAL_LT_IMP_LE]);;

let RP_LA_LE_MUL_SCAL = prove
 (`forall a b c d s:real. &0 <= s /\ a * c <= b * d ==> a * (s * c) <= b * (s * d)`,
  REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[REAL_RING `a * (s * c) = s * (a * c:real)`] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]);;

let RP_LA_SHEET_ONE = prove
 (`forall n D (x:num->real) (cf:num->real) (cn:num->real) (mu:num->num).
     (forall i. i < n ==> ~(x i = &0) /\ abs(x i) <= &1)
     ==> abs(ndet {i | i < n}
           (\i r. if mu i = 0 then cf i * x i pow (n - 1 - r)
                  else cn i * x i pow (r + D))) <=
         product {i | i < n} (\i. if mu i = 0 then abs(cf i) else abs(cn i)) *
         (sqrt(&n) pow n * inv(&2) pow ((n * (n - 1)) DIV 2) *
          product {i | i < n} (\i. sqrt(&1 + x i pow 2) pow (n - 1)))`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `zz = \i. if (mu:num->num) i = 0 then inv((x:num->real) i) else x i` THEN
  ABBREV_TAC `wt = \i. if (mu:num->num) i = 0 then (cf:num->real) i * x i pow (n - 1)
                       else cn i * (x:num->real) i pow D` THEN
  SUBGOAL_THEN
   `ndet {i | i < n}
      (\i r. if mu i = 0 then cf i * x i pow (n - 1 - r)
             else cn i * x i pow (r + D)) =
    ndet {i | i < n} (\i r. (wt:num->real) i * (zz:num->real) i pow r)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC RP_LA_NDET_EQ THEN REWRITE_TAC[IN_ELIM_THM] THEN
    MAP_EVERY X_GEN_TAC [`i:num`; `r:num`] THEN STRIP_TAC THEN
    MAP_EVERY EXPAND_TAC ["wt"; "zz"] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL
     [SUBGOAL_THEN `n - 1 = (n - 1 - r) + r:num` SUBST1_TAC THENL
       [RP_LA_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[ARITH_RULE `(a + r) - r = a:num`; REAL_POW_ADD; REAL_POW_INV] THEN
      SUBGOAL_THEN `~((x:num->real) i pow r = &0)` MP_TAC THENL
       [ASM_SIMP_TAC[REAL_POW_EQ_0]; CONV_TAC REAL_FIELD];
      REWRITE_TAC[REAL_POW_ADD] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SIMP_TAC[RP_LA_NDET_ROWS_MUL; FINITE_NUMSEG_LT; RP_LA_NDET_VANDERMONDE] THEN
  REWRITE_TAC[REAL_ABS_MUL] THEN
  SIMP_TAC[GSYM PRODUCT_ABS; FINITE_NUMSEG_LT] THEN
  TRANS_TAC REAL_LE_TRANS
   `product {i | i < n} (\i. abs((wt:num->real) i)) *
    (sqrt(&n) pow n * inv(&2) pow ((n * (n - 1)) DIV 2) *
     product {i | i < n} (\i. sqrt(&1 + (zz:num->real) i pow 2) pow (n - 1)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[RP_LA_WVDM] THEN
    MATCH_MP_TAC PRODUCT_POS_LE THEN REWRITE_TAC[FINITE_NUMSEG_LT; REAL_ABS_POS];
    ALL_TAC] THEN
  MATCH_MP_TAC RP_LA_LE_MUL_SCAL THEN
  SIMP_TAC[REAL_POW_LE; SQRT_POS_LE; REAL_POS] THEN
  MATCH_MP_TAC RP_LA_LE_MUL_SCAL THEN
  SIMP_TAC[REAL_POW_LE; REAL_LE_INV_EQ; REAL_POS] THEN
  SIMP_TAC[GSYM PRODUCT_MUL; FINITE_NUMSEG_LT] THEN
  MATCH_MP_TAC PRODUCT_LE THEN REWRITE_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MAP_EVERY EXPAND_TAC ["wt"; "zz"] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  (CONJ_TAC THENL
    [REPEAT(FIRST [MATCH_ACCEPT_TAC REAL_ABS_POS;
       MATCH_ACCEPT_TAC (MATCH_MP REAL_LT_IMP_LE (SPEC_ALL RP_LA_SQRT1_POS));
       MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC;
       MATCH_MP_TAC REAL_POW_LE]); ALL_TAC]) THENL
   [REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_POW; GSYM REAL_MUL_ASSOC;
                GSYM REAL_POW_MUL] THEN
    MATCH_MP_TAC REAL_EQ_IMP_LE THEN AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[GSYM POW_2_SQRT_ABS] THEN
    SIMP_TAC[GSYM SQRT_MUL; REAL_LE_POW_2; REAL_LE_ADD; REAL_POS] THEN
    AP_TERM_TAC THEN UNDISCH_TAC `~((x:num->real) i = &0)` THEN
    CONV_TAC REAL_FIELD;
    REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_POW; GSYM REAL_MUL_ASSOC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_ABS_POS] THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN
    SIMP_TAC[REAL_POW_LE; SQRT_POS_LE; REAL_LE_ADD; REAL_POS; REAL_LE_POW_2] THEN
    MATCH_MP_TAC REAL_POW_1_LE THEN ASM_REWRITE_TAC[REAL_ABS_POS]]);;

let RP_LA_SHEET = prove
 (`forall n D (x:num->real) (cf:num->real) (cn:num->real).
     (forall i. i < n ==> ~(x i = &0) /\ abs(x i) <= &1 /\
                    abs(cf i) + abs(cn i) <= &3 / &2)
     ==> abs(ndet {i | i < n}
               (\r i. cf i * x i pow (n - 1 - r) + cn i * x i pow (r + D))) <=
         (&3 / &2) pow n *
         (sqrt(&n) pow n * inv(&2) pow ((n * (n - 1)) DIV 2) *
          product {i | i < n} (\i. sqrt(&1 + x i pow 2) pow (n - 1)))`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `K = sqrt(&n) pow n * inv(&2) pow ((n * (n - 1)) DIV 2) *
          product {i | i < n} (\i. sqrt(&1 + (x:num->real) i pow 2) pow (n - 1))` THEN
  SUBGOAL_THEN `&0 <= K` ASSUME_TAC THENL
   [EXPAND_TAC "K" THEN MATCH_MP_TAC REAL_LE_MUL THEN
    SIMP_TAC[REAL_POW_LE; SQRT_POS_LE; REAL_POS] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN
    SIMP_TAC[REAL_POW_LE; REAL_LE_INV_EQ; REAL_POS] THEN
    MATCH_MP_TAC PRODUCT_POS_LE THEN
    SIMP_TAC[FINITE_NUMSEG_LT; REAL_POW_LE; SQRT_POS_LE; REAL_LE_ADD; REAL_POS;
             REAL_LE_POW_2];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`{i:num | i < n}`;
    `\i r. (cf:num->real) i * (x:num->real) i pow (n - 1 - r) +
           (cn:num->real) i * x i pow (r + D)`] RP_LA_NDET_TRANSP) THEN
  REWRITE_TAC[FINITE_NUMSEG_LT] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`{i:num | i < n}`; `\i:num. {0,1}`;
    `\i r. (cf:num->real) i * (x:num->real) i pow (n - 1 - r) +
           (cn:num->real) i * x i pow (r + D)`;
    `\i c r. if c = 0 then (cf:num->real) i * (x:num->real) i pow (n - 1 - r)
             else (cn:num->real) i * x i pow (r + D)`]
    RP_LA_NDET_MULTILINEAR) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[FINITE_NUMSEG_LT; FINITE_INSERT; FINITE_EMPTY] THEN
    REPEAT STRIP_TAC THEN
    SIMP_TAC[SUM_CLAUSES; FINITE_INSERT; FINITE_EMPTY; IN_SING; NOT_IN_EMPTY] THEN
    REWRITE_TAC[ARITH_EQ; REAL_ADD_RID];
    DISCH_THEN SUBST1_TAC] THEN
  ABBREV_TAC `C = cartesian_product {i | i < n} (\i:num. {0,1})` THEN
  SUBGOAL_THEN `FINITE(C:(num->num)->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "C" THEN SIMP_TAC[FINITE_CARTESIAN_PRODUCT] THEN DISJ2_TAC THEN
    REWRITE_TAC[FINITE_INSERT; FINITE_EMPTY] THEN
    MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `{i:num | i < n}` THEN
    REWRITE_TAC[FINITE_NUMSEG_LT] THEN SET_TAC[];
    ALL_TAC] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) SUM_ABS o lhand o snd) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(REAL_ARITH `b <= c ==> a <= b ==> a <= c`) THEN
  TRANS_TAC REAL_LE_TRANS
   `sum C (\mu. product {i | i < n}
       (\i. (\i c. if c = 0 then abs((cf:num->real) i) else abs((cn:num->real) i))
            i ((mu:num->num) i)) * K)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_LE THEN ASM_REWRITE_TAC[] THEN X_GEN_TAC `mu:num->num` THEN
    DISCH_TAC THEN REWRITE_TAC[] THEN EXPAND_TAC "K" THEN
    MATCH_MP_TAC RP_LA_SHEET_ONE THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[SUM_RMUL] THEN EXPAND_TAC "C" THEN
  SIMP_TAC[RP_LA_SUM_PRODUCT_CART; FINITE_NUMSEG_LT; FINITE_INSERT;
           FINITE_EMPTY] THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN
  SIMP_TAC[SUM_CLAUSES; FINITE_INSERT; FINITE_EMPTY; IN_SING; NOT_IN_EMPTY] THEN
  REWRITE_TAC[ARITH_EQ; REAL_ADD_RID] THEN
  GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [GSYM CARD_NUMSEG_LT] THEN
  SIMP_TAC[GSYM PRODUCT_CONST; FINITE_NUMSEG_LT] THEN
  MATCH_MP_TAC PRODUCT_LE THEN REWRITE_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN ASM_REWRITE_TAC[] THEN
  REAL_ARITH_TAC);;

let RP_HAD_THM = prove
 (`RP_HAD_STMT`,
  REWRITE_TAC[RP_HAD_STMT; rp_R] THEN REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
    (LABEL_TAC "nd" o CONJUNCT1 o REWRITE_RULE[rp_nodes])) THEN
  MP_TAC(SPECL [`48 * N`; `40 * N - 1`; `x:num->real`;
                `\i. rp_xif((x:num->real) i)`; `\i. rp_xin((x:num->real) i)`]
         RP_LA_SHEET) THEN
  REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  USE_THEN "nd" (MP_TAC o SPEC `i:num`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  ASM_REWRITE_TAC[rp_xif; rp_xin] THEN
  REPEAT CONJ_TAC THEN TRY ASM_REAL_ARITH_TAC THEN
  COND_CASES_TAC THEN CONV_TAC REAL_RAT_REDUCE_CONV);;

