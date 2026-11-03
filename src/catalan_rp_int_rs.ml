(* ========================================================================= *)
(* rp_int: midpoint Riemann sums on a compact interval.                      *)
(* ========================================================================= *)

needs "src/catalan_rp_defs.ml";;

let rp_int_rsum = new_definition
 `rp_int_rsum (g:real->real) a b M =
    sum {i | i < M} (\i. (b - a) / &M * g(a + (&i + &1 / &2) * ((b - a) / &M)))`;;

let RP_INT_RS_CELL = prove
 (`forall g c h z e. &0 < h /\ g real_integrable_on real_interval[c,c + h] /\
     (forall x. x IN real_interval[c,c + h] ==> abs(g x - g z) <= e)
     ==> abs(real_integral (real_interval[c,c + h]) g - h * g z) <= h * e`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `h * (g:real->real) z = real_integral (real_interval[c,c + h]) (\x. g z)`
  SUBST1_TAC THENL
  [SIMP_TAC[REAL_INTEGRAL_CONST; REAL_ARITH `&0 < h ==> c <= c + h`;
            ASSUME `&0 < h`] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  W(MP_TAC o PART_MATCH (rand o rand) REAL_INTEGRAL_SUB o rand o lhand o snd) THEN
  ASM_REWRITE_TAC[REAL_INTEGRABLE_CONST] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `real_integral (real_interval[c,c + h]) (\x. e)` THEN CONJ_TAC THENL
  [MATCH_MP_TAC REAL_INTEGRAL_ABS_BOUND_INTEGRAL THEN
   ASM_SIMP_TAC[REAL_INTEGRABLE_CONST; REAL_INTEGRABLE_SUB];
   ASM_SIMP_TAC[REAL_INTEGRAL_CONST; REAL_ARITH `&0 < h ==> c <= c + h`] THEN
   REAL_ARITH_TAC]);;

let RP_INT_RS_ERR = prove
 (`forall g a b M e.
     a < b /\ ~(M = 0) /\ g real_continuous_on real_interval[a,b] /\
     (forall x y. x IN real_interval[a,b] /\ y IN real_interval[a,b] /\
            abs(x - y) <= (b - a) / &M ==> abs(g x - g y) <= e)
     ==> abs(real_integral (real_interval[a,b]) g - rp_int_rsum g a b M)
         <= (b - a) * e`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[rp_int_rsum] THEN
  ABBREV_TAC `h = (b - a) / &M` THEN
  SUBGOAL_THEN `&0 < h /\ &M * h = b - a` STRIP_ASSUME_TAC THENL
  [EXPAND_TAC "h" THEN
   SUBGOAL_THEN `&0 < &M` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC; ALL_TAC] THEN
   CONJ_TAC THENL [ASM_SIMP_TAC[REAL_LT_DIV; REAL_SUB_LT]; ALL_TAC] THEN
   UNDISCH_TAC `&0 < &M` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  SUBGOAL_THEN
   `forall m. m <= M ==>
        abs(real_integral (real_interval[a,a + &m * h]) g -
            sum {i | i < m} (\i. h * g(a + (&i + &1 / &2) * h))) <= &m * h * e`
  MP_TAC THENL
  [INDUCT_TAC THENL
   [REWRITE_TAC[SUM_CLAUSES_NUMSEG_LT; REAL_MUL_LZERO; REAL_ADD_RID;
                REAL_INTEGRAL_REFL] THEN REAL_ARITH_TAC; ALL_TAC] THEN
   DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
   ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
   SUBGOAL_THEN `&(SUC m) <= &M` MP_TAC THENL
   [ASM_REWRITE_TAC[REAL_OF_NUM_LE]; ALL_TAC] THEN
   REWRITE_TAC[GSYM REAL_OF_NUM_SUC] THEN DISCH_TAC THEN
   REWRITE_TAC[GSYM REAL_OF_NUM_SUC] THEN
   SUBGOAL_THEN `(&m + &1) * h <= b - a` ASSUME_TAC THENL
   [FIRST_ASSUM(SUBST1_TAC o SYM o check (is_eq o concl)) THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   SUBGOAL_THEN `&0 <= &m * h` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
   SUBGOAL_THEN `(g:real->real) real_integrable_on real_interval[a,a + (&m + &1) * h]`
   ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_INTEGRABLE_SUBINTERVAL THEN
    MAP_EVERY EXISTS_TAC [`a:real`; `b:real`] THEN
    ASM_SIMP_TAC[REAL_INTEGRABLE_CONTINUOUS; SUBSET_REAL_INTERVAL] THEN
    ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   MP_TAC(ISPECL [`g:real->real`; `a:real`; `a + (&m + &1) * h`; `a + &m * h`]
     REAL_INTEGRAL_COMBINE) THEN
   ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   DISCH_THEN(SUBST1_TAC o SYM) THEN
   REWRITE_TAC[SUM_CLAUSES_NUMSEG_LT] THEN
   MP_TAC(ISPECL [`g:real->real`; `a + &m * h`; `h:real`;
                  `a + (&m + &1 / &2) * h`; `e:real`] RP_INT_RS_CELL) THEN
   REWRITE_TAC[REAL_ARITH `(a + m * h) + h = a + (m + &1) * h`] THEN
   ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
    [MATCH_MP_TAC REAL_INTEGRABLE_SUBINTERVAL THEN
     MAP_EVERY EXISTS_TAC [`a:real`; `a + (&m + &1) * h`] THEN
     ASM_REWRITE_TAC[SUBSET_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC;
     ALL_TAC] THEN
    REWRITE_TAC[IN_REAL_INTERVAL] THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    REWRITE_TAC[IN_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
   REWRITE_TAC[REAL_ARITH `(m + &1) * h * e = m * h * e + h * e`] THEN
   REPEAT DISCH_TAC THEN MATCH_MP_TAC(REAL_ARITH `abs(c - y) <= u /\ abs(a - x) <= v ==> abs((a + c) - (x + y)) <= v + u`) THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `M:num`) THEN ASM_REWRITE_TAC[LE_REFL; REAL_MUL_ASSOC] THEN
  REWRITE_TAC[REAL_ARITH `a + (b - a) = b:real`]);;

let RP_INT_RS_LIM = prove
 (`forall g a b. a < b /\ g real_continuous_on real_interval[a,b]
           ==> ((\M. rp_int_rsum g a b M) --->
                real_integral (real_interval[a,b]) g) sequentially`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`g:real->real`; `real_interval[a,b]`]
    REAL_COMPACT_UNIFORMLY_CONTINUOUS) THEN
  ASM_REWRITE_TAC[REAL_COMPACT_INTERVAL; real_uniformly_continuous_on] THEN
  DISCH_TAC THEN REWRITE_TAC[REALLIM_SEQUENTIALLY] THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `e / &2 / (b - a)`) THEN
  ASM_SIMP_TAC[REAL_LT_DIV; REAL_SUB_LT; REAL_HALF] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(SPEC `(b - a) / d:real` REAL_ARCH_SIMPLE) THEN
  DISCH_THEN(X_CHOOSE_TAC `N0:num`) THEN EXISTS_TAC `N0 + 1` THEN
  X_GEN_TAC `M:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 < &M /\ (b - a) / &M < d` STRIP_ASSUME_TAC THENL
  [SUBGOAL_THEN `(b - a) / d < &M` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `&N0` THEN
    ASM_REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC; ALL_TAC] THEN
   SUBGOAL_THEN `&0 < &M` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC; ALL_TAC] THEN
   ASM_SIMP_TAC[REAL_LT_LDIV_EQ] THEN
   UNDISCH_TAC `(b - a) / d < &M` THEN ASM_SIMP_TAC[REAL_LT_LDIV_EQ] THEN
   REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`g:real->real`; `a:real`; `b:real`; `M:num`; `e / &2 / (b - a)`]
    RP_INT_RS_ERR) THEN
  ANTS_TAC THENL
  [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[GSYM REAL_OF_NUM_EQ] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN
   FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
   ALL_TAC] THEN
  SUBGOAL_THEN `(b - a) * e / &2 / (b - a) = e / &2` SUBST1_TAC THENL
  [UNDISCH_TAC `a < b` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;
