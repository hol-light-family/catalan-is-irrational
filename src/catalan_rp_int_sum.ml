(* ========================================================================= *)
(* rp_int: midpoint double Riemann sums of the entries.                      *)
(* ========================================================================= *)

needs "src/catalan_rp_int_entry.ml";;

let rp_int_xn = new_definition
 `rp_int_xn M a = --(&1) + (&a + &1 / &2) * ((&1 - --(&1)) / &(2 * M))`;;

let rp_int_sn = new_definition
 `rp_int_sn M b = &0 + (&b + &1 / &2) * ((&1 - &0) / &M)`;;

let rp_int_E = new_definition
 `rp_int_E N M r k =
    sum {a | a < 2 * M}
     (\a. sum {b | b < M}
       (\b. rp_row N r (rp_int_xn M a) * (&1 - --(&1)) / &(2 * M) *
            inv(&1 - rp_t (rp_int_xn M a) * rp_int_sn M b) *
            (&1 - &0) / &M * cat_psi N k (rp_int_sn M b)))`;;

let RP_INT_XN_ALT = prove
 (`forall M a. ~(M = 0)
         ==> rp_int_xn M a = (&(2 * a + 1) - &(2 * M)) / &(2 * M) /\
             rp_int_sn M a = &(2 * a + 1) / &(2 * M)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[rp_int_xn; rp_int_sn; GSYM REAL_OF_NUM_MUL; GSYM REAL_OF_NUM_ADD] THEN
  SUBGOAL_THEN `~(&M = &0)` MP_TAC THENL
  [ASM_REWRITE_TAC[REAL_OF_NUM_EQ]; ALL_TAC] THEN
  CONV_TAC REAL_FIELD);;

let RP_INT_XN_PROPS = prove
 (`forall M a. ~(M = 0) /\ a < 2 * M
         ==> --(&1) < rp_int_xn M a /\ rp_int_xn M a < &1 /\
             ~(rp_int_xn M a = &0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_SIMP_TAC[RP_INT_XN_ALT] THEN
  SUBGOAL_THEN `&0 < &(2 * M)` ASSUME_TAC THENL
  [REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LT_LDIV_EQ; REAL_LT_RDIV_EQ; REAL_DIV_EQ_0;
               REAL_LT_IMP_NZ] THEN
  SUBGOAL_THEN `&0 < &(2 * a + 1) /\ &(2 * a + 1) < &(2 * M) + &(2 * M)`
  STRIP_ASSUME_TAC THENL
  [REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_LT] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[REAL_SUB_0; REAL_OF_NUM_EQ] THEN
  DISCH_THEN(MP_TAC o AP_TERM `EVEN`) THEN
  REWRITE_TAC[EVEN_ADD; EVEN_MULT; ARITH]);;

let RP_INT_SN_PROPS = prove
 (`forall M b. ~(M = 0) /\ b < M ==> &0 < rp_int_sn M b /\ rp_int_sn M b < &1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_SIMP_TAC[RP_INT_XN_ALT] THEN
  SUBGOAL_THEN `&0 < &(2 * M)` ASSUME_TAC THENL
  [REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LT_LDIV_EQ; REAL_LT_RDIV_EQ; REAL_MUL_LZERO;
               REAL_MUL_LID; REAL_OF_NUM_LT] THEN
  ASM_ARITH_TAC);;

let RP_INT_XN_INJ = prove
 (`forall M a a'. ~(M = 0)
     ==> (rp_int_xn M a = rp_int_xn M a' ==> a = a') /\
         (rp_int_sn M a = rp_int_sn M a' ==> a = a')`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN ASM_SIMP_TAC[RP_INT_XN_ALT] THEN
  SUBGOAL_THEN `&0 < &(2 * M)` ASSUME_TAC THENL
  [REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LT_IMP_NZ;
    REAL_FIELD `&0 < d ==> (x / d = y / d <=> x = y)`] THEN
  REWRITE_TAC[REAL_EQ_SUB_RADD; REAL_SUB_ADD; REAL_OF_NUM_EQ] THEN
  ARITH_TAC);;

let RP_INT_E_ALT = prove
 (`forall N M r k.
     rp_int_E N M r k =
     sum {a | a < 2 * M}
      (\a. (&1 - --(&1)) / &(2 * M) *
           (rp_row N r (rp_int_xn M a) *
            rp_int_rsum (rp_int_h (7 * N + k) (4 * N) (rp_t (rp_int_xn M a)))
                        (&0) (&1) M))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[rp_int_E; rp_int_rsum] THEN
  MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `a:num` THEN DISCH_TAC THEN
  REWRITE_TAC[GSYM SUM_LMUL] THEN MATCH_MP_TAC SUM_EQ THEN
  X_GEN_TAC `b:num` THEN DISCH_TAC THEN
  REWRITE_TAC[rp_int_h; cat_psi; GSYM rp_int_sn] THEN REAL_ARITH_TAC);;

let RP_INT_TERM_BOUND = prove
 (`forall w R X Y B e. &0 <= w /\ abs R <= B /\ abs(Y - X) <= e
     ==> abs(w * (R * X) - w * (R * Y)) <= w * (B * e)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(w:real) * (R * X) - w * (R * Y) = w * (R * (X - Y))` SUBST1_TAC THENL
  [REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[REAL_ABS_MUL] THEN ASM_SIMP_TAC[REAL_ARITH `&0 <= w ==> abs w = w`] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[REAL_ABS_POS] THEN
  ASM_MESON_TAC[REAL_ABS_SUB]);;

let RP_INT_E_CONV = prove
 (`forall N r k. 1 <= N /\ r < 48 * N
     ==> ((\M. rp_int_E N M r k) ---> cat_entry N r k) sequentially`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[RP_INT_ENTRY_INT] THEN
  MP_TAC(ISPECL [`\x. rp_row N r x`; `real_interval[--(&1),&1]`]
    REAL_COMPACT_CONTINUOUS_IMAGE) THEN
  ASM_SIMP_TAC[RP_INT_ROW_CONT; REAL_COMPACT_INTERVAL] THEN
  DISCH_THEN(MP_TAC o MATCH_MP REAL_COMPACT_IMP_BOUNDED) THEN
  REWRITE_TAC[REAL_BOUNDED_POS; FORALL_IN_IMAGE; IN_REAL_INTERVAL] THEN
  DISCH_THEN(X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`\x. rp_row N r x * rp_int_G (7 * N + k) (4 * N) (rp_t x)`;
                 `--(&1)`; `&1`] RP_INT_RS_LIM) THEN
  ANTS_TAC THENL
  [CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
   MP_TAC(SPECL [`N:num`; `r:num`; `k:num`; `real_interval[--(&1),&1]`]
     RP_INT_AB_CONT) THEN
   ASM_REWRITE_TAC[RP_INT_INTERVALS] THEN SIMP_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[REALLIM_SEQUENTIALLY] THEN DISCH_TAC THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `e / &2`) THEN ASM_REWRITE_TAC[REAL_HALF] THEN
  DISCH_THEN(X_CHOOSE_THEN `M1:num` (LABEL_TAC "rs")) THEN
  MP_TAC(SPECL [`7 * N + k`; `4 * N`; `e / &8 / B`] RP_INT_G_RS) THEN
  ANTS_TAC THENL
  [CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
   MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `M0:num` (LABEL_TAC "g")) THEN
  EXISTS_TAC `M0 + M1 + 1` THEN X_GEN_TAC `M:num` THEN DISCH_TAC THEN
  REMOVE_THEN "rs" (MP_TAC o SPEC `2 * M`) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[rp_int_rsum; GSYM rp_int_xn] THEN REWRITE_TAC[RP_INT_E_ALT] THEN
  MATCH_MP_TAC(REAL_ARITH
   `abs(x - y) <= e / &4 /\ &0 < e ==> abs(y - l) < e / &2 ==> abs(x - l) < e`) THEN
  ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[GSYM SUM_SUB; FINITE_NUMSEG_LT] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum {a | a < 2 * M} (\a. (&1 - --(&1)) / &(2 * M) * (B * (e / &8 / B)))` THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC SUM_ABS_LE THEN REWRITE_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM] THEN
   X_GEN_TAC `a:num` THEN DISCH_TAC THEN BETA_TAC THEN
   MATCH_MP_TAC RP_INT_TERM_BOUND THEN
   MP_TAC(SPECL [`M:num`; `a:num`] RP_INT_XN_PROPS) THEN
   ANTS_TAC THENL [ASM_ARITH_TAC; STRIP_TAC] THEN
   REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_DIV THEN REWRITE_TAC[REAL_POS] THEN REAL_ARITH_TAC;
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    REMOVE_THEN "g" MATCH_MP_TAC THEN
    REWRITE_TAC[RP_INT_CV_RP_T_ABS] THEN ASM_ARITH_TAC];
   ALL_TAC] THEN
  REWRITE_TAC[SUM_CONST_NUMSEG; FINITE_NUMSEG_LT] THEN
  SIMP_TAC[SUM_CONST; FINITE_NUMSEG_LT; CARD_NUMSEG_LT] THEN
  SUBGOAL_THEN `~(&(2 * M) = &0)` MP_TAC THENL
  [REWRITE_TAC[REAL_OF_NUM_EQ] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  UNDISCH_TAC `&0 < B` THEN
  REPEAT(POP_ASSUM(K ALL_TAC)) THEN REPEAT DISCH_TAC THEN
  MATCH_MP_TAC REAL_EQ_IMP_LE THEN
  REPEAT(POP_ASSUM MP_TAC) THEN CONV_TAC REAL_FIELD);;
