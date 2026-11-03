needs "src/catalan_fin_base.ml";;

(* ========================================================================= *)
(* fin_two_cb: combinatorial lower bound (FIN_TWO_CB_MAIN) and a little-o    *)
(* estimate for the flog term (FIN_TWO_CB_LITTLE_O).                         *)
(* ========================================================================= *)

let FIN_TWO_CB_SUMCARD = prove
 (`forall s:num->bool. FINITE s
     ==> &(CARD s) * (&(CARD s) - &1) <= &2 * sum s (\k. &k)`,
  SUBGOAL_THEN
   `forall n (s:num->bool). FINITE s /\ CARD s = n
       ==> &(CARD s) * (&(CARD s) - &1) <= &2 * sum s (\k. &k)`
   (fun th -> MESON_TAC[th]) THEN
  INDUCT_TAC THEN REPEAT STRIP_TAC THENL
   [ASM_REWRITE_TAC[REAL_MUL_LZERO] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &0 <= &2 * x`) THEN
    MATCH_MP_TAC SUM_POS_LE THEN REWRITE_TAC[REAL_POS];
    ALL_TAC] THEN
  SUBGOAL_THEN `exists m:num. m IN s /\ forall y. y IN s ==> y <= m` STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPEC `\x:num. x IN s` num_MAX) THEN
    REWRITE_TAC[] THEN DISCH_THEN(MATCH_MP_TAC o fst o EQ_IMP_RULE) THEN CONJ_TAC THENL
     [REWRITE_TAC[MEMBER_NOT_EMPTY] THEN
      DISCH_THEN SUBST_ALL_TAC THEN
      RULE_ASSUM_TAC(REWRITE_RULE[CARD_CLAUSES]) THEN
      ASM_MESON_TAC[NOT_SUC];
      ASM_MESON_TAC[num_FINITE]];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `s DELETE (m:num)`) THEN
  ASM_SIMP_TAC[FINITE_DELETE; CARD_DELETE; SUM_DELETE; SUC_SUB1] THEN
  SUBGOAL_THEN `n <= m:num` MP_TAC THENL
   [MATCH_MP_TAC(ARITH_RULE `SUC n <= m + 1 ==> n <= m`) THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
    TRANS_TAC LE_TRANS `CARD(0..m)` THEN
    CONJ_TAC THENL [ALL_TAC; REWRITE_TAC[CARD_NUMSEG] THEN ARITH_TAC] THEN
    MATCH_MP_TAC CARD_SUBSET THEN REWRITE_TAC[FINITE_NUMSEG] THEN
    REWRITE_TAC[SUBSET; IN_NUMSEG; LE_0] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_LE; GSYM REAL_OF_NUM_SUC] THEN
  CONV_TAC REAL_ARITH);;

let FIN_TWO_CB_SUMCARD_INJ = prove
 (`forall (g:A->num) s. FINITE s /\ (forall x y. x IN s /\ y IN s /\ g x = g y ==> x = y)
     ==> &(CARD s) * (&(CARD s) - &1) <= &2 * sum s (\k. &(g k))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `IMAGE (g:A->num) s` FIN_TWO_CB_SUMCARD) THEN
  ASM_SIMP_TAC[FINITE_IMAGE] THEN
  MP_TAC(ISPECL [`g:A->num`; `s:A->bool`] CARD_IMAGE_INJ) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`g:A->num`; `\k:num. &k`; `s:A->bool`] SUM_IMAGE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[o_DEF]);;

let FIN_TWO_CB_CORE = prove
 (`forall n m l. &0 <= n /\ &0 <= m /\ &0 <= l /\ m + l <= &48 * n
   ==> --(&505 / &4608 * (&48 * n) pow 2) <=
       &63 * n * (&48 * n - m - l) + &3 / &2 * m pow 2 - &58 * n * m +
       &1 / &2 * l pow 2`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= ((&48 * n - m) - l) * (&63 * n - (l + (&48 * n - m)) / &2)`
  MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPEC `m - &53 / &2 * n` REAL_LE_SQUARE) THEN
  CONV_TAC REAL_ARITH);;

let FIN_TWO_CB_MAIN = prove
 (`forall N lam (f:num->num#num).
   1 <= N /\ &0 <= lam /\
   (forall k. k < 48 * N ==> FST(f k) <= 2) /\
   (forall k1 k2. k1 < 48 * N /\ k2 < 48 * N /\ f k1 = f k2 ==> k1 = k2)
   ==> --(&505 / &4608 * &(48 * N) pow 2) - &48 * &N * (lam + &2) <=
       sum (0..48 * N - 1)
         (\k. if FST(f k) = 0 then &(63 * N) - lam
              else if FST(f k) = 1 then &2 * &(SND(f k)) + &k - &(58 * N) - lam
              else &(SND(f k)) - lam)`,
  INTRO_TAC "!N lam f; N1 lam0 fst inj" THEN
  SUBGOAL_THEN `forall k. k IN 0..48 * N - 1 <=> k < 48 * N` ASSUME_TAC THENL
   [REWRITE_TAC[IN_NUMSEG] THEN UNDISCH_TAC `1 <= N` THEN ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `s = 0..48 * N - 1` THEN
  SUBGOAL_THEN `FINITE(s:num->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "s" THEN REWRITE_TAC[FINITE_NUMSEG]; ALL_TAC] THEN
  SUBGOAL_THEN `CARD(s:num->bool) = 48 * N` ASSUME_TAC THENL
   [EXPAND_TAC "s" THEN REWRITE_TAC[CARD_NUMSEG] THEN
    UNDISCH_TAC `1 <= N` THEN ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[MATCH_MP SUM_CASES (ASSUME `FINITE(s:num->bool)`)] THEN
  SUBGOAL_THEN `FINITE {x | x IN s /\ ~(FST((f:num->num#num) x) = 0)}`
   (fun th -> REWRITE_TAC[MATCH_MP SUM_CASES th]) THENL
   [ASM_SIMP_TAC[FINITE_RESTRICT]; ALL_TAC] THEN
  REWRITE_TAC[IN_ELIM_THM] THEN
  ABBREV_TAC `S0 = {x | x IN s /\ FST((f:num->num#num) x) = 0}` THEN
  ABBREV_TAC `S1 = {x | x IN s /\ FST((f:num->num#num) x) = 1}` THEN
  ABBREV_TAC `S2 = {x | x IN s /\ FST((f:num->num#num) x) = 2}` THEN
  SUBGOAL_THEN
   `{x | (x IN s /\ ~(FST((f:num->num#num) x) = 0)) /\ FST(f x) = 1} = S1 /\
    {x | (x IN s /\ ~(FST((f:num->num#num) x) = 0)) /\ ~(FST(f x) = 1)} = S2`
  (CONJUNCTS_THEN SUBST1_TAC) THENL
   [MAP_EVERY EXPAND_TAC ["S1"; "S2"] THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN CONJ_TAC THEN
    X_GEN_TAC `x:num` THEN ASM_CASES_TAC `x:num IN s` THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "fst" (MP_TAC o SPEC `x:num`) THEN ASM_MESON_TAC[ARITH_RULE
     `(a <= 2 ==> (~(a = 0) /\ ~(a = 1) <=> a = 2)) /\ (a = 1 ==> ~(a = 0))`];
    ALL_TAC] THEN
  SUBGOAL_THEN `FINITE(S0:num->bool) /\ FINITE(S1:num->bool) /\ FINITE(S2:num->bool)`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["S0"; "S1"; "S2"] THEN ASM_SIMP_TAC[FINITE_RESTRICT];
    ALL_TAC] THEN
  SUBGOAL_THEN `CARD(S0:num->bool) + CARD(S1:num->bool) + CARD(S2:num->bool) = 48 * N`
  ASSUME_TAC THENL
   [FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC RAND_CONV [SYM th]) THEN
    SUBGOAL_THEN `CARD(S1:num->bool) + CARD(S2:num->bool) = CARD(S1 UNION S2)`
    SUBST1_TAC THENL
     [MATCH_MP_TAC CARD_UNION_EQ THEN ASM_REWRITE_TAC[FINITE_UNION] THEN
      MAP_EVERY EXPAND_TAC ["S1"; "S2"] THEN
      REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_INTER; NOT_IN_EMPTY] THEN
      ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC CARD_UNION_EQ THEN ASM_REWRITE_TAC[] THEN
    MAP_EVERY EXPAND_TAC ["S0"; "S1"; "S2"] THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_INTER; IN_UNION; NOT_IN_EMPTY] THEN
    CONJ_TAC THENL [ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `x:num` THEN ASM_CASES_TAC `x:num IN s` THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "fst" (MP_TAC o SPEC `x:num`) THEN ASM_MESON_TAC[ARITH_RULE
     `a <= 2 ==> (a = 0 \/ a = 1 \/ a = 2)`];
    ALL_TAC] THEN
  SUBGOAL_THEN `forall k1 k2. k1 IN S1 /\ k2 IN S1 /\ SND((f:num->num#num) k1) = SND(f k2)
                        ==> k1 = k2` ASSUME_TAC THENL
   [EXPAND_TAC "S1" THEN REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
    USE_THEN "inj" MATCH_MP_TAC THEN ASM_MESON_TAC[PAIR_EQ; PAIR]; ALL_TAC] THEN
  SUBGOAL_THEN `forall k1 k2. k1 IN S2 /\ k2 IN S2 /\ SND((f:num->num#num) k1) = SND(f k2)
                        ==> k1 = k2` ASSUME_TAC THENL
   [EXPAND_TAC "S2" THEN REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
    USE_THEN "inj" MATCH_MP_TAC THEN ASM_MESON_TAC[PAIR_EQ; PAIR]; ALL_TAC] THEN
  MP_TAC(ISPECL [`\k. SND((f:num->num#num) k)`; `S1:num->bool`]
    FIN_TWO_CB_SUMCARD_INJ) THEN
  MP_TAC(ISPECL [`\k. SND((f:num->num#num) k)`; `S2:num->bool`]
    FIN_TWO_CB_SUMCARD_INJ) THEN
  MP_TAC(ISPEC `S1:num->bool` FIN_TWO_CB_SUMCARD) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`&N`; `&(CARD(S1:num->bool))`; `&(CARD(S2:num->bool))`]
    FIN_TWO_CB_CORE) THEN
  SUBGOAL_THEN `&(CARD(S0:num->bool)) = &48 * &N - &(CARD(S1:num->bool)) - &(CARD(S2:num->bool)) /\
                &(CARD S1) + &(CARD S2) <= &48 * &N`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `CARD(S0:num->bool) + CARD(S1:num->bool) + CARD(S2:num->bool) = 48 * N` THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_EQ; GSYM REAL_OF_NUM_ADD; GSYM REAL_OF_NUM_MUL] THEN
    MP_TAC(SPEC `CARD(S0:num->bool)` REAL_POS) THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[REAL_POS] THEN
  SIMP_TAC[SUM_CONST; SUM_ADD; SUM_SUB; SUM_LMUL;
    ASSUME `FINITE(S0:num->bool)`; ASSUME `FINITE(S1:num->bool)`;
    ASSUME `FINITE(S2:num->bool)`] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_MUL] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[ETA_AX] THEN
  MP_TAC(SPEC `CARD(S1:num->bool)` REAL_POS) THEN
  MP_TAC(SPEC `CARD(S2:num->bool)` REAL_POS) THEN
  UNDISCH_TAC `&(CARD(S1:num->bool)) + &(CARD(S2:num->bool)) <= &48 * &N` THEN
  MAP_EVERY (fun t -> SPEC_TAC(t, genvar(type_of t)))
   [`sum S1 (\k. &(SND((f:num->num#num) k)))`;
    `sum S2 (\k. &(SND((f:num->num#num) k)))`;
    `sum (S1:num->bool) (&)`] THEN
  MAP_EVERY (fun t -> SPEC_TAC(t, genvar(type_of t)))
   [`&(CARD(S1:num->bool))`; `&(CARD(S2:num->bool))`; `&N`] THEN
  CONV_TAC REAL_ARITH);;

let FIN_TWO_CB_FLOG_LE = prove
 (`forall M n. fin_flog 2 n <= M + n DIV 2 EXP M`,
  REPEAT GEN_TAC THEN REWRITE_TAC[fin_flog] THEN
  TRANS_TAC LE_TRANS `CARD(1..(M + n DIV 2 EXP M))` THEN CONJ_TAC THENL
   [ALL_TAC; REWRITE_TAC[CARD_NUMSEG] THEN ARITH_TAC] THEN
  MATCH_MP_TAC CARD_SUBSET THEN REWRITE_TAC[FINITE_NUMSEG] THEN
  REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_NUMSEG] THEN
  X_GEN_TAC `e:num` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `e <= M:num` THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `e - M <= n DIV 2 EXP M:num` MP_TAC THENL
   [ALL_TAC; ASM_ARITH_TAC] THEN
  SIMP_TAC[LE_RDIV_EQ; EXP_EQ_0; ARITH_EQ] THEN
  TRANS_TAC LE_TRANS `2 EXP e` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `e = M + (e - M:num)` (fun th -> GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [th])
  THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[EXP_ADD; LE_MULT_LCANCEL] THEN
  DISJ2_TAC THEN MATCH_MP_TAC LT_IMP_LE THEN REWRITE_TAC[LT_POW2_REFL]);;

let FIN_TWO_CB_FLOG_REAL = prove
 (`forall M n. &2 pow M * &(fin_flog 2 n) <= &2 pow M * &M + &n`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[REAL_OF_NUM_POW; REAL_OF_NUM_MUL; REAL_OF_NUM_ADD; REAL_OF_NUM_LE] THEN
  TRANS_TAC LE_TRANS `2 EXP M * (M + n DIV 2 EXP M)` THEN
  REWRITE_TAC[LE_MULT_LCANCEL; FIN_TWO_CB_FLOG_LE; LEFT_ADD_DISTRIB; LE_ADD_LCANCEL;
              DIV_MUL_LE]);;

let FIN_TWO_CB_LITTLE_O = prove
 (`forall c d e. &0 <= c /\ &0 <= d /\ &0 < e
   ==> exists N0. forall N. N0 <= N ==> c * &N * (d + &(fin_flog 2 (65 * N + 1))) <= e * &N pow 2`,
  REPEAT STRIP_TAC THEN
  X_CHOOSE_TAC `M:num` (SPEC `&132 * c / e` REAL_ARCH_SIMPLE) THEN
  ABBREV_TAC `pp = &2 pow M` THEN
  SUBGOAL_THEN `&0 < pp /\ &132 * c <= (pp:real) * e` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "pp" THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LT THEN REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&M <= &2 pow M` MP_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_POW; REAL_OF_NUM_LE] THEN
      MATCH_MP_TAC LT_IMP_LE THEN REWRITE_TAC[LT_POW2_REFL]; ALL_TAC] THEN
    DISCH_TAC THEN
    MP_TAC(SPECL [`&M`; `&2 pow M`; `e:real`] REAL_LE_RMUL) THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
    UNDISCH_TAC `&132 * c / e <= &M` THEN
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_ARITH `&132 * c / e = (&132 * c) / e`] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  X_CHOOSE_TAC `n0:num` (SPEC `&2 * c * (d + &M) / e` REAL_ARCH_SIMPLE) THEN
  EXISTS_TAC `n0 + 1` THEN X_GEN_TAC `N:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `&1 <= &N /\ &n0 <= &N` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LE] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&2 * c * (d + &M) <= e * &N` ASSUME_TAC THENL
   [UNDISCH_TAC `&2 * c * (d + &M) / e <= &n0` THEN
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ;
      REAL_ARITH `&2 * c * (d + &M) / e = (&2 * c * (d + &M)) / e`] THEN
    MP_TAC(SPECL [`e:real`; `&n0`; `&N`] REAL_LE_LMUL) THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `fl = &(fin_flog 2 (65 * N + 1))` THEN
  SUBGOAL_THEN `(pp:real) * fl <= pp * &M + &65 * &N + &1` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["pp"; "fl"] THEN
    REWRITE_TAC[REAL_ARITH `a + &65 * x + &1 = a + (&65 * x + &1)`] THEN
    REWRITE_TAC[REAL_OF_NUM_MUL; REAL_OF_NUM_ADD; FIN_TWO_CB_FLOG_REAL];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= c * &N` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`c * &N`; `(pp:real) * fl`; `(pp:real) * &M + &65 * &N + &1`] REAL_LE_LMUL) THEN
  MP_TAC(SPECL [`c * &N`; `&65 * &N + &1`; `&66 * &N`] REAL_LE_LMUL) THEN
  MP_TAC(SPECL [`(pp:real) * &N`; `&2 * c * (d + &M)`; `e * &N`] REAL_LE_LMUL) THEN
  MP_TAC(SPECL [`&N * &N`; `&132 * c`; `(pp:real) * e`] REAL_LE_LMUL) THEN
  SUBGOAL_THEN `&0 <= (pp:real) * &N /\ &0 <= &N * &N` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&65 * &N + &1 <= &66 * &N` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT DISCH_TAC THEN
  ONCE_REWRITE_TAC[GSYM(MATCH_MP REAL_LE_LMUL_EQ (ASSUME `&0 < pp`))] THEN
  POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
  REWRITE_TAC[REAL_POW_2] THEN
  SPEC_TAC(`fl:real`, `fl:real`) THEN SPEC_TAC(`pp:real`, `pp:real`) THEN
  SPEC_TAC(`&N`, `x:real`) THEN SPEC_TAC(`&M`, `y:real`) THEN
  REPEAT GEN_TAC THEN CONV_TAC REAL_ARITH);;
