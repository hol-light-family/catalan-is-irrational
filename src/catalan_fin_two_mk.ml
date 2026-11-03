(* ========================================================================= *)
(* fin_two_: truncated 2-adic moment series MK and the discrepancy with the  *)
(* rational array M'.                                                         *)
(* ========================================================================= *)

needs "src/catalan_fin_two_val.ml";;
needs "src/catalan_rat_series.ml";;

let fin_two_mk = new_definition
 `fin_two_mk R i j = sum (0..R) (\k. cat_m (i + k) / &(j + k + 1))`;;

let fin_two_ck2 = new_definition
 `fin_two_ck2 i j = if i < j then cat_ckern (j - 1) i else &0`;;

(* X(i,j) = M'(i,j) + (4z - e1) ckern - e2 ck2 with e1 = 4z - MK(0,0), e2 = -MK(0,1) *)
let fin_two_X = new_definition
 `fin_two_X R i j = cat_M0 i j + fin_two_mk R 0 0 * cat_ckern i j +
                    fin_two_mk R 0 1 * fin_two_ck2 i j`;;

(* ------------------------------------------------------------------------- *)
(* Recurrences.                                                              *)
(* ------------------------------------------------------------------------- *)

let FIN_TWO_SUM_SHIFT1 = prove
 (`forall f n. sum(0..n) (\k. f(k + 1)) = sum(1..n + 1) f`,
  REPEAT GEN_TAC THEN MP_TAC(ISPECL [`1`; `f:num->real`; `0`; `n:num`] SUM_OFFSET) THEN
  REWRITE_TAC[ADD_CLAUSES] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN REFL_TAC);;

let FIN_TWO_SUM_LAST = prove
 (`forall f n. sum(1..n + 1) f = sum(1..n) f + f(n + 1)`,
  REWRITE_TAC[GSYM ADD1; SUM_CLAUSES_NUMSEG; ARITH_RULE `1 <= SUC n`]);;

let FIN_TWO_SUM_FIRST = prove
 (`forall f n. sum(0..n) f = f 0 + sum(1..n) f`,
  SIMP_TAC[SUM_CLAUSES_LEFT; LE_0; ADD_CLAUSES]);;

let FIN_TWO_NUMNORM_CONV tm =
  if type_of tm = `:num` && not (is_numeral tm) && not (is_var tm)
  then NUM_NORMALIZE_CONV tm else failwith "FIN_TWO_NUMNORM_CONV";;

let FIN_TWO_NUMNORM_TAC =
  REWRITE_TAC[ADD1] THEN CONV_TAC(ONCE_DEPTH_CONV FIN_TWO_NUMNORM_CONV);;

let FIN_TWO_MK_DIAG = prove
 (`forall R i j. fin_two_mk R i j =
           cat_m i / &(j + 1) + fin_two_mk R (i + 1) (j + 1) -
           cat_m (i + R + 1) / &(j + R + 2)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[fin_two_mk] THEN
  MP_TAC(ISPECL [`\k. cat_m (i + k) / &(j + k + 1)`; `R:num`] FIN_TWO_SUM_SHIFT1) THEN
  REWRITE_TAC[FIN_TWO_SUM_LAST; FIN_TWO_SUM_FIRST] THEN
  FIN_TWO_NUMNORM_TAC THEN REAL_ARITH_TAC);;

let FIN_TWO_FIELD_TAC =
  FIN_TWO_NUMNORM_TAC THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_ADD; GSYM REAL_OF_NUM_MUL] THEN
  MAP_EVERY (fun t -> MP_TAC(SPEC t REAL_POS)) [`d:num`; `R:num`] THEN
  CONV_TAC REAL_FIELD;;

let FIN_TWO_M2 = prove
 (`cat_m 2 = &4 / &3`,
  MP_TAC(SPEC `0` RAT_B_M_STEP) THEN REWRITE_TAC[RAT_B_M_0] THEN
  CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC REAL_FIELD);;

let FIN_TWO_MK_10 = prove
 (`forall R. fin_two_mk R 1 0 = &2 - cat_m R - cat_m (R + 1)`,
  REWRITE_TAC[fin_two_mk] THEN INDUCT_TAC THEN
  REWRITE_TAC[SUM_CLAUSES_NUMSEG; LE_0] THEN CONV_TAC NUM_REDUCE_CONV THENL
   [REWRITE_TAC[RAT_B_M_0] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN MP_TAC(SPEC `R:num` RAT_B_M_TELE) THEN
  FIN_TWO_NUMNORM_TAC THEN REAL_ARITH_TAC);;

let FIN_TWO_MK_MINUS = prove
 (`forall R d. &(d + 2) * fin_two_mk R (d + 2) 0 =
         &(d + 1) * fin_two_mk R d 0 + cat_m d + cat_m (d + 1) -
         cat_m (d + R + 1) - cat_m (d + R + 2)`,
  REWRITE_TAC[fin_two_mk] THEN INDUCT_TAC THEN GEN_TAC THEN
  REWRITE_TAC[SUM_CLAUSES_NUMSEG; LE_0] THENL
   [MP_TAC(SPEC `d:num` RAT_B_M_STEP) THEN FIN_TWO_FIELD_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `d:num`) THEN
  MP_TAC(SPEC `d + R + 1` RAT_B_M_STEP) THEN FIN_TWO_FIELD_TAC);;

let FIN_TWO_MK_PLUS = prove
 (`forall R d. &(d + 1) * fin_two_mk R 0 (d + 2) =
         &d * fin_two_mk R 0 d + &2 / &(d + 1) +
         (&d * cat_m (R + 1) / &(d + R + 2) + &d * cat_m (R + 2) / &(d + R + 3) -
          cat_m (R + 1) - cat_m (R + 2))`,
  REWRITE_TAC[fin_two_mk] THEN INDUCT_TAC THEN GEN_TAC THEN
  REWRITE_TAC[SUM_CLAUSES_NUMSEG; LE_0] THENL
   [REWRITE_TAC[ADD_CLAUSES; RAT_B_M_0; FIN_TWO_M2] THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[RAT_B_M_0; FIN_TWO_M2] THEN
    FIN_TWO_FIELD_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `d:num`) THEN
  MP_TAC(SPEC `R + 1` RAT_B_M_STEP) THEN FIN_TWO_FIELD_TAC);;

(* ------------------------------------------------------------------------- *)
(* The discrepancy D = X - MK: diagonal and boundary recurrences.            *)
(* ------------------------------------------------------------------------- *)

let FIN_TWO_M0_DIAG = prove
 (`forall i j. cat_M0 i j = cat_m i / &(j + 1) + cat_M0 (i + 1) (j + 1)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[cat_M0; LE_ADD_RCANCEL; ARITH_RULE `(i + 1) - (j + 1) = i - j:num`] THEN
  COND_CASES_TAC THEN REWRITE_TAC[FIN_TWO_SUM_LAST] THENL
   [SUBGOAL_THEN `i - j + (j + 1) - 1 = i` SUBST1_TAC THENL
     [ASM_ARITH_TAC; REAL_ARITH_TAC];
    SUBGOAL_THEN `(i + 1) - 1 = i /\ j - i + i + 1 = j + 1` (CONJUNCTS_THEN SUBST1_TAC) THENL
     [ASM_ARITH_TAC; REAL_ARITH_TAC]]);;

let FIN_TWO_CKERN_DIAG = prove
 (`forall i j. cat_ckern (i + 1) (j + 1) = cat_ckern i j`,
  REWRITE_TAC[cat_ckern; LE_ADD_RCANCEL; ARITH_RULE `(i + 1) - (j + 1) = i - j:num`]);;

let FIN_TWO_CK2_DIAG = prove
 (`forall i j. fin_two_ck2 (i + 1) (j + 1) = fin_two_ck2 i j`,
  REPEAT GEN_TAC THEN REWRITE_TAC[fin_two_ck2; LT_ADD_RCANCEL; ADD_SUB] THEN
  COND_CASES_TAC THEN REWRITE_TAC[] THEN
  MP_TAC(SPECL [`j - 1`; `i:num`] FIN_TWO_CKERN_DIAG) THEN
  SUBGOAL_THEN `j - 1 + 1 = j` SUBST1_TAC THENL [ASM_ARITH_TAC; REWRITE_TAC[]]);;

let FIN_TWO_D_DIAG = prove
 (`forall R i j. fin_two_X R i j - fin_two_mk R i j =
           (fin_two_X R (i + 1) (j + 1) - fin_two_mk R (i + 1) (j + 1)) +
           cat_m (i + R + 1) / &(j + R + 2)`,
  REPEAT GEN_TAC THEN
  MP_TAC(SPECL [`i:num`; `j:num`] FIN_TWO_M0_DIAG) THEN
  MP_TAC(SPECL [`R:num`; `i:num`; `j:num`] FIN_TWO_MK_DIAG) THEN
  REWRITE_TAC[fin_two_X; FIN_TWO_CKERN_DIAG; FIN_TWO_CK2_DIAG] THEN
  REAL_ARITH_TAC);;

let FIN_TWO_X_LEFT = prove
 (`forall R d. fin_two_X R d 0 = cat_kminus d + fin_two_mk R 0 0 * cat_ckern d 0`,
  REPEAT GEN_TAC THEN REWRITE_TAC[fin_two_X; cat_M0; fin_two_ck2; LE_0; LT; SUB_0] THEN
  SIMP_TAC[SUM_TRIV_NUMSEG; ARITH] THEN REAL_ARITH_TAC);;

let FIN_TWO_X_TOP = prove
 (`forall R d. 1 <= d ==> fin_two_X R 0 d = cat_kplus d + fin_two_mk R 0 1 * cat_ckern (d - 1) 0`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[fin_two_X; cat_M0; fin_two_ck2; RAT_B_CK0] THEN
  ASM_SIMP_TAC[ARITH_RULE `1 <= d ==> ~(d <= 0) /\ 0 < d /\ ~(d = 0)`; SUB_0] THEN
  SIMP_TAC[SUM_TRIV_NUMSEG; ARITH] THEN REAL_ARITH_TAC);;

let FIN_TWO_D00 = prove
 (`forall R. fin_two_X R 0 0 - fin_two_mk R 0 0 = &0`,
  REWRITE_TAC[FIN_TWO_X_LEFT; RAT_B_CK0; RAT_B_KPM01] THEN REAL_ARITH_TAC);;

let FIN_TWO_D10 = prove
 (`forall R. fin_two_X R 1 0 - fin_two_mk R 1 0 = cat_m R + cat_m (R + 1)`,
  REWRITE_TAC[FIN_TWO_X_LEFT; FIN_TWO_MK_10; RAT_B_KPM01] THEN
  REWRITE_TAC[cat_ckern] THEN CONV_TAC NUM_REDUCE_CONV THEN REAL_ARITH_TAC);;

let FIN_TWO_D01 = prove
 (`forall R. fin_two_X R 0 1 - fin_two_mk R 0 1 = &0`,
  SIMP_TAC[FIN_TWO_X_TOP; LE_REFL; RAT_B_KPM01; SUB_REFL; RAT_B_CK0] THEN
  REAL_ARITH_TAC);;

let FIN_TWO_D_MINUS = prove
 (`forall R d. &(d + 2) * (fin_two_X R (d + 2) 0 - fin_two_mk R (d + 2) 0) =
         &(d + 1) * (fin_two_X R d 0 - fin_two_mk R d 0) +
         cat_m (d + R + 1) + cat_m (d + R + 2)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[FIN_TWO_X_LEFT] THEN
  MP_TAC(SPECL [`R:num`; `d:num`] FIN_TWO_MK_MINUS) THEN
  MP_TAC(SPEC `d:num` RAT_B_KM_STEP) THEN
  MP_TAC(SPEC `d:num` RAT_B_CK_STEP) THEN
  CONV_TAC REAL_RING);;

let FIN_TWO_D_PLUS = prove
 (`forall R d. &(d + 1) * (fin_two_X R 0 (d + 2) - fin_two_mk R 0 (d + 2)) =
         &d * (fin_two_X R 0 d - fin_two_mk R 0 d) -
         (&d * cat_m (R + 1) / &(d + R + 2) + &d * cat_m (R + 2) / &(d + R + 3) -
          cat_m (R + 1) - cat_m (R + 2))`,
  REPEAT GEN_TAC THEN
  SIMP_TAC[FIN_TWO_X_TOP; ARITH_RULE `1 <= d + 2`; ARITH_RULE `(d + 2) - 1 = d + 1`] THEN
  MP_TAC(SPECL [`R:num`; `d:num`] FIN_TWO_MK_PLUS) THEN
  MP_TAC(SPEC `d:num` RAT_B_KP_STEP) THEN
  MP_TAC(SPEC `d:num` RAT_B_CK_STEP2) THEN
  ASM_CASES_TAC `d = 0` THENL
   [ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[cat_ckern] THEN CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC REAL_RING;
    ALL_TAC] THEN
  ASM_SIMP_TAC[FIN_TWO_X_TOP; ARITH_RULE `~(d = 0) ==> 1 <= d /\ 0 < d`] THEN
  CONV_TAC REAL_RING);;

(* ------------------------------------------------------------------------- *)
(* Valuations.                                                               *)
(* ------------------------------------------------------------------------- *)

let FIN_TWO_MK_TERM_VAL = prove
 (`forall H i j k. 1 <= H /\ i <= H /\ j < H
             ==> fin_vge 2 (&i - &2 * &(fin_flog 2 H) - &2)
                         (cat_m (i + k) / &(j + k + 1))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC FIN_VGE_MONO THEN
  EXISTS_TAC `(&(i + k) + &1 - &(fin_flog 2 (i + k))) - &(fin_flog 2 (H + k))` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC FIN_TWO_DIV_VAL THEN REWRITE_TAC[FIN_TWO_M_VAL] THEN ASM_ARITH_TAC] THEN
  MP_TAC(SPECL [`i + k:num`; `H + k:num`] FIN_TWO_FLOG_MONO) THEN
  MP_TAC(SPECL [`H:num`; `k:num`] FIN_TWO_FLOG_ADD) THEN
  MP_TAC(SPEC `k + 1:num` FIN_TWO_FLOG_HALF) THEN
  ASM_REWRITE_TAC[LE_ADD_RCANCEL] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_LE; GSYM REAL_OF_NUM_ADD; GSYM REAL_OF_NUM_MUL] THEN
  REAL_ARITH_TAC);;

let FIN_TWO_MK_VAL = prove
 (`forall R H i j. 1 <= H /\ i <= H /\ j < H
             ==> fin_vge 2 (&i - &2 * &(fin_flog 2 H) - &2) (fin_two_mk R i j)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[fin_two_mk] THEN
  MATCH_MP_TAC FIN_VGE_SUM THEN REWRITE_TAC[FIN_TWO_PRIME; FINITE_NUMSEG] THEN
  ASM_SIMP_TAC[FIN_TWO_MK_TERM_VAL]);;

let FIN_TWO_TAILM = prove
 (`forall E n. 2 EXP E <= n /\ n < 2 * 2 EXP E
         ==> fin_vge 2 (&(2 EXP E) + &1 - &E) (cat_m n)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC FIN_VGE_MONO THEN
  EXISTS_TAC `&n + &1 - &(fin_flog 2 n)` THEN REWRITE_TAC[FIN_TWO_M_VAL] THEN
  SUBGOAL_THEN `fin_flog 2 n <= E` MP_TAC THENL
   [MATCH_MP_TAC FIN_TWO_FLOG_UB THEN ASM_REWRITE_TAC[EXP_ADD; EXP_1] THEN
    ASM_ARITH_TAC;
    UNDISCH_TAC `2 EXP E <= n` THEN REWRITE_TAC[GSYM REAL_OF_NUM_LE] THEN
    REAL_ARITH_TAC]);;

let FIN_TWO_TAILQ = prove
 (`forall E n b c. 2 EXP E <= n /\ n < 2 * 2 EXP E /\ 1 <= b /\ b < 2 * 2 EXP E
             ==> fin_vge 2 (&(2 EXP E) + &1 - &2 * &E) (&c * cat_m n / &b)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC FIN_VGE_ZP_MUL THEN
  SIMP_TAC[FIN_TWO_PRIME; FIN_ZP_NUM] THEN MATCH_MP_TAC FIN_VGE_MONO THEN
  EXISTS_TAC `(&(2 EXP E) + &1 - &E) - &(fin_flog 2 b)` THEN CONJ_TAC THENL
   [SUBGOAL_THEN `fin_flog 2 b <= E` MP_TAC THENL
     [MATCH_MP_TAC FIN_TWO_FLOG_UB THEN ASM_REWRITE_TAC[EXP_ADD; EXP_1] THEN
      ASM_ARITH_TAC;
      REWRITE_TAC[GSYM REAL_OF_NUM_LE] THEN REAL_ARITH_TAC];
    MATCH_MP_TAC FIN_TWO_DIV_VAL THEN ASM_SIMP_TAC[FIN_TWO_TAILM; LE_REFL]]);;

let FIN_TWO_TAILQ1 = prove
 (`forall E n b. 2 EXP E <= n /\ n < 2 * 2 EXP E /\ 1 <= b /\ b < 2 * 2 EXP E
           ==> fin_vge 2 (&(2 EXP E) + &1 - &2 * &E) (cat_m n / &b)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`E:num`; `n:num`; `b:num`; `1`] FIN_TWO_TAILQ) THEN
  ASM_REWRITE_TAC[REAL_MUL_LID]);;

let FIN_TWO_TAILM2 = prove
 (`forall E n. 2 EXP E <= n /\ n < 2 * 2 EXP E
         ==> fin_vge 2 (&(2 EXP E) + &1 - &2 * &E) (cat_m n)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC FIN_VGE_MONO THEN
  EXISTS_TAC `&(2 EXP E) + &1 - &E` THEN ASM_SIMP_TAC[FIN_TWO_TAILM] THEN
  REAL_ARITH_TAC);;

let FIN_TWO_DIV_EQ = prove
 (`forall x y n. ~(n = 0) /\ &n * x = y ==> x = y / &n`,
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC(REAL_FIELD `~(a = &0) ==> x = (a * x) / a`) THEN
  ASM_REWRITE_TAC[REAL_OF_NUM_EQ]);;

let FIN_TWO_VMONO = prove
 (`forall V d L x. fin_vge 2 V x ==> fin_vge 2 (V - &d * &L) x`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC FIN_VGE_MONO THEN EXISTS_TAC `V:real` THEN
  ASM_REWRITE_TAC[REAL_ARITH `V - x <= V <=> &0 <= x`] THEN
  MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS]);;

let FIN_TWO_SPLIT_TAC =
  REPEAT((MATCH_MP_TAC FIN_VGE_ADD ORELSE MATCH_MP_TAC FIN_VGE_SUB) THEN
         REWRITE_TAC[FIN_TWO_PRIME] THEN REPEAT CONJ_TAC);;

let FIN_TWO_STEP_MONO = prove
 (`forall V d L. V - &d * &L - &L >= V - &(d + 2) * &L:real /\
           V - &d * &L - &L >= V - &(d + 1) * &L:real`,
  REPEAT GEN_TAC THEN MP_TAC(SPEC `L:num` REAL_POS) THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN REAL_ARITH_TAC);;

let FIN_TWO_DLEFT_VAL = prove
 (`forall H E. 1 <= H /\ H + 3 < 2 EXP E
         ==> forall d. d <= H
                 ==> fin_vge 2 ((&(2 EXP E) + &1 - &2 * &E) - &d * &(fin_flog 2 H))
                       (fin_two_X (2 EXP E) d 0 - fin_two_mk (2 EXP E) d 0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `V = &(2 EXP E) + &1 - &2 * &E` THEN
  SUBGOAL_THEN
   `forall d. (d <= H ==> fin_vge 2 (V - &d * &(fin_flog 2 H))
                     (fin_two_X (2 EXP E) d 0 - fin_two_mk (2 EXP E) d 0)) /\
        (d + 1 <= H ==> fin_vge 2 (V - &(d + 1) * &(fin_flog 2 H))
                     (fin_two_X (2 EXP E) (d + 1) 0 - fin_two_mk (2 EXP E) (d + 1) 0))`
   (fun th -> MESON_TAC[th]) THEN
  INDUCT_TAC THENL
   [REWRITE_TAC[FIN_TWO_D00; ADD_CLAUSES; FIN_TWO_D10] THEN CONJ_TAC THEN DISCH_TAC THENL
     [SIMP_TAC[FIN_VGE_0; FIN_TWO_PRIME]; ALL_TAC] THEN
    MATCH_MP_TAC FIN_TWO_VMONO THEN FIN_TWO_SPLIT_TAC THEN
    EXPAND_TAC "V" THEN MATCH_MP_TAC FIN_TWO_TAILM2 THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  POP_ASSUM STRIP_ASSUME_TAC THEN ASM_REWRITE_TAC[ADD1] THEN
  REWRITE_TAC[ARITH_RULE `(d + 1) + 1 = d + 2`] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`2 EXP E`; `d:num`] FIN_TWO_D_MINUS) THEN
  DISCH_THEN(SUBST1_TAC o MATCH_MP FIN_TWO_DIV_EQ o
             CONJ (ARITH_RULE `~(d + 2 = 0)`)) THEN
  MATCH_MP_TAC FIN_VGE_MONO THEN
  EXISTS_TAC `V - &d * &(fin_flog 2 H) - &(fin_flog 2 H)` THEN
  REWRITE_TAC[GSYM real_ge; FIN_TWO_STEP_MONO] THEN
  MATCH_MP_TAC FIN_TWO_DIV_VAL THEN CONJ_TAC THENL [ALL_TAC; ASM_ARITH_TAC] THEN
  FIN_TWO_SPLIT_TAC THENL
   [MATCH_MP_TAC FIN_VGE_ZP_MUL THEN SIMP_TAC[FIN_TWO_PRIME; FIN_ZP_NUM] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    MATCH_MP_TAC FIN_TWO_VMONO THEN EXPAND_TAC "V" THEN
    MATCH_MP_TAC FIN_TWO_TAILM2 THEN ASM_ARITH_TAC;
    MATCH_MP_TAC FIN_TWO_VMONO THEN EXPAND_TAC "V" THEN
    MATCH_MP_TAC FIN_TWO_TAILM2 THEN ASM_ARITH_TAC]);;

let FIN_TWO_DTOP_VAL = prove
 (`forall H E. 1 <= H /\ H + 3 < 2 EXP E
         ==> forall d. d <= H
                 ==> fin_vge 2 ((&(2 EXP E) + &1 - &2 * &E) - &d * &(fin_flog 2 H))
                       (fin_two_X (2 EXP E) 0 d - fin_two_mk (2 EXP E) 0 d)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `V = &(2 EXP E) + &1 - &2 * &E` THEN
  SUBGOAL_THEN
   `forall d. (d <= H ==> fin_vge 2 (V - &d * &(fin_flog 2 H))
                     (fin_two_X (2 EXP E) 0 d - fin_two_mk (2 EXP E) 0 d)) /\
        (d + 1 <= H ==> fin_vge 2 (V - &(d + 1) * &(fin_flog 2 H))
                     (fin_two_X (2 EXP E) 0 (d + 1) - fin_two_mk (2 EXP E) 0 (d + 1)))`
   (fun th -> MESON_TAC[th]) THEN
  INDUCT_TAC THENL
   [REWRITE_TAC[FIN_TWO_D00; ADD_CLAUSES; FIN_TWO_D01] THEN
    SIMP_TAC[FIN_VGE_0; FIN_TWO_PRIME];
    ALL_TAC] THEN
  POP_ASSUM STRIP_ASSUME_TAC THEN ASM_REWRITE_TAC[ADD1] THEN
  REWRITE_TAC[ARITH_RULE `(d + 1) + 1 = d + 2`] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`2 EXP E`; `d:num`] FIN_TWO_D_PLUS) THEN
  DISCH_THEN(SUBST1_TAC o MATCH_MP FIN_TWO_DIV_EQ o
             CONJ (ARITH_RULE `~(d + 1 = 0)`)) THEN
  MATCH_MP_TAC FIN_VGE_MONO THEN
  EXISTS_TAC `V - &d * &(fin_flog 2 H) - &(fin_flog 2 H)` THEN
  REWRITE_TAC[GSYM real_ge; FIN_TWO_STEP_MONO] THEN
  MATCH_MP_TAC FIN_TWO_DIV_VAL THEN CONJ_TAC THENL [ALL_TAC; ASM_ARITH_TAC] THEN
  FIN_TWO_SPLIT_TAC THENL
   [MATCH_MP_TAC FIN_VGE_ZP_MUL THEN SIMP_TAC[FIN_TWO_PRIME; FIN_ZP_NUM] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    MATCH_MP_TAC FIN_TWO_VMONO THEN EXPAND_TAC "V" THEN
    MATCH_MP_TAC FIN_TWO_TAILQ THEN ASM_ARITH_TAC;
    MATCH_MP_TAC FIN_TWO_VMONO THEN EXPAND_TAC "V" THEN
    MATCH_MP_TAC FIN_TWO_TAILQ THEN ASM_ARITH_TAC;
    MATCH_MP_TAC FIN_TWO_VMONO THEN EXPAND_TAC "V" THEN
    MATCH_MP_TAC FIN_TWO_TAILM2 THEN ASM_ARITH_TAC;
    MATCH_MP_TAC FIN_TWO_VMONO THEN EXPAND_TAC "V" THEN
    MATCH_MP_TAC FIN_TWO_TAILM2 THEN ASM_ARITH_TAC]);;

let FIN_TWO_VMONO2 = prove
 (`forall V a b L. a <= b ==> V - &b * &L <= V - &a * &L`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(REAL_ARITH `x <= y ==> V - y <= V - x:real`) THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[REAL_OF_NUM_LE; REAL_POS]);;

let FIN_TWO_D_VAL_K = prove
 (`forall H E k i j. 1 <= H /\ H + 3 < 2 EXP E /\
               (i = 0 \/ j = 0) /\ i + k <= H /\ j + k <= H
               ==> fin_vge 2 ((&(2 EXP E) + &1 - &2 * &E) - &H * &(fin_flog 2 H))
                     (fin_two_X (2 EXP E) (i + k) (j + k) -
                      fin_two_mk (2 EXP E) (i + k) (j + k))`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THENL
   [REWRITE_TAC[ADD_CLAUSES] THEN REPEAT GEN_TAC THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 DISJ_CASES_TAC STRIP_ASSUME_TAC))) THEN
    FIRST_X_ASSUM SUBST_ALL_TAC THEN MATCH_MP_TAC FIN_VGE_MONO THENL
     [EXISTS_TAC `(&(2 EXP E) + &1 - &2 * &E) - &j * &(fin_flog 2 H)` THEN
      ASM_SIMP_TAC[FIN_TWO_VMONO2] THEN
      MP_TAC(SPECL [`H:num`; `E:num`] FIN_TWO_DTOP_VAL) THEN ASM_SIMP_TAC[];
      EXISTS_TAC `(&(2 EXP E) + &1 - &2 * &E) - &i * &(fin_flog 2 H)` THEN
      ASM_SIMP_TAC[FIN_TWO_VMONO2] THEN
      MP_TAC(SPECL [`H:num`; `E:num`] FIN_TWO_DLEFT_VAL) THEN ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN ASSUME_TAC) THEN
  REWRITE_TAC[ARITH_RULE `i + SUC k = (i + k) + 1`] THEN
  MP_TAC(SPECL [`2 EXP E`; `i + k:num`; `j + k:num`] FIN_TWO_D_DIAG) THEN
  REWRITE_TAC[REAL_ARITH `a = b + c <=> b = a - c:real`] THEN
  DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC FIN_VGE_SUB THEN
  REWRITE_TAC[FIN_TWO_PRIME] THEN CONJ_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    MATCH_MP_TAC FIN_TWO_VMONO THEN
    MATCH_MP_TAC FIN_TWO_TAILQ1 THEN ASM_ARITH_TAC]);;

let FIN_TWO_D_VAL = prove
 (`forall H E. 1 <= H /\ H + 3 < 2 EXP E
         ==> forall i j. i <= H /\ j <= H
                   ==> fin_vge 2 ((&(2 EXP E) + &1 - &2 * &E) - &H * &(fin_flog 2 H))
                         (fin_two_X (2 EXP E) i j - fin_two_mk (2 EXP E) i j)`,
  REPEAT STRIP_TAC THEN DISJ_CASES_TAC(ARITH_RULE `i:num <= j \/ j < i`) THENL
   [MP_TAC(SPECL [`H:num`; `E:num`; `i:num`; `0`; `j - i:num`] FIN_TWO_D_VAL_K) THEN
    ASM_SIMP_TAC[ADD_CLAUSES; SUB_ADD] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_ARITH_TAC;
    MP_TAC(SPECL [`H:num`; `E:num`; `j:num`; `i - j:num`; `0`] FIN_TWO_D_VAL_K) THEN
    ASM_SIMP_TAC[ADD_CLAUSES; SUB_ADD; LT_IMP_LE] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_ARITH_TAC]);;

let FIN_TWO_EXP_3 = prove
 (`forall e. 3 * e <= 2 EXP e + 4`,
  INDUCT_TAC THEN REWRITE_TAC[EXP; ARITH] THEN
  MP_TAC(SPEC `e:num` LT_POW2_REFL) THEN POP_ASSUM MP_TAC THEN ARITH_TAC);;

let FIN_TWO_X_VAL = prove
 (`forall H i j. 1 <= H /\ i <= H /\ j < H
           ==> fin_vge 2 (&i - &2 * &(fin_flog 2 H) - &2)
                 (fin_two_X (2 EXP (H * H + H + 4)) i j)`,
  REPEAT STRIP_TAC THEN ABBREV_TAC `E = H * H + H + 4` THEN
  SUBGOAL_THEN `fin_two_X (2 EXP E) i j = fin_two_mk (2 EXP E) i j +
     (fin_two_X (2 EXP E) i j - fin_two_mk (2 EXP E) i j)` SUBST1_TAC THENL
   [REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC FIN_VGE_ADD THEN ASM_SIMP_TAC[FIN_TWO_PRIME; FIN_TWO_MK_VAL] THEN
  MATCH_MP_TAC FIN_VGE_MONO THEN
  EXISTS_TAC `(&(2 EXP E) + &1 - &2 * &E) - &H * &(fin_flog 2 H)` THEN CONJ_TAC THENL
   [ALL_TAC;
    MP_TAC(SPECL [`H:num`; `E:num`] FIN_TWO_D_VAL) THEN ANTS_TAC THENL
     [MP_TAC(SPEC `E:num` LT_POW2_REFL) THEN ASM_ARITH_TAC;
      DISCH_THEN MATCH_MP_TAC THEN ASM_ARITH_TAC]] THEN
  MP_TAC(SPEC `E:num` FIN_TWO_EXP_3) THEN
  MP_TAC(SPEC `H:num` FIN_TWO_FLOG_HALF) THEN
  SUBGOAL_THEN `H * fin_flog 2 H <= H * H` MP_TAC THENL
   [REWRITE_TAC[LE_MULT_LCANCEL] THEN MP_TAC(SPEC `H:num` FIN_TWO_FLOG_HALF) THEN
    ARITH_TAC;
    ALL_TAC] THEN
  UNDISCH_TAC `H * H + H + 4 = E` THEN UNDISCH_TAC `i:num <= H` THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_LE; GSYM REAL_OF_NUM_MUL; GSYM REAL_OF_NUM_ADD;
              GSYM REAL_OF_NUM_EQ] THEN
  REAL_ARITH_TAC);;
