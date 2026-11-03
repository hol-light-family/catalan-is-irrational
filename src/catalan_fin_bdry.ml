(* ========================================================================= *)
(* CAT_FINITE_PLACE: boundary formulas (Equations (18), (19)) and the basic  *)
(* valuation bounds for 1/n, 1/binom(2l,l) and floor(log_p n).               *)
(* ========================================================================= *)

needs "src/catalan_fin_base.ml";;

(* ------------------------------------------------------------------------- *)
(* Elementary facts on c_l, m_i, H*_z.                                       *)
(* ------------------------------------------------------------------------- *)

let fin_bdry_nz_tac tms =
  MAP_EVERY (fun t -> SUBGOAL_THEN t MP_TAC THENL
    [REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_MUL; REAL_OF_NUM_EQ] THEN
     ARITH_TAC; ALL_TAC]) tms;;

let FIN_BDRY_BINOM_STEP = prove
 (`forall l. &(l + 1) * &(binom(2 * (l + 1),l + 1)) =
       &2 * &(2 * l + 1) * &(binom(2 * l,l))`,
  GEN_TAC THEN
  MP_TAC(SPECL [`l:num`; `l:num`] BINOM_FACT) THEN
  MP_TAC(SPECL [`l + 1`; `l + 1`] BINOM_FACT) THEN
  REWRITE_TAC[ARITH_RULE `(l + 1) + l + 1 = SUC(SUC(l + l))`;
              ARITH_RULE `2 * (l + 1) = (l + 1) + l + 1`;
              ARITH_RULE `2 * l = l + l`] THEN
  REWRITE_TAC[ARITH_RULE `(l + 1) + l + 1 = SUC(SUC(l + l))`] THEN
  REWRITE_TAC[GSYM ADD1; FACT] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_EQ; GSYM REAL_OF_NUM_MUL; GSYM REAL_OF_NUM_ADD;
              GSYM REAL_OF_NUM_SUC] THEN
  MP_TAC(SPEC `l:num` FACT_NZ) THEN REWRITE_TAC[GSYM REAL_OF_NUM_EQ] THEN
  fin_bdry_nz_tac [`~(&l + &1 = &0)`] THEN
  CONV_TAC REAL_FIELD);;

let FIN_BDRY_C_REC = prove
 (`forall l. &(2 * l + 2) * cat_c (l + 1) = &(2 * l + 1) * cat_c l`,
  GEN_TAC THEN REWRITE_TAC[cat_c] THEN
  MP_TAC(SPEC `l:num` FIN_BDRY_BINOM_STEP) THEN
  REWRITE_TAC[REAL_POW_ADD; REAL_POW_1; GSYM REAL_OF_NUM_ADD;
              GSYM REAL_OF_NUM_MUL] THEN
  SUBGOAL_THEN `~(&4 pow l = &0)` MP_TAC THENL
   [REWRITE_TAC[REAL_POW_EQ_0] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  CONV_TAC REAL_FIELD);;

let FIN_BDRY_C_POS = prove
 (`forall l. &0 < cat_c l`,
  GEN_TAC THEN REWRITE_TAC[cat_c] THEN MATCH_MP_TAC REAL_LT_DIV THEN
  SIMP_TAC[REAL_POW_LT; REAL_OF_NUM_LT; ARITH] THEN
  REWRITE_TAC[LT_NZ; BINOM_EQ_0] THEN ARITH_TAC);;

let FIN_BDRY_C_0 = prove
 (`cat_c 0 = &1`,
  REWRITE_TAC[cat_c; MULT_CLAUSES; binom; real_pow] THEN REAL_ARITH_TAC);;

let FIN_BDRY_C_STEP = prove
 (`forall l. cat_c (l + 1) = cat_c l * &(2 * l + 1) / &(2 * l + 2)`,
  GEN_TAC THEN MP_TAC(SPEC `l:num` FIN_BDRY_C_REC) THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_ADD; GSYM REAL_OF_NUM_MUL] THEN
  fin_bdry_nz_tac [`~(&2 * &l + &2 = &0)`] THEN CONV_TAC REAL_FIELD);;

let FIN_BDRY_M_EVEN2 = prove
 (`forall a. cat_m (2 * a) = &2 / (&(2 * a + 1) * cat_c a)`,
  GEN_TAC THEN REWRITE_TAC[cat_m; EVEN_MULT; ARITH] THEN
  SIMP_TAC[DIV_MULT; ARITH_EQ]);;

let FIN_BDRY_M_ODD2 = prove
 (`forall a. cat_m (2 * a + 1) = &0`,
  REWRITE_TAC[cat_m; EVEN_ADD; EVEN_MULT; ARITH]);;

let FIN_BDRY_M_REC = prove
 (`forall i. &(i + 3) * cat_m (i + 2) = &(i + 2) * cat_m i`,
  GEN_TAC THEN DISJ_CASES_TAC(SPEC `i:num` EVEN_OR_ODD) THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `a:num` SUBST1_TAC o
    REWRITE_RULE[EVEN_EXISTS; ODD_EXISTS; ADD1]) THENL
   [REWRITE_TAC[ARITH_RULE `2 * a + 2 = 2 * (a + 1)`; FIN_BDRY_M_EVEN2] THEN
    REWRITE_TAC[FIN_BDRY_C_STEP] THEN
    MP_TAC(SPEC `a:num` FIN_BDRY_C_POS) THEN
    DISCH_THEN(MP_TAC o MATCH_MP REAL_LT_IMP_NZ) THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_ADD; GSYM REAL_OF_NUM_MUL] THEN
    fin_bdry_nz_tac [`~(&2 * &a + &1 = &0)`; `~(&2 * &a + &2 = &0)`;
                     `~(&2 * &a + &3 = &0)`] THEN
    CONV_TAC REAL_FIELD;
    REWRITE_TAC[ARITH_RULE `(2 * a + 1) + 2 = 2 * (a + 1) + 1`;
                FIN_BDRY_M_ODD2; REAL_MUL_RZERO]]);;

let FIN_BDRY_HSTAR_EVEN2 = prove
 (`forall a. fin_hstar (2 * a) = cat_c a`,
  GEN_TAC THEN REWRITE_TAC[fin_hstar; EVEN_MULT; ARITH] THEN
  SIMP_TAC[DIV_MULT; ARITH_EQ]);;

let FIN_BDRY_HSTAR_ODD2 = prove
 (`forall a. fin_hstar (2 * a + 1) = inv(&(2 * a + 1) * cat_c a)`,
  GEN_TAC THEN REWRITE_TAC[fin_hstar; EVEN_ADD; EVEN_MULT; ARITH; ADD_SUB] THEN
  SIMP_TAC[DIV_MULT; ARITH_EQ]);;

let FIN_BDRY_HSTAR_POS = prove
 (`forall z. &0 < fin_hstar z`,
  GEN_TAC THEN DISJ_CASES_TAC(SPEC `z:num` EVEN_OR_ODD) THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `a:num` SUBST1_TAC o
    REWRITE_RULE[EVEN_EXISTS; ODD_EXISTS; ADD1]) THEN
  REWRITE_TAC[FIN_BDRY_HSTAR_EVEN2; FIN_BDRY_HSTAR_ODD2; FIN_BDRY_C_POS] THEN
  MATCH_MP_TAC REAL_LT_INV THEN MATCH_MP_TAC REAL_LT_MUL THEN
  REWRITE_TAC[FIN_BDRY_C_POS; REAL_OF_NUM_LT] THEN ARITH_TAC);;

let FIN_BDRY_HSTAR_NZ = prove
 (`forall z. ~(fin_hstar z = &0)`,
  MESON_TAC[FIN_BDRY_HSTAR_POS; REAL_LT_IMP_NZ]);;

let FIN_BDRY_HSTAR_1 = prove
 (`fin_hstar 1 = &1`,
  MP_TAC(SPEC `0` FIN_BDRY_HSTAR_ODD2) THEN
  REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; FIN_BDRY_C_0] THEN
  DISCH_THEN SUBST1_TAC THEN CONV_TAC REAL_RAT_REDUCE_CONV);;

let FIN_BDRY_HSTAR_STEP = prove
 (`forall z. fin_hstar (z + 2) = fin_hstar z * &(z + 1) / &(z + 2)`,
  GEN_TAC THEN DISJ_CASES_TAC(SPEC `z:num` EVEN_OR_ODD) THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `a:num` SUBST1_TAC o
    REWRITE_RULE[EVEN_EXISTS; ODD_EXISTS; ADD1]) THENL
   [REWRITE_TAC[ARITH_RULE `2 * a + 2 = 2 * (a + 1)`; FIN_BDRY_HSTAR_EVEN2] THEN
    REWRITE_TAC[FIN_BDRY_C_STEP; ARITH_RULE `2 * (a + 1) = 2 * a + 2`] THEN
    REWRITE_TAC[REAL_MUL_ASSOC];
    REWRITE_TAC[ARITH_RULE `(2 * a + 1) + 2 = 2 * (a + 1) + 1`;
                FIN_BDRY_HSTAR_ODD2] THEN
    REWRITE_TAC[FIN_BDRY_C_STEP] THEN
    MP_TAC(SPEC `a:num` FIN_BDRY_C_POS) THEN
    DISCH_THEN(MP_TAC o MATCH_MP REAL_LT_IMP_NZ) THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_ADD; GSYM REAL_OF_NUM_MUL] THEN
    fin_bdry_nz_tac [`~(&2 * &a + &1 = &0)`; `~(&2 * &a + &2 = &0)`;
                     `~(&2 * &a + &3 = &0)`] THEN
    CONV_TAC REAL_FIELD]);;

let FIN_BDRY_M_ODD = prove
 (`forall z. ODD z ==> cat_m (z - 1) = &2 * fin_hstar z`,
  GEN_TAC THEN REWRITE_TAC[ODD_EXISTS; ADD1] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:num` SUBST1_TAC) THEN
  REWRITE_TAC[ADD_SUB; FIN_BDRY_M_EVEN2; FIN_BDRY_HSTAR_ODD2; real_div]);;

(* parity-pair forms used in the boundary recurrences *)

let FIN_BDRY_M_EVEN_PAIR = prove
 (`forall d. EVEN d ==> cat_m d = &2 / (&(d + 1) * fin_hstar d) /\ cat_m (d + 1) = &0`,
  GEN_TAC THEN REWRITE_TAC[EVEN_EXISTS] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:num` SUBST1_TAC) THEN
  REWRITE_TAC[FIN_BDRY_M_EVEN2; FIN_BDRY_M_ODD2; FIN_BDRY_HSTAR_EVEN2]);;

let FIN_BDRY_M_ODD_PAIR = prove
 (`forall d. ODD d ==> cat_m d = &0 /\ cat_m (d + 1) = &2 * fin_hstar (d + 2)`,
  GEN_TAC THEN REWRITE_TAC[ODD_EXISTS; ADD1] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:num` SUBST1_TAC) THEN
  REWRITE_TAC[FIN_BDRY_M_ODD2] THEN
  MP_TAC(SPEC `(2 * a + 1) + 2` FIN_BDRY_M_ODD) THEN
  REWRITE_TAC[ODD_ADD; ODD_MULT; ARITH] THEN
  REWRITE_TAC[ARITH_RULE `((2 * a + 1) + 2) - 1 = (2 * a + 1) + 1`]);;

(* ------------------------------------------------------------------------- *)
(* Boundary recurrences solved explicitly, Equation (19).                    *)
(* ------------------------------------------------------------------------- *)

let FIN_BDRY_IND2 = prove
 (`forall P. P 0 /\ P 1 /\ (forall d. P d ==> P (d + 2)) ==> forall n. P n`,
  GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `forall n. P n /\ P (n + 1)` (fun th -> MESON_TAC[th]) THEN
  INDUCT_TAC THENL
   [ASM_REWRITE_TAC[ADD_CLAUSES];
    ASM_REWRITE_TAC[ADD1; ARITH_RULE `(n + 1) + 1 = n + 2`] THEN
    ASM_MESON_TAC[]]);;

let FIN_BDRY_SUM_STEP2 = prove
 (`forall f n. sum(1..n + 2) f = sum(1..n) f + f(n + 1) + f(n + 2)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[ARITH_RULE `n + 2 = SUC(SUC n)`; SUM_CLAUSES_NUMSEG;
              ARITH_RULE `1 <= SUC n`] THEN
  REWRITE_TAC[ADD1; REAL_ADD_ASSOC]);;

let FIN_BDRY_KMINUS_STEP = prove
 (`forall d. cat_kminus (d + 2) =
       (&(d + 1) * cat_kminus d + cat_m d + cat_m (d + 1)) / &(d + 2)`,
  GEN_TAC THEN REWRITE_TAC[GSYM(el 2 (CONJUNCTS cat_kminus))] THEN
  AP_TERM_TAC THEN ARITH_TAC);;

let FIN_BDRY_KPLUS_STEP = prove
 (`forall d. cat_kplus (d + 2) = (&d * cat_kplus d + &2 / &(d + 1)) / &(d + 1)`,
  GEN_TAC THEN REWRITE_TAC[GSYM(el 2 (CONJUNCTS cat_kplus))] THEN
  AP_TERM_TAC THEN ARITH_TAC);;

let FIN_BDRY_KMINUS_1 = prove
 (`cat_kminus 1 = &2`,
  REWRITE_TAC[num_CONV `1`; cat_kminus]);;

let FIN_BDRY_KPLUS_1 = prove
 (`cat_kplus 1 = &0`,
  REWRITE_TAC[num_CONV `1`; cat_kplus]);;

let FIN_BDRY_KPLUS_2 = prove
 (`cat_kplus 2 = &2`,
  MP_TAC(SPEC `0` FIN_BDRY_KPLUS_STEP) THEN
  REWRITE_TAC[ADD_CLAUSES; cat_kplus] THEN DISCH_THEN SUBST1_TAC THEN
  CONV_TAC REAL_RAT_REDUCE_CONV);;

let FIN_BDRY_KMINUS_BOTH = prove
 (`forall u. (EVEN u ==> cat_kminus u = fin_hstar u * sum (1..u)
          (\z. if EVEN z then &2 / (&z pow 2 * fin_hstar z pow 2) else &0)) /\
       (ODD u ==> cat_kminus u = fin_hstar u * sum (1..u)
          (\z. if ODD z then &2 / &z else &0))`,
  MATCH_MP_TAC FIN_BDRY_IND2 THEN BETA_TAC THEN CONJ_TAC THENL
   [REWRITE_TAC[ARITH; cat_kminus; SUM_CLAUSES_NUMSEG; REAL_MUL_RZERO];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[ARITH; FIN_BDRY_KMINUS_1; SUM_SING_NUMSEG; FIN_BDRY_HSTAR_1;
                BETA_THM] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV;
    X_GEN_TAC `d:num` THEN STRIP_TAC THEN CONJ_TAC THEN DISCH_TAC THENL
     [SUBGOAL_THEN `EVEN d` ASSUME_TAC THENL
       [UNDISCH_TAC `EVEN(d + 2)` THEN REWRITE_TAC[EVEN_ADD; ARITH]; ALL_TAC] THEN
      FIRST_X_ASSUM(MP_TAC o C MATCH_MP (ASSUME `EVEN d`)) THEN
      MP_TAC(SPEC `d:num` FIN_BDRY_M_EVEN_PAIR) THEN ASM_REWRITE_TAC[] THEN
      REPEAT STRIP_TAC THEN
      ASM_REWRITE_TAC[FIN_BDRY_KMINUS_STEP; FIN_BDRY_SUM_STEP2;
                      FIN_BDRY_HSTAR_STEP; EVEN_ADD; ARITH; BETA_THM] THEN
      MP_TAC(SPEC `d:num` FIN_BDRY_HSTAR_NZ) THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN
      fin_bdry_nz_tac [`~(&d + &1 = &0)`; `~(&d + &2 = &0)`] THEN
      CONV_TAC REAL_FIELD;
      SUBGOAL_THEN `ODD d` ASSUME_TAC THENL
       [UNDISCH_TAC `ODD(d + 2)` THEN REWRITE_TAC[ODD_ADD; ARITH]; ALL_TAC] THEN
      FIRST_X_ASSUM(MP_TAC o C MATCH_MP (ASSUME `ODD d`)) THEN
      MP_TAC(SPEC `d:num` FIN_BDRY_M_ODD_PAIR) THEN ASM_REWRITE_TAC[] THEN
      REPEAT STRIP_TAC THEN
      ASM_REWRITE_TAC[FIN_BDRY_KMINUS_STEP; FIN_BDRY_SUM_STEP2;
                      FIN_BDRY_HSTAR_STEP; ODD_ADD; ARITH; BETA_THM] THEN
      MP_TAC(SPEC `d:num` FIN_BDRY_HSTAR_NZ) THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN
      fin_bdry_nz_tac [`~(&d + &1 = &0)`; `~(&d + &2 = &0)`] THEN
      CONV_TAC REAL_FIELD]]);;

let FIN_BDRY_KMINUS_EVEN = prove
 (`forall u. EVEN u ==> cat_kminus u = fin_hstar u * sum (1..u)
          (\z. if EVEN z then &2 / (&z pow 2 * fin_hstar z pow 2) else &0)`,
  MESON_TAC[FIN_BDRY_KMINUS_BOTH]);;

let FIN_BDRY_KMINUS_ODD = prove
 (`forall u. ODD u ==> cat_kminus u = fin_hstar u * sum (1..u)
          (\z. if ODD z then &2 / &z else &0)`,
  MESON_TAC[FIN_BDRY_KMINUS_BOTH]);;

let FIN_BDRY_KPLUS = prove
 (`forall u. cat_kplus (u + 1) = fin_hstar u * sum (1..u)
          (\z. if (EVEN z <=> EVEN u) then &2 / (&z pow 2 * fin_hstar z) else &0)`,
  MATCH_MP_TAC FIN_BDRY_IND2 THEN BETA_TAC THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[ADD_CLAUSES; FIN_BDRY_KPLUS_1; SUM_CLAUSES_NUMSEG; ARITH;
                REAL_MUL_RZERO];
    REWRITE_TAC[ARITH; FIN_BDRY_KPLUS_2; SUM_SING_NUMSEG; FIN_BDRY_HSTAR_1;
                BETA_THM] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV;
    X_GEN_TAC `d:num` THEN DISCH_TAC THEN
    REWRITE_TAC[ARITH_RULE `(d + 2) + 1 = (d + 1) + 2`] THEN
    REWRITE_TAC[FIN_BDRY_KPLUS_STEP] THEN
    REWRITE_TAC[ARITH_RULE `(d + 1) + 1 = d + 2`] THEN
    REWRITE_TAC[FIN_BDRY_SUM_STEP2; EVEN_ADD; ARITH; BETA_THM;
                TAUT `(~p <=> p) <=> false`] THEN
    ASM_REWRITE_TAC[FIN_BDRY_HSTAR_STEP] THEN
    MP_TAC(SPEC `d:num` FIN_BDRY_HSTAR_NZ) THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN
    fin_bdry_nz_tac [`~(&d + &1 = &0)`; `~(&d + &2 = &0)`] THEN
    CONV_TAC REAL_FIELD]);;

(* ------------------------------------------------------------------------- *)
(* floor(log_p n).                                                           *)
(* ------------------------------------------------------------------------- *)

let FIN_BDRY_FLOG_GE = prove
 (`forall p n e. 2 <= p /\ p EXP e <= n ==> e <= fin_flog p n`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[fin_flog] THEN
  MP_TAC(ISPECL [`1..e`; `{j | 1 <= j /\ p EXP j <= n}`] CARD_SUBSET) THEN
  ASM_SIMP_TAC[FINITE_EXP_LE; CARD_NUMSEG_1] THEN DISCH_THEN MATCH_MP_TAC THEN
  REWRITE_TAC[SUBSET; IN_NUMSEG; IN_ELIM_THM] THEN
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  TRANS_TAC LE_TRANS `p EXP e` THEN ASM_REWRITE_TAC[LE_EXP] THEN
  ASM_ARITH_TAC);;

let FIN_BDRY_FLOG_EXP = prove
 (`forall p n. 2 <= p /\ 1 <= n ==> p EXP (fin_flog p n) <= n`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `\e. p EXP e <= n` num_MAX) THEN BETA_TAC THEN
  MATCH_MP_TAC(TAUT `a /\ (b ==> c) ==> (a <=> b) ==> c`) THEN CONJ_TAC THENL
   [CONJ_TAC THENL
     [EXISTS_TAC `0` THEN ASM_REWRITE_TAC[EXP];
      EXISTS_TAC `n:num` THEN X_GEN_TAC `e:num` THEN DISCH_TAC THEN
      TRANS_TAC LE_TRANS `p EXP e` THEN ASM_REWRITE_TAC[] THEN
      TRANS_TAC LE_TRANS `2 EXP e` THEN
      ASM_SIMP_TAC[LT_IMP_LE; LT_POW2_REFL; EXP_MONO_LE]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:num` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `fin_flog p n = k` (fun th -> ASM_REWRITE_TAC[th]) THEN
  REWRITE_TAC[fin_flog] THEN
  SUBGOAL_THEN `{e | 1 <= e /\ p EXP e <= n} = 1..k` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_NUMSEG] THEN
    X_GEN_TAC `e:num` THEN EQ_TAC THEN STRIP_TAC THEN ASM_SIMP_TAC[] THEN
    TRANS_TAC LE_TRANS `p EXP k` THEN ASM_REWRITE_TAC[LE_EXP] THEN
    ASM_ARITH_TAC;
    REWRITE_TAC[CARD_NUMSEG_1]]);;

let FIN_BDRY_FLOG_ZERO = prove
 (`forall p n. n < p ==> fin_flog p n = 0`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[fin_flog] THEN
  SUBGOAL_THEN `{e | 1 <= e /\ p EXP e <= n} = {}` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY] THEN
    X_GEN_TAC `e:num` THEN STRIP_TAC THEN
    SUBGOAL_THEN `p EXP 1 <= p EXP e` MP_TAC THENL
     [REWRITE_TAC[LE_EXP] THEN COND_CASES_TAC THEN ASM_ARITH_TAC;
      REWRITE_TAC[EXP_1] THEN ASM_ARITH_TAC];
    REWRITE_TAC[CARD_CLAUSES]]);;

let FIN_BDRY_FLOG_MONO = prove
 (`forall p m n. m <= n ==> fin_flog p m <= fin_flog p n`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[fin_flog] THEN
  ASM_CASES_TAC `2 <= p` THENL
   [MATCH_MP_TAC CARD_SUBSET THEN ASM_SIMP_TAC[FINITE_EXP_LE] THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN ASM_MESON_TAC[LE_TRANS];
    ALL_TAC] THEN
  SUBGOAL_THEN `p = 0 \/ p = 1` (DISJ_CASES_THEN SUBST_ALL_TAC) THENL
   [ASM_ARITH_TAC; ALL_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[EXP_ONE; EXP_ZERO] THENL
   [MATCH_MP_TAC EQ_IMP_LE THEN AP_TERM_TAC THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN X_GEN_TAC `e:num` THEN
    ASM_CASES_TAC `e = 0` THEN ASM_REWRITE_TAC[] THEN ARITH_TAC;
    ASM_CASES_TAC `m = 0` THENL
     [ASM_REWRITE_TAC[ARITH; EMPTY_GSPEC; CARD_CLAUSES; LE_0];
      MATCH_MP_TAC EQ_IMP_LE THEN AP_TERM_TAC THEN
      REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN ASM_ARITH_TAC]]);;

let FIN_BDRY_FLOG_LOG = prove
 (`forall p n. 2 <= p /\ 1 <= n ==> &(fin_flog p n) * log(&p) <= log(&n)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < &p` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[GSYM LOG_POW] THEN MATCH_MP_TAC LOG_MONO_LE_IMP THEN
  ASM_SIMP_TAC[REAL_POW_LT; REAL_OF_NUM_POW; REAL_OF_NUM_LE;
               FIN_BDRY_FLOG_EXP]);;

(* ------------------------------------------------------------------------- *)
(* Valuations of 1/n and 1/binom(2l,l).                                      *)
(* ------------------------------------------------------------------------- *)

let FIN_BDRY_INV_INDEX = prove
 (`forall p n b. prime p /\ ~(n = 0) /\ index p n <= b
           ==> fin_vge p (--(&b)) (inv(&n))`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[FIN_VGE_NEGPOW] THEN
  ABBREV_TAC `e = index p n` THEN
  MP_TAC(SPECL [`n:num`; `p:num`] INDEX_DECOMPOSITION) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `m:num` STRIP_ASSUME_TAC) THENL
   [ASM_MESON_TAC[PRIME_1]; ALL_TAC] THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `f:num` SUBST1_TAC o REWRITE_RULE[LE_EXISTS]) THEN
  REWRITE_TAC[fin_zp] THEN MAP_EVERY EXISTS_TAC [`&p pow f`; `m:num`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [SIMP_TAC[INTEGER_CLOSED]; ALL_TAC] THEN
  SUBGOAL_THEN `~(m = 0)` ASSUME_TAC THENL
   [ASM_MESON_TAC[MULT_CLAUSES]; ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (is_eq o concl) o
    check (fun th -> rand(concl th) = `n:num`)) THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_MUL; GSYM REAL_OF_NUM_POW; REAL_POW_ADD] THEN
  MP_TAC(SPECL [`p:num`; `e:num`] FIN_PPOW_NZ) THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `~(m = 0)` THEN REWRITE_TAC[GSYM REAL_OF_NUM_EQ] THEN
  CONV_TAC REAL_FIELD);;

let FIN_BDRY_NUM_VAL = prove
 (`forall p n H. prime p /\ 1 <= n /\ n <= H
           ==> fin_vge p (--(&(fin_flog p H))) (inv(&n))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC FIN_BDRY_INV_INDEX THEN
  ASM_REWRITE_TAC[ARITH_RULE `~(n = 0) <=> 1 <= n`] THEN
  MATCH_MP_TAC FIN_BDRY_FLOG_GE THEN ASM_SIMP_TAC[PRIME_GE_2] THEN
  TRANS_TAC LE_TRANS `n:num` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC DIVIDES_LE_IMP THEN
  ASM_REWRITE_TAC[EXP_INDEX_DIVIDES] THEN ASM_ARITH_TAC);;

let FIN_BDRY_DIV2_LEMMA = prove
 (`forall l q. ~(q = 0) ==> (2 * l) DIV q <= 2 * (l DIV q) + 1`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[ARITH_RULE `a <= b + 1 <=> a < b + 2`] THEN
  ASM_SIMP_TAC[RDIV_LT_EQ] THEN
  MP_TAC(SPECL [`l:num`; `q:num`] DIVISION) THEN ASM_REWRITE_TAC[] THEN
  SPEC_TAC(`l DIV q`,`d:num`) THEN SPEC_TAC(`l MOD q`,`r:num`) THEN
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [th])
    ASSUME_TAC) THEN
  REWRITE_TAC[LEFT_ADD_DISTRIB; MULT_CLAUSES] THEN
  REWRITE_TAC[ARITH_RULE `2 * (d * q + r) = (q * 2 * d) + 2 * r`] THEN
  ASM_ARITH_TAC);;

let FIN_BDRY_INDEX_BINOM = prove
 (`forall p l. prime p ==> index p (binom(2 * l,l)) <= fin_flog p (2 * l)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `2 <= p` ASSUME_TAC THENL [ASM_SIMP_TAC[PRIME_GE_2]; ALL_TAC] THEN
  MP_TAC(SPECL [`l:num`; `l:num`] BINOM_FACT) THEN
  REWRITE_TAC[GSYM MULT_2] THEN
  DISCH_THEN(MP_TAC o AP_TERM `index p`) THEN
  ASM_SIMP_TAC[INDEX_MUL; FACT_NZ; MULT_EQ_0; BINOM_EQ_0;
               ARITH_RULE `~(2 * l < l)`] THEN
  ASM_SIMP_TAC[INDEX_FACT_ALT] THEN
  REWRITE_TAC[fin_flog] THEN
  SUBGOAL_THEN
   `nsum {j | 1 <= j /\ p EXP j <= l} (\j. l DIV p EXP j) =
    nsum {j | 1 <= j /\ p EXP j <= 2 * l} (\j. l DIV p EXP j)`
  SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC NSUM_SUPERSET THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN CONJ_TAC THENL
     [ARITH_TAC;
      X_GEN_TAC `j:num` THEN STRIP_TAC THEN
      SUBGOAL_THEN `~(p EXP j = 0)` ASSUME_TAC THENL
       [REWRITE_TAC[EXP_EQ_0] THEN ASM_ARITH_TAC; ALL_TAC] THEN
      ASM_SIMP_TAC[DIV_EQ_0] THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `S = {j | 1 <= j /\ p EXP j <= 2 * l}` THEN
  SUBGOAL_THEN `FINITE (S:num->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "S" THEN ASM_SIMP_TAC[FINITE_EXP_LE]; ALL_TAC] THEN
  MATCH_MP_TAC(ARITH_RULE `b <= 2 * a + c ==> a + a + i = b ==> i <= c`) THEN
  TRANS_TAC LE_TRANS `nsum S (\j. 2 * (l DIV p EXP j) + 1)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC NSUM_LE THEN ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    REWRITE_TAC[] THEN MATCH_MP_TAC FIN_BDRY_DIV2_LEMMA THEN
    REWRITE_TAC[EXP_EQ_0] THEN ASM_ARITH_TAC;
    ASM_SIMP_TAC[NSUM_ADD; NSUM_LMUL; NSUM_CONST; MULT_CLAUSES; LE_REFL]]);;

let FIN_BDRY_BINOM_VAL = prove
 (`forall p l H. prime p /\ 2 * l <= H
           ==> fin_vge p (--(&(fin_flog p H))) (inv(&(binom(2 * l,l))))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC FIN_BDRY_INV_INDEX THEN
  ASM_REWRITE_TAC[BINOM_EQ_0; ARITH_RULE `~(2 * l < l)`] THEN
  TRANS_TAC LE_TRANS `fin_flog p (2 * l)` THEN
  ASM_SIMP_TAC[FIN_BDRY_INDEX_BINOM; FIN_BDRY_FLOG_MONO]);;
