(* ========================================================================= *)
(* Series algebra for the moment arrays M(i,j), Z(i,j) (prefix rat_b).       *)
(* ========================================================================= *)

needs "src/catalan_defs.ml";;

(* ------------------------------------------------------------------------- *)
(* Central binomial coefficients c_l and the moments m_k.                    *)
(* ------------------------------------------------------------------------- *)

let RAT_B_C_POS = prove
 (`forall l. &0 < cat_c l`,
  GEN_TAC THEN REWRITE_TAC[cat_c] THEN MATCH_MP_TAC REAL_LT_DIV THEN
  SIMP_TAC[REAL_LT_POW2; REAL_POW_LT; REAL_OF_NUM_LT; ARITH; LT_NZ; BINOM_EQ_0] THEN
  ARITH_TAC);;

let RAT_B_BINOM_STEP = prove
 (`forall l. (l + 1) * binom(2 * l + 2,l + 1) = 2 * (2 * l + 1) * binom(2 * l,l)`,
  GEN_TAC THEN
  MP_TAC(SPECL [`l:num`; `l:num`] BINOM_FACT) THEN
  MP_TAC(SPECL [`l + 1`; `l + 1`] BINOM_FACT) THEN
  REWRITE_TAC[ARITH_RULE `(l + 1) + (l + 1) = SUC(SUC(l + l))`;
              ARITH_RULE `2 * l + 2 = SUC(SUC(l + l))`;
              ARITH_RULE `2 * l = l + l`; GSYM ADD1; FACT] THEN
  MP_TAC(SPEC `l:num` FACT_LT) THEN
  DISCH_TAC THEN DISCH_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC(MESON[EQ_MULT_LCANCEL]
    `forall k. ~(k = 0) /\ k * x = k * y ==> x = y`) THEN
  EXISTS_TAC `FACT l * FACT l * SUC l` THEN CONJ_TAC THENL
   [ASM_SIMP_TAC[MULT_EQ_0; NOT_SUC; ARITH_RULE `0 < f ==> ~(f = 0)`];
    REPEAT(FIRST_X_ASSUM(MP_TAC o check (is_eq o concl))) THEN
    CONV_TAC NUM_RING]);;

let RAT_B_C_STEP = prove
 (`forall l. &(2 * l + 2) * cat_c(l + 1) = &(2 * l + 1) * cat_c l`,
  GEN_TAC THEN REWRITE_TAC[cat_c] THEN
  MP_TAC(SPEC `l:num` RAT_B_BINOM_STEP) THEN
  REWRITE_TAC[ARITH_RULE `2 * (l + 1) = 2 * l + 2`] THEN
  DISCH_THEN(MP_TAC o AP_TERM `real_of_num`) THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_MUL; REAL_POW_ADD; REAL_POW_1] THEN
  REWRITE_TAC[ARITH_RULE `2 * l + 2 = 2 * (l + 1)`; GSYM REAL_OF_NUM_MUL] THEN
  MP_TAC(SPECL [`&4`; `l:num`] REAL_POW_LT) THEN REWRITE_TAC[REAL_OF_NUM_LT; ARITH] THEN
  SPEC_TAC(`&4 pow l`,`p:real`) THEN REPEAT STRIP_TAC THEN
  POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN CONV_TAC REAL_FIELD);;

let RAT_B_DIV2 = prove
 (`forall l. (2 * l) DIV 2 = l /\ (2 * l + 2) DIV 2 = l + 1`,
  GEN_TAC THEN REWRITE_TAC[ARITH_RULE `2 * l + 2 = 2 * (l + 1)`] THEN
  SIMP_TAC[DIV_MULT; ARITH_EQ]);;

let RAT_B_M_POS = prove
 (`forall k. &0 <= cat_m k`,
  GEN_TAC THEN REWRITE_TAC[cat_m] THEN COND_CASES_TAC THEN
  REWRITE_TAC[REAL_LE_REFL] THEN MATCH_MP_TAC REAL_LE_DIV THEN
  REWRITE_TAC[REAL_POS] THEN MATCH_MP_TAC REAL_LE_MUL THEN
  SIMP_TAC[REAL_POS; REAL_LT_IMP_LE; RAT_B_C_POS]);;


let RAT_B_M_0 = prove
 (`cat_m 0 = &2 /\ cat_m 1 = &0`,
  REWRITE_TAC[cat_m; cat_c] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[BINOM_REFL; real_pow] THEN CONV_TAC REAL_RAT_REDUCE_CONV);;

let RAT_B_M_STEP = prove
 (`forall k. &(k + 3) * cat_m(k + 2) = &(k + 2) * cat_m k`,
  GEN_TAC THEN REWRITE_TAC[cat_m; EVEN_ADD; ARITH] THEN
  COND_CASES_TAC THEN REWRITE_TAC[REAL_MUL_RZERO] THEN
  FIRST_X_ASSUM(CHOOSE_THEN SUBST1_TAC o REWRITE_RULE[EVEN_EXISTS]) THEN
  REWRITE_TAC[RAT_B_DIV2] THEN
  MP_TAC(SPEC `m:num` RAT_B_C_STEP) THEN
  MP_TAC(SPEC `m:num` RAT_B_C_POS) THEN MP_TAC(SPEC `m + 1` RAT_B_C_POS) THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_ADD; GSYM REAL_OF_NUM_MUL] THEN
  SPEC_TAC(`cat_c m`,`a:real`) THEN SPEC_TAC(`cat_c(m + 1)`,`b:real`) THEN
  MP_TAC(SPEC `m:num` REAL_POS) THEN
  SPEC_TAC(`&m`,`x:real`) THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `~(&2 * x + &1 = &0) /\ ~((&2 * x + &2) + &1 = &0)` MP_TAC THENL
  [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  CONV_TAC REAL_FIELD);;

let RAT_B_M_TELE = prove
 (`forall k. cat_m k - cat_m(k + 2) = cat_m(k + 2) / &(k + 2)`,
  GEN_TAC THEN MP_TAC(SPEC `k:num` RAT_B_M_STEP) THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN
  MP_TAC(SPEC `k:num` REAL_POS) THEN
  SPEC_TAC(`&k`,`x:real`) THEN GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `~(x + &2 = &0)` MP_TAC THENL
  [ASM_REAL_ARITH_TAC; CONV_TAC REAL_FIELD]);;

let RAT_B_M_BOUND = prove
 (`forall k. cat_m k pow 2 * &(k + 2) <= &8`,
  SUBGOAL_THEN `forall k. cat_m k pow 2 * &(k + 2) <= &8 /\
                    cat_m (k + 1) pow 2 * &((k + 1) + 2) <= &8`
   (fun th -> MESON_TAC[th]) THEN
  INDUCT_TAC THENL
   [CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[RAT_B_M_0] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV;
    ALL_TAC] THEN
  POP_ASSUM STRIP_ASSUME_TAC THEN ASM_REWRITE_TAC[ADD1] THEN
  REWRITE_TAC[ARITH_RULE `(k + 1) + 1 = k + 2`] THEN
  MP_TAC(SPEC `k:num` RAT_B_M_STEP) THEN
  UNDISCH_TAC `cat_m k pow 2 * &(k + 2) <= &8` THEN
  REWRITE_TAC[ARITH_RULE `(k + 2) + 2 = k + 4`] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN
  MP_TAC(SPEC `k:num` REAL_POS) THEN
  SPEC_TAC(`cat_m k`,`a:real`) THEN SPEC_TAC(`cat_m (k + 2)`,`b:real`) THEN
  SPEC_TAC(`&k`,`x:real`) THEN REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `&0 < (x + &3) pow 2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  FIRST_ASSUM(fun th -> ONCE_REWRITE_TAC[GSYM(MATCH_MP REAL_LE_LMUL_EQ th)]) THEN
  SUBGOAL_THEN `(x + &3) pow 2 * b pow 2 * (x + &4) =
                (a pow 2 * (x + &2)) * ((x + &2) * (x + &4))` SUBST1_TAC THENL
   [UNDISCH_TAC `(x + &3) * b = (x + &2) * a` THEN CONV_TAC REAL_RING;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(a pow 2 * (x + &2)) * (x + &3) pow 2` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN
      ASM_REAL_ARITH_TAC;
      REAL_ARITH_TAC];
    GEN_REWRITE_TAC RAND_CONV [REAL_MUL_SYM] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]]);;

let RAT_B_M_LIM = prove
 (`forall d. ((\u. cat_m(d + u)) ---> &0) sequentially`,
  REWRITE_TAC[REALLIM_SEQUENTIALLY; REAL_SUB_RZERO] THEN
  X_GEN_TAC `d:num` THEN X_GEN_TAC `r:real` THEN DISCH_TAC THEN
  MP_TAC(SPEC `&8 / (r:real) pow 2` REAL_ARCH_SIMPLE) THEN
  DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN EXISTS_TAC `N:num` THEN
  X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  MP_TAC(SPEC `d + n:num` RAT_B_M_BOUND) THEN
  MP_TAC(SPEC `d + n:num` RAT_B_M_POS) THEN
  REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `abs(cat_m(d + n)) < abs r` MP_TAC THENL
   [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
  REWRITE_TAC[REAL_LT_SQUARE_ABS] THEN
  SUBGOAL_THEN `&0 < r pow 2` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_POW_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `&8 <= &N * r pow 2` ASSUME_TAC THENL
   [ASM_MESON_TAC[REAL_LE_LDIV_EQ]; ALL_TAC] THEN
  SUBGOAL_THEN `&N * r pow 2 < &((d + n) + 2) * r pow 2` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_RMUL_EQ; REAL_OF_NUM_LT] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `cat_m(d + n) pow 2 * &((d + n) + 2) < r pow 2 * &((d + n) + 2)`
  MP_TAC THENL
   [ASM_REAL_ARITH_TAC;
    SIMP_TAC[REAL_LT_RMUL_EQ; REAL_OF_NUM_LT; ARITH_RULE `0 < (d + n) + 2`]]);;

(* ------------------------------------------------------------------------- *)
(* Generic series lemmas.                                                    *)
(* ------------------------------------------------------------------------- *)

let RAT_B_TELE = prove
 (`forall g d. (g ---> &0) sequentially
         ==> ((\u. g u - g(u + d + 1)) real_sums sum(0..d) g) (from 0)`,
  GEN_TAC THEN REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN DISCH_TAC THEN
  INDUCT_TAC THENL
   [REWRITE_TAC[SUM_SING_NUMSEG; ADD_CLAUSES] THEN
    ASM_SIMP_TAC[REAL_SERIES_DIFFS];
    ALL_TAC] THEN
  SUBGOAL_THEN `((\x. g(x + d + 1) - g((x + d + 1) + 1)) real_sums g(d + 1))
                (from 0)` MP_TAC THENL
   [MP_TAC(ISPECL [`d + 1:num`; `\n. (g:num->real) n - g(n + 1)`;
                   `(g:num->real)(d + 1)`; `0`] REAL_SUMS_REINDEX) THEN
    REWRITE_TAC[ADD_CLAUSES; BETA_THM] THEN DISCH_THEN SUBST1_TAC THEN
    MATCH_MP_TAC REAL_SERIES_DIFFS THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `((\u. g u - g (u + d + 1)) real_sums sum (0..d) g) (from 0)` THEN
  REWRITE_TAC[IMP_IMP] THEN DISCH_THEN(MP_TAC o MATCH_MP REAL_SERIES_ADD) THEN
  REWRITE_TAC[SUM_CLAUSES_NUMSEG; LE_0; ADD1] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN
  REWRITE_TAC[ARITH_RULE `(x + d + 1) + 1 = x + (d + 1) + 1`] THEN
  REAL_ARITH_TAC);;

let RAT_B_DIAG = prove
 (`forall f S. (forall i j. ((\u. f (i + u) (j + u)) real_sums S i j) (from 0))
         ==> forall i j. S i j = f i j + S (i + 1) (j + 1)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\u. (f:num->num->real) (i + u) (j + u)`;
                 `(S:num->num->real) i j`; `0`; `1`] REAL_SUMS_OFFSET) THEN
  ASM_REWRITE_TAC[ARITH] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[SUM_SING_NUMSEG; ADD_CLAUSES] THEN
  MP_TAC(ISPECL [`1`; `\u. (f:num->num->real) (i + u) (j + u)`;
                 `(S:num->num->real) i j - f i j`; `0`] REAL_SUMS_REINDEX) THEN
  REWRITE_TAC[ADD_CLAUSES] THEN DISCH_THEN(fun th -> REWRITE_TAC[GSYM th]) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`i + 1:num`; `j + 1:num`]) THEN
  REWRITE_TAC[ARITH_RULE `(i + 1) + u = i + u + 1`] THEN
  REWRITE_TAC[IMP_IMP] THEN DISCH_THEN(MP_TAC o MATCH_MP REAL_SERIES_UNIQUE) THEN
  REAL_ARITH_TAC);;

let RAT_B_DIAG_ITER = prove
 (`forall f S. (forall i j. S i j = f i j + S (i + 1) (j + 1))
         ==> forall i j k. S (i + k) (j + k) =
                     S i j - sum(1..k) (\t. f (i + t - 1) (j + t - 1))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN GEN_TAC THEN
  INDUCT_TAC THENL
   [REWRITE_TAC[ADD_CLAUSES; SUM_CLAUSES_NUMSEG; ARITH; REAL_SUB_RZERO];
    ALL_TAC] THEN
  REWRITE_TAC[SUM_CLAUSES_NUMSEG; ARITH_RULE `1 <= SUC k`] THEN
  FIRST_ASSUM(MP_TAC o SPECL [`i + k:num`; `j + k:num`]) THEN
  REWRITE_TAC[ARITH_RULE `i + SUC k - 1 = i + k`; ARITH_RULE `i + SUC k = (i + k) + 1`] THEN
  ASM_REAL_ARITH_TAC);;

let RAT_B_DIAG_EVAL = prove
 (`forall f S. (forall i j. S i j = f i j + S (i + 1) (j + 1))
         ==> forall i j. S i j =
                   if j <= i
                   then S (i - j) 0 - sum(1..j) (\k. f (i - j + k - 1) (k - 1))
                   else S 0 (j - i) - sum(1..i) (\k. f (k - 1) (j - i + k - 1))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(ASSUME_TAC o MATCH_MP RAT_B_DIAG_ITER) THEN
  REPEAT GEN_TAC THEN COND_CASES_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPECL [`i - j:num`; `0`; `j:num`]);
    SUBGOAL_THEN `i <= j:num` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`0`; `j - i:num`; `i:num`])] THEN
  ASM_SIMP_TAC[SUB_ADD; ADD_CLAUSES]);;

let RAT_B_SUM01 = prove
 (`forall g. sum(0..1) g = g 0 + g 1`,
  GEN_TAC THEN REWRITE_TAC[num_CONV `1`; SUM_CLAUSES_NUMSEG; LE_0] THEN
  REWRITE_TAC[]);;

let RAT_B_SHIFT = prove
 (`forall f l n. (f real_sums l) (from 0)
           ==> ((\u. f(u + n + 1)) real_sums (l - sum(0..n) f)) (from 0)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`f:num->real`; `l:real`; `0`; `n + 1:num`] REAL_SUMS_OFFSET) THEN
  ASM_REWRITE_TAC[ARITH_RULE `0 < n + 1`; ADD_SUB] THEN
  MP_TAC(ISPECL [`n + 1:num`; `f:num->real`; `l - sum(0..n) f`; `0`]
    REAL_SUMS_REINDEX) THEN
  REWRITE_TAC[ADD_CLAUSES] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]));;

let RAT_B_LIN = prove
 (`forall f g h a b l1 l2 l.
     (f real_sums l1) (from 0) /\ (g real_sums l2) (from 0) /\
     (h real_sums l) (from 0) /\ (forall u. a * f u - b * g u = h u)
     ==> a * l1 - b * l2 = l`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_SERIES_UNIQUE THEN
  MAP_EVERY EXISTS_TAC [`h:num->real`; `from 0`] THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_SUMS_EQ THEN
  EXISTS_TAC `\u. a * (f:num->real) u - b * (g:num->real) u` THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`\u. a * (f:num->real) u`; `a * l1:real`;
                 `\u. b * (g:num->real) u`; `b * l2:real`; `from 0`]
    REAL_SERIES_SUB) THEN
  ASM_SIMP_TAC[REAL_SERIES_LMUL]);;

(* ------------------------------------------------------------------------- *)
(* Boundary recurrences for M.                                               *)
(* ------------------------------------------------------------------------- *)

let RAT_B_KM_REC = prove
 (`forall M. (forall i j. ((\u. cat_m (i + u) / &(j + u + 1)) real_sums M i j) (from 0))
       ==> forall e. &(e + 2) * M (e + 2) 0 - &(e + 1) * M e 0 =
               cat_m e + cat_m (e + 1)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC RAT_B_LIN THEN
  MAP_EVERY EXISTS_TAC
   [`\u. cat_m ((e + 2) + u) / &(0 + u + 1)`;
    `\u. cat_m (e + u) / &(0 + u + 1)`;
    `\u. cat_m (e + u) - cat_m (e + (u + 1 + 1))`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`\u. cat_m(e + u)`; `1`] RAT_B_TELE) THEN
    REWRITE_TAC[RAT_B_M_LIM; RAT_B_SUM01; ADD_CLAUSES] THEN REWRITE_TAC[BETA_THM];
    ALL_TAC] THEN
  X_GEN_TAC `u:num` THEN REWRITE_TAC[ADD_CLAUSES] THEN
  REWRITE_TAC[ARITH_RULE `(e + 2) + u = (e + u) + 2`;
              ARITH_RULE `e + u + 1 + 1 = (e + u) + 2`] THEN
  MP_TAC(SPEC `e + u:num` RAT_B_M_STEP) THEN
  MP_TAC(SPEC `u:num` REAL_POS) THEN MP_TAC(SPEC `e:num` REAL_POS) THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN
  SPEC_TAC(`cat_m((e + u) + 2)`,`x:real`) THEN SPEC_TAC(`cat_m(e + u)`,`y:real`) THEN
  SPEC_TAC(`&u`,`b:real`) THEN SPEC_TAC(`&e`,`a:real`) THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN DISCH_TAC THEN
  MP_TAC(REAL_ARITH `&0 <= b ==> ~(b + &1 = &0)`) THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC REAL_FIELD);;

let RAT_B_KP_REC0 = prove
 (`forall M. (forall i j. ((\u. cat_m (i + u) / &(j + u + 1)) real_sums M i j) (from 0))
       ==> forall e. &(e + 1) * M 0 (e + 2) - &e * (M 0 e - &2 / &(e + 1)) = &2`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC RAT_B_LIN THEN
  MAP_EVERY EXISTS_TAC
   [`\u. cat_m (0 + u) / &((e + 2) + u + 1)`;
    `\u. (\u. cat_m (0 + u) / &(e + u + 1)) (u + 1 + 1)`;
    `\u. cat_m (0 + u) - cat_m (0 + (u + 1 + 1))`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MP_TAC(ISPECL [`\u. cat_m (0 + u) / &(e + u + 1)`;
                   `(M:num->num->real) 0 e`; `1`] RAT_B_SHIFT) THEN
    ASM_REWRITE_TAC[RAT_B_SUM01] THEN
    REWRITE_TAC[ADD_CLAUSES; RAT_B_M_0; real_div; REAL_MUL_LZERO; REAL_ADD_RID];
    MP_TAC(ISPECL [`\u. cat_m(0 + u)`; `1`] RAT_B_TELE) THEN
    REWRITE_TAC[RAT_B_M_LIM; RAT_B_SUM01] THEN
    REWRITE_TAC[ADD_CLAUSES; RAT_B_M_0; REAL_ADD_RID];
    ALL_TAC] THEN
  X_GEN_TAC `u:num` THEN REWRITE_TAC[ADD_CLAUSES] THEN
  REWRITE_TAC[ARITH_RULE `(e + 2) + u + 1 = (e + u) + 3`;
              ARITH_RULE `e + (u + 1 + 1) + 1 = (e + u) + 3`;
              ARITH_RULE `u + 1 + 1 = u + 2`] THEN
  MP_TAC(SPEC `u:num` RAT_B_M_STEP) THEN
  MP_TAC(SPEC `u:num` REAL_POS) THEN MP_TAC(SPEC `e:num` REAL_POS) THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN
  SPEC_TAC(`cat_m(u + 2)`,`x:real`) THEN SPEC_TAC(`cat_m u`,`y:real`) THEN
  SPEC_TAC(`&u`,`b:real`) THEN SPEC_TAC(`&e`,`a:real`) THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN DISCH_TAC THEN
  MP_TAC(REAL_ARITH `&0 <= a /\ &0 <= b ==> ~((a + b) + &3 = &0)`) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC REAL_FIELD);;

let RAT_B_K1 = prove
 (`forall M. (forall i j. ((\u. cat_m (i + u) / &(j + u + 1)) real_sums M i j) (from 0))
       ==> M 1 0 = &2`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_SERIES_UNIQUE THEN
  MAP_EVERY EXISTS_TAC
   [`\u. cat_m (0 + u) - cat_m (0 + (u + 1 + 1))`; `from 0`] THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`\u. cat_m (1 + u) / &(0 + u + 1)`;
                   `(M:num->num->real) 1 0`; `0`] RAT_B_SHIFT) THEN
    ASM_REWRITE_TAC[SUM_SING_NUMSEG] THEN
    REWRITE_TAC[ADD_CLAUSES; RAT_B_M_0; real_div; REAL_MUL_LZERO;
                REAL_SUB_RZERO] THEN
    REWRITE_TAC[ARITH_RULE `1 + u + 1 = u + 2`;
                ARITH_RULE `(u + 1) + 1 = u + 2`;
                ARITH_RULE `u + 1 + 1 = u + 2`] THEN
    REWRITE_TAC[GSYM real_div; GSYM RAT_B_M_TELE];
    MP_TAC(ISPECL [`\u. cat_m(0 + u)`; `1`] RAT_B_TELE) THEN
    REWRITE_TAC[RAT_B_M_LIM; RAT_B_SUM01] THEN
    REWRITE_TAC[ADD_CLAUSES; RAT_B_M_0; REAL_ADD_RID]]);;

let RAT_B_C0 = prove
 (`cat_c 0 = &1`,
  REWRITE_TAC[cat_c] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[BINOM_REFL; real_pow] THEN CONV_TAC REAL_RAT_REDUCE_CONV);;

let RAT_B_KPM01 = prove
 (`cat_kminus 0 = &0 /\ cat_kminus 1 = &2 /\
   cat_kplus 0 = &0 /\ cat_kplus 1 = &0`,
  REWRITE_TAC[cat_kminus; cat_kplus; ONE]);;

let RAT_B_KM_STEP = prove
 (`forall e. &(e + 2) * cat_kminus(e + 2) =
       &(e + 1) * cat_kminus e + cat_m e + cat_m(e + 1)`,
  GEN_TAC THEN REWRITE_TAC[ARITH_RULE `e + 2 = SUC(SUC e)`; cat_kminus] THEN
  SIMP_TAC[REAL_DIV_LMUL; REAL_OF_NUM_EQ; NOT_SUC]);;

let RAT_B_KP_STEP = prove
 (`forall e. &(e + 1) * cat_kplus(e + 2) = &e * cat_kplus e + &2 / &(e + 1)`,
  GEN_TAC THEN REWRITE_TAC[ARITH_RULE `e + 2 = SUC(SUC e)`; cat_kplus] THEN
  SIMP_TAC[REAL_DIV_LMUL; REAL_OF_NUM_EQ; ARITH_RULE `~(e + 1 = 0)`]);;

let RAT_B_CK_STEP = prove
 (`forall d. &(d + 2) * cat_ckern (d + 2) 0 = &(d + 1) * cat_ckern d 0`,
  GEN_TAC THEN REWRITE_TAC[cat_ckern; LE_0; SUB_0; EVEN_ADD; ARITH] THEN
  COND_CASES_TAC THEN REWRITE_TAC[REAL_MUL_RZERO] THEN
  FIRST_X_ASSUM(CHOOSE_THEN SUBST1_TAC o REWRITE_RULE[EVEN_EXISTS]) THEN
  REWRITE_TAC[RAT_B_DIV2; RAT_B_C_STEP]);;

let RAT_B_CK_STEP2 = prove
 (`forall e. &(e + 1) * cat_ckern (e + 1) 0 =
       &e * (if 0 < e then cat_ckern (e - 1) 0 else &0)`,
  INDUCT_TAC THENL
   [REWRITE_TAC[cat_ckern; ARITH; REAL_MUL_RZERO]; ALL_TAC] THEN
  REWRITE_TAC[ARITH_RULE `0 < SUC e`; ARITH_RULE `SUC e - 1 = e`;
              ARITH_RULE `SUC e + 1 = e + 2`; ADD1; RAT_B_CK_STEP]);;

let RAT_B_CK0 = prove
 (`forall d. cat_ckern 0 d = if d = 0 then &1 else &0`,
  GEN_TAC THEN REWRITE_TAC[cat_ckern; LE] THEN
  ASM_CASES_TAC `d = 0` THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[RAT_B_C0]);;

let RAT_B_KMINUS_EVAL = prove
 (`forall M G. (forall i j. ((\u. cat_m (i + u) / &(j + u + 1)) real_sums M i j) (from 0)) /\
         M 0 0 = &4 * G
         ==> forall d. M d 0 = cat_kminus d + &4 * G * cat_ckern d 0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP RAT_B_KM_REC) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP RAT_B_K1) THEN
  SUBGOAL_THEN
   `forall d. M d 0 = cat_kminus d + &4 * G * cat_ckern d 0 /\
        M (d + 1) 0 = cat_kminus (d + 1) + &4 * G * cat_ckern (d + 1) 0`
   (fun th -> MESON_TAC[th]) THEN
  INDUCT_TAC THENL
   [ASM_REWRITE_TAC[ADD_CLAUSES; RAT_B_KPM01; RAT_B_CK0] THEN
    REWRITE_TAC[cat_ckern; ARITH] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  POP_ASSUM STRIP_ASSUME_TAC THEN
  ASM_REWRITE_TAC[ADD1; ARITH_RULE `(d + 1) + 1 = d + 2`] THEN
  MATCH_MP_TAC REAL_EQ_LCANCEL_IMP THEN EXISTS_TAC `&(d + 2)` THEN
  CONJ_TAC THENL [REWRITE_TAC[REAL_OF_NUM_EQ] THEN ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPEC `d:num` RAT_B_CK_STEP) THEN
  MP_TAC(SPEC `d:num` RAT_B_KM_STEP) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `d:num` o
    check (fun th -> can (find_term ((=) `cat_m`)) (concl th) &&
                     is_forall (concl th) &&
                     not (can (find_term ((=) `real_sums`)) (concl th)))) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RING);;

let RAT_B_KPLUS_EVAL = prove
 (`forall M G kappa.
     (forall i j. ((\u. cat_m (i + u) / &(j + u + 1)) real_sums M i j) (from 0)) /\
     M 0 0 = &4 * G /\ M 0 1 = &3 / &2 * kappa
     ==> forall d. M 0 d = cat_kplus d + &4 * G * cat_ckern 0 d +
                     &3 / &2 * kappa *
                     (if 0 < d then cat_ckern (d - 1) 0 else &0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP RAT_B_KP_REC0) THEN
  SUBGOAL_THEN
   `forall d. M 0 d = cat_kplus d + &4 * G * cat_ckern 0 d +
                &3 / &2 * kappa * (if 0 < d then cat_ckern (d - 1) 0 else &0) /\
        M 0 (d + 1) = cat_kplus (d + 1) + &4 * G * cat_ckern 0 (d + 1) +
                &3 / &2 * kappa *
                (if 0 < d + 1 then cat_ckern ((d + 1) - 1) 0 else &0)`
   (fun th -> MESON_TAC[th]) THEN
  INDUCT_TAC THENL
   [ASM_REWRITE_TAC[ADD_CLAUSES; RAT_B_KPM01; RAT_B_CK0; ARITH] THEN
    REWRITE_TAC[cat_ckern; ARITH; RAT_B_C0] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  POP_ASSUM STRIP_ASSUME_TAC THEN
  ASM_REWRITE_TAC[ADD1; ARITH_RULE `(d + 1) + 1 = d + 2`] THEN
  REWRITE_TAC[ARITH_RULE `0 < d + 2`; ARITH_RULE `(d + 2) - 1 = d + 1`] THEN
  MATCH_MP_TAC REAL_EQ_LCANCEL_IMP THEN EXISTS_TAC `&(d + 1)` THEN
  CONJ_TAC THENL [REWRITE_TAC[REAL_OF_NUM_EQ] THEN ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPEC `d:num` RAT_B_CK_STEP2) THEN
  MP_TAC(SPEC `d:num` RAT_B_KP_STEP) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `d:num` o
    check (fun th -> can (find_term ((=) `&2 / &(e + 1)`)) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[RAT_B_CK0; ARITH_RULE `~(d + 2 = 0)`] THEN
  MP_TAC(SPEC `d:num` (prove(`forall d. &d * (if d = 0 then &1 else &0) = &0`,
    GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[REAL_MUL_LZERO; REAL_MUL_RZERO]))) THEN
  MP_TAC(SPEC `&d + &1` (prove(`forall z. ~(z = &0) ==> z * (&2 / z) = &2`,
    SIMP_TAC[REAL_DIV_LMUL]))) THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN
  ANTS_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  SPEC_TAC(`&2 / (&d + &1)`,`w:real`) THEN SPEC_TAC(`&3 / &2`,`q:real`) THEN
  SPEC_TAC(`if d = 0 then &1 else &0`,`t:real`) THEN
  REPEAT GEN_TAC THEN CONV_TAC REAL_RING);;

let RAT_MSERIES_EVAL = prove
 (`forall M:num->num->real G kappa.
   (forall i j. ((\u. cat_m (i + u) / &(j + u + 1)) real_sums M i j) (from 0)) /\
   M 0 0 = &4 * G /\ M 0 1 = &3 / &2 * kappa
   ==> forall i j. M i j = cat_M0 i j + &4 * G * cat_ckern i j +
                     &3 / &2 * kappa * (if i < j then cat_ckern (j - 1) i else &0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`M:num->num->real`; `G:real`] RAT_B_KMINUS_EVAL) THEN
  MP_TAC(ISPECL [`M:num->num->real`; `G:real`; `kappa:real`]
    RAT_B_KPLUS_EVAL) THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
  MP_TAC(ISPECL [`\a b. cat_m a / &(b + 1)`; `M:num->num->real`] RAT_B_DIAG) THEN
  ANTS_TAC THENL [REWRITE_TAC[GSYM ADD_ASSOC] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP RAT_B_DIAG_EVAL) THEN
  DISCH_THEN(fun th -> REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[th]) THEN
  REWRITE_TAC[cat_M0] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL
   [SUBGOAL_THEN
     `sum (1..j) (\k. cat_m (i - j + k - 1) / &(k - 1 + 1)) =
      sum (1..j) (\k. cat_m (i - j + k - 1) / &k)` SUBST1_TAC THENL
     [MATCH_MP_TAC SUM_EQ_NUMSEG THEN
      SIMP_TAC[ARITH_RULE `1 <= k ==> k - 1 + 1 = k`];
      ALL_TAC] THEN
    SUBGOAL_THEN `cat_ckern i j = cat_ckern (i - j) 0` SUBST1_TAC THENL
     [REWRITE_TAC[cat_ckern; LE_0; SUB_0] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `~(i < j:num)` (fun th -> REWRITE_TAC[th]) THENL
     [ASM_ARITH_TAC; REAL_ARITH_TAC];
    SUBGOAL_THEN
     `sum (1..i) (\k. cat_m (k - 1) / &((j - i + k - 1) + 1)) =
      sum (1..i) (\k. cat_m (k - 1) / &(j - i + k))` SUBST1_TAC THENL
     [MATCH_MP_TAC SUM_EQ_NUMSEG THEN
      SIMP_TAC[ARITH_RULE `1 <= k ==> (j - i + k - 1) + 1 = j - i + k`];
      ALL_TAC] THEN
    SUBGOAL_THEN `cat_ckern (j - 1) i = cat_ckern (j - i - 1) 0` SUBST1_TAC THENL
     [REWRITE_TAC[cat_ckern; LE_0; SUB_0; ARITH_RULE `j - 1 - i = j - i - 1`] THEN
      ASM_SIMP_TAC[ARITH_RULE `~(j <= i) ==> i <= j - 1`];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[cat_ckern; RAT_B_CK0] THEN
    ASM_SIMP_TAC[ARITH_RULE `~(j <= i) ==> ~(j - i = 0) /\ 0 < j - i /\ i < j`] THEN
    REWRITE_TAC[GSYM cat_ckern] THEN REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The zeta array Z.                                                         *)
(* ------------------------------------------------------------------------- *)

let RAT_B_HARM_DIFF = prove
 (`forall i n. sum(0..n) (\k. &1 / &(i + k + 1)) =
         cat_harm 1 (i + n + 1) - cat_harm 1 i`,
  GEN_TAC THEN REWRITE_TAC[cat_harm; REAL_POW_1] THEN INDUCT_TAC THENL
   [REWRITE_TAC[SUM_SING_NUMSEG; ADD_CLAUSES; GSYM ADD1] THEN
    REWRITE_TAC[SUM_CLAUSES_NUMSEG; ARITH_RULE `1 <= SUC i`] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[SUM_CLAUSES_NUMSEG; LE_0] THEN
  REWRITE_TAC[ARITH_RULE `i + SUC n + 1 = SUC(i + n + 1)`] THEN
  REWRITE_TAC[SUM_CLAUSES_NUMSEG; ARITH_RULE `1 <= SUC n`] THEN
  REAL_ARITH_TAC);;

let RAT_B_DIVSYM = prove
 (`forall a b c d:real. (a - b) / (c - d) = (b - a) / (d - c)`,
  REPEAT GEN_TAC THEN
  SUBST1_TAC(GSYM(ISPECL [`a:real`; `b:real`] REAL_NEG_SUB)) THEN
  SUBST1_TAC(GSYM(ISPECL [`c:real`; `d:real`] REAL_NEG_SUB)) THEN
  REWRITE_TAC[real_div; REAL_INV_NEG; REAL_MUL_LNEG; REAL_MUL_RNEG;
              REAL_NEG_NEG]);;

let RAT_B_GLIM = prove
 (`forall i. ((\u. &1 / &(i + u + 1)) ---> &0) sequentially`,
  GEN_TAC THEN MP_TAC(SPEC `&(i + 1)` REALLIM_1_OVER_N_OFFSET) THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM; real_div; REAL_MUL_LID; REAL_OF_NUM_ADD] THEN
  GEN_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC);;

let RAT_B_Z_LT = prove
 (`forall Z. (forall i j. ((\u. &1 / (&(i + u + 1) * &(j + u + 1))) real_sums Z i j) (from 0))
       ==> forall i j. i < j ==> Z i j = (cat_harm 1 i - cat_harm 1 j) / (&i - &j)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `exists n. j = i + n + 1` (CHOOSE_THEN SUBST_ALL_TAC) THENL
   [EXISTS_TAC `j - i - 1` THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `(cat_harm 1 i - cat_harm 1 (i + n + 1)) / (&i - &(i + n + 1)) =
    inv(&(n + 1)) * (cat_harm 1 (i + n + 1) - cat_harm 1 i)`
  SUBST1_TAC THENL
   [ONCE_REWRITE_TAC[RAT_B_DIVSYM] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_ADD; REAL_ARITH `(i + n + &1) - i = n + &1`] THEN
    REWRITE_TAC[real_div; REAL_MUL_SYM];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_SERIES_UNIQUE THEN
  MAP_EVERY EXISTS_TAC
   [`\u. &1 / (&(i + u + 1) * &((i + n + 1) + u + 1))`; `from 0`] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`\u. &1 / &(i + u + 1)`; `n:num`] RAT_B_TELE) THEN
  REWRITE_TAC[RAT_B_GLIM; RAT_B_HARM_DIFF] THEN
  DISCH_THEN(MP_TAC o SPEC `inv(&(n + 1))` o MATCH_MP REAL_SERIES_LMUL) THEN
  DISCH_THEN(fun th -> MATCH_MP_TAC
    (MATCH_MP (REWRITE_RULE[IMP_CONJ_ALT] REAL_SUMS_EQ) th)) THEN
  X_GEN_TAC `u:num` THEN DISCH_THEN(K ALL_TAC) THEN REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN
  MP_TAC(SPEC `u:num` REAL_POS) THEN MP_TAC(SPEC `n:num` REAL_POS) THEN
  MP_TAC(SPEC `i:num` REAL_POS) THEN
  SPEC_TAC(`&u`,`c:real`) THEN SPEC_TAC(`&n`,`b:real`) THEN
  SPEC_TAC(`&i`,`a:real`) THEN REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `~((a:real) + c + &1 = &0) /\ ~((b:real) + &1 = &0) /\
                ~(((a + b + &1) + c + &1) = &0) /\
                ~(a + (c + b + &1) + &1 = &0)` MP_TAC THENL
   [ASM_REAL_ARITH_TAC; CONV_TAC REAL_FIELD]);;

let RAT_B_Z_SYM = prove
 (`forall Z. (forall i j. ((\u. &1 / (&(i + u + 1) * &(j + u + 1))) real_sums Z i j) (from 0))
       ==> forall i j. Z i j = Z j i`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_SERIES_UNIQUE THEN
  MAP_EVERY EXISTS_TAC
   [`\u. &1 / (&(i + u + 1) * &(j + u + 1))`; `from 0`] THEN
  ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  ASM_REWRITE_TAC[]);;

let RAT_ZSERIES_EVAL = prove
 (`forall Z:num->num->real.
   (forall i j. ((\u. &1 / (&(i + u + 1) * &(j + u + 1))) real_sums Z i j) (from 0))
   ==> forall i j. Z i j = cat_Z0 i j + (if i = j then Z 0 0 else &0)`,
  GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[cat_Z0] THEN COND_CASES_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
    MP_TAC(ISPECL [`\a b. &1 / (&(a + 1) * &(b + 1))`; `Z:num->num->real`]
      RAT_B_DIAG) THEN
    ANTS_TAC THENL [REWRITE_TAC[GSYM ADD_ASSOC] THEN ASM_REWRITE_TAC[];
                    ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPECL [`0`; `0`; `i:num`] o MATCH_MP RAT_B_DIAG_ITER) THEN
    REWRITE_TAC[ADD_CLAUSES] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[cat_harm] THEN
    MATCH_MP_TAC(REAL_ARITH `(a:real) = b ==> z - a = --b + z`) THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN
    SIMP_TAC[ARITH_RULE `1 <= k ==> k - 1 + 1 = k`; REAL_POW_2];
    ALL_TAC] THEN
  REWRITE_TAC[REAL_ADD_RID] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP RAT_B_Z_LT) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP RAT_B_Z_SYM) THEN
  ASM_CASES_TAC `i < j:num` THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `j < i:num` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ONCE_REWRITE_TAC[RAT_B_DIVSYM] THEN ASM_MESON_TAC[]);;
