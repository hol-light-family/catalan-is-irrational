(* ========================================================================= *)
(* zeta(2) cancellation (RAT_CANCEL): pure algebra on finite sums.           *)
(* Formal power series as coefficient functions num->real, Cauchy product.   *)
(* ========================================================================= *)

needs "src/catalan_defs.ml";;

let rat_a_conv = new_definition
 `rat_a_conv (a:num->real) (b:num->real) n = sum(0..n) (\k. a k * b(n - k))`;;

let rat_a_e = new_definition
 `rat_a_e k (n:num) = if n = k then &1 else &0`;;

let RAT_A_SUM_GUARD = prove
 (`forall f m n. m <= n ==> sum(0..n) (\k. if k <= m then f k else &0) = sum(0..m) f`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM SUM_RESTRICT_SET] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_NUMSEG] THEN ASM_ARITH_TAC);;

let RAT_A_CONV_SYM = prove
 (`forall a b. rat_a_conv a b = rat_a_conv b a`,
  REWRITE_TAC[FUN_EQ_THM; rat_a_conv] THEN REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [SUM_REFLECT] THEN
  REWRITE_TAC[LT; SUB_0] THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
  SUBGOAL_THEN `x - (x - i):num = i` SUBST1_TAC THENL
   [ASM_ARITH_TAC; REWRITE_TAC[REAL_MUL_AC]]);;

let RAT_A_SUM_FROM = prove
 (`forall f k n. k <= n
           ==> sum(0..n) (\m. if k <= m then f m else &0) =
               sum(0..n-k) (\i. f(i + k))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM SUM_RESTRICT_SET] THEN
  SUBGOAL_THEN `{m | m IN 0..n /\ k <= m} = k..n` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_NUMSEG] THEN ARITH_TAC;
    ASM_SIMP_TAC[SUM_OFFSET_0]]);;

let RAT_A_CONV_ASSOC = prove
 (`forall a b c. rat_a_conv a (rat_a_conv b c) = rat_a_conv (rat_a_conv a b) c`,
  REWRITE_TAC[FUN_EQ_THM; rat_a_conv] THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[GSYM SUM_RMUL] THEN
  TRANS_TAC EQ_TRANS
   `sum(0..x) (\m. sum(0..x) (\k. if k <= m then
       (a:num->real) k * b (m - k) * c (x - m) else &0))` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN REPEAT STRIP_TAC THEN
    ASM_SIMP_TAC[RAT_A_SUM_GUARD; REAL_MUL_ASSOC]] THEN
  GEN_REWRITE_TAC RAND_CONV [SUM_SWAP_NUMSEG] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[] THEN
  ASM_SIMP_TAC[RAT_A_SUM_FROM; ADD_SUB; GSYM SUM_LMUL] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
  REPEAT AP_TERM_TAC THEN ASM_ARITH_TAC);;

let RAT_A_CONV_SUB_L = prove
 (`forall a b c. rat_a_conv (\n. a n - b n) c =
           \n. rat_a_conv a c n - rat_a_conv b c n`,
  REWRITE_TAC[FUN_EQ_THM; rat_a_conv; REAL_SUB_RDISTRIB; SUM_SUB_NUMSEG]);;

let RAT_A_CONV_ADD_L = prove
 (`forall a b c. rat_a_conv (\n. a n + b n) c =
           \n. rat_a_conv a c n + rat_a_conv b c n`,
  REWRITE_TAC[FUN_EQ_THM; rat_a_conv; REAL_ADD_RDISTRIB; SUM_ADD_NUMSEG]);;

let RAT_A_CONV_CMUL_L = prove
 (`forall x a c. rat_a_conv (\n. x * a n) c = \n. x * rat_a_conv a c n`,
  REWRITE_TAC[FUN_EQ_THM; rat_a_conv; GSYM REAL_MUL_ASSOC; SUM_LMUL]);;

let RAT_A_CONV_SUB_R = prove
 (`forall a b c. rat_a_conv c (\n. a n - b n) =
           \n. rat_a_conv c a n - rat_a_conv c b n`,
  ONCE_REWRITE_TAC[RAT_A_CONV_SYM] THEN REWRITE_TAC[RAT_A_CONV_SUB_L]);;

let RAT_A_CONV_ADD_R = prove
 (`forall a b c. rat_a_conv c (\n. a n + b n) =
           \n. rat_a_conv c a n + rat_a_conv c b n`,
  ONCE_REWRITE_TAC[RAT_A_CONV_SYM] THEN REWRITE_TAC[RAT_A_CONV_ADD_L]);;

let RAT_A_CONV_CMUL_R = prove
 (`forall x a c. rat_a_conv c (\n. x * a n) = \n. x * rat_a_conv c a n`,
  ONCE_REWRITE_TAC[RAT_A_CONV_SYM] THEN REWRITE_TAC[RAT_A_CONV_CMUL_L]);;

let RAT_A_CONV_E = prove
 (`forall k b n. rat_a_conv (rat_a_e k) b n = if k <= n then b(n - k) else &0`,
  REPEAT GEN_TAC THEN REWRITE_TAC[rat_a_conv; rat_a_e] THEN
  TRANS_TAC EQ_TRANS `sum(0..n) (\j. if j = k then (b:num->real)(n - k) else &0)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_EQ_NUMSEG THEN REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[REAL_MUL_LID; REAL_MUL_LZERO];
    REWRITE_TAC[SUM_DELTA; IN_NUMSEG; LE_0]]);;

let RAT_A_CONV_E_R = prove
 (`forall k b n. rat_a_conv b (rat_a_e k) n = if k <= n then b(n - k) else &0`,
  ONCE_REWRITE_TAC[RAT_A_CONV_SYM] THEN REWRITE_TAC[RAT_A_CONV_E]);;

let RAT_A_CONV_E0 = prove
 (`forall b. rat_a_conv (rat_a_e 0) b = b /\ rat_a_conv b (rat_a_e 0) = b`,
  REWRITE_TAC[FUN_EQ_THM; RAT_A_CONV_E; RAT_A_CONV_E_R; LE_0; SUB_0]);;

let RAT_A_CONV_LOCAL = prove
 (`forall a x y n. (forall m. m <= n ==> x m = y m) ==> rat_a_conv a x n = rat_a_conv a y n`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[rat_a_conv] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
  AP_TERM_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The central binomial series F = 1/sqrt(1 - t^2).                          *)
(* ------------------------------------------------------------------------- *)

let RAT_A_BINOM_REC = prove
 (`forall l. SUC l * binom(SUC(SUC(l + l)),SUC l) = 2 * (2 * l + 1) * binom(l + l,l)`,
  GEN_TAC THEN
  MP_TAC(SPECL [`l:num`; `l:num`] BINOM_FACT) THEN
  MP_TAC(SPECL [`SUC l`; `SUC l`] BINOM_FACT) THEN
  REWRITE_TAC[ADD_CLAUSES; FACT] THEN
  DISCH_TAC THEN DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
  MATCH_MP_TAC(MESON[EQ_MULT_LCANCEL]
    `forall a b c. ~(c = 0) /\ c * a = c * b ==> a:num = b`) THEN
  EXISTS_TAC `SUC l * FACT l * FACT l` THEN
  REWRITE_TAC[MULT_EQ_0; FACT_NZ; NOT_SUC] THEN
  POP_ASSUM MP_TAC THEN CONV_TAC NUM_RING);;

let RAT_A_CATC_0 = prove
 (`cat_c 0 = &1`,
  REWRITE_TAC[cat_c; MULT_CLAUSES; binom; real_pow] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV);;

let RAT_A_CATC_REC = prove
 (`forall l. &(2 * l + 2) * cat_c(l + 1) = &(2 * l + 1) * cat_c l`,
  GEN_TAC THEN REWRITE_TAC[cat_c] THEN
  MP_TAC(SPEC `l:num` RAT_A_BINOM_REC) THEN
  REWRITE_TAC[ARITH_RULE `2 * (l + 1) = SUC(SUC(l + l)) /\ l + 1 = SUC l /\
                          2 * l = l + l`] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_EQ; GSYM REAL_OF_NUM_MUL; real_pow] THEN
  REWRITE_TAC[GSYM ADD1; GSYM REAL_OF_NUM_SUC; GSYM REAL_OF_NUM_ADD;
              GSYM REAL_OF_NUM_MUL] THEN
  MP_TAC(SPECL [`&4`; `l:num`] REAL_POW_LT) THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN
  SPEC_TAC(`&4 pow l`,`p:real`) THEN
  SPEC_TAC(`&(binom(SUC(SUC(l + l)),SUC l))`,`x:real`) THEN
  SPEC_TAC(`&(binom(l + l,l))`,`y:real`) THEN
  SPEC_TAC(`&l`,`z:real`) THEN CONV_TAC REAL_FIELD);;

let rat_a_F = new_definition
 `rat_a_F n = if EVEN n then cat_c (n DIV 2) else &0`;;

let RAT_A_F_01 = prove
 (`rat_a_F 0 = &1 /\ rat_a_F 1 = &0`,
  REWRITE_TAC[rat_a_F] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[RAT_A_CATC_0]);;

let RAT_A_F_REC = prove
 (`forall n. &(n + 2) * rat_a_F(n + 2) = &(n + 1) * rat_a_F n`,
  GEN_TAC THEN REWRITE_TAC[rat_a_F; EVEN_ADD; ARITH] THEN
  COND_CASES_TAC THEN REWRITE_TAC[REAL_MUL_RZERO] THEN
  FIRST_X_ASSUM(CHOOSE_THEN SUBST1_TAC o REWRITE_RULE[EVEN_EXISTS]) THEN
  REWRITE_TAC[ARITH_RULE `2 * m + 2 = 2 * (m + 1)`] THEN
  SIMP_TAC[DIV_MULT; ARITH_EQ] THEN
  REWRITE_TAC[ARITH_RULE `2 * (m + 1) = 2 * m + 2`; RAT_A_CATC_REC]);;
let RAT_A_SYM_WEIGHT = prove
 (`forall x m. (forall k. k <= m ==> x(m - k) = x k)
         ==> &2 * sum(0..m) (\k. &k * x k) = &m * sum(0..m) x`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `sum(0..m) (\k. &k * x k) = sum(0..m) (\k. (&m - &k) * x k)`
  MP_TAC THENL
   [GEN_REWRITE_TAC LAND_CONV [SUM_REFLECT] THEN
    REWRITE_TAC[LT; SUB_0] THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN
    REPEAT STRIP_TAC THEN ASM_SIMP_TAC[REAL_OF_NUM_SUB];
    REWRITE_TAC[REAL_SUB_RDISTRIB; SUM_SUB_NUMSEG; SUM_LMUL] THEN
    REAL_ARITH_TAC]);;

let RAT_A_FF_WEIGHT = prove
 (`forall m. &2 * sum(0..m) (\k. &k * (rat_a_F k * rat_a_F (m - k))) =
       &m * sum(0..m) (\k. rat_a_F k * rat_a_F (m - k))`,
  GEN_TAC THEN
  MP_TAC(ISPECL [`\k. rat_a_F k * rat_a_F (m - k)`; `m:num`]
    RAT_A_SYM_WEIGHT) THEN
  REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `m - (m - k):num = k` SUBST1_TAC THENL
   [ASM_ARITH_TAC; REWRITE_TAC[REAL_MUL_SYM]]);;

let RAT_A_H_REC = prove
 (`forall n. rat_a_conv rat_a_F rat_a_F (n + 2) = rat_a_conv rat_a_F rat_a_F n`,
  GEN_TAC THEN REWRITE_TAC[rat_a_conv] THEN
  MP_TAC(SPEC `n + 2` RAT_A_FF_WEIGHT) THEN
  MP_TAC(SPEC `n:num` RAT_A_FF_WEIGHT) THEN
  SUBGOAL_THEN
   `sum(0..n + 2) (\k. &k * (rat_a_F k * rat_a_F ((n + 2) - k))) =
    sum(0..n) (\k. &k * (rat_a_F k * rat_a_F (n - k))) +
    sum(0..n) (\k. rat_a_F k * rat_a_F (n - k))`
  SUBST1_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN REPEAT DISCH_TAC THEN
    MATCH_MP_TAC(REAL_FIELD `forall c x y. ~(c = &0) /\ c * x = c * y ==> x = y`) THEN
    EXISTS_TAC `&n + &2` THEN CONJ_TAC THENL
     [MP_TAC(SPEC `n:num` REAL_POS) THEN REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC]] THEN
  REWRITE_TAC[GSYM SUM_ADD_NUMSEG] THEN
  GEN_REWRITE_TAC LAND_CONV
    [MATCH_MP SUM_CLAUSES_LEFT (ARITH_RULE `0 <= n + 2`)] THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV)
    [MATCH_MP SUM_CLAUSES_LEFT (ARITH_RULE `0 + 1 <= n + 2`)] THEN
  SIMP_TAC[SUM_OFFSET_0; ARITH_RULE `(0 + 1) + 1 <= n + 2`] THEN
  REWRITE_TAC[ARITH_RULE `(n + 2) - ((0 + 1) + 1) = n /\ (0 + 1) + 1 = 2 /\
                          0 + 1 = 1`] THEN
  REWRITE_TAC[RAT_A_F_01; REAL_MUL_LZERO; REAL_MUL_RZERO; REAL_ADD_LID] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
  SUBGOAL_THEN `(n + 2) - (i + 2) = n - i` SUBST1_TAC THENL
   [ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[REAL_MUL_ASSOC; RAT_A_F_REC] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN REAL_ARITH_TAC);;

let RAT_A_FF = prove
 (`forall n. rat_a_conv rat_a_F rat_a_F n = if EVEN n then &1 else &0`,
  SUBGOAL_THEN `forall n. rat_a_conv rat_a_F rat_a_F n = (if EVEN n then &1 else &0) /\
                    rat_a_conv rat_a_F rat_a_F (n + 1) =
                    (if EVEN (n + 1) then &1 else &0)`
   (fun th -> REWRITE_TAC[th]) THEN
  INDUCT_TAC THENL
   [REWRITE_TAC[rat_a_conv; ARITH_RULE `0 + 1 = SUC 0`; SUM_CLAUSES_NUMSEG] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[RAT_A_F_01] THEN REAL_ARITH_TAC;
    ASM_REWRITE_TAC[ADD1; ARITH_RULE `(n + 1) + 1 = n + 2`; RAT_A_H_REC] THEN
    REWRITE_TAC[EVEN_ADD; ARITH]]);;

let RAT_A_FF_FUN = prove
 (`rat_a_conv rat_a_F rat_a_F = \n. if EVEN n then &1 else &0`,
  REWRITE_TAC[FUN_EQ_THM; RAT_A_FF]);;

let rat_a_omu = new_definition
 `rat_a_omu = \n. rat_a_e 0 n - rat_a_e 2 n`;;

let rat_a_s = new_definition
 `rat_a_s = rat_a_conv rat_a_omu rat_a_F`;;

let rat_a_g = new_definition
 `rat_a_g = \n. rat_a_e 0 n - rat_a_s n`;;

let RAT_A_OMU_EV = prove
 (`rat_a_conv rat_a_omu (\n. if EVEN n then &1 else &0) = rat_a_e 0`,
  REWRITE_TAC[rat_a_omu; RAT_A_CONV_SUB_L; ETA_AX] THEN
  REWRITE_TAC[FUN_EQ_THM; RAT_A_CONV_E] THEN
  X_GEN_TAC `n:num` THEN REWRITE_TAC[LE_0; SUB_0; rat_a_e] THEN
  ASM_CASES_TAC `2 <= n` THEN ASM_REWRITE_TAC[] THENL
   [FIRST_X_ASSUM(CHOOSE_THEN SUBST1_TAC o REWRITE_RULE[LE_EXISTS]) THEN
    REWRITE_TAC[ADD_SUB2; EVEN_ADD; ARITH] THEN
    REWRITE_TAC[ARITH_RULE `~(2 + d = 0)`] THEN REAL_ARITH_TAC;
    FIRST_X_ASSUM(DISJ_CASES_THEN SUBST1_TAC o MATCH_MP (ARITH_RULE
      `~(2 <= n) ==> n = 0 \/ n = 1`)) THEN
    CONV_TAC NUM_REDUCE_CONV THEN REAL_ARITH_TAC]);;

let RAT_A_SF = prove
 (`rat_a_conv rat_a_s rat_a_F = rat_a_e 0`,
  REWRITE_TAC[rat_a_s; GSYM RAT_A_CONV_ASSOC; RAT_A_FF_FUN; RAT_A_OMU_EV]);;

let RAT_A_SS = prove
 (`rat_a_conv rat_a_s rat_a_s = rat_a_omu`,
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [rat_a_s] THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [RAT_A_CONV_SYM] THEN
  REWRITE_TAC[RAT_A_CONV_ASSOC; RAT_A_SF; RAT_A_CONV_E0]);;

let RAT_A_GG = prove
 (`rat_a_conv rat_a_g rat_a_g = \n. &2 * rat_a_g n - rat_a_e 2 n`,
  REWRITE_TAC[rat_a_g; RAT_A_CONV_SUB_L; RAT_A_CONV_SUB_R; ETA_AX] THEN
  REWRITE_TAC[RAT_A_CONV_E0; RAT_A_SS; FUN_EQ_THM; rat_a_omu] THEN
  REAL_ARITH_TAC);;

let RAT_A_GF = prove
 (`rat_a_conv rat_a_g rat_a_F = \n. rat_a_F n - rat_a_e 0 n`,
  REWRITE_TAC[rat_a_g; RAT_A_CONV_SUB_L; ETA_AX] THEN
  REWRITE_TAC[RAT_A_CONV_E0; RAT_A_SF]);;

let RAT_A_G0 = prove
 (`rat_a_g 0 = &0`,
  REWRITE_TAC[rat_a_g; rat_a_s; rat_a_conv; SUM_SING_NUMSEG; rat_a_omu;
              rat_a_e; SUB_0; RAT_A_F_01] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Chebyshev rows reversed.                                                  *)
(* ------------------------------------------------------------------------- *)

let RAT_A_CHEB_T_REC = prove
 (`forall d k. cheb_T (d + 2) k =
         (if k = 0 then &0 else &2 * cheb_T (d + 1) (k - 1)) - cheb_T d k`,
  REWRITE_TAC[ARITH_RULE `d + 2 = SUC(SUC d) /\ d + 1 = SUC d`; cheb_T]);;

let RAT_A_CHEB_U_REC = prove
 (`forall d k. cheb_U (d + 2) k =
         (if k = 0 then &0 else &2 * cheb_U (d + 1) (k - 1)) - cheb_U d k`,
  REWRITE_TAC[ARITH_RULE `d + 2 = SUC(SUC d) /\ d + 1 = SUC d`; cheb_U]);;

let RAT_A_DEG_GEN = prove
 (`forall p:num->num->real.
     (forall k. 0 < k ==> p 0 k = &0) /\ (forall k. 1 < k ==> p 1 k = &0) /\
     (forall d k. p (d + 2) k =
            (if k = 0 then &0 else &2 * p (d + 1) (k - 1)) - p d k)
     ==> forall d k. d < k ==> p d k = &0`,
  GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `forall d. (forall k. d < k ==> (p:num->num->real) d k = &0) /\
                    (forall k. d + 1 < k ==> p (d + 1) k = &0)`
   (fun th -> MESON_TAC[th]) THEN
  INDUCT_TAC THENL
   [ASM_REWRITE_TAC[ARITH]; FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC)] THEN
  ASM_REWRITE_TAC[ADD1; ARITH_RULE `(d + 1) + 1 = d + 2`] THEN
  REPEAT STRIP_TAC THEN
  COND_CASES_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `x = &0 /\ y = &0 ==> &2 * x - y = &0`) THEN
  CONJ_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC);;

let RAT_A_CHEB_T_DEG = prove
 (`forall d k. d < k ==> cheb_T d k = &0`,
  MATCH_MP_TAC(ISPEC `cheb_T` RAT_A_DEG_GEN) THEN
  REWRITE_TAC[RAT_A_CHEB_T_REC] THEN
  REWRITE_TAC[ARITH_RULE `1 = SUC 0`; cheb_T] THEN
  SIMP_TAC[ARITH_RULE `0 < k ==> ~(k = 0)`;
           ARITH_RULE `SUC 0 < k ==> ~(k = SUC 0)`]);;

let RAT_A_CHEB_U_DEG = prove
 (`forall d k. d < k ==> cheb_U d k = &0`,
  MATCH_MP_TAC(ISPEC `cheb_U` RAT_A_DEG_GEN) THEN
  REWRITE_TAC[RAT_A_CHEB_U_REC] THEN
  REWRITE_TAC[ARITH_RULE `1 = SUC 0`; cheb_U] THEN
  SIMP_TAC[ARITH_RULE `0 < k ==> ~(k = 0)`;
           ARITH_RULE `SUC 0 < k ==> ~(k = SUC 0)`]);;

let rat_a_row = new_definition
 `rat_a_row (p:num->num->real) d k = if k <= d then p d (d - k) else &0`;;

let rat_a_b = new_definition
 `rat_a_b d k = if d = 0 then &0 else rat_a_row cheb_U (d - 1) k`;;

let RAT_A_ROW_REC = prove
 (`forall p:num->num->real.
     (forall d k. p (d + 2) k =
            (if k = 0 then &0 else &2 * p (d + 1) (k - 1)) - p d k) /\
     (forall d k. d < k ==> p d k = &0)
     ==> forall d. rat_a_row p (d + 2) =
             \k. &2 * rat_a_row p (d + 1) k -
                 rat_a_conv (rat_a_e 2) (rat_a_row p d) k`,
  GEN_TAC THEN STRIP_TAC THEN GEN_TAC THEN
  REWRITE_TAC[FUN_EQ_THM; RAT_A_CONV_E; rat_a_row] THEN
  X_GEN_TAC `k:num` THEN
  ASM_CASES_TAC `k <= d + 1` THENL
   [ASM_SIMP_TAC[ARITH_RULE `k <= d + 1 ==> k <= d + 2`] THEN
    ASM_SIMP_TAC[ARITH_RULE `k <= d + 1 ==> ~((d + 2) - k = 0)`;
                 ARITH_RULE `k <= d + 1 ==> ((d + 2) - k) - 1 = (d + 1) - k`] THEN
    ASM_CASES_TAC `2 <= k` THEN ASM_REWRITE_TAC[] THENL
     [ASM_SIMP_TAC[ARITH_RULE `k <= d + 1 /\ 2 <= k ==> k - 2 <= d`;
                   ARITH_RULE `k <= d + 1 /\ 2 <= k ==> d - (k - 2) = (d + 2) - k`];
      SUBGOAL_THEN `p (d:num) ((d + 2) - k) = &0` SUBST1_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC; REAL_ARITH_TAC]];
    ASM_CASES_TAC `k = d + 2` THENL
     [ASM_REWRITE_TAC[LE_REFL; SUB_REFL; ARITH_RULE `2 <= d + 2`;
                      ARITH_RULE `(d + 2) - 2 = d`] THEN
      REAL_ARITH_TAC;
      ASM_SIMP_TAC[ARITH_RULE `~(k <= d + 1) /\ ~(k = d + 2) ==> ~(k <= d + 2)`;
                   ARITH_RULE `~(k <= d + 1) /\ ~(k = d + 2) ==> ~(k - 2 <= d)`] THEN
      REAL_ARITH_TAC]]);;

let RAT_A_ROWT_REC = MATCH_MP RAT_A_ROW_REC
  (CONJ RAT_A_CHEB_T_REC RAT_A_CHEB_T_DEG);;

let RAT_A_ROWU_REC = MATCH_MP RAT_A_ROW_REC
  (CONJ RAT_A_CHEB_U_REC RAT_A_CHEB_U_DEG);;

let RAT_A_CHEB_01 = prove
 (`(forall k. cheb_T 0 k = if k = 0 then &1 else &0) /\
   (forall k. cheb_T 1 k = if k = 1 then &1 else &0) /\
   (forall k. cheb_U 0 k = if k = 0 then &1 else &0) /\
   (forall k. cheb_U 1 k = if k = 1 then &2 else &0)`,
  REWRITE_TAC[ARITH_RULE `1 = SUC 0`; cheb_T; cheb_U]);;

let RAT_A_ROW_01 = prove
 (`rat_a_row cheb_T 0 = rat_a_e 0 /\ rat_a_row cheb_T 1 = rat_a_e 0 /\
   rat_a_row cheb_U 0 = rat_a_e 0 /\
   rat_a_row cheb_U 1 = (\k. &2 * rat_a_e 0 k)`,
  REWRITE_TAC[FUN_EQ_THM; rat_a_row; rat_a_e; RAT_A_CHEB_01] THEN
  REPEAT CONJ_TAC THEN X_GEN_TAC `k:num` THEN
  ASM_CASES_TAC `k = 0` THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  ASM_CASES_TAC `k = 1` THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  ASM_SIMP_TAC[ARITH_RULE `~(k = 0) ==> ~(k <= 0)`;
               ARITH_RULE `~(k = 0) /\ ~(k = 1) ==> ~(k <= 1)`] THEN
  REAL_ARITH_TAC);;

let RAT_A_B_0 = prove
 (`rat_a_b 0 = \k. &0`,
  REWRITE_TAC[FUN_EQ_THM; rat_a_b]);;

let RAT_A_B_SUC = prove
 (`forall e. rat_a_b (SUC e) = rat_a_row cheb_U e`,
  REWRITE_TAC[FUN_EQ_THM; rat_a_b; NOT_SUC; SUC_SUB1]);;

let RAT_A_B_REC = prove
 (`forall d. rat_a_b (d + 2) =
       \k. &2 * rat_a_b (d + 1) k - rat_a_conv (rat_a_e 2) (rat_a_b d) k`,
  INDUCT_TAC THENL
   [REWRITE_TAC[ARITH_RULE `0 + 2 = SUC 1 /\ 0 + 1 = SUC 0`; RAT_A_B_SUC;
                RAT_A_B_0; RAT_A_ROW_01; RAT_A_CONV_E] THEN
    REWRITE_TAC[FUN_EQ_THM] THEN REAL_ARITH_TAC;
    REWRITE_TAC[ARITH_RULE `SUC d + 2 = SUC(d + 2) /\ SUC d + 1 = SUC(d + 1)`;
                RAT_A_B_SUC; RAT_A_ROWU_REC]]);;

let rat_a_E = new_definition
 `rat_a_E d = \n. rat_a_conv (rat_a_row cheb_T d) rat_a_F n - rat_a_b d n`;;

let RAT_A_E_REC = prove
 (`forall d. rat_a_E (d + 2) =
       \n. &2 * rat_a_E (d + 1) n - rat_a_conv (rat_a_e 2) (rat_a_E d) n`,
  GEN_TAC THEN
  REWRITE_TAC[rat_a_E; RAT_A_ROWT_REC; RAT_A_B_REC] THEN
  REWRITE_TAC[RAT_A_CONV_SUB_L; RAT_A_CONV_SUB_R; RAT_A_CONV_CMUL_L; ETA_AX] THEN
  REWRITE_TAC[GSYM RAT_A_CONV_ASSOC; FUN_EQ_THM] THEN REAL_ARITH_TAC);;

let RAT_A_E_STEP = prove
 (`forall d. rat_a_E (d + 1) = rat_a_conv rat_a_g (rat_a_E d)`,
  INDUCT_TAC THENL
   [REWRITE_TAC[ARITH_RULE `0 + 1 = 1`; rat_a_E; RAT_A_ROW_01; RAT_A_CONV_E0;
                RAT_A_B_0; ARITH_RULE `1 = SUC 0`; RAT_A_B_SUC] THEN
    REWRITE_TAC[REAL_SUB_RZERO; ETA_AX; RAT_A_GF; GSYM(ARITH_RULE `1 = SUC 0`)] THEN
    REWRITE_TAC[RAT_A_ROW_01; RAT_A_CONV_E0];
    REWRITE_TAC[ARITH_RULE `SUC d + 1 = d + 2 /\ SUC d = d + 1`] THEN
    ASM_REWRITE_TAC[RAT_A_E_REC] THEN
    REWRITE_TAC[RAT_A_CONV_ASSOC; RAT_A_GG; RAT_A_CONV_SUB_L;
                RAT_A_CONV_CMUL_L; ETA_AX]]);;

let RAT_A_E_ORD = prove
 (`forall d n. n < d ==> rat_a_E d n = &0`,
  INDUCT_TAC THENL [REWRITE_TAC[LT]; ALL_TAC] THEN
  REWRITE_TAC[ADD1; RAT_A_E_STEP; rat_a_conv] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUM_EQ_0_NUMSEG THEN
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  ASM_CASES_TAC `i = 0` THEN ASM_REWRITE_TAC[RAT_A_G0; REAL_MUL_LZERO] THEN
  SUBGOAL_THEN `rat_a_E d (n - i) = &0` SUBST1_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC; REAL_ARITH_TAC]);;

let RAT_A_CORE0 = prove
 (`forall d n. n < d ==> rat_a_conv (rat_a_row cheb_T d) rat_a_F n = rat_a_b d n`,
  REPEAT STRIP_TAC THEN MP_TAC(SPECL [`d:num`; `n:num`] RAT_A_E_ORD) THEN
  ASM_REWRITE_TAC[rat_a_E] THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Translation to the shared definitions.                                    *)
(* ------------------------------------------------------------------------- *)

let rat_a_bin = new_definition
 `rat_a_bin h v = (--(&1)) pow v * &(binom(h,v))`;;

let RAT_A_MULFAC_CONV = prove
 (`forall h c. cat_mulfac h c = rat_a_conv (rat_a_bin h) c`,
  REPEAT GEN_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `i:num` THEN
  REWRITE_TAC[cat_mulfac; rat_a_conv; rat_a_bin] THEN
  MP_TAC(BETA_RULE(ISPECL
    [`\v. (--(&1)) pow v * &(binom(h,v)) * (c:num->real)(i - v)`;
     `i:num`; `h + i:num`] RAT_A_SUM_GUARD)) THEN
  MP_TAC(BETA_RULE(ISPECL
    [`\v. if v <= i then (--(&1)) pow v * &(binom(h,v)) * (c:num->real)(i - v)
          else &0`; `h:num`; `h + i:num`] RAT_A_SUM_GUARD)) THEN
  REWRITE_TAC[ARITH_RULE `h <= h + i /\ i <= h + i:num`; REAL_MUL_ASSOC] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `v:num` THEN STRIP_TAC THEN
  REWRITE_TAC[] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[BINOM_LT; ARITH_RULE `~(v <= h) ==> h < v:num`] THEN
  REAL_ARITH_TAC);;

let RAT_A_LHS = prove
 (`forall N r j. j <= 65 * N
           ==> sum (0..65 * N) (\i. cat_pcoef N r i *
                   (if i < j then cat_ckern (j - 1) i else &0)) =
               rat_a_conv (rat_a_e 1) (rat_a_conv (cat_pcoef N r) rat_a_F) j`,
  REPEAT GEN_TAC THEN REWRITE_TAC[RAT_A_CONV_E] THEN
  STRUCT_CASES_TAC(SPEC `j:num` num_CASES) THENL
  [REWRITE_TAC[LT; REAL_MUL_RZERO; SUM_0; ARITH_RULE `~(1 <= 0:num)`];
   ALL_TAC] THEN
  REWRITE_TAC[ARITH_RULE `1 <= SUC n /\ SUC n - 1 = n`; LT_SUC_LE] THEN
  DISCH_TAC THEN REWRITE_TAC[rat_a_conv] THEN
  MP_TAC(BETA_RULE(ISPECL
    [`\k. cat_pcoef N r k * rat_a_F (n - k)`; `n:num`; `65 * N`]
    RAT_A_SUM_GUARD)) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN(SUBST1_TAC o SYM)] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  REWRITE_TAC[] THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[REAL_MUL_RZERO; cat_ckern; rat_a_F]);;

let rat_a_close tm =
  FIRST [REFL_TAC; (MATCH_MP_TAC(TAUT `false ==> p`) THEN ASM_ARITH_TAC);
         (AP_TERM_TAC THEN ASM_ARITH_TAC);
         (MATCH_MP_TAC tm THEN ASM_ARITH_TAC);
         (CONV_TAC SYM_CONV THEN MATCH_MP_TAC tm THEN ASM_ARITH_TAC)];;

let RAT_A_REVC_T = prove
 (`forall C d. d < C
         ==> rat_a_conv (rat_a_e 1) (cat_revc C (cheb_T d)) =
             rat_a_conv (rat_a_e (C - d)) (rat_a_row cheb_T d)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[FUN_EQ_THM; RAT_A_CONV_E] THEN
  X_GEN_TAC `n:num` THEN REWRITE_TAC[cat_revc; rat_a_row] THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
  rat_a_close RAT_A_CHEB_T_DEG);;

let RAT_A_REVC_U = prove
 (`forall C d. 1 <= d /\ d < C
         ==> cat_revc C (cheb_U (d - 1)) =
             rat_a_conv (rat_a_e (C - d)) (rat_a_b d)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[FUN_EQ_THM; RAT_A_CONV_E] THEN
  X_GEN_TAC `n:num` THEN REWRITE_TAC[cat_revc; rat_a_row; rat_a_b] THEN
  ASM_SIMP_TAC[ARITH_RULE `1 <= d ==> ~(d = 0:num)`] THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
  rat_a_close RAT_A_CHEB_U_DEG);;

let RAT_A_CORE = prove
 (`forall C d m. d < C /\ m < C
           ==> rat_a_conv (rat_a_conv (rat_a_e 1) (cat_revc C (cheb_T d)))
                          rat_a_F m =
               rat_a_conv (rat_a_e (C - d)) (rat_a_b d) m`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[RAT_A_REVC_T] THEN
  REWRITE_TAC[GSYM RAT_A_CONV_ASSOC; RAT_A_CONV_E] THEN
  COND_CASES_TAC THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC RAT_A_CORE0 THEN ASM_ARITH_TAC);;

let RAT_A_REARR = prove
 (`forall x y. rat_a_conv (rat_a_e 1) (rat_a_conv (rat_a_conv x y) rat_a_F) =
         rat_a_conv x (rat_a_conv (rat_a_conv (rat_a_e 1) y) rat_a_F)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM RAT_A_CONV_ASSOC] THEN
  REWRITE_TAC[RAT_A_CONV_ASSOC] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  MATCH_ACCEPT_TAC RAT_A_CONV_SYM);;

let RAT_A_ZERO_LOW = prove
 (`forall x y k j. j < k ==> rat_a_conv x (rat_a_conv (rat_a_e k) y) j = &0`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[rat_a_conv; RAT_A_CONV_E] THEN
  MATCH_MP_TAC SUM_EQ_0_NUMSEG THEN REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
  COND_CASES_TAC THEN REWRITE_TAC[REAL_MUL_RZERO] THEN ASM_ARITH_TAC);;

let RAT_A_PCOEF_FUN = prove
 (`forall N r. cat_pcoef N r =
         rat_a_conv (rat_a_bin (2 * N)) (cat_revc (63 * N) (cheb_T (cat_dist N r)))`,
  REWRITE_TAC[FUN_EQ_THM; cat_pcoef; RAT_A_MULFAC_CONV]);;

let RAT_CANCEL = prove
 (`forall N r j. 1 <= N /\ r < 48 * N /\ j < 59 * N
     ==> sum (0..65 * N) (\i. cat_pcoef N r i *
              (if i < j then cat_ckern (j - 1) i else &0)) = cat_dcoef N r j`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[RAT_A_LHS; ARITH_RULE `j < 59 * N ==> j <= 65 * N:num`] THEN
  REWRITE_TAC[cat_dcoef; RAT_A_PCOEF_FUN; RAT_A_MULFAC_CONV] THEN
  REWRITE_TAC[RAT_A_REARR] THEN
  ABBREV_TAC `d = cat_dist N r` THEN
  SUBGOAL_THEN `d < 63 * N:num` ASSUME_TAC THENL
   [EXPAND_TAC "d" THEN REWRITE_TAC[cat_dist] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `rat_a_conv (rat_a_bin (2 * N))
      (rat_a_conv (rat_a_conv (rat_a_e 1) (cat_revc (63 * N) (cheb_T d)))
                  rat_a_F) j =
    rat_a_conv (rat_a_bin (2 * N))
      (rat_a_conv (rat_a_e (63 * N - d)) (rat_a_b d)) j`
  SUBST1_TAC THENL
   [MATCH_MP_TAC RAT_A_CONV_LOCAL THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC RAT_A_CORE THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[cat_sgn] THEN
  ASM_CASES_TAC `r < 4 * N` THEN ASM_REWRITE_TAC[] THENL
   [SUBGOAL_THEN `j < 63 * N - d /\ 1 <= d` STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "d" THEN REWRITE_TAC[cat_dist] THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    ASM_SIMP_TAC[RAT_A_REVC_U; RAT_A_ZERO_LOW] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `r = 4 * N` THEN ASM_REWRITE_TAC[] THENL
   [REWRITE_TAC[REAL_MUL_LZERO] THEN
    SUBGOAL_THEN `d = 0:num` SUBST1_TAC THENL
     [EXPAND_TAC "d" THEN REWRITE_TAC[cat_dist] THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[rat_a_conv; RAT_A_B_0; REAL_MUL_RZERO; COND_ID; SUM_0];
    ALL_TAC] THEN
  SUBGOAL_THEN `1 <= d` ASSUME_TAC THENL
   [EXPAND_TAC "d" THEN REWRITE_TAC[cat_dist] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[RAT_A_REVC_U; REAL_MUL_LID]);;
