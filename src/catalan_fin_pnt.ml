(* ========================================================================= *)
(* Upper bound for sum_{p <= 65N} d(p/N) log p via the prime number theorem. *)
(*                                                                           *)
(* Route: theta(n) <= pi(n) log n <= (1+e) n + C (from PNT); Abel summation   *)
(* with the nonincreasing nonnegative weights d(k/N); and the lower Riemann  *)
(* sum bound sum_{k=1}^{65N} d(k/N) <= N * 8609/2 obtained by telescoping an *)
(* explicit antiderivative fin_pnt_F of d (d(y)(y-x) <= F(y) - F(x)).        *)
(* ========================================================================= *)

needs "src/catalan_defs.ml";;
needs "100/pnt.ml";;

let fin_dfun = new_definition
 `fin_dfun x =
    if x <= &25 then &96
    else if x <= &29 then &146 - &2 * x
    else if x <= &65 / &2 then &88
    else if x <= &69 / &2 then &153 - &2 * x
    else if x <= &40 then &222 - &4 * x
    else if x <= &58 then &182 - &3 * x
    else if x <= &59 then &124 - &2 * x
    else if x <= &65 then &65 - x
    else &0`;;

let fin_pnt_F = new_definition
 `fin_pnt_F x =
    if x <= &25 then &96 * x
    else if x <= &29 then &146 * x - x * x - &625
    else if x <= &65 / &2 then &88 * x + &216
    else if x <= &69 / &2 then &153 * x - x * x - &3361 / &4
    else if x <= &40 then &222 * x - &2 * x * x - &4061 / &2
    else if x <= &58 then &182 * x - &3 / &2 * x * x - &2461 / &2
    else if x <= &59 then &124 * x - x * x + &903 / &2
    else if x <= &65 then &65 * x - x * x / &2 + &2192
    else &8609 / &2`;;

let FIN_PNT_DFUN_MONO = prove
 (`forall x y. x <= y ==> fin_dfun y <= fin_dfun x`,
  REPEAT GEN_TAC THEN REWRITE_TAC[fin_dfun] THEN
  REPEAT COND_CASES_TAC THEN ASM_REAL_ARITH_TAC);;

let FIN_PNT_DFUN_POS = prove
 (`forall x. &0 <= fin_dfun x`,
  GEN_TAC THEN REWRITE_TAC[fin_dfun] THEN
  REPEAT COND_CASES_TAC THEN ASM_REAL_ARITH_TAC);;

let FIN_PNT_DFUN_LE = prove
 (`forall x. fin_dfun x <= &96`,
  GEN_TAC THEN REWRITE_TAC[fin_dfun] THEN
  REPEAT COND_CASES_TAC THEN ASM_REAL_ARITH_TAC);;

let FIN_PNT_PIECE_TAC b =
  GEN_TAC THEN STRIP_TAC THEN ASM_CASES_TAC (mk_eq(`t:real`,b)) THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC; ALL_TAC] THEN
  REWRITE_TAC[fin_dfun; fin_pnt_F] THEN
  REPEAT COND_CASES_TAC THEN ASM_REAL_ARITH_TAC;;

let fin_pnt_piece (b,c,d,f) =
  let bt = parse_term b and ct = parse_term c in
  let dt = parse_term d and ft = parse_term f in
  let form = subst [`t:real`,`x:real`] in
  let eqn = mk_imp(mk_conj(mk_binop `(<=):real->real->bool` bt `t:real`,
                           mk_binop `(<=):real->real->bool` `t:real` ct),
                   mk_conj(mk_eq(`fin_dfun t`,dt), mk_eq(`fin_pnt_F t`,ft))) in
  let lem = prove(mk_forall(`t:real`,eqn), FIN_PNT_PIECE_TAC bt) in
  let goal = mk_forall(`x:real`,mk_forall(`y:real`,
     mk_imp(list_mk_conj[mk_binop `(<=):real->real->bool` bt `x:real`;
                         `x:real <= y`;
                         mk_binop `(<=):real->real->bool` `y:real` ct],
            `fin_dfun y * (y - x) <= fin_pnt_F y - fin_pnt_F x`))) in
  ignore form;
  prove(goal,
    REPEAT STRIP_TAC THEN
    MP_TAC(SPEC `x:real` lem) THEN MP_TAC(SPEC `y:real` lem) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(CONJUNCTS_THEN SUBST1_TAC) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(CONJUNCTS_THEN SUBST1_TAC) THEN
    MP_TAC(SPEC `y - x:real` REAL_LE_SQUARE) THEN REAL_ARITH_TAC);;

let FIN_PNT_PIECES = map fin_pnt_piece
 ["&25","&29","&146 - &2 * t","&146 * t - t * t - &625";
  "&29","&65 / &2","&88","&88 * t + &216";
  "&65 / &2","&69 / &2","&153 - &2 * t","&153 * t - t * t - &3361 / &4";
  "&69 / &2","&40","&222 - &4 * t","&222 * t - &2 * t * t - &4061 / &2";
  "&40","&58","&182 - &3 * t","&182 * t - &3 / &2 * t * t - &2461 / &2";
  "&58","&59","&124 - &2 * t","&124 * t - t * t + &903 / &2";
  "&59","&65","&65 - t","&65 * t - t * t / &2 + &2192"];;

let FIN_PNT_PIECE_LAST = prove
 (`forall c x y. &65 <= x /\ x <= y /\ y <= c
         ==> fin_dfun y * (y - x) <= fin_pnt_F y - fin_pnt_F x`,
  SUBGOAL_THEN `forall t. &65 <= t ==> fin_dfun t = &0 /\ fin_pnt_F t = &8609 / &2`
  ASSUME_TAC THENL [FIN_PNT_PIECE_TAC `&65`; ALL_TAC] THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&65 <= y` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[] THEN REAL_ARITH_TAC);;

let FIN_PNT_PIECE_FIRST = prove
 (`forall x y. x <= y /\ y <= &25
         ==> fin_dfun y * (y - x) <= fin_pnt_F y - fin_pnt_F x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[fin_dfun; fin_pnt_F] THEN
  REPEAT COND_CASES_TAC THEN ASM_REAL_ARITH_TAC);;

let FIN_PNT_CHAIN = prove
 (`forall b c. (forall x y. x <= y /\ y <= b
                ==> fin_dfun y * (y - x) <= fin_pnt_F y - fin_pnt_F x) /\
         (forall x y. b <= x /\ x <= y /\ y <= c
                ==> fin_dfun y * (y - x) <= fin_pnt_F y - fin_pnt_F x)
         ==> (forall x y. x <= y /\ y <= c
                ==> fin_dfun y * (y - x) <= fin_pnt_F y - fin_pnt_F x)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `y <= b:real` THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_CASES_TAC `b <= x:real` THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`b:real`; `y:real`]) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`x:real`; `b:real`]) THEN
  MP_TAC(SPECL [`b:real`; `y:real`] FIN_PNT_DFUN_MONO) THEN
  ASM_REWRITE_TAC[REAL_LE_REFL] THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_TAC THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN DISCH_TAC THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN DISCH_TAC THEN
  SUBGOAL_THEN `fin_dfun y * (b - x) <= fin_dfun b * (b - x)` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

let FIN_PNT_KEY = prove
 (`forall x y. x <= y ==> fin_dfun y * (y - x) <= fin_pnt_F y - fin_pnt_F x`,
  let step th lem = MATCH_MP FIN_PNT_CHAIN (CONJ th lem) in
  let th8 = itlist (fun l th -> step th l) (rev FIN_PNT_PIECES) FIN_PNT_PIECE_FIRST in
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(MATCH_MP FIN_PNT_CHAIN
    (CONJ th8 (SPEC `y:real` FIN_PNT_PIECE_LAST))) THEN
  ASM_REWRITE_TAC[REAL_LE_REFL]);;

let FIN_PNT_LOWER_SUM = prove
 (`forall N. ~(N = 0)
       ==> sum(1..65 * N) (\k. fin_dfun(&k / &N)) <= &N * &8609 / &2`,
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 < &N` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `forall n. sum(1..n) (\k. fin_dfun(&k / &N)) <=
                    &N * (fin_pnt_F(&n / &N) - fin_pnt_F(&0))`
  ASSUME_TAC THENL
   [INDUCT_TAC THEN REWRITE_TAC[SUM_CLAUSES_NUMSEG; ARITH_RULE `1 <= SUC n`] THENL
     [CONV_TAC NUM_REDUCE_CONV THEN
      REWRITE_TAC[real_div; REAL_MUL_LZERO; REAL_SUB_REFL; REAL_MUL_RZERO;
                  REAL_LE_REFL];
      ALL_TAC] THEN
    MP_TAC(SPECL [`&n / &N`; `&(SUC n) / &N`] FIN_PNT_KEY) THEN
    ASM_SIMP_TAC[REAL_LE_DIV2_EQ; REAL_OF_NUM_LE; ARITH_RULE `n <= SUC n`] THEN
    SUBGOAL_THEN `&(SUC n) / &N - &n / &N = inv(&N)` SUBST1_TAC THENL
     [REWRITE_TAC[GSYM REAL_OF_NUM_SUC] THEN
      UNDISCH_TAC `&0 < &N` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `fin_dfun (&(SUC n) / &N) =
                  &N * (fin_dfun (&(SUC n) / &N) * inv(&N))` SUBST1_TAC THENL
     [UNDISCH_TAC `&0 < &N` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
    SUBGOAL_THEN `&N * (fin_dfun (&(SUC n) / &N) * inv(&N)) <=
                  &N * (fin_pnt_F (&(SUC n) / &N) - fin_pnt_F (&n / &N))`
    MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `65 * N`) THEN
  SUBGOAL_THEN `&(65 * N) / &N = &65` SUBST1_TAC THENL
   [REWRITE_TAC[GSYM REAL_OF_NUM_MUL] THEN
    UNDISCH_TAC `&0 < &N` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  REWRITE_TAC[fin_pnt_F] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN REAL_ARITH_TAC);;

let FIN_PNT_ABEL_EQ = prove
 (`forall g a m. sum(1..m) (\k. g k * a k) =
           sum(1..m) (\n. (g n - g(n + 1)) * sum(1..n) a) +
           g(m + 1) * sum(1..m) a`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN
  REWRITE_TAC[SUM_CLAUSES_NUMSEG; ARITH_RULE `1 <= SUC n`] THENL
   [CONV_TAC NUM_REDUCE_CONV THEN REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[ADD1] THEN REAL_ARITH_TAC);;

let FIN_PNT_ABEL_LE = prove
 (`forall g a b m. (forall n. g(n + 1) <= g n) /\ (forall n. &0 <= g n) /\
             (forall n. n <= m ==> sum(1..n) a <= sum(1..n) b)
             ==> sum(1..m) (\k. g k * a k) <= sum(1..m) (\k. g k * b k)`,
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC LAND_CONV
   [ISPECL [`g:num->real`; `a:num->real`; `m:num`] FIN_PNT_ABEL_EQ] THEN
  GEN_REWRITE_TAC RAND_CONV
   [ISPECL [`g:num->real`; `b:num->real`; `m:num`] FIN_PNT_ABEL_EQ] THEN
  MATCH_MP_TAC REAL_LE_ADD2 THEN CONJ_TAC THENL
   [MATCH_MP_TAC SUM_LE_NUMSEG THEN REPEAT STRIP_TAC THEN BETA_TAC THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_SUB_LE; LE_TRANS];
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[LE_REFL]]);;

let FIN_PNT_THETA_POS = prove
 (`forall m. &0 <= sum {p | prime p /\ p <= m} (\p. log(&p))`,
  GEN_TAC THEN MATCH_MP_TAC SUM_POS_LE THEN REWRITE_TAC[IN_ELIM_THM] THEN
  REPEAT STRIP_TAC THEN BETA_TAC THEN MATCH_MP_TAC LOG_POS THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP PRIME_GE_2) THEN
  REWRITE_TAC[REAL_OF_NUM_LE] THEN ARITH_TAC);;

let FIN_PNT_THETA_UB = prove
 (`forall e. &0 < e
       ==> exists C. &0 <= C /\
               forall n. sum {p | prime p /\ p <= n} (\p. log(&p)) <= (&1 + e) * &n + C`,
  REPEAT STRIP_TAC THEN MP_TAC PNT THEN REWRITE_TAC[REALLIM_SEQUENTIALLY] THEN
  DISCH_THEN(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_TAC `M:num`) THEN
  EXISTS_TAC `sum {p | prime p /\ p <= M + 2} (\p. log(&p))` THEN
  REWRITE_TAC[FIN_PNT_THETA_POS] THEN X_GEN_TAC `n:num` THEN
  ASM_CASES_TAC `M + 2 <= n` THENL
   [MATCH_MP_TAC(REAL_ARITH `x1 <= y1 /\ &0 <= z1:real ==> x1 <= y1 + z1`) THEN
    REWRITE_TAC[FIN_PNT_THETA_POS] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&2 <= &n` ASSUME_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_LE] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&0 < log(&n)` ASSUME_TAC THENL
     [MATCH_MP_TAC LOG_POS_LT THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ABBREV_TAC `c = &(CARD {p | prime p /\ p <= n})` THEN
    SUBGOAL_THEN `sum {p | prime p /\ p <= n} (\p. log(&p)) <= c * log(&n)`
    MP_TAC THENL
     [EXPAND_TAC "c" THEN MATCH_MP_TAC SUM_BOUND THEN
      REWRITE_TAC[FINITE_ATMOST; IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN BETA_TAC THEN
      MATCH_MP_TAC LOG_MONO_LE_IMP THEN
      ASM_REWRITE_TAC[REAL_OF_NUM_LE; REAL_OF_NUM_LT] THEN
      FIRST_ASSUM(MP_TAC o MATCH_MP PRIME_GE_2) THEN ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `c / (&n / log(&n)) = (c * log(&n)) / &n` SUBST1_TAC THENL
     [UNDISCH_TAC `&0 < log(&n)` THEN UNDISCH_TAC `&2 <= &n` THEN
      CONV_TAC REAL_FIELD; ALL_TAC] THEN
    SUBGOAL_THEN `&0 < &n` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP (REAL_ARITH
      `abs(x - &1) < e ==> x < &1 + e`)) THEN
    ASM_SIMP_TAC[REAL_LT_LDIV_EQ] THEN
    DISCH_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `c * log(&n)` THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
    MATCH_MP_TAC(REAL_ARITH `x1 <= z1 /\ &0 <= y1:real ==> x1 <= y1 + z1`) THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SUM_SUBSET_SIMPLE THEN
      REWRITE_TAC[FINITE_ATMOST; SUBSET; IN_DIFF; IN_ELIM_THM] THEN
      CONJ_TAC THENL
       [REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
      REPEAT STRIP_TAC THEN BETA_TAC THEN MATCH_MP_TAC LOG_POS THEN
      FIRST_ASSUM(MP_TAC o MATCH_MP PRIME_GE_2) THEN
      REWRITE_TAC[REAL_OF_NUM_LE] THEN ARITH_TAC;
      MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
      ASM_REAL_ARITH_TAC]]);;

let FIN_PNT_PRIMESUM = prove
 (`forall f m. sum {p | prime p /\ p <= m} f =
         sum(1..m) (\k. if prime k then f k else &0)`,
  REWRITE_TAC[PRIME_ATMOST_ALT; SUM_RESTRICT_SET]);;

let FIN_PNT_SUM_DELTA1 = prove
 (`forall f c m. 1 <= m
           ==> sum(1..m) (\k. f k * (if k = 1 then c else &0)) = f 1 * c`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[SUM_CLAUSES_LEFT] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC(REAL_ARITH `y = &0 ==> x + y = x:real`) THEN
  MATCH_MP_TAC SUM_EQ_0_NUMSEG THEN REPEAT STRIP_TAC THEN BETA_TAC THEN
  COND_CASES_TAC THEN REWRITE_TAC[REAL_MUL_RZERO] THEN ASM_ARITH_TAC);;

let FIN_PNT_DSUM = prove
 (`forall e. &0 < e
       ==> exists N0. forall N. N0 <= N
                ==> sum {p | prime p /\ p <= 65 * N} (\p. fin_dfun(&p / &N) * log(&p))
                    <= (&8609 / &2 + e) * &N`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `e / &8609` FIN_PNT_THETA_UB) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `C:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(SPEC `(&192 * C) / e` REAL_ARCH_SIMPLE) THEN
  DISCH_THEN(X_CHOOSE_TAC `K:num`) THEN
  EXISTS_TAC `K + 1` THEN X_GEN_TAC `N:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 < &N` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[FIN_PNT_PRIMESUM] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum(1..65 * N) (\k. fin_dfun(&k / &N) *
                 ((&1 + e / &8609) + (if k = 1 then C else &0)))` THEN
  CONJ_TAC THENL
   [SUBGOAL_THEN
     `(\k. if prime k then fin_dfun(&k / &N) * log(&k) else &0) =
      (\k. fin_dfun(&k / &N) * (if prime k then log(&k) else &0))`
    SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN COND_CASES_TAC THEN
      REWRITE_TAC[REAL_MUL_RZERO];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`\k. fin_dfun(&k / &N)`;
                   `\k. if prime k then log(&k) else &0`;
                   `\k. (&1 + e / &8609) + (if k = 1 then C else &0)`;
                   `65 * N`] FIN_PNT_ABEL_LE) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    REWRITE_TAC[FIN_PNT_DFUN_POS] THEN CONJ_TAC THENL
     [GEN_TAC THEN MATCH_MP_TAC FIN_PNT_DFUN_MONO THEN
      ASM_SIMP_TAC[REAL_LE_DIV2_EQ; REAL_OF_NUM_LE] THEN ARITH_TAC;
      ALL_TAC] THEN
    X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    ASM_CASES_TAC `n = 0` THENL
     [ASM_REWRITE_TAC[SUM_CLAUSES_NUMSEG] THEN CONV_TAC NUM_REDUCE_CONV THEN
      REWRITE_TAC[REAL_LE_REFL];
      ALL_TAC] THEN
    REWRITE_TAC[GSYM FIN_PNT_PRIMESUM] THEN
    REWRITE_TAC[SUM_ADD_NUMSEG; SUM_CONST_NUMSEG; SUM_DELTA; IN_NUMSEG] THEN
    ASM_SIMP_TAC[ADD_SUB; LE_REFL; ARITH_RULE `~(n = 0) ==> 1 <= n`] THEN
    FIRST_X_ASSUM(fun th -> MATCH_MP_TAC(MATCH_MP
     (REAL_ARITH `forall x y z:real. x <= y ==> y <= z ==> x <= z`)
     (SPEC `n:num` th))) THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[REAL_ADD_LDISTRIB; SUM_ADD_NUMSEG; SUM_RMUL] THEN
  SUBGOAL_THEN `1 <= 65 * N` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[FIN_PNT_SUM_DELTA1] THEN BETA_TAC THEN
  MP_TAC(SPEC `N:num` FIN_PNT_LOWER_SUM) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `S = sum (1..65 * N) (\k. fin_dfun (&k / &N))` THEN DISCH_TAC THEN
  SUBGOAL_THEN `S * (&1 + e / &8609) <= (&N * &8609 / &2) * (&1 + e / &8609)`
  MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_ADD THEN REWRITE_TAC[REAL_POS] THEN
    MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `fin_dfun(&1 / &N) * C <= &96 * C` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[FIN_PNT_DFUN_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `&192 * C <= &K * e` MP_TAC THENL
   [ASM_SIMP_TAC[GSYM REAL_LE_LDIV_EQ]; ALL_TAC] THEN
  SUBGOAL_THEN `&K * e <= &N * e` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_OF_NUM_LE] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  REAL_ARITH_TAC);;
