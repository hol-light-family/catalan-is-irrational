(* ========================================================================= *)
(* EN part: one-variable endpoint weakening, unnormalised identity (80),    *)
(* and the finite-n uniform bound.                                           *)
(* ========================================================================= *)

needs "src/catalan_rp_en_part.ml";;
needs "src/catalan_rp_en_x.ml";;

(* constants of the final bound *)
let rp_en_Dc = new_definition
 `rp_en_Dc kappa (p:num->real) (v:num->real) =
    &2 * kappa + &12 + &2 * kappa * real_infsum (from 1) (\k. abs(p k)) +
    &4 * real_infsum (from 1) (\k. abs(v k))`;;

let rp_en_Cf = new_definition
 `rp_en_Cf kappa e lam (p:num->real) (v:num->real) Bx Bs =
    (kappa + &2) / &2 * log(&2) +
    kappa * (log(&2) - &2 * log(&1 - (&1 - e) pow 2)) / &2 +
    (log(&2) - log e) / &2 + (log(&2) - &2 * log e) + lam +
    &6 * (lam / &6 + &2 * kappa * real_infsum (from 1) (\k. abs(p k)) +
          real_infsum (from 1) (\k. abs(v k)) - Bx) +
    &12 * (&2 * real_infsum (from 1) (\k. abs(v k)) - Bs)`;;

(* ------------------------------------------------------------------------- *)
(* Endpoint weakening (convex combination with the residual bound).          *)
(* ------------------------------------------------------------------------- *)

let RP_EN_X_RESIDUAL = prove
 (`forall kappa lam p v x.
     &0 <= kappa /\ &0 <= lam /\ rp_summable p /\ rp_summable v /\
     --(&1) < x /\ x < &1 /\ ~(x = &0)
     ==> rp_X kappa lam p v x - &1 / &12 * log(&1 - x) <=
         lam / &6 + &2 * kappa * real_infsum (from 1) (\k. abs(p k)) +
         real_infsum (from 1) (\k. abs(v k))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `abs x <= &1` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`p:num->real`; `x:real`] RP_EN_TSER_BOUND) THEN
  MP_TAC(SPECL [`v:num->real`; `x:real`] RP_EN_SSER_BOUND) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `log(abs x) <= &0` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `abs x - &1` THEN CONJ_TAC THENL
     [MATCH_MP_TAC RP_EN_DMP_LOG_LE_SUB1 THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= (kappa / &2 + &17 / &48) * log(&1 + x pow 2)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; MATCH_MP_TAC LOG_POS THEN
      MP_TAC(SPEC `x:real` REAL_LE_POW_2) THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= lam * (&2 * x pow 2 / (&1 + x pow 2))` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
    MATCH_MP_TAC REAL_LE_DIV THEN REWRITE_TAC[REAL_LE_POW_2] THEN
    MP_TAC(SPEC `x:real` REAL_LE_POW_2) THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `kappa * --(real_infsum (from 1) (\k. abs(p k))) <= kappa * rp_Tser p x`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[rp_X] THEN ASM_REAL_ARITH_TAC);;

let RP_EN_X_WEAKEN = prove
 (`forall kappa lam p v x Bx m.
     &0 <= kappa /\ &0 <= lam /\ rp_summable p /\ rp_summable v /\
     --(&1) < x /\ x < &1 /\ ~(x = &0) /\ rp_X kappa lam p v x <= Bx /\ &6 <= m
     ==> m * rp_X kappa lam p v x - &1 / &2 * log(&1 - x) <=
         m * Bx +
         &6 * ((lam / &6 + &2 * kappa * real_infsum (from 1) (\k. abs(p k)) +
                real_infsum (from 1) (\k. abs(v k))) - Bx)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`kappa:real`; `lam:real`; `p:num->real`; `v:num->real`; `x:real`]
         RP_EN_X_RESIDUAL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 <= (m - &6) * (Bx - rp_X kappa lam p v x)` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  POP_ASSUM MP_TAC THEN REAL_ARITH_TAC);;

let RP_EN_Y_RESIDUAL = prove
 (`forall v s. rp_summable v /\ &0 < s /\ s < &1
         ==> rp_Y v s - &1 / &12 * log(&1 - s) <=
             &2 * real_infsum (from 1) (\k. abs(v k))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`v:num->real`; `s:real`] RP_EN_TSER_BOUND) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  SUBGOAL_THEN `log s <= &0` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `s - &1` THEN CONJ_TAC THENL
     [MATCH_MP_TAC RP_EN_DMP_LOG_LE_SUB1 THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[rp_Y] THEN ASM_REAL_ARITH_TAC);;

let RP_EN_Y_WEAKEN = prove
 (`forall v s Bs m.
     rp_summable v /\ &0 < s /\ s < &1 /\ rp_Y v s <= Bs /\ &12 <= m
     ==> m * rp_Y v s - log(&1 - s) <=
         m * Bs + &12 * (&2 * real_infsum (from 1) (\k. abs(v k)) - Bs)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`v:num->real`; `s:real`] RP_EN_Y_RESIDUAL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 <= (m - &12) * (Bs - rp_Y v s)` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  POP_ASSUM MP_TAC THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* n^2 times the exact identity, with all sums split into atoms.            *)
(* ------------------------------------------------------------------------- *)

let RP_EN_F_UNNORM = prove
 (`forall kappa N (x:num->real) (s:num->real).
     1 <= N
     ==> &(48 * N) pow 2 * rp_en_F kappa N x s =
         (&(48 * N) * &(63 * N) + &(48 * N) pow 2 * (kappa - &2) / &2 -
          (kappa + &1) * &(48 * N) / &2) * log(&2) +
         &(48 * N) * sum {i | i < 48 * N} (\i. rp_en_W kappa (x i)) +
         (kappa + &2) / &2 * sum {i | i < 48 * N} (\i. log(&1 + x i pow 2)) +
         &(48 * N) * sum {j | j < 48 * N} (\j. rp_en_Ws (s j)) +
         kappa * rp_en_psum (48 * N) (\i j. log(abs(x j - x i))) +
         rp_en_psum (48 * N) (\i j. log(&1 - x i * x j)) +
         &2 * rp_en_psum (48 * N) (\i j. log(abs(s j - s i))) -
         sum {i | i < 48 * N}
           (\i. sum {j | j < 48 * N} (\j. log(&1 - &2 * x i * s j + x i pow 2)))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[rp_en_F] THEN
  SIMP_TAC[SUM_ADD; SUM_LMUL; FINITE_NUMSEG_LT] THEN
  SUBGOAL_THEN `&0 < &N` MP_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_MUL] THEN
  RP_EN_GEN_SUMS_TAC THEN CONV_TAC REAL_FIELD);;

(* ------------------------------------------------------------------------- *)
(* The finite-n bound.                                                       *)
(* ------------------------------------------------------------------------- *)

let RP_EN_SUM_LE_CONST_UP = prove
 (`forall c (f:num->real) n. (forall i. i < n ==> f i <= c)
           ==> sum {i | i < n} f <= &n * c`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM RP_EN_SUM_CONST_LT] THEN
  MATCH_MP_TAC RP_EN_SUM_LE_LT THEN ASM_SIMP_TAC[]);;

let RP_EN_DIV_N2 = prove
 (`forall y A C m. &0 < m /\ m pow 2 * y <= m pow 2 * A + m * C ==> y <= A + C / m`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < m pow 2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(m:real) pow 2 * (A + C / m) = m pow 2 * A + m * C` ASSUME_TAC THENL
   [SUBGOAL_THEN `(m:real) * ((C:real) / m) = C` MP_TAC THENL
     [MATCH_MP_TAC REAL_DIV_LMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ABBREV_TAC `q = (C:real) / m` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(m:real) pow 2 * y <= m pow 2 * (A + C / m)` MP_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_LMUL_EQ]);;

let RP_EN_LAM_FACT = prove
 (`forall lam N (x:num->real).
     1 <= N /\ &0 <= lam /\
     (lam = &0 \/
      &(40 * N - 1) < sum {i | i < 48 * N} (\i. (&1 - x i pow 2) / (&1 + x i pow 2)))
     ==> --lam <= lam * sum {i | i < 48 * N}
                          (\i. &1 / &6 - &2 * x i pow 2 / (&1 + x i pow 2))`,
  REPEAT GEN_TAC THEN STRIP_TAC THENL
   [ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `lam * --(&1) <= lam * t ==> --lam <= lam * t`) THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `sum {i | i < 48 * N} (\i. &1 / &6 - &2 * (x:num->real) i pow 2 / (&1 + x i pow 2)) =
    sum {i | i < 48 * N} (\i. (&1 - x i pow 2) / (&1 + x i pow 2)) -
    sum {i | i < 48 * N} (\i. &5 / &6)` SUBST1_TAC THENL
   [SIMP_TAC[GSYM SUM_SUB; FINITE_NUMSEG_LT] THEN MATCH_MP_TAC SUM_EQ THEN
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    SUBGOAL_THEN `~(&1 + (x:num->real) i pow 2 = &0)` MP_TAC THENL
     [MP_TAC(SPEC `(x:num->real) i` REAL_LE_POW_2) THEN REAL_ARITH_TAC; ALL_TAC] THEN
    CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  REWRITE_TAC[RP_EN_SUM_CONST_LT] THEN
  UNDISCH_TAC `&(40 * N - 1) < sum {i | i < 48 * N}
                 (\i. (&1 - (x:num->real) i pow 2) / (&1 + x i pow 2))` THEN
  ASM_SIMP_TAC[GSYM REAL_OF_NUM_SUB; ARITH_RULE `1 <= N ==> 1 <= 40 * N`] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_MUL] THEN RP_EN_SUMARITH_TAC);;

(* positive linear combination of inequalities a_i <= b_i *)
let RP_EN_LESUM =
  let scale (c,th) =
    let cpos = REAL_ARITH (mk_comb(mk_comb(`(<=):real->real->bool`, `&0`), c)) in
    MATCH_MP REAL_LE_LMUL (CONJ cpos th) in
  fun l -> end_itlist (fun a b -> MATCH_MP REAL_LE_ADD2 (CONJ a b)) (map scale l);;

let RP_EN_FIN_BOUND = prove
 (`forall kappa lam p v Bx Bs e N (x:num->real) (s:num->real).
     &0 <= kappa /\ &0 <= lam /\ rp_summable p /\ rp_summable v /\
     (forall x. --(&1) <= x /\ x < &1 /\ ~(x = &0) ==> rp_X kappa lam p v x <= Bx) /\
     (forall s. &0 < s /\ s < &1 ==> rp_Y v s <= Bs) /\
     &0 < e /\ e < &1 / &8 /\ 1 <= N /\ rp_config N x s /\
     (lam = &0 \/
      &(40 * N - 1) < sum {i | i < 48 * N} (\i. (&1 - x i pow 2) / (&1 + x i pow 2)))
     ==> rp_en_F kappa N x s <=
         rp_dual kappa p v Bx Bs + e * rp_en_Dc kappa p v +
         rp_en_Cf kappa e lam p v Bx Bs / &(48 * N)`,
  REPEAT GEN_TAC THEN DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)) THEN
  MP_TAC(SPECL [`lam:real`; `N:num`; `x:num->real`] RP_EN_LAM_FACT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  FIRST_X_ASSUM(K ALL_TAC o check (is_disj o concl)) THEN
  UNDISCH_TAC `rp_config N x s` THEN REWRITE_TAC[rp_config; rp_nodes] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `forall i. i < 48 * N ==> --(&1) < (x:num->real) i /\ x i < &1`
  ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `1 <= 48 * N` ASSUME_TAC THENL
   [UNDISCH_TAC `1 <= N` THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &(48 * N)` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT] THEN UNDISCH_TAC `1 <= N` THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&12 <= &(48 * N)` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LE] THEN UNDISCH_TAC `1 <= N` THEN ARITH_TAC;
    ALL_TAC] THEN
  (* the two interaction bounds *)
  MP_TAC(SPECL [`48 * N`; `x:num->real`; `p:num->real`; `e:real`] RP_EN_PART_X) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`48 * N`; `x:num->real`; `s:num->real`; `v:num->real`; `e:real`]
         RP_EN_PART_PS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "PPS") THEN
  (* drop the distinctness hypotheses (bad conditional rewrites) *)
  REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (fun th ->
    try let b = snd(strip_forall(concl th)) in
        is_imp b && is_eq(rand b) && type_of(lhand(rand b)) = `:num`
    with Failure _ -> false))) THEN
  (* endpoint weakening, summed *)
  SUBGOAL_THEN
   `sum {i | i < 48 * N} (\i. &(48 * N) * rp_X kappa lam p v (x i) -
                               &1 / &2 * log(&1 - x i)) <=
    &(48 * N) * (&(48 * N) * Bx +
      &6 * ((lam / &6 + &2 * kappa * real_infsum (from 1) (\k. abs(p k)) +
             real_infsum (from 1) (\k. abs(v k))) - Bx))` (LABEL_TAC "EX") THENL
   [MATCH_MP_TAC RP_EN_SUM_LE_CONST_UP THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    REWRITE_TAC[] THEN MATCH_MP_TAC RP_EN_X_WEAKEN THEN
    SUBGOAL_THEN `--(&1) < (x:num->real) i /\ x i < &1 /\ ~(x i = &0)`
    STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `sum {j | j < 48 * N} (\j. &(48 * N) * rp_Y v ((s:num->real) j) - log(&1 - s j)) <=
    &(48 * N) * (&(48 * N) * Bs +
      &12 * (&2 * real_infsum (from 1) (\k. abs(v k)) - Bs))` (LABEL_TAC "EY") THENL
   [MATCH_MP_TAC RP_EN_SUM_LE_CONST_UP THEN X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    REWRITE_TAC[] THEN MATCH_MP_TAC RP_EN_Y_WEAKEN THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  (* damped versus undamped trial series *)
  SUBGOAL_THEN
   `kappa * (&(48 * N) * sum {i | i < 48 * N} (\i. rp_Tser p ((x:num->real) i))) <=
    kappa * (&(48 * N) * sum {i | i < 48 * N}
      (\i. rp_en_Te p e (x i) + e * real_infsum (from 1) (\k. abs(p k))))`
  (LABEL_TAC "ETK") THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
    MATCH_MP_TAC RP_EN_SUM_LE_LT THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    REWRITE_TAC[] THEN
    MP_TAC(SPECL [`p:num->real`; `e:real`; `(x:num->real) i`] RP_EN_TE_CLOSE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `--(&1) < (x:num->real) i /\ x i < &1` MP_TAC THENL
       [ASM_SIMP_TAC[]; ALL_TAC] THEN
      UNDISCH_TAC `e < &1 / &8` THEN REAL_ARITH_TAC;
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `&(48 * N) * sum {i | i < 48 * N} (\i. rp_Sser v ((x:num->real) i)) <=
    &(48 * N) * sum {i | i < 48 * N}
      (\i. rp_en_Se v e (x i) + &2 * e * real_infsum (from 1) (\k. abs(v k)))`
  (LABEL_TAC "ES") THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
    MATCH_MP_TAC RP_EN_SUM_LE_LT THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    REWRITE_TAC[] THEN
    MP_TAC(SPECL [`v:num->real`; `e:real`; `(x:num->real) i`] RP_EN_SE_CLOSE) THEN
    ASM_SIMP_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `&(48 * N) * sum {j | j < 48 * N} (\j. rp_en_Ts v e ((s:num->real) j)) <=
    &(48 * N) * sum {j | j < 48 * N}
      (\j. rp_Tser v (s j) + e * real_infsum (from 1) (\k. abs(v k)))`
  (LABEL_TAC "ETS") THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
    MATCH_MP_TAC RP_EN_SUM_LE_LT THEN X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    REWRITE_TAC[] THEN
    MP_TAC(SPECL [`v:num->real`; `e:real`; `(s:num->real) j`] RP_EN_TS_CLOSE) THEN
    ASM_SIMP_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* finite-size corrections *)
  SUBGOAL_THEN
   `(kappa + &2) / &2 * sum {i | i < 48 * N} (\i. log(&1 + (x:num->real) i pow 2)) <=
    (kappa + &2) / &2 * (&(48 * N) * log(&2))` (LABEL_TAC "ELOG") THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC RP_EN_SUM_LE_CONST_UP THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    REWRITE_TAC[] THEN MATCH_MP_TAC LOG_MONO_LE_IMP THEN
    SUBGOAL_THEN `--(&1) < (x:num->real) i /\ x i < &1` MP_TAC THENL
     [ASM_SIMP_TAC[]; ALL_TAC] THEN
    MP_TAC(SPEC `(x:num->real) i` REAL_LE_POW_2) THEN
    MP_TAC(SPECL [`2`; `abs((x:num->real) i)`] REAL_POW_1_LE) THEN
    REWRITE_TAC[REAL_POW2_ABS; REAL_ABS_POS] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= (kappa + &1) * (&(48 * N) * log(&2))` (LABEL_TAC "E9") THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
    MATCH_MP_TAC LOG_POS THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `&(48 * N) * --lam <=
    &(48 * N) * (lam * sum {i | i < 48 * N}
                   (\i. &1 / &6 - &2 * (x:num->real) i pow 2 / (&1 + x i pow 2)))`
  (LABEL_TAC "ELAM") THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
  SUBGOAL_THEN
   `kappa * rp_en_psum (48 * N) (\i j. log(abs((x:num->real) j - x i))) <=
    kappa * (&(48 * N) pow 2 * (--(log(&2)) / &2 + rp_nsq p) -
         &2 * &(48 * N) * sum {i | i < 48 * N} (\i. rp_en_Te p e (x i)) +
         &(48 * N) * (log(&2) - &2 * log(&1 - (&1 - e) pow 2)) / &2 +
         &2 * e * &(48 * N) pow 2)` (LABEL_TAC "PXK") THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  (* reduce to the unnormalised inequality *)
  ONCE_REWRITE_TAC[REAL_ADD_ASSOC] THEN
  MATCH_MP_TAC RP_EN_DIV_N2 THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[RP_EN_F_UNNORM] THEN
  REWRITE_TAC[rp_dual; rp_en_Dc; rp_en_Cf] THEN
  USE_THEN "PXK" (fun pxk -> USE_THEN "PPS" (fun pps ->
  USE_THEN "EX" (fun ex -> USE_THEN "EY" (fun ey ->
  USE_THEN "ETK" (fun etk -> USE_THEN "ES" (fun es ->
  USE_THEN "ETS" (fun ets -> USE_THEN "ELOG" (fun elog ->
  USE_THEN "E9" (fun e9 -> USE_THEN "ELAM" (fun elam ->
    MP_TAC(RP_EN_LESUM [`&1`,pxk; `&1`,pps; `&1`,ex; `&1`,ey; `&2`,etk;
                        `&1`,es; `&2`,ets; `&1`,elog; `&1 / &2`,e9;
                        `&1`,elam]))))))))))) THEN
  REWRITE_TAC[rp_X; rp_Y; rp_en_W; rp_en_Ws] THEN
  SIMP_TAC[SUM_ADD; SUM_SUB; SUM_LMUL; FINITE_NUMSEG_LT; RP_EN_SUM_CONST_LT] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_MUL] THEN
  RP_EN_SUMARITH_TAC);;
