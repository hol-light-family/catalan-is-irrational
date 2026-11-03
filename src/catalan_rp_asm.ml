(* ========================================================================= *)
(* CAT_REAL_PLACE assembly: all interface statements ==> CAT_REAL_PLACE.     *)
(* ========================================================================= *)

needs "src/catalan_rp_defs.ml";;

let RP_VDM_SUC = prove
 (`forall n y. rp_vdm (SUC n) y =
         product {i | i < n} (\i. y n - y i) * rp_vdm n y`,
  REPEAT GEN_TAC THEN REWRITE_TAC[rp_vdm; NUMSEG_CLAUSES_LT] THEN
  SIMP_TAC[PRODUCT_CLAUSES; FINITE_NUMSEG_LT; IN_ELIM_THM; LT_REFL]);;

let RP_ABS_INV_SUB = prove
 (`forall a b. ~(a = &0) /\ ~(b = &0)
         ==> abs(b - a) = abs(inv b - inv a) * abs b * abs a`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM REAL_ABS_MUL] THEN
  MATCH_MP_TAC(REAL_ARITH `x = --y ==> abs x = abs y`) THEN
  UNDISCH_TAC `~(a = &0)` THEN UNDISCH_TAC `~(b = &0)` THEN
  CONV_TAC REAL_FIELD);;

let RP_VDM_INV = prove
 (`forall n x. (forall i. i < n ==> ~(x i = &0))
         ==> abs(rp_vdm n x) =
             abs(rp_vdm n (\i. inv(x i))) *
             product {i | i < n} (\i. abs(x i) pow (n - 1))`,
  INDUCT_TAC THENL
   [REWRITE_TAC[rp_vdm; NUMSEG_CLAUSES_LT; PRODUCT_CLAUSES] THEN
    REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x:num->real`) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[ARITH_RULE `i < n ==> i < SUC n`]; ALL_TAC] THEN
  DISCH_TAC THEN
  ASM_REWRITE_TAC[RP_VDM_SUC; REAL_ABS_MUL] THEN
  SUBGOAL_THEN `~(x(n:num) = &0)` ASSUME_TAC THENL
   [ASM_MESON_TAC[ARITH_RULE `n < SUC n`]; ALL_TAC] THEN
  SUBGOAL_THEN
   `abs(product {i | i < n} (\i. x n - x i)) =
    abs(product {i | i < n} (\i. inv(x n) - inv(x i))) * abs(x n) pow n *
    product {i | i < n} (\i. abs(x i))`
  SUBST1_TAC THENL
   [SIMP_TAC[GSYM PRODUCT_ABS; FINITE_NUMSEG_LT] THEN
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `product {i | i < n}
       (\i. (abs(inv((x:num->real) n) - inv(x i)) * abs(x n)) * abs(x i))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC PRODUCT_EQ THEN REWRITE_TAC[IN_ELIM_THM] THEN
      REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN
      MATCH_MP_TAC RP_ABS_INV_SUB THEN
      ASM_MESON_TAC[ARITH_RULE `i < n ==> i < SUC n`];
      SIMP_TAC[PRODUCT_MUL; FINITE_NUMSEG_LT; PRODUCT_CONST; CARD_NUMSEG_LT;
               REAL_MUL_ASSOC]];
    ALL_TAC] THEN
  REWRITE_TAC[NUMSEG_CLAUSES_LT; SUC_SUB1] THEN
  SIMP_TAC[PRODUCT_CLAUSES; FINITE_NUMSEG_LT; IN_ELIM_THM; LT_REFL] THEN
  SUBGOAL_THEN
   `product {i | i < n} (\i. abs(x i) pow n) =
    product {i | i < n} (\i. abs(x i) pow (n - 1)) *
    product {i | i < n} (\i. abs(x i))`
  SUBST1_TAC THENL
   [SIMP_TAC[GSYM PRODUCT_MUL; FINITE_NUMSEG_LT] THEN
    MATCH_MP_TAC PRODUCT_EQ THEN REWRITE_TAC[IN_ELIM_THM] THEN
    REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `n = SUC(n - 1)`
     (fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [th]) THENL
     [ASM_ARITH_TAC; REWRITE_TAC[real_pow] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `p1 = product {i | i < n} (\i. abs((x:num->real) i))` THEN
  ABBREV_TAC `p2 = product {i | i < n} (\i. abs((x:num->real) i) pow (n - 1))` THEN
  ABBREV_TAC `p3 = abs(product {i | i < n} (\i. inv((x:num->real) n) - inv(x i)))` THEN
  CONV_TAC REAL_RING);;

let RP_POW_EXP_GROWTH = prove
 (`forall B e. &0 < B /\ &0 < e
         ==> exists M. forall n. M <= n ==> (B * &n) pow n <= exp(e * &n pow 2)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `&4 * B / e pow 2 + &1` REAL_ARCH_SIMPLE) THEN
  DISCH_THEN(X_CHOOSE_TAC `M:num`) THEN EXISTS_TAC `M:num` THEN
  X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `&4 * B / e pow 2 + &1 <= &n` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&M` THEN
    ASM_REWRITE_TAC[REAL_OF_NUM_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < e pow 2` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_POW_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `&4 * B <= &n * e pow 2` ASSUME_TAC THENL
   [ASM_SIMP_TAC[GSYM REAL_LE_LDIV_EQ] THEN
    UNDISCH_TAC `&4 * B / e pow 2 + &1 <= &n` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= &n` ASSUME_TAC THENL [REWRITE_TAC[REAL_POS]; ALL_TAC] THEN
  SUBGOAL_THEN `B * &n <= exp(e * &n)` ASSUME_TAC THENL
   [SUBGOAL_THEN `exp(e * &n) = exp(e * &n / &2) * exp(e * &n / &2)`
    SUBST1_TAC THENL
     [REWRITE_TAC[GSYM REAL_EXP_ADD] THEN AP_TERM_TAC THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(e * &n / &2) * (e * &n / &2)` THEN CONJ_TAC THENL
     [MP_TAC(SPECL [`&n`; `&4 * B`; `&n * e pow 2`] REAL_LE_LMUL) THEN
      ASM_REWRITE_TAC[] THEN REWRITE_TAC[REAL_POW_2] THEN REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_MUL2 THEN
      SUBGOAL_THEN `&0 <= e * &n / &2` ASSUME_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
         [ASM_REAL_ARITH_TAC;
          MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC]; ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN
      MP_TAC(SPEC `e * &n / &2` REAL_EXP_LE_X) THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `e * &n pow 2 = &n * (e * &n)` SUBST1_TAC THENL
   [REWRITE_TAC[REAL_POW_2] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[REAL_EXP_N] THEN MATCH_MP_TAC REAL_POW_LE2 THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Elementary facts on the coordinate t.                                     *)
(* ------------------------------------------------------------------------- *)

let RP_T_BOUNDS = prove
 (`forall x. abs(rp_t x) <= &1 /\ &0 <= &1 - rp_t x`,
  GEN_TAC THEN
  SUBGOAL_THEN `rp_t x = (&2 * x) / (&1 + x pow 2)` SUBST1_TAC THENL
   [REWRITE_TAC[rp_t; real_div; REAL_MUL_ASSOC]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &1 + x pow 2` ASSUME_TAC THENL
   [MP_TAC(SPEC `x:real` REAL_LE_POW_2) THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPEC `x - &1` REAL_LE_POW_2) THEN
  MP_TAC(SPEC `x + &1` REAL_LE_POW_2) THEN
  ASM_SIMP_TAC[REAL_ABS_DIV; REAL_ARITH `&0 < a ==> abs a = a`;
               REAL_LE_LDIV_EQ; REAL_SUB_LE] THEN
  REAL_ARITH_TAC);;

let RP_KERNEL_POS = prove
 (`forall x s. &0 < s /\ s < &1 ==> &0 < &1 - rp_t x * s`,
  REPEAT STRIP_TAC THEN MP_TAC(CONJUNCT1(SPEC `x:real` RP_T_BOUNDS)) THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `abs(rp_t x * s) <= &1 * s` MP_TAC THENL
   [ASM_SIMP_TAC[REAL_ABS_MUL; REAL_ARITH `&0 < s ==> abs s = s`] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC;
    ASM_REAL_ARITH_TAC]);;

let RP_J_POS_LE = prove
 (`forall N x s. rp_config N x s ==> &0 <= rp_J N x s`,
  REWRITE_TAC[rp_config; rp_J] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= product {i | i < 48 * N}
     (\i. product {j | j < 48 * N} (\j. &1 - rp_t ((x:num->real) i) * s j))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC PRODUCT_POS_LE THEN REWRITE_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM] THEN
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    MATCH_MP_TAC PRODUCT_POS_LE THEN REWRITE_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM] THEN
    X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    MATCH_MP_TAC REAL_LT_IMP_LE THEN MATCH_MP_TAC RP_KERNEL_POS THEN
    ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= product {j | j < 48 * N}
     (\j. (s:num->real) j pow (7 * N) * (&1 - s j) pow (4 * N))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC PRODUCT_POS_LE THEN REWRITE_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM] THEN
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `&0 < (s:num->real) i /\ s i < &1` MP_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    STRIP_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THEN
    MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= product {i | i < 48 * N}
     (\i. abs(rp_t ((x:num->real) i)) pow (63 * N - 1) *
          (&1 - rp_t (x i)) pow (2 * N))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC PRODUCT_POS_LE THEN REWRITE_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM] THEN
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THEN MATCH_MP_TAC REAL_POW_LE THEN
    REWRITE_TAC[REAL_ABS_POS; RP_T_BOUNDS]; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_MUL; REAL_LE_DIV; REAL_ABS_POS; REAL_LE_POW_2]);;

let RP_I2_EQ = prove
 (`forall N x s. 1 <= N /\ rp_nodes (48 * N) x
           ==> rp_I2 N x s =
               product {i | i < 48 * N} (\i. inv(abs(x i)) pow (44 * N - 1)) *
               abs(rp_vdm (48 * N) x) * rp_J N x s`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`48 * N`; `x:num->real`] RP_VDM_INV) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[rp_nodes]; DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[rp_I2] THEN
  SUBGOAL_THEN
   `product {i | i < 48 * N} (\i. abs(x i) pow (4 * N)) =
    product {i | i < 48 * N} (\i. inv(abs(x i)) pow (44 * N - 1)) *
    product {i | i < 48 * N} (\i. abs(x i) pow (48 * N - 1))`
  SUBST1_TAC THENL
   [SIMP_TAC[GSYM PRODUCT_MUL; FINITE_NUMSEG_LT] THEN
    MATCH_MP_TAC PRODUCT_EQ THEN REWRITE_TAC[IN_ELIM_THM] THEN
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `~(abs((x:num->real) i) = &0)` ASSUME_TAC THENL
     [REWRITE_TAC[REAL_ABS_ZERO] THEN ASM_MESON_TAC[rp_nodes]; ALL_TAC] THEN
    SUBGOAL_THEN `48 * N - 1 = (44 * N - 1) + 4 * N` SUBST1_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[REAL_POW_ADD; REAL_MUL_ASSOC; REAL_POW_INV] THEN
    ASM_SIMP_TAC[REAL_MUL_LINV; REAL_POW_NZ; REAL_MUL_LID];
    ALL_TAC] THEN
  ABBREV_TAC `p1 = product {i | i < 48 * N} (\i. inv(abs((x:num->real) i)) pow (44 * N - 1))` THEN
  ABBREV_TAC `p2 = product {i | i < 48 * N} (\i. abs((x:num->real) i) pow (48 * N - 1))` THEN
  CONV_TAC REAL_RING);;

let RP_ARITH_L1 = prove
 (`forall W X R J V A B FF.
      &0 <= W /\ W <= FF /\ &0 <= X /\ &0 <= R /\ &0 <= J /\ &0 <= V /\
      R <= A * V /\ A <= B
      ==> W * X * R * J <= FF * B * (X * V * J)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `R <= B * V` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(A:real) * V` THEN
    ASM_SIMP_TAC[REAL_LE_RMUL]; ALL_TAC] THEN
  SUBGOAL_THEN `W * R <= FF * (B * V)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(W * R) * (X * J) <= (FF * (B * V)) * (X * J)` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LE_MUL]; ALL_TAC] THEN
  REWRITE_TAC[REAL_MUL_AC]);;

let RP_ARITH_L2 = prove
 (`forall W X R J a b i P B FF.
      &0 <= W /\ W <= FF /\ &0 <= X /\ &0 <= R /\ &0 <= J /\
      &0 <= i /\ &0 <= P /\
      R <= a * b * i * P /\ a * b <= B
      ==> W * X * R * J <= FF * B * (J * i * (P * X))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `R <= B * (i * P)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `((a:real) * b) * (i * P)` THEN
    CONJ_TAC THENL [ASM_REWRITE_TAC[GSYM REAL_MUL_ASSOC]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LE_MUL]; ALL_TAC] THEN
  SUBGOAL_THEN `W * R <= FF * (B * (i * P))` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(W * R) * (X * J) <= (FF * (B * (i * P))) * (X * J)` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LE_MUL]; ALL_TAC] THEN
  REWRITE_TAC[REAL_MUL_AC]);;

let RP_K0_POS = prove
 (`&0 < rp_K0`,
  REWRITE_TAC[rp_K0] THEN MATCH_MP_TAC REAL_LT_MUL THEN
  REWRITE_TAC[REAL_EXP_POS_LT] THEN REAL_ARITH_TAC);;

let RP_W_BOUND = prove
 (`forall x. abs x < &1
       ==> &0 <= &4 * abs x / (&1 + x pow 2) pow 2 /\
           &4 * abs x / (&1 + x pow 2) pow 2 <= &4`,
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `&1 <= (&1 + x pow 2) pow 2` ASSUME_TAC THENL
   [GEN_REWRITE_TAC LAND_CONV [GSYM(SPEC `2` REAL_POW_ONE)] THEN
    MATCH_MP_TAC REAL_POW_LE2 THEN MP_TAC(SPEC `x:real` REAL_LE_POW_2) THEN
    REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < (&1 + x pow 2) pow 2` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= abs x / (&1 + x pow 2) pow 2 /\
                abs x / (&1 + x pow 2) pow 2 <= &1`
  MP_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_DIV; REAL_ABS_POS; REAL_LT_IMP_LE; REAL_LE_LDIV_EQ] THEN
    ASM_REAL_ARITH_TAC;
    REAL_ARITH_TAC]);;

let RP_CONFIG_BOUND = prove
 (`RP_ALG_STMT /\ RP_HAD_STMT /\ RP_INTERP_STMT
   ==> forall N x s. 1 <= N /\ rp_config N x s
       ==> abs(rp_integrand N x s) <=
           &4 pow (48 * N) * ((&3 + rp_K0) * &(48 * N)) pow (48 * N) *
           (if sum {i | i < 48 * N} (\i. (&1 - x i pow 2) / (&1 + x i pow 2))
               <= &(40 * N - 1)
            then rp_I2 N x s else rp_I1 N x s)`,
  REWRITE_TAC[RP_ALG_STMT; RP_HAD_STMT; RP_INTERP_STMT] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "alg")
    (CONJUNCTS_THEN2 (LABEL_TAC "had") (LABEL_TAC "ip"))) THEN
  REPEAT STRIP_TAC THEN
  REMOVE_THEN "alg" (fun th -> ASM_SIMP_TAC[th]) THEN
  SUBGOAL_THEN `rp_nodes (48 * N) x` ASSUME_TAC THENL
   [ASM_MESON_TAC[rp_config]; ALL_TAC] THEN
  SUBGOAL_THEN
   `&0 <= product {i | i < 48 * N}
            (\i. &4 * abs((x:num->real) i) / (&1 + x i pow 2) pow 2) /\
    product {i | i < 48 * N}
            (\i. &4 * abs((x:num->real) i) / (&1 + x i pow 2) pow 2)
    <= &4 pow (48 * N)`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `forall i. i < 48 * N ==> abs((x:num->real) i) < &1`
    ASSUME_TAC THENL
     [REPEAT STRIP_TAC THEN
      SUBGOAL_THEN `--(&1) < (x:num->real) i /\ x i < &1` MP_TAC THENL
       [ASM_MESON_TAC[rp_nodes]; REAL_ARITH_TAC]; ALL_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC PRODUCT_POS_LE THEN
      ASM_SIMP_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM; RP_W_BOUND];
      SUBGOAL_THEN `&4 pow (48 * N) = product {i | i < 48 * N} (\i. &4)`
      SUBST1_TAC THENL
       [SIMP_TAC[PRODUCT_CONST; FINITE_NUMSEG_LT; CARD_NUMSEG_LT]; ALL_TAC] THEN
      MATCH_MP_TAC PRODUCT_LE THEN
      ASM_SIMP_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM; RP_W_BOUND]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `&0 <= product {i | i < 48 * N}
            (\i. inv(abs((x:num->real) i)) pow (44 * N - 1))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC PRODUCT_POS_LE THEN
    SIMP_TAC[FINITE_NUMSEG_LT; REAL_POW_LE; REAL_LE_INV_EQ; REAL_ABS_POS];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= rp_J N x s` ASSUME_TAC THENL
   [ASM_MESON_TAC[RP_J_POS_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `&1 <= &(48 * N)` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LE] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= rp_K0 * &(48 * N)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN
    REWRITE_TAC[REAL_POS] THEN MP_TAC RP_K0_POS THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  COND_CASES_TAC THENL
   [ASM_SIMP_TAC[RP_I2_EQ] THEN
    ABBREV_TAC `XX = product {i | i < 48 * N}
            (\i. inv(abs((x:num->real) i)) pow (44 * N - 1))` THEN
    MATCH_MP_TAC RP_ARITH_L1 THEN
    EXISTS_TAC `(&1 + rp_K0 * &(48 * N)) pow (48 * N)` THEN
    ASM_SIMP_TAC[REAL_ABS_POS] THEN
    MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
    ABBREV_TAC `WW = product {i | i < 48 * N}
            (\i. &4 * abs((x:num->real) i) / (&1 + x i pow 2) pow 2)` THEN
    REWRITE_TAC[rp_I1] THEN SIMP_TAC[PRODUCT_MUL; FINITE_NUMSEG_LT] THEN
    ABBREV_TAC `XX = product {i | i < 48 * N}
            (\i. inv(abs((x:num->real) i)) pow (44 * N - 1))` THEN
    MATCH_MP_TAC RP_ARITH_L2 THEN
    EXISTS_TAC `(&3 / &2) pow (48 * N)` THEN
    EXISTS_TAC `sqrt(&(48 * N)) pow (48 * N)` THEN
    ASM_SIMP_TAC[REAL_ABS_POS; REAL_POW_LE; REAL_LE_INV_EQ; REAL_POS] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC PRODUCT_POS_LE THEN
      SIMP_TAC[FINITE_NUMSEG_LT; REAL_POW_LE; SQRT_POS_LE; REAL_LE_ADD;
               REAL_POS; REAL_LE_POW_2];
      ALL_TAC] THEN
    REWRITE_TAC[GSYM REAL_POW_MUL] THEN MATCH_MP_TAC REAL_POW_LE2 THEN
    SUBGOAL_THEN `sqrt(&(48 * N)) <= &(48 * N)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_LSQRT THEN REWRITE_TAC[REAL_POS; REAL_POW_2] THEN
      MATCH_MP_TAC(REAL_ARITH `&1 * a <= b ==> a <= b`) THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[REAL_POS];
      ALL_TAC] THEN
    MP_TAC(SPEC `&(48 * N)` SQRT_POS_LE) THEN REWRITE_TAC[REAL_POS] THEN
    ASM_REAL_ARITH_TAC]);;

let RP_POW_COMBINE = prove
 (`forall n K G. &2 pow n * &4 pow n * (K * &n) pow n * G =
           ((&8 * K) * &n) pow n * G`,
  REPEAT GEN_TAC THEN REWRITE_TAC[REAL_MUL_ASSOC; GSYM REAL_POW_MUL] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REAL_ARITH_TAC);;

let RP_ASSEMBLY = prove
 (`RP_INT_STMT /\ RP_ALG_STMT /\ RP_HAD_STMT /\ RP_INTERP_STMT /\
   RP_EN1_STMT /\ RP_EN2_STMT /\ RP_CERT1_STMT /\ RP_CERT2_STMT
   ==> CAT_REAL_PLACE`,
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "int") MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "alg") MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "had") MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ip") MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "en1") MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "en2") MP_TAC) THEN
  REWRITE_TAC[RP_CERT1_STMT; RP_CERT2_STMT] THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (X_CHOOSE_THEN `lam:real` (X_CHOOSE_THEN `p1:num->real`
     (X_CHOOSE_THEN `v1:num->real` (X_CHOOSE_THEN `Bx1:real`
       (X_CHOOSE_THEN `Bs1:real` STRIP_ASSUME_TAC)))))
   (X_CHOOSE_THEN `p2:num->real`
     (X_CHOOSE_THEN `v2:num->real` (X_CHOOSE_THEN `Bx2:real`
       (X_CHOOSE_THEN `Bs2:real` STRIP_ASSUME_TAC))))) THEN
  ABBREV_TAC `D1 = rp_dual (&1) p1 v1 Bx1 Bs1` THEN
  ABBREV_TAC `D2 = rp_dual (&2) p2 v2 Bx2 Bs2` THEN
  ABBREV_TAC `c0 = --(&22909 / &10000)` THEN
  SUBGOAL_THEN `exists e. &0 < e /\ D1 + &4 * e < c0 /\ D2 + &4 * e < c0`
  STRIP_ASSUME_TAC THENL
   [EXISTS_TAC `min ((c0 - D1) / &8) ((c0 - D2) / &8)` THEN
    ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REMOVE_THEN "en1" (MP_TAC o SPECL
    [`lam:real`; `p1:num->real`; `v1:num->real`; `Bx1:real`; `Bs1:real`;
     `e:real`] o REWRITE_RULE[RP_EN1_STMT]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `N1:num` (LABEL_TAC "e1")) THEN
  REMOVE_THEN "en2" (MP_TAC o SPECL
    [`p2:num->real`; `v2:num->real`; `Bx2:real`; `Bs2:real`;
     `e:real`] o REWRITE_RULE[RP_EN2_STMT]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `N2:num` (LABEL_TAC "e2")) THEN
  MP_TAC(SPECL [`&8 * (&3 + rp_K0)`; `e:real`] RP_POW_EXP_GROWTH) THEN
  ANTS_TAC THENL [MP_TAC RP_K0_POS THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `M:num`) THEN
  MP_TAC(MATCH_MP RP_CONFIG_BOUND
   (CONJ (REWRITE_RULE[] (ASSUME `RP_ALG_STMT`))
     (CONJ (ASSUME `RP_HAD_STMT`) (ASSUME `RP_INTERP_STMT`)))) THEN
  DISCH_THEN(LABEL_TAC "cb") THEN
  REWRITE_TAC[CAT_REAL_PLACE] THEN EXISTS_TAC `N1 + N2 + M + 1` THEN
  X_GEN_TAC `N:num` THEN STRIP_TAC THEN
  SUBGOAL_THEN `1 <= N /\ N1 <= N /\ N2 <= N /\ M <= 48 * N`
  STRIP_ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `n = 48 * N` THEN
  ABBREV_TAC `G = exp(&n pow 2 * (c0 - &3 * e + log(&2) / &2))` THEN
  SUBGOAL_THEN `&0 < &n pow 2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LT THEN REWRITE_TAC[REAL_OF_NUM_LT] THEN
    EXPAND_TAC "n" THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `forall x s. rp_config N x s
          ==> abs(rp_integrand N x s) <=
              &4 pow n * ((&3 + rp_K0) * &n) pow n * G`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    USE_THEN "cb" (MP_TAC o SPECL [`N:num`; `x:num->real`; `s:num->real`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[ASSUME `48 * N = n`] THEN
    MATCH_MP_TAC(REAL_ARITH `b <= c ==> a <= b ==> a <= c`) THEN
    REWRITE_TAC[REAL_MUL_ASSOC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THEN MATCH_MP_TAC REAL_POW_LE THEN
      REWRITE_TAC[REAL_POS] THEN MATCH_MP_TAC REAL_LE_MUL THEN
      REWRITE_TAC[REAL_POS] THEN MP_TAC RP_K0_POS THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    EXPAND_TAC "G" THEN COND_CASES_TAC THENL
     [USE_THEN "e2" (MP_TAC o SPECL [`N:num`; `x:num->real`; `s:num->real`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC];
      USE_THEN "e1" (MP_TAC o SPECL [`N:num`; `x:num->real`; `s:num->real`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[GSYM REAL_NOT_LE]; ALL_TAC]] THEN
    REWRITE_TAC[ASSUME `48 * N = n`] THEN
    MATCH_MP_TAC(REAL_ARITH `b <= c ==> a <= b ==> a <= c`) THEN
    REWRITE_TAC[REAL_EXP_MONO_LE] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REMOVE_THEN "int" (MP_TAC o SPECL
    [`N:num`; `&4 pow n * ((&3 + rp_K0) * &n) pow n * G`] o
    REWRITE_RULE[RP_INT_STMT]) THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `n:num` o check (fun th -> can (find_term ((=) `exp`)) (concl th) && is_forall(concl th))) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[RP_POW_COMBINE] THEN
  REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `abs(cat_det N) <= exp(&n pow 2 * (c0 - &2 * e + log(&2) / &2))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `((&8 * (&3 + rp_K0)) * &n) pow n * G` THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `exp(e * &n pow 2) * G` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN
      EXPAND_TAC "G" THEN REWRITE_TAC[REAL_EXP_POS_LE];
      EXPAND_TAC "G" THEN REWRITE_TAC[GSYM REAL_EXP_ADD; REAL_EXP_MONO_LE] THEN
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[cat_nlog] THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `log(abs(cat_det N)) <= &n pow 2 * (c0 - &2 * e + log(&2) / &2)`
  MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `log(exp(&n pow 2 * (c0 - &2 * e + log(&2) / &2)))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC LOG_MONO_LE_IMP THEN ASM_REWRITE_TAC[GSYM REAL_ABS_NZ];
      REWRITE_TAC[LOG_EXP; REAL_LE_REFL]];
    ALL_TAC] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `log(abs(cat_det N)) / &n pow 2 <= c0 - &2 * e + log(&2) / &2`
  MP_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
    ASM_REWRITE_TAC[];
    ASM_REAL_ARITH_TAC]);;
