(* ========================================================================= *)
(* CAT_NONVANISHING, part Lb (prefix nv_mz_): Lemma 3.1, Equation (31).     *)
(*   NV_MZ_Z0      : harmonic-sum reduction of Z' (proved outright).        *)
(*   NV_MZ_M0_IMP  : the M' reduction, assuming the digit facts             *)
(*                   NV_DIG_C_PINT, NV_DIG_M, NV_DIG_KMINUS, NV_DIG_KPLUS.  *)
(* ========================================================================= *)

needs "src/catalan_nv_base.ml";;
needs "Library/pocklington.ml";;
needs "src/catalan_nv_iface.ml";;

let NV_MZ_DIV_SUC = prove
 (`forall p n. ~(p = 0)
         ==> (n + 1) DIV p = (if p divides (n + 1) then n DIV p + 1 else n DIV p) /\
             (p divides (n + 1) ==> p * ((n + 1) DIV p) = n + 1)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(SPECL [`n:num`; `p:num`] DIVISION) THEN ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `q = n DIV p` THEN ABBREV_TAC `s = n MOD p` THEN
  STRIP_TAC THEN REWRITE_TAC[DIVIDES_MOD] THEN
  ASM_CASES_TAC `s + 1 < p` THENL
   [SUBGOAL_THEN `(n + 1) MOD p = s + 1 /\ (n + 1) DIV p = q` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL [MATCH_MP_TAC MOD_UNIQ THEN EXISTS_TAC `q:num`;
                       MATCH_MP_TAC DIV_UNIQ THEN EXISTS_TAC `s + 1`] THEN ASM_ARITH_TAC;
      ASM_REWRITE_TAC[ARITH_RULE `~(s + 1 = 0)`]];
    SUBGOAL_THEN `(n + 1) MOD p = 0 /\ (n + 1) DIV p = q + 1` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL [MATCH_MP_TAC MOD_UNIQ THEN EXISTS_TAC `q + 1`;
                       MATCH_MP_TAC DIV_UNIQ THEN EXISTS_TAC `0`] THEN
      REWRITE_TAC[RIGHT_ADD_DISTRIB] THEN ASM_ARITH_TAC;
      ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[LEFT_ADD_DISTRIB] THEN ASM_ARITH_TAC]]);;

let NV_MZ_SUM_MULT = prove
 (`forall p g a n. prime p /\
     (forall k. a + 1 <= k /\ k <= a + n /\ ~(p divides k) ==> nv_cong p (g k) (&0))
     ==> nv_cong p (sum(a + 1..a + n) g) (sum(a DIV p + 1..(a + n) DIV p) (\m. g(p * m)))`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THENL
   [STRIP_TAC THEN REWRITE_TAC[ADD_CLAUSES] THEN
    SIMP_TAC[SUM_TRIV_NUMSEG; ARITH_RULE `a < a + 1`] THEN ASM_SIMP_TAC[NV_CONG_REFL];
    ALL_TAC] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `~(p = 0)` ASSUME_TAC THENL [ASM_MESON_TAC[PRIME_0]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN UNDISCH_TAC `k <= a + n:num` THEN ARITH_TAC; ALL_TAC] THEN
  DISCH_TAC THEN
  REWRITE_TAC[ADD_CLAUSES; SUM_CLAUSES_NUMSEG; ARITH_RULE `a + 1 <= SUC(a + n)`] THEN
  MP_TAC(SPECL [`p:num`; `a + n:num`] NV_MZ_DIV_SUC) THEN
  ASM_REWRITE_TAC[ADD1] THEN
  ASM_CASES_TAC `p divides ((a + n) + 1)` THEN ASM_REWRITE_TAC[] THENL
   [DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN ASM_REWRITE_TAC[] THEN
    DISCH_TAC THEN ASM_REWRITE_TAC[GSYM ADD1; SUM_CLAUSES_NUMSEG] THEN
    REWRITE_TAC[ADD1] THEN
    SUBGOAL_THEN `a DIV p + 1 <= (a + n) DIV p + 1` (fun th -> REWRITE_TAC[th]) THENL
     [REWRITE_TAC[LE_ADD_RCANCEL] THEN MATCH_MP_TAC DIV_MONO THEN ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC NV_CONG_ADD THEN ASM_SIMP_TAC[NV_CONG_REFL];
    DISCH_TAC THEN GEN_REWRITE_TAC (RAND_CONV) [GSYM REAL_ADD_RID] THEN
    MATCH_MP_TAC NV_CONG_ADD THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ARITH_TAC]);;


let NV_MZ_PINT_INV_SMALL = prove
 (`forall p n. prime p /\ 0 < n /\ n < p ==> nv_pint p (inv(&n))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC NV_PINT_INV_NUM THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o MATCH_MP DIVIDES_LE) THEN ASM_ARITH_TAC);;

let NV_MZ_PINT_INV_NDIV = prove
 (`forall p n. prime p /\ ~(p divides n) ==> nv_pint p (inv(&n))`,
  SIMP_TAC[NV_PINT_INV_NUM]);;

let NV_MZ_HARM_PINT = prove
 (`forall p e n. prime p /\ n < p ==> nv_pint p (cat_harm e n)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[cat_harm] THEN MATCH_MP_TAC NV_PINT_SUM THEN
  ASM_REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[real_div; REAL_MUL_LID; GSYM REAL_POW_INV] THEN
  MATCH_MP_TAC NV_PINT_POW THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC NV_MZ_PINT_INV_SMALL THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

let NV_MZ_HARM_CONG = prove
 (`forall p e n. prime p /\ 1 <= e
           ==> nv_cong p (&p pow e * cat_harm e n) (cat_harm e (n DIV p))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(&p = &0)` ASSUME_TAC THENL [ASM_SIMP_TAC[NV_PRIME_NZ]; ALL_TAC] THEN
  REWRITE_TAC[cat_harm; GSYM SUM_LMUL] THEN
  MP_TAC(ISPECL [`p:num`; `\k. &p pow e * &1 / &k pow e`; `0`; `n:num`]
    NV_MZ_SUM_MULT) THEN
  REWRITE_TAC[ADD_CLAUSES; DIV_0] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `&p pow e * &1 / &k pow e = &p * (&p pow (e - 1) * inv(&k) pow e)`
    SUBST1_TAC THENL
     [SUBGOAL_THEN `e = (e - 1) + 1` (fun th -> GEN_REWRITE_TAC (LAND_CONV o LAND_CONV o RAND_CONV) [th]) THENL
       [UNDISCH_TAC `1 <= e` THEN ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[REAL_POW_ADD; REAL_POW_1; real_div; REAL_MUL_LID; REAL_POW_INV] THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC NV_CONG_PMUL_0 THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC NV_PINT_MUL THEN ASM_SIMP_TAC[NV_PINT_POW; NV_PINT_NUM] THEN
    MATCH_MP_TAC NV_PINT_POW THEN ASM_SIMP_TAC[NV_MZ_PINT_INV_NDIV];
    ALL_TAC] THEN
  MATCH_MP_TAC(MESON[] `y = y' ==> nv_cong p x y ==> nv_cong p x y'`) THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_MUL; REAL_POW_MUL] THEN
  SUBGOAL_THEN `~(&i = &0)` MP_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_EQ] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  UNDISCH_TAC `~(&p = &0)` THEN
  REWRITE_TAC[IMP_IMP; GSYM REAL_POW_EQ_0; DE_MORGAN_THM] THEN
  CONV_TAC REAL_FIELD);;


let NV_MZ_PINT_INV_DIFF = prove
 (`forall p a b. prime p /\ ~(a MOD p = b MOD p) ==> nv_pint p (inv(&a - &b))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[REAL_OF_NUM_SUB_CASES] THEN
  COND_CASES_TAC THEN REWRITE_TAC[REAL_INV_NEG; NV_PINT_NEG_EQ] THEN
  MATCH_MP_TAC NV_PINT_INV_NUM THEN ASM_REWRITE_TAC[divides] THEN
  DISCH_THEN(X_CHOOSE_TAC `q:num`) THEN UNDISCH_TAC `~(a MOD p = b MOD p)` THEN
  REWRITE_TAC[] THENL
   [SUBGOAL_THEN `a = p * q + b:num` SUBST1_TAC THENL
     [FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN MATCH_MP_TAC(GSYM SUB_ADD) THEN
      ASM_REWRITE_TAC[];
      REWRITE_TAC[MOD_MULT_ADD]];
    SUBGOAL_THEN `b = p * q + a:num` SUBST1_TAC THENL
     [FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN MATCH_MP_TAC(GSYM SUB_ADD) THEN
      UNDISCH_TAC `~(b <= a:num)` THEN ARITH_TAC;
      REWRITE_TAC[MOD_MULT_ADD]]]);;

let NV_MZ_Z0 = prove
 (`forall p i j. prime p /\ 260 < p /\ i < 65 * p /\ j < 65 * p
           ==> nv_pint p (cat_Z0 (i DIV p) (j DIV p)) /\
               nv_cong p (&p pow 2 * cat_Z0 i j)
                 (if i MOD p = j MOD p then cat_Z0 (i DIV p) (j DIV p) else &0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(p = 0)` ASSUME_TAC THENL [ASM_MESON_TAC[PRIME_0]; ALL_TAC] THEN
  SUBGOAL_THEN `~(&p = &0)` ASSUME_TAC THENL [ASM_SIMP_TAC[NV_PRIME_NZ]; ALL_TAC] THEN
  MP_TAC(SPECL [`i:num`; `p:num`] DIVISION) THEN
  MP_TAC(SPECL [`j:num`; `p:num`] DIVISION) THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `i DIV p < 65 /\ j DIV p < 65` MP_TAC THENL
   [ASM_SIMP_TAC[RDIV_LT_EQ] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `I0 = i DIV p` THEN ABBREV_TAC `J0 = j DIV p` THEN
  ABBREV_TAC `s = i MOD p` THEN ABBREV_TAC `t = j MOD p` THEN
  REPEAT(DISCH_THEN(STRIP_ASSUME_TAC o GSYM)) THEN
  SUBGOAL_THEN `I0 < p /\ J0 < p:num` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `260 < p` THEN UNDISCH_TAC `I0 < 65` THEN UNDISCH_TAC `J0 < 65` THEN
    ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `forall e. nv_pint p (cat_harm e I0) /\ nv_pint p (cat_harm e J0)`
  ASSUME_TAC THENL [ASM_SIMP_TAC[NV_MZ_HARM_PINT]; ALL_TAC] THEN
  SUBGOAL_THEN `forall e. 1 <= e ==> nv_cong p (&p pow e * cat_harm e i) (cat_harm e I0) /\
                               nv_cong p (&p pow e * cat_harm e j) (cat_harm e J0)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "I0" THEN EXPAND_TAC "J0" THEN
    ASM_SIMP_TAC[NV_MZ_HARM_CONG]; ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[cat_Z0] THEN COND_CASES_TAC THEN
    ASM_SIMP_TAC[NV_PINT_NEG] THEN REWRITE_TAC[real_div] THEN
    MATCH_MP_TAC NV_PINT_MUL THEN ASM_SIMP_TAC[NV_PINT_SUB] THEN
    MATCH_MP_TAC NV_MZ_PINT_INV_DIFF THEN ASM_SIMP_TAC[MOD_LT];
    ALL_TAC] THEN
  ASM_CASES_TAC `i:num = j` THENL
   [UNDISCH_TAC `i:num = j` THEN DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
    SUBGOAL_THEN `J0:num = I0 /\ t:num = s` STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "I0" THEN EXPAND_TAC "J0" THEN EXPAND_TAC "s" THEN
      EXPAND_TAC "t" THEN REWRITE_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[cat_Z0; REAL_MUL_RNEG] THEN MATCH_MP_TAC NV_CONG_NEG THEN
    ASM_SIMP_TAC[ARITH_RULE `1 <= 2`];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[cat_Z0] THEN
  SUBGOAL_THEN `&p pow 2 * (cat_harm 1 i - cat_harm 1 j) / (&i - &j) =
                (&p pow 1 * cat_harm 1 i - &p pow 1 * cat_harm 1 j) *
                (&p * inv(&i - &j))` SUBST1_TAC THENL
   [REWRITE_TAC[REAL_POW_2; REAL_POW_1; real_div] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `nv_pint p (&p pow 1 * cat_harm 1 i - &p pow 1 * cat_harm 1 j)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC NV_PINT_SUB THEN ASM_MESON_TAC[NV_CONG_PINT; ARITH_RULE `1 <= 1`];
    ALL_TAC] THEN
  COND_CASES_TAC THENL
   [SUBGOAL_THEN `~(I0:num = J0)` ASSUME_TAC THENL
     [DISCH_TAC THEN UNDISCH_TAC `~(i:num = j)` THEN REWRITE_TAC[] THEN
      EXPAND_TAC "i" THEN EXPAND_TAC "j" THEN
      REWRITE_TAC[ASSUME `I0:num = J0`; ASSUME `s:num = t`]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `&p * inv(&i - &j) = inv(&I0 - &J0)` SUBST1_TAC THENL
     [SUBGOAL_THEN `&i - &j = &p * (&I0 - &J0)` SUBST1_TAC THENL
       [SUBGOAL_THEN `&i = &I0 * &p + &s /\ &j = &J0 * &p + &t` STRIP_ASSUME_TAC THENL
         [REWRITE_TAC[REAL_OF_NUM_MUL; REAL_OF_NUM_ADD; REAL_OF_NUM_EQ] THEN
          ASM_REWRITE_TAC[]; ALL_TAC] THEN
        ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `~(&I0 - &J0 = &0)` MP_TAC THENL
       [ASM_REWRITE_TAC[REAL_SUB_0; REAL_OF_NUM_EQ]; ALL_TAC] THEN
      UNDISCH_TAC `~(&p = &0)` THEN CONV_TAC REAL_FIELD;
      ALL_TAC] THEN
    REWRITE_TAC[real_div] THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
    MATCH_MP_TAC NV_CONG_LMUL THEN ASM_SIMP_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC NV_MZ_PINT_INV_DIFF THEN ASM_SIMP_TAC[MOD_LT]; ALL_TAC] THEN
    MATCH_MP_TAC NV_CONG_SUB THEN ASM_SIMP_TAC[ARITH_RULE `1 <= 1`];
    ALL_TAC] THEN
  ONCE_REWRITE_TAC[REAL_ARITH `x * (&p * y) = &p * (x * y)`] THEN
  MATCH_MP_TAC NV_CONG_PMUL_0 THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC NV_PINT_MUL THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC NV_MZ_PINT_INV_DIFF THEN ASM_REWRITE_TAC[]);;


let NV_MZ_HYP_C = `forall p l. prime p /\ ~(p = 2) ==> nv_pint p (cat_c l)`;;
let NV_MZ_HYP_M = `forall p z. prime p /\ 260 < p /\ 1 <= z /\ z <= 65 * p
                       ==> nv_pint p (if z DIV p = 0 then &0 else cat_m (z DIV p - 1)) /\
                           nv_cong p (&p * cat_m (z - 1))
                             (nv_E (p - 1 - z MOD p) *
                              (if z DIV p = 0 then &0 else cat_m (z DIV p - 1)))`;;
let NV_MZ_HYP_KM = `forall p u. prime p /\ 260 < p /\ u <= 65 * p
                       ==> nv_pint p (cat_kminus (u DIV p)) /\
                           nv_cong p (&p pow 2 * cat_kminus u)
                             (nv_E (p - 1 - u MOD p) * cat_kminus (u DIV p))`;;
let NV_MZ_HYP_KP = `forall p u. prime p /\ 260 < p /\ u <= 65 * p
                       ==> nv_pint p (cat_kplus (u DIV p + 1)) /\
                           nv_cong p (&p pow 2 * cat_kplus (u + 1))
                             (nv_E (u MOD p) * cat_kplus (u DIV p + 1))`;;

let NV_MZ_E_PINT = prove
 (mk_imp(NV_MZ_HYP_C, `forall p d. prime p /\ 260 < p ==> nv_pint p (nv_E d)`),
  REPEAT STRIP_TAC THEN REWRITE_TAC[nv_E] THEN COND_CASES_TAC THEN
  ASM_SIMP_TAC[NV_PINT_0] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[] THEN UNDISCH_TAC `260 < p` THEN ARITH_TAC);;

let NV_MZ_M_PINT = prove
 (mk_imp(NV_MZ_HYP_M, `forall p n. prime p /\ 260 < p /\ n < 65 ==> nv_pint p (cat_m n)`),
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(p = 0)` ASSUME_TAC THENL [ASM_MESON_TAC[PRIME_0]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`p:num`; `p * (n + 1)`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [REWRITE_TAC[ARITH_RULE `1 <= x <=> ~(x = 0)`; MULT_EQ_0] THEN
      ASM_REWRITE_TAC[] THEN ARITH_TAC;
      GEN_REWRITE_TAC RAND_CONV [MULT_SYM] THEN REWRITE_TAC[LE_MULT_LCANCEL] THEN
      UNDISCH_TAC `n < 65` THEN ARITH_TAC];
    ASM_SIMP_TAC[DIV_MULT; ARITH_RULE `~(n + 1 = 0)`; ADD_SUB]]);;

let NV_MZ_PM_PINT = prove
 (mk_imp(NV_MZ_HYP_C, mk_imp(NV_MZ_HYP_M,
   `forall p z. prime p /\ 260 < p /\ 1 <= z /\ z <= 65 * p ==> nv_pint p (&p * cat_m (z - 1))`)),
  REPEAT DISCH_TAC THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`p:num`; `z:num`]) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN MATCH_MP_TAC NV_CONG_PINT THEN
  EXISTS_TAC `nv_E (p - 1 - z MOD p) * (if z DIV p = 0 then &0 else cat_m (z DIV p - 1))` THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC NV_PINT_MUL THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(UNDISCH NV_MZ_E_PINT) THEN ASM_SIMP_TAC[]);;


let NV_MZ_CASE_A = prove
 (mk_imp(NV_MZ_HYP_C, mk_imp(NV_MZ_HYP_M, mk_imp(NV_MZ_HYP_KM,
  `forall p i j. prime p /\ 260 < p /\ j <= i /\ i < 65 * p
    ==> nv_pint p (cat_M0 (j DIV p + (i - j) DIV p) (j DIV p)) /\
        nv_cong p (&p pow 2 * cat_M0 i j)
          (nv_E (p - 1 - (i - j) MOD p) * cat_M0 (j DIV p + (i - j) DIV p) (j DIV p))`))),
  DISCH_TAC THEN DISCH_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(p = 0)` ASSUME_TAC THENL [ASM_MESON_TAC[PRIME_0]; ALL_TAC] THEN
  SUBGOAL_THEN `~(&p = &0)` ASSUME_TAC THENL [ASM_SIMP_TAC[NV_PRIME_NZ]; ALL_TAC] THEN
  SUBGOAL_THEN `(i - j) + j = i:num` ASSUME_TAC THENL
   [UNDISCH_TAC `j <= i:num` THEN ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`i - j:num`; `p:num`] DIVISION) THEN
  MP_TAC(SPECL [`j:num`; `p:num`] DIVISION) THEN ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `u = i - j:num` THEN ABBREV_TAC `P = u DIV p` THEN
  ABBREV_TAC `r = u MOD p` THEN ABBREV_TAC `J = j DIV p` THEN
  ABBREV_TAC `t = j MOD p` THEN
  REPEAT(DISCH_THEN(STRIP_ASSUME_TAC o GSYM)) THEN
  SUBGOAL_THEN `P + J < 65:num` ASSUME_TAC THENL
   [SUBGOAL_THEN `(P + J) * p < 65 * p:num` MP_TAC THENL
     [MATCH_MP_TAC LET_TRANS THEN EXISTS_TAC `i:num` THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `P * p + r = u:num` THEN UNDISCH_TAC `J * p + t = j:num` THEN
      UNDISCH_TAC `u + j = i:num` THEN ARITH_TAC;
      REWRITE_TAC[LT_MULT_RCANCEL] THEN SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `u <= 65 * p:num` ASSUME_TAC THENL
   [UNDISCH_TAC `u + j = i:num` THEN UNDISCH_TAC `i < 65 * p` THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `forall k. 1 <= k /\ k < 65 ==> nv_pint p (inv(&k))` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC NV_MZ_PINT_INV_SMALL THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `1 <= k` THEN UNDISCH_TAC `k < 65` THEN UNDISCH_TAC `260 < p` THEN
    ARITH_TAC; ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o SPECL [`p:num`; `u:num`] o
    check (fun th -> can (find_term ((=) `cat_kminus`)) (concl th))) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[ASSUME `u DIV p = P`; ASSUME `u MOD p = r`] THEN STRIP_TAC THEN
  REWRITE_TAC[cat_M0; ARITH_RULE `J <= J + P:num`; ARITH_RULE `(J + P) - J = P:num`] THEN
  ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC NV_PINT_SUB THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC NV_PINT_SUM THEN ASM_REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
    X_GEN_TAC `k:num` THEN STRIP_TAC THEN REWRITE_TAC[real_div] THEN
    MATCH_MP_TAC NV_PINT_MUL THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC(UNDISCH NV_MZ_M_PINT) THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `P + J < 65` THEN UNDISCH_TAC `k <= J:num` THEN ARITH_TAC;
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `P + J < 65` THEN UNDISCH_TAC `k <= J:num` THEN ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[REAL_SUB_LDISTRIB; GSYM SUM_LMUL] THEN
  MATCH_MP_TAC NV_CONG_SUB THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`p:num`; `\k. &p pow 2 * cat_m (u + k - 1) / &k`; `0`; `j:num`]
    NV_MZ_SUM_MULT) THEN
  REWRITE_TAC[ADD_CLAUSES; DIV_0] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `&p pow 2 * cat_m (u + k - 1) / &k =
                  &p * ((&p * cat_m ((u + k) - 1)) * inv(&k))` SUBST1_TAC THENL
     [SUBGOAL_THEN `u + k - 1 = (u + k) - 1:num` SUBST1_TAC THENL
       [UNDISCH_TAC `1 <= k` THEN ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[real_div; REAL_POW_2] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC NV_CONG_PMUL_0 THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC NV_PINT_MUL THEN ASM_SIMP_TAC[NV_MZ_PINT_INV_NDIV] THEN
    MP_TAC(UNDISCH(UNDISCH NV_MZ_PM_PINT)) THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `1 <= k` THEN UNDISCH_TAC `k <= j:num` THEN
    UNDISCH_TAC `u + j = i:num` THEN UNDISCH_TAC `i < 65 * p` THEN ARITH_TAC;
    ALL_TAC] THEN
  DISCH_TAC THEN MATCH_MP_TAC NV_CONG_TRANS THEN
  FIRST_X_ASSUM(fun th -> EXISTS_TAC (rand(concl th)) THEN REWRITE_TAC[th]) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC NV_CONG_SUM THEN
  ASM_REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN X_GEN_TAC `m:num` THEN STRIP_TAC THEN
  REWRITE_TAC[] THEN
  SUBGOAL_THEN `1 <= u + p * m:num /\ u + p * m <= 65 * p /\
                (u + p * m) MOD p = r /\ (u + p * m) DIV p = P + m`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `u + p * m = (P + m) * p + r:num` SUBST1_TAC THENL
     [UNDISCH_TAC `P * p + r = u:num` THEN ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[MOD_MULT_ADD; DIV_MULT_ADD; MOD_LT; DIV_LT; ADD_CLAUSES] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC(ARITH_RULE `1 * 1 <= a * b ==> 1 <= a * b + r:num`) THEN
      MATCH_MP_TAC LE_MULT2 THEN UNDISCH_TAC `1 <= m` THEN UNDISCH_TAC `~(p = 0)` THEN
      ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `p * m <= j:num` MP_TAC THENL
     [MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `p * J:num` THEN
      ASM_REWRITE_TAC[LE_MULT_LCANCEL] THEN UNDISCH_TAC `J * p + t = j:num` THEN
      ARITH_TAC;
      ALL_TAC] THEN
    UNDISCH_TAC `u + j = i:num` THEN UNDISCH_TAC `i < 65 * p` THEN
    UNDISCH_TAC `P * p + r = u:num` THEN ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`p:num`; `u + p * m:num`] o
    check (fun th -> can (find_term ((=) `cat_m`)) (concl th) &&
                     is_forall (concl th))) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[ASSUME `(u + p * m) DIV p = P + m`; ASSUME `(u + p * m) MOD p = r`] THEN
  SUBGOAL_THEN `~(P + m = 0:num)` (fun th -> REWRITE_TAC[th]) THENL
   [UNDISCH_TAC `1 <= m` THEN ARITH_TAC; ALL_TAC] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `&p pow 2 * cat_m (u + p * m - 1) / &(p * m) =
                inv(&m) * (&p * cat_m ((u + p * m) - 1))` SUBST1_TAC THENL
   [SUBGOAL_THEN `u + p * m - 1 = (u + p * m) - 1:num` SUBST1_TAC THENL
     [SUBGOAL_THEN `1 <= p * m:num` MP_TAC THENL
       [MATCH_MP_TAC(ARITH_RULE `1 * 1 <= a * b ==> 1 <= a * b:num`) THEN
        MATCH_MP_TAC LE_MULT2 THEN UNDISCH_TAC `1 <= m` THEN UNDISCH_TAC `~(p = 0)` THEN
        ARITH_TAC; ARITH_TAC];
      ALL_TAC] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_MUL; real_div; REAL_POW_2; REAL_INV_MUL] THEN
    UNDISCH_TAC `~(&p = &0)` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  SUBGOAL_THEN `nv_E (p - 1 - r) * cat_m (P + m - 1) / &m =
                inv(&m) * (nv_E (p - 1 - r) * cat_m ((P + m) - 1))` SUBST1_TAC THENL
   [SUBGOAL_THEN `P + m - 1 = (P + m) - 1:num` SUBST1_TAC THENL
     [UNDISCH_TAC `1 <= m` THEN ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[real_div] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC NV_CONG_LMUL THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `P + J < 65` THEN UNDISCH_TAC `m <= J:num` THEN ARITH_TAC);;


let NV_MZ_SUM_SHIFT = prove
 (`forall P K x. (x = P \/ x = P + 1)
     ==> sum(x + 1..K + P + 1)
           (\m. inv(&m) * (if m - P - 1 = 0 then &0 else cat_m((m - P - 1) - 1))) =
         sum(1..K) (\k. cat_m(k - 1) / &((P + 1) + k))`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN
   `sum((P + 1) + 1..K + P + 1)
      (\m. inv(&m) * (if m - P - 1 = 0 then &0 else cat_m((m - P - 1) - 1))) =
    sum(1..K) (\k. cat_m(k - 1) / &((P + 1) + k))` ASSUME_TAC THENL
   [SUBGOAL_THEN `(P + 1) + 1 = 1 + (P + 1) /\ K + P + 1 = K + (P + 1)`
    (fun th -> REWRITE_TAC[th]) THENL [ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[SUM_OFFSET] THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN
    X_GEN_TAC `k:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    SUBGOAL_THEN `(k + P + 1) - P - 1 = k:num` SUBST1_TAC THENL
     [ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `~(k = 0:num)` (fun th -> REWRITE_TAC[th]) THENL
     [UNDISCH_TAC `1 <= k:num` THEN ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[real_div; ARITH_RULE `(P + 1) + k = k + P + 1:num`] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  SIMP_TAC[SUM_CLAUSES_LEFT; ARITH_RULE `P + 1 <= K + P + 1:num`] THEN
  ASM_REWRITE_TAC[ARITH_RULE `(P + 1) - P - 1 = 0:num`] THEN REAL_ARITH_TAC);;


let NV_MZ_CASE_B = prove
 (mk_imp(NV_MZ_HYP_C, mk_imp(NV_MZ_HYP_M, mk_imp(NV_MZ_HYP_KP,
  `forall p i j. prime p /\ 260 < p /\ p <= i /\ i < j /\ j < 65 * p
    ==> nv_pint p (cat_M0 ((i + 1 + (j - (i + 1)) MOD p) DIV p - 1) (j DIV p)) /\
        nv_cong p (&p pow 2 * cat_M0 i j)
          (nv_E ((j - (i + 1)) MOD p) *
           cat_M0 ((i + 1 + (j - (i + 1)) MOD p) DIV p - 1) (j DIV p))`))),
  DISCH_TAC THEN DISCH_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(p = 0)` ASSUME_TAC THENL [ASM_MESON_TAC[PRIME_0]; ALL_TAC] THEN
  SUBGOAL_THEN `~(&p = &0)` ASSUME_TAC THENL [ASM_SIMP_TAC[NV_PRIME_NZ]; ALL_TAC] THEN
  SUBGOAL_THEN `(j - (i + 1)) + i + 1 = j:num /\ j - i = (j - (i + 1)) + 1`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `i < j:num` THEN ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`j - (i + 1):num`; `p:num`] DIVISION) THEN ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `u = j - (i + 1):num` THEN ABBREV_TAC `P = u DIV p` THEN
  ABBREV_TAC `r = u MOD p` THEN ABBREV_TAC `J = j DIV p` THEN
  ABBREV_TAC `X = (i + 1 + r) DIV p` THEN ABBREV_TAC `K = X - 1:num` THEN
  REPEAT(DISCH_THEN(STRIP_ASSUME_TAC o GSYM)) THEN
  SUBGOAL_THEN `J < 65:num` ASSUME_TAC THENL
   [EXPAND_TAC "J" THEN ASM_SIMP_TAC[RDIV_LT_EQ] THEN
    UNDISCH_TAC `j < 65 * p:num` THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `J = K + P + 1:num` ASSUME_TAC THENL
   [SUBGOAL_THEN `J = X + P:num` MP_TAC THENL
     [MAP_EVERY EXPAND_TAC ["J"; "X"] THEN
      SUBGOAL_THEN `j = (i + 1 + r) + P * p:num` SUBST1_TAC THENL
       [UNDISCH_TAC `u + i + 1 = j:num` THEN UNDISCH_TAC `P * p + r = u:num` THEN
        ARITH_TAC; ASM_SIMP_TAC[DIV_MULT_ADD]];
      ALL_TAC] THEN
    SUBGOAL_THEN `1 <= X:num` MP_TAC THENL
     [EXPAND_TAC "X" THEN ASM_SIMP_TAC[LE_RDIV_EQ] THEN
      UNDISCH_TAC `p <= i:num` THEN ARITH_TAC; ALL_TAC] THEN
    EXPAND_TAC "K" THEN ARITH_TAC; ALL_TAC] THEN
  UNDISCH_TAC `J = K + P + 1:num` THEN DISCH_THEN SUBST_ALL_TAC THEN
  SUBGOAL_THEN `u <= 65 * p:num` ASSUME_TAC THENL
   [UNDISCH_TAC `u + i + 1 = j:num` THEN UNDISCH_TAC `j < 65 * p:num` THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `forall k. 1 <= k /\ k < 65 ==> nv_pint p (inv(&k))` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC NV_MZ_PINT_INV_SMALL THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `1 <= k` THEN UNDISCH_TAC `k < 65` THEN UNDISCH_TAC `260 < p` THEN
    ARITH_TAC; ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o SPECL [`p:num`; `u:num`] o
    check (fun th -> can (find_term ((=) `cat_kplus`)) (concl th))) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[ASSUME `u DIV p = P`; ASSUME `u MOD p = r`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(j <= i:num)` ASSUME_TAC THENL
   [UNDISCH_TAC `i < j:num` THEN ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[cat_M0; ARITH_RULE `~(K + P + 1 <= K:num)`;
                  ARITH_RULE `(K + P + 1) - K = P + 1:num`] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC NV_PINT_SUB THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC NV_PINT_SUM THEN ASM_REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
    X_GEN_TAC `k:num` THEN STRIP_TAC THEN REWRITE_TAC[real_div] THEN
    MATCH_MP_TAC NV_PINT_MUL THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC(UNDISCH NV_MZ_M_PINT) THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `K + P + 1 < 65:num` THEN
      UNDISCH_TAC `k <= K:num` THEN ARITH_TAC;
      FIRST_X_ASSUM MATCH_MP_TAC THEN
      UNDISCH_TAC `K + P + 1 < 65:num` THEN
      UNDISCH_TAC `k <= K:num` THEN ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[REAL_SUB_LDISTRIB; GSYM SUM_LMUL] THEN
  MATCH_MP_TAC NV_CONG_SUB THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `sum(1..i) (\k. &p pow 2 * cat_m (k - 1) / &((u + 1) + k)) =
    sum((u + 1) + 1..(u + 1) + i) (\k. &p pow 2 * cat_m ((k - (u + 1)) - 1) / &k)`
  SUBST1_TAC THENL
   [SUBGOAL_THEN `(u + 1) + 1 = 1 + (u + 1) /\ (u + 1) + i = i + (u + 1)`
    (fun th -> REWRITE_TAC[th]) THENL [ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[SUM_OFFSET] THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN
    X_GEN_TAC `k:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    REWRITE_TAC[ARITH_RULE `(k + u + 1) - (u + 1) = k:num`;
                ARITH_RULE `(u + 1) + k = k + u + 1:num`];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`p:num`; `\k. &p pow 2 * cat_m ((k - (u + 1)) - 1) / &k`;
                 `u + 1:num`; `i:num`] NV_MZ_SUM_MULT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `k:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    SUBGOAL_THEN `&p pow 2 * cat_m ((k - (u + 1)) - 1) / &k =
                  &p * ((&p * cat_m ((k - (u + 1)) - 1)) * inv(&k))` SUBST1_TAC THENL
     [REWRITE_TAC[real_div; REAL_POW_2] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC NV_CONG_PMUL_0 THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC NV_PINT_MUL THEN ASM_SIMP_TAC[NV_MZ_PINT_INV_NDIV] THEN
    MP_TAC(UNDISCH(UNDISCH NV_MZ_PM_PINT)) THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(u + 1) + 1 <= k:num` THEN UNDISCH_TAC `k <= (u + 1) + i:num` THEN
    UNDISCH_TAC `i < j:num` THEN UNDISCH_TAC `j < 65 * p:num` THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(u + 1) + i = j:num` (fun th -> REWRITE_TAC[th]) THENL
   [UNDISCH_TAC `u + i + 1 = j:num` THEN ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN MATCH_MP_TAC NV_CONG_TRANS THEN
  FIRST_X_ASSUM(fun th -> EXISTS_TAC (rand(concl th)) THEN REWRITE_TAC[th]) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(u + 1) DIV p = P \/ (u + 1) DIV p = P + 1` ASSUME_TAC THENL
   [MP_TAC(SPECL [`p:num`; `u:num`] NV_MZ_DIV_SUC) THEN ASM_REWRITE_TAC[] THEN
    MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `P <= (u + 1) DIV p /\ u + 1 < p * ((u + 1) DIV p + 1)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [UNDISCH_TAC `(u + 1) DIV p = P \/ (u + 1) DIV p = P + 1` THEN
                    ARITH_TAC; ALL_TAC] THEN
    MP_TAC(SPECL [`u + 1:num`; `p:num`] DIVISION) THEN ASM_REWRITE_TAC[] THEN
    ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `sum(1..K) (\k. nv_E r * cat_m(k - 1) / &((P + 1) + k)) =
    sum((u + 1) DIV p + 1..K + P + 1)
      (\m. nv_E r * (inv(&m) * (if m - P - 1 = 0 then &0 else cat_m((m - P - 1) - 1))))`
  SUBST1_TAC THENL
   [REWRITE_TAC[SUM_LMUL] THEN AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC NV_MZ_SUM_SHIFT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC NV_CONG_SUM THEN
  ASM_REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN X_GEN_TAC `m:num` THEN STRIP_TAC THEN
  REWRITE_TAC[] THEN
  SUBGOAL_THEN `p * ((u + 1) DIV p + 1) <= p * m /\ p * m <= j:num` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[LE_MULT_LCANCEL] THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `p * (K + P + 1):num` THEN
    ASM_REWRITE_TAC[LE_MULT_LCANCEL] THEN
    MP_TAC(SPECL [`j:num`; `p:num`] DIVISION) THEN ASM_REWRITE_TAC[] THEN
    ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `z = p * m - (u + 1):num` THEN
  SUBGOAL_THEN `(m - P - 1) * p + (p - 1 - r) = z:num` ASSUME_TAC THENL
   [EXPAND_TAC "z" THEN
    SUBGOAL_THEN `m = (m - P - 1) + P + 1:num` MP_TAC THENL
     [UNDISCH_TAC `(u + 1) DIV p + 1 <= m:num` THEN UNDISCH_TAC `P <= (u + 1) DIV p:num` THEN
      ARITH_TAC; ALL_TAC] THEN
    ABBREV_TAC `w = m - P - 1:num` THEN
    DISCH_THEN SUBST1_TAC THEN
    UNDISCH_TAC `P * p + r = u:num` THEN UNDISCH_TAC `r < p:num` THEN
    REWRITE_TAC[LEFT_ADD_DISTRIB; RIGHT_ADD_DISTRIB] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `1 <= z /\ z <= 65 * p /\ z MOD p = p - 1 - r /\ z DIV p = m - P - 1:num`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [REWRITE_TAC[SYM(ASSUME `p * m - (u + 1) = z:num`)] THEN
      UNDISCH_TAC `u + 1 < p * ((u + 1) DIV p + 1)` THEN
      UNDISCH_TAC `p * ((u + 1) DIV p + 1) <= p * m:num` THEN ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[SYM(ASSUME `p * m - (u + 1) = z:num`)] THEN
      UNDISCH_TAC `p * m <= j:num` THEN
      UNDISCH_TAC `j < 65 * p:num` THEN ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[SYM(ASSUME `(m - P - 1) * p + (p - 1 - r) = z:num`)] THEN
    SUBGOAL_THEN `p - 1 - r < p:num` ASSUME_TAC THENL
     [UNDISCH_TAC `~(p = 0)` THEN ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[MOD_MULT_ADD; DIV_MULT_ADD; MOD_LT; DIV_LT; ADD_CLAUSES];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`p:num`; `z:num`] o
    check (fun th -> can (find_term ((=) `cat_m`)) (concl th) &&
                     is_forall (concl th))) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[ASSUME `z DIV p = m - P - 1:num`; ASSUME `z MOD p = p - 1 - r:num`] THEN
  SUBGOAL_THEN `p - 1 - (p - 1 - r) = r:num` SUBST1_TAC THENL
   [UNDISCH_TAC `r < p:num` THEN ARITH_TAC; ALL_TAC] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `&p pow 2 * cat_m (z - 1) / &(p * m) =
                inv(&m) * (&p * cat_m (z - 1))` SUBST1_TAC THENL
   [REWRITE_TAC[GSYM REAL_OF_NUM_MUL; real_div; REAL_POW_2; REAL_INV_MUL] THEN
    UNDISCH_TAC `~(&p = &0)` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  GEN_REWRITE_TAC RAND_CONV [REAL_ARITH `e * (i * f):real = i * (e * f)`] THEN
  MATCH_MP_TAC NV_CONG_LMUL THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  UNDISCH_TAC `(u + 1) DIV p + 1 <= m:num` THEN UNDISCH_TAC `m <= K + P + 1:num` THEN
  UNDISCH_TAC `K + P + 1 < 65:num` THEN UNDISCH_TAC `P <= (u + 1) DIV p:num` THEN
  ARITH_TAC);;


let NV_MZ_MODCANCEL = prove
 (`forall p a x y. x < p /\ y < p /\ (a + x) MOD p = (a + y) MOD p ==> x = y`,
  REWRITE_TAC[GSYM CONG] THEN MESON_TAC[CONG_ADD_LCANCEL_EQ; CONG_IMP_EQ]);;

let NV_MZ_IDX_A = prove
 (`forall p i j d. ~(p = 0) /\ j <= i /\ d < p /\ (i + 1 + d) MOD p = j MOD p
     ==> d = p - 1 - (i - j) MOD p /\
         (i + 1 + d) DIV p - 1 = j DIV p + (i - j) DIV p`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`i - j:num`; `p:num`] DIVISION) THEN ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `P = (i - j) DIV p` THEN ABBREV_TAC `r = (i - j) MOD p` THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `(i + 1) + (p - 1 - r) = (P + 1) * p + j:num` ASSUME_TAC THENL
   [UNDISCH_TAC `i - j = P * p + r:num` THEN UNDISCH_TAC `j <= i:num` THEN
    UNDISCH_TAC `r < p:num` THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `d = p - 1 - r:num` ASSUME_TAC THENL
   [MATCH_MP_TAC NV_MZ_MODCANCEL THEN
    MAP_EVERY EXISTS_TAC [`p:num`; `i + 1:num`] THEN
    ASM_REWRITE_TAC[MOD_MULT_ADD; GSYM ADD_ASSOC] THEN
    UNDISCH_TAC `~(p = 0)` THEN ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[ADD_ASSOC] THEN ASM_SIMP_TAC[DIV_MULT_ADD] THEN ARITH_TAC);;

let NV_MZ_IDX_B = prove
 (`forall p i j d. ~(p = 0) /\ i < j /\ d < p /\ (i + 1 + d) MOD p = j MOD p
     ==> d = (j - (i + 1)) MOD p`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`j - (i + 1):num`; `p:num`] DIVISION) THEN ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `P = (j - (i + 1)) DIV p` THEN ABBREV_TAC `r = (j - (i + 1)) MOD p` THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `j = P * p + (i + 1) + r:num` ASSUME_TAC THENL
   [UNDISCH_TAC `j - (i + 1) = P * p + r:num` THEN UNDISCH_TAC `i < j:num` THEN
    ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC NV_MZ_MODCANCEL THEN
  MAP_EVERY EXISTS_TAC [`p:num`; `i + 1:num`] THEN
  ASM_REWRITE_TAC[GSYM ADD_ASSOC] THEN
  UNDISCH_TAC `(i + 1 + d) MOD p = j MOD p` THEN
  ASM_REWRITE_TAC[MOD_MULT_ADD; GSYM ADD_ASSOC]);;

let NV_MZ_M0_IMP = prove
 (mk_imp(list_mk_conj [NV_MZ_HYP_C; NV_MZ_HYP_M; NV_MZ_HYP_KM; NV_MZ_HYP_KP],
  `forall p i j d. prime p /\ 260 < p /\ p <= i /\ i < 65 * p /\ j < 65 * p /\
             d < p /\ (i + 1 + d) MOD p = j MOD p
     ==> nv_pint p (cat_M0 ((i + 1 + d) DIV p - 1) (j DIV p)) /\
         nv_cong p (&p pow 2 * cat_M0 i j)
           (nv_E d * cat_M0 ((i + 1 + d) DIV p - 1) (j DIV p))`),
  STRIP_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(p = 0)` ASSUME_TAC THENL [ASM_MESON_TAC[PRIME_0]; ALL_TAC] THEN
  ASM_CASES_TAC `j <= i:num` THENL
   [MP_TAC(SPECL [`p:num`; `i:num`; `j:num`; `d:num`] NV_MZ_IDX_A) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[CONJUNCT2 th] THEN SUBST1_TAC(CONJUNCT1 th)) THEN
    MP_TAC(UNDISCH(UNDISCH(UNDISCH NV_MZ_CASE_A))) THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    MP_TAC(SPECL [`p:num`; `i:num`; `j:num`; `d:num`] NV_MZ_IDX_B) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [UNDISCH_TAC `~(j <= i:num)` THEN ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN SUBST_ALL_TAC THEN
    MP_TAC(UNDISCH(UNDISCH(UNDISCH NV_MZ_CASE_B))) THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `~(j <= i:num)` THEN ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Interface forms.                                                          *)
(* ------------------------------------------------------------------------- *)

let NV_MZ_IF_Z0 = prove
 (`nv_if_z0`,
  REWRITE_TAC[nv_if_z0; NV_MZ_Z0]);;

let NV_MZ_IF_M0_IMP = prove
 (mk_imp(list_mk_conj [`nv_if_c_pint`; NV_MZ_HYP_M; NV_MZ_HYP_KM; NV_MZ_HYP_KP],
         `nv_if_m0`),
  REWRITE_TAC[nv_if_c_pint; nv_if_m0; NV_MZ_M0_IMP]);;
