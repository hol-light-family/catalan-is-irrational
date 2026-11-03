(* ========================================================================= *)
(* CAT_NONVANISHING, part P: Chebyshev polynomial functions, exact          *)
(* identities and the Frobenius congruences T_p == x^p, U_(p-1) == G.       *)
(*   nv_pal_T n x = T_n(x),  nv_pal_S n x = U_(n-1)(x)  (S_0 = 0).           *)
(* ========================================================================= *)

needs "src/catalan_nv_misc.ml";;
needs "src/catalan_nv_pal_poly.ml";;

let nv_pal_T = new_definition
 `nv_pal_T n (x:real) = sum(0..n) (\k. cheb_T n k * x pow k)`;;

let nv_pal_S = new_definition
 `nv_pal_S n (x:real) =
    if n = 0 then &0 else sum(0..n-1) (\k. cheb_U (n-1) k * x pow k)`;;

(* ------------------------------------------------------------------------- *)
(* Recurrences.                                                              *)
(* ------------------------------------------------------------------------- *)

let NV_PAL_POLY_SHIFT = prove
 (`forall g:num->real n (y:real). 1 <= n ==>
    sum(0..n) (\k. (if k = 0 then &0 else g (k - 1)) * y pow k) =
    y * sum(0..n-1) (\k. g k * y pow k)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `exists m. n = m + 1` (CHOOSE_THEN SUBST1_TAC) THENL
   [EXISTS_TAC `n - 1` THEN UNDISCH_TAC `1 <= n` THEN ARITH_TAC; ALL_TAC] THEN
  GEN_REWRITE_TAC LAND_CONV
   [MATCH_MP SUM_CLAUSES_LEFT (SPEC `m + 1` LE_0)] THEN
  REWRITE_TAC[SUM_OFFSET; ADD_EQ_0; ARITH_EQ; ADD_SUB; REAL_MUL_LZERO;
              REAL_ADD_LID; REAL_POW_ADD; REAL_POW_1] THEN
  REWRITE_TAC[GSYM SUM_LMUL] THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN REAL_ARITH_TAC);;

let NV_PAL_POLY_REC = prove
 (`forall f:num->num->real d n (y:real).
    (forall k. f (SUC(SUC d)) k =
         (if k = 0 then &0 else &2 * f (SUC d) (k - 1)) - f d k) /\
    1 <= n
    ==> sum(0..n) (\k. f (SUC(SUC d)) k * y pow k) =
        &2 * y * sum(0..n-1) (\k. f (SUC d) k * y pow k) -
        sum(0..n) (\k. f d k * y pow k)`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[REAL_SUB_RDISTRIB; SUM_SUB_NUMSEG] THEN
  ASM_SIMP_TAC[NV_PAL_POLY_SHIFT] THEN REWRITE_TAC[GSYM SUM_LMUL] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN REAL_ARITH_TAC);;

let NV_PAL_T_REC = prove
 (`forall n x. nv_pal_T (n + 2) x = &2 * x * nv_pal_T (n + 1) x - nv_pal_T n x`,
  REPEAT GEN_TAC THEN REWRITE_TAC[nv_pal_T] THEN
  REWRITE_TAC[ARITH_RULE `n + 2 = SUC(SUC n) /\ n + 1 = SUC n`] THEN
  MP_TAC(ISPECL [`cheb_T`; `n:num`; `SUC(SUC n)`; `x:real`] NV_PAL_POLY_REC) THEN
  REWRITE_TAC[cheb_T; ARITH_RULE `1 <= SUC(SUC n) /\ SUC(SUC n) - 1 = SUC n`] THEN
  DISCH_THEN SUBST1_TAC THEN AP_TERM_TAC THEN
  MATCH_MP_TAC NV_PAL_TRUNC THEN SIMP_TAC[NV_CHEB_T_DEG] THEN ARITH_TAC);;

let NV_PAL_U_REC = prove
 (`forall n x. sum(0..n+2) (\k. cheb_U (n + 2) k * x pow k) =
         &2 * x * sum(0..n+1) (\k. cheb_U (n + 1) k * x pow k) -
         sum(0..n) (\k. cheb_U n k * x pow k)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[ARITH_RULE `n + 2 = SUC(SUC n) /\ n + 1 = SUC n`] THEN
  MP_TAC(ISPECL [`cheb_U`; `n:num`; `SUC(SUC n)`; `x:real`] NV_PAL_POLY_REC) THEN
  REWRITE_TAC[cheb_U; ARITH_RULE `1 <= SUC(SUC n) /\ SUC(SUC n) - 1 = SUC n`] THEN
  DISCH_THEN SUBST1_TAC THEN AP_TERM_TAC THEN
  MATCH_MP_TAC NV_PAL_TRUNC THEN SIMP_TAC[NV_CHEB_U_DEG] THEN ARITH_TAC);;

let NV_PAL_T_0 = prove
 (`forall x. nv_pal_T 0 x = &1`,
  REWRITE_TAC[nv_pal_T; SUM_SING_NUMSEG; cheb_T; real_pow; REAL_MUL_LID]);;

let NV_PAL_T_1 = prove
 (`forall x. nv_pal_T 1 x = x`,
  REWRITE_TAC[nv_pal_T; num_CONV `1`; SUM_CLAUSES_NUMSEG; cheb_T] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[real_pow] THEN REAL_ARITH_TAC);;

let NV_PAL_S_0 = prove
 (`forall x. nv_pal_S 0 x = &0`,
  REWRITE_TAC[nv_pal_S]);;

let NV_PAL_S_1 = prove
 (`forall x. nv_pal_S 1 x = &1`,
  REWRITE_TAC[nv_pal_S; ARITH_RULE `~(1 = 0) /\ 1 - 1 = 0`;
              SUM_SING_NUMSEG; cheb_U; real_pow; REAL_MUL_LID]);;

let NV_PAL_S_REC = prove
 (`forall n x. nv_pal_S (n + 2) x = &2 * x * nv_pal_S (n + 1) x - nv_pal_S n x`,
  GEN_TAC THEN STRUCT_CASES_TAC(SPEC `n:num` num_CASES) THEN GEN_TAC THENL
   [REWRITE_TAC[ADD_CLAUSES; NV_PAL_S_0; NV_PAL_S_1] THEN
    REWRITE_TAC[nv_pal_S] THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[num_CONV `1`; SUM_CLAUSES_NUMSEG] THEN
    REWRITE_TAC[cheb_U; LE_0] THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[real_pow] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[nv_pal_S; ARITH_RULE `~(SUC m + 2 = 0) /\ ~(SUC m + 1 = 0) /\
    ~(SUC m = 0) /\ (SUC m + 2) - 1 = m + 2 /\ (SUC m + 1) - 1 = m + 1 /\
    SUC m - 1 = m`] THEN
  REWRITE_TAC[NV_PAL_U_REC]);;

let NV_PAL_T_2 = prove
 (`forall x. nv_pal_T 2 x = &2 * x pow 2 - &1`,
  GEN_TAC THEN MP_TAC(SPECL [`0`; `x:real`] NV_PAL_T_REC) THEN
  REWRITE_TAC[ARITH; NV_PAL_T_0; NV_PAL_T_1] THEN REAL_ARITH_TAC);;

let NV_PAL_S_2 = prove
 (`forall x. nv_pal_S 2 x = &2 * x`,
  GEN_TAC THEN MP_TAC(SPECL [`0`; `x:real`] NV_PAL_S_REC) THEN
  REWRITE_TAC[ARITH; NV_PAL_S_0; NV_PAL_S_1] THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Integrality.                                                              *)
(* ------------------------------------------------------------------------- *)

let NV_PAL_T_IP = prove
 (`forall p n. prime p ==> nv_pal_ip p (\x. nv_pal_T n x)`,
  SIMP_TAC[nv_pal_T; NV_PAL_IP_INTPOLY; NV_CHEB_INT]);;

let NV_PAL_S_IP = prove
 (`forall p n. prime p ==> nv_pal_ip p (\x. nv_pal_S n x)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[nv_pal_S] THEN
  ASM_CASES_TAC `n = 0` THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[NV_PAL_IP_INTPOLY; NV_CHEB_INT; NV_PAL_IP_CONST; NV_PINT_0]);;

let NV_PAL_T_IP_ETA = prove
 (`forall p n. prime p ==> nv_pal_ip p (nv_pal_T n)`,
  REPEAT STRIP_TAC THEN MP_TAC(SPECL [`p:num`; `n:num`] NV_PAL_T_IP) THEN
  ASM_REWRITE_TAC[ETA_AX]);;

let NV_PAL_S_IP_ETA = prove
 (`forall p n. prime p ==> nv_pal_ip p (nv_pal_S n)`,
  REPEAT STRIP_TAC THEN MP_TAC(SPECL [`p:num`; `n:num`] NV_PAL_S_IP) THEN
  ASM_REWRITE_TAC[ETA_AX]);;

(* A tactic proving nv_pal_ip goals built from the usual operations; it    *)
(* expects `prime p` among the assumptions.                                *)

let NV_PAL_PINT_TAC =
  REPEAT(FIRST [FIRST_ASSUM MATCH_ACCEPT_TAC; CONJ_TAC; COND_CASES_TAC;
    MATCH_MP_TAC NV_PINT_NUM; MATCH_MP_TAC NV_PINT_NEG;
    MATCH_MP_TAC NV_PINT_ADD; MATCH_MP_TAC NV_PINT_SUB;
    MATCH_MP_TAC NV_PINT_MUL; MATCH_MP_TAC NV_PINT_POW]);;

let NV_PAL_IP_TAC =
  REPEAT(FIRST [FIRST_ASSUM MATCH_ACCEPT_TAC; CONJ_TAC;
    MATCH_MP_TAC NV_PAL_T_IP; MATCH_MP_TAC NV_PAL_S_IP;
    MATCH_MP_TAC NV_PAL_T_IP_ETA; MATCH_MP_TAC NV_PAL_S_IP_ETA;
    MATCH_MP_TAC NV_PAL_IP_X;
    MATCH_MP_TAC NV_PAL_IP_CONST THEN NV_PAL_PINT_TAC;
    MATCH_MP_TAC NV_PAL_IP_ADD; MATCH_MP_TAC NV_PAL_IP_SUB;
    MATCH_MP_TAC NV_PAL_IP_MUL; MATCH_MP_TAC NV_PAL_IP_NEG;
    MATCH_MP_TAC NV_PAL_IP_POW;
    MATCH_MP_TAC NV_PAL_IP_SUM THEN REWRITE_TAC[FINITE_NUMSEG] THEN
      CONJ_TAC THENL [FIRST_ASSUM MATCH_ACCEPT_TAC; ALL_TAC] THEN
      GEN_TAC THEN DISCH_TAC THEN BETA_TAC;
    MATCH_MP_TAC NV_PAL_IP_COMPOSE]);;

(* ------------------------------------------------------------------------- *)
(* Binet form and the exact identities (first for x > 1).                    *)
(* ------------------------------------------------------------------------- *)

let NV_PAL_BINET = prove
 (`forall x y. y pow 2 = x pow 2 - &1
         ==> forall n. nv_pal_T n x + y * nv_pal_S n x = (x + y) pow n`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `forall n. (nv_pal_T n x + y * nv_pal_S n x = (x + y) pow n) /\
                    (nv_pal_T (n + 1) x + y * nv_pal_S (n + 1) x =
                     (x + y) pow (n + 1))`
   (fun th -> MESON_TAC[th]) THEN
  INDUCT_TAC THENL
   [REWRITE_TAC[ARITH; NV_PAL_T_0; NV_PAL_T_1; NV_PAL_S_0; NV_PAL_S_1] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  POP_ASSUM STRIP_ASSUME_TAC THEN ASM_REWRITE_TAC[ADD1] THEN
  REWRITE_TAC[ARITH_RULE `(n + 1) + 1 = n + 2`; NV_PAL_T_REC; NV_PAL_S_REC] THEN
  REPEAT(POP_ASSUM MP_TAC) THEN REWRITE_TAC[REAL_POW_ADD; REAL_POW_1] THEN
  CONV_TAC REAL_RING);;

let NV_PAL_SQRT_EX = prove
 (`forall x. &1 < x ==> exists y. y pow 2 = x pow 2 - &1 /\ ~(y = &0)`,
  REPEAT STRIP_TAC THEN EXISTS_TAC `sqrt(x pow 2 - &1)` THEN
  SUBGOAL_THEN `&0 < x pow 2 - &1` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_SUB_LT] THEN
    MATCH_MP_TAC(REAL_ARITH `&1 < x /\ &1 * x < x * x ==> &1 < x pow 2`) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LT_RMUL THEN ASM_REAL_ARITH_TAC;
    ASM_SIMP_TAC[SQRT_POW_2; REAL_LT_IMP_LE; SQRT_EQ_0] THEN
    ASM_REAL_ARITH_TAC]);;

let NV_PAL_COMB = prove
 (`forall y a b c d:real. ~(y = &0) /\ a + y * b = c + y * d /\ a + --y * b = c + --y * d
         ==> a = c /\ b = d`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `y * (b - d) = &0` MP_TAC THENL
   [UNDISCH_TAC `a + y * b = c + y * d:real` THEN
    UNDISCH_TAC `a + --y * b = c + --y * d:real` THEN REAL_ARITH_TAC;
    ASM_REWRITE_TAC[REAL_ENTIRE] THEN
    UNDISCH_TAC `a + y * b = c + y * d:real` THEN CONV_TAC REAL_RING]);;

let NV_PAL_BINET_TAC idx =
  MAP_EVERY (fun t ->
    MP_TAC(SPEC t (UNDISCH(SPECL [`x:real`; `y:real`] NV_PAL_BINET))) THEN
    MP_TAC(SPEC t (UNDISCH(SPECL [`x:real`; `--y:real`] NV_PAL_BINET)))) idx;;

let NV_PAL_GT_START0_TAC =
  DISCH_THEN(X_CHOOSE_THEN `y:real` STRIP_ASSUME_TAC o MATCH_MP NV_PAL_SQRT_EX) THEN
  SUBGOAL_THEN `(--y) pow 2 = x pow 2 - &1` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[REAL_POW_NEG; ARITH]; ALL_TAC];;

let NV_PAL_GT_START_TAC =
  GEN_TAC THEN
  DISCH_THEN(X_CHOOSE_THEN `y:real` STRIP_ASSUME_TAC o MATCH_MP NV_PAL_SQRT_EX) THEN
  SUBGOAL_THEN `(--y) pow 2 = x pow 2 - &1` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[REAL_POW_NEG; ARITH]; ALL_TAC];;

let NV_PAL_EXT_TAC gt =
  W(fun (asl,w) -> let l,r = dest_eq w in
     MP_TAC(ISPECL [`2`; mk_abs(`x:real`,l); mk_abs(`x:real`,r)] NV_PAL_IP_EXT)) THEN
  BETA_TAC THEN ASSUME_TAC PRIME_2 THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL [NV_PAL_IP_TAC; NV_PAL_IP_TAC; SIMP_TAC[gt]];
    SIMP_TAC[]];;

let NV_PAL_ADD_GT = prove
 (`forall a b x. &1 < x
     ==> nv_pal_T (a + b) x =
           nv_pal_T a x * nv_pal_T b x + (x pow 2 - &1) * nv_pal_S a x * nv_pal_S b x /\
         nv_pal_S (a + b) x = nv_pal_T a x * nv_pal_S b x + nv_pal_S a x * nv_pal_T b x`,
  GEN_TAC THEN GEN_TAC THEN NV_PAL_GT_START_TAC THEN
  MATCH_MP_TAC NV_PAL_COMB THEN EXISTS_TAC `y:real` THEN ASM_REWRITE_TAC[] THEN
  NV_PAL_BINET_TAC [`a + b:num`; `a:num`; `b:num`] THEN
  REWRITE_TAC[REAL_POW_ADD] THEN
  UNDISCH_TAC `y pow 2 = x pow 2 - &1` THEN CONV_TAC REAL_RING);;

let NV_PAL_ADD_T = prove
 (`forall a b x. nv_pal_T (a + b) x =
           nv_pal_T a x * nv_pal_T b x + (x pow 2 - &1) * nv_pal_S a x * nv_pal_S b x`,
  REPEAT GEN_TAC THEN NV_PAL_EXT_TAC NV_PAL_ADD_GT);;

let NV_PAL_ADD_S = prove
 (`forall a b x. nv_pal_S (a + b) x = nv_pal_T a x * nv_pal_S b x + nv_pal_S a x * nv_pal_T b x`,
  REPEAT GEN_TAC THEN NV_PAL_EXT_TAC NV_PAL_ADD_GT);;

let NV_PAL_LAMMU_TAC k =
  SUBGOAL_THEN (subst [k,`k:num`] `(x + y) pow k * (x + --y) pow k = &1`) MP_TAC THENL
   [REWRITE_TAC[GSYM REAL_POW_MUL] THEN
    SUBGOAL_THEN `(x + y) * (x + --y) = &1` (fun th -> REWRITE_TAC[th; REAL_POW_ONE]) THEN
    UNDISCH_TAC `y pow 2 = x pow 2 - &1` THEN CONV_TAC REAL_RING;
    ALL_TAC];;

let NV_PAL_STEP_GT = prove
 (`forall m k x. &1 < x
     ==> nv_pal_T (m + k + k) x = &2 * nv_pal_T k x * nv_pal_T (m + k) x - nv_pal_T m x /\
         nv_pal_S (m + k + k) x = &2 * nv_pal_T k x * nv_pal_S (m + k) x - nv_pal_S m x`,
  GEN_TAC THEN GEN_TAC THEN NV_PAL_GT_START_TAC THEN
  MATCH_MP_TAC NV_PAL_COMB THEN EXISTS_TAC `y:real` THEN ASM_REWRITE_TAC[] THEN
  NV_PAL_LAMMU_TAC `k:num` THEN
  NV_PAL_BINET_TAC [`m + k + k:num`; `m + k:num`; `m:num`; `k:num`] THEN
  REWRITE_TAC[REAL_POW_ADD] THEN
  UNDISCH_TAC `y pow 2 = x pow 2 - &1` THEN CONV_TAC REAL_RING);;

let NV_PAL_STEP_T = prove
 (`forall m k x. nv_pal_T (m + k + k) x = &2 * nv_pal_T k x * nv_pal_T (m + k) x - nv_pal_T m x`,
  REPEAT GEN_TAC THEN NV_PAL_EXT_TAC NV_PAL_STEP_GT);;

let NV_PAL_STEP_S = prove
 (`forall m k x. nv_pal_S (m + k + k) x = &2 * nv_pal_T k x * nv_pal_S (m + k) x - nv_pal_S m x`,
  REPEAT GEN_TAC THEN NV_PAL_EXT_TAC NV_PAL_STEP_GT);;

let NV_PAL_PELL_GT = prove
 (`forall k x. &1 < x
     ==> nv_pal_T k x pow 2 = &1 + (x pow 2 - &1) * nv_pal_S k x pow 2`,
  GEN_TAC THEN NV_PAL_GT_START_TAC THEN
  NV_PAL_LAMMU_TAC `k:num` THEN NV_PAL_BINET_TAC [`k:num`] THEN
  UNDISCH_TAC `y pow 2 = x pow 2 - &1` THEN CONV_TAC REAL_RING);;

let NV_PAL_PELL = prove
 (`forall k x. nv_pal_T k x pow 2 = &1 + (x pow 2 - &1) * nv_pal_S k x pow 2`,
  REPEAT GEN_TAC THEN NV_PAL_EXT_TAC NV_PAL_PELL_GT);;

(* ------------------------------------------------------------------------- *)
(* Binomial coefficients binom(p,k), 0 < k < p, are divisible by p.          *)
(* ------------------------------------------------------------------------- *)

let nv_pal_q = new_definition
 `nv_pal_q p k = if 0 < k /\ k < p then binom(p,k) DIV p else 0`;;

let NV_PAL_BINOM_TERM = prove
 (`forall p k (ff:real). prime p /\ k <= p
     ==> &(binom(p,k)) * ff =
         (if k = 0 then ff else &0) + (if k = p then ff else &0) +
         &p * (&(nv_pal_q p k) * ff)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(p = 0)` ASSUME_TAC THENL [ASM_MESON_TAC[PRIME_0]; ALL_TAC] THEN
  REWRITE_TAC[nv_pal_q] THEN ASM_CASES_TAC `k = 0` THENL
   [ASM_REWRITE_TAC[binom; LT_REFL] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `k = p:num` THENL
   [ASM_REWRITE_TAC[BINOM_REFL; LT_REFL] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `0 < k /\ k < p:num` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ASM_REWRITE_TAC[]] THEN
  MP_TAC(SPECL [`k:num`; `p:num`] DIVIDES_PRIME_BINOM) THEN
  ASM_REWRITE_TAC[DIVIDES_DIV_MULT] THEN
  DISCH_THEN(fun th -> GEN_REWRITE_TAC (LAND_CONV o LAND_CONV o RAND_CONV)
    [SYM th]) THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_MUL] THEN REAL_ARITH_TAC);;

let NV_PAL_BINOM_SUMSPLIT = prove
 (`forall p (ff:num->real). prime p
     ==> sum(0..p) (\k. &(binom(p,k)) * ff k) =
         ff 0 + ff p + &p * sum(0..p) (\k. &(nv_pal_q p k) * ff k)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `sum(0..p) (\k. &(binom(p,k)) * ff k) =
     sum(0..p) (\k. (if k = 0 then ff 0 else &0) + (if k = p then ff p else &0) +
                    &p * (&(nv_pal_q p k) * ff k))` SUBST1_TAC THENL
   [MATCH_MP_TAC SUM_EQ_NUMSEG THEN REPEAT STRIP_TAC THEN BETA_TAC THEN
    ASM_SIMP_TAC[NV_PAL_BINOM_TERM] THEN
    REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[SUM_ADD_NUMSEG; SUM_LMUL; SUM_DELTA; IN_NUMSEG; LE_0; LE_REFL]]);;

let NV_PAL_DIV2 = prove
 (`(forall m. (2 * m) DIV 2 = m) /\ (forall m. (SUC(2 * m)) DIV 2 = m)`,
  CONJ_TAC THEN GEN_TAC THEN MATCH_MP_TAC DIV_UNIQ THENL
   [EXISTS_TAC `0`; EXISTS_TAC `1`] THEN ARITH_TAC);;

let NV_PAL_POWPM = prove
 (`forall y k. y pow k + (--y) pow k =
         &2 * (if EVEN k then &1 else &0) * (y pow 2) pow (k DIV 2) /\
         y pow k - (--y) pow k =
         &2 * y * (if EVEN k then &0 else &1) * (y pow 2) pow (k DIV 2)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[REAL_POW_NEG] THEN
  ASM_CASES_TAC `EVEN k` THEN ASM_REWRITE_TAC[] THENL
   [FIRST_X_ASSUM(X_CHOOSE_THEN `m:num` SUBST1_TAC o REWRITE_RULE[EVEN_EXISTS]) THEN
    REWRITE_TAC[NV_PAL_DIV2; REAL_POW_POW] THEN REAL_ARITH_TAC;
    FIRST_X_ASSUM(X_CHOOSE_THEN `m:num` SUBST1_TAC o
      REWRITE_RULE[NOT_EVEN; ODD_EXISTS]) THEN
    REWRITE_TAC[NV_PAL_DIV2; REAL_POW_POW; real_pow] THEN REAL_ARITH_TAC]);;

let NV_PAL_ODD_DIV2 = prove
 (`forall p. ODD p ==> p DIV 2 = (p - 1) DIV 2 /\ ~EVEN p`,
  GEN_TAC THEN REWRITE_TAC[ODD_EXISTS] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[NV_PAL_DIV2; SUC_SUB1; EVEN; EVEN_DOUBLE]);;

(* ------------------------------------------------------------------------- *)
(* Frobenius congruences.                                                    *)
(* ------------------------------------------------------------------------- *)

let NV_PAL_FROB_LIN = prove
 (`forall p c. prime p /\ integer c
         ==> nv_pal_pc p (\x. (x + c) pow p) (\x. x pow p + c pow p)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `nv_pint p c` ASSUME_TAC THENL
   [ASM_SIMP_TAC[NV_PINT_INTEGER]; ALL_TAC] THEN
  REWRITE_TAC[nv_pal_pc] THEN
  EXISTS_TAC `\x. sum(0..p) (\k. &(nv_pal_q p k) * (x pow k * c pow (p - k)))` THEN
  CONJ_TAC THENL [NV_PAL_IP_TAC; ALL_TAC] THEN
  GEN_TAC THEN REWRITE_TAC[REAL_BINOMIAL_THEOREM] THEN
  ASM_SIMP_TAC[NV_PAL_BINOM_SUMSPLIT] THEN
  REWRITE_TAC[real_pow; SUB_0; SUB_REFL] THEN REAL_ARITH_TAC);;

let NV_PAL_FROB_T_GT = prove
 (`forall p x. prime p /\ ~(p = 2) /\ &1 < x
     ==> nv_pal_T p x =
         x pow p + &p * sum(0..p) (\k. &(nv_pal_q p k) *
           ((if EVEN(p - k) then &1 else &0) * (x pow 2 - &1) pow ((p - k) DIV 2) *
            x pow k))`,
  GEN_TAC THEN GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN DISCH_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `~EVEN p` ASSUME_TAC THENL
   [MP_TAC(SPEC `p:num` PRIME_ODD) THEN ASM_REWRITE_TAC[] THEN
    SIMP_TAC[NV_PAL_ODD_DIV2]; ALL_TAC] THEN
  NV_PAL_GT_START0_TAC THEN
  SUBGOAL_THEN `&2 * nv_pal_T p x = (x + y) pow p + (x + --y) pow p` MP_TAC THENL
   [NV_PAL_BINET_TAC [`p:num`] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(x + y) pow p + (x + --y) pow p =
     sum(0..p) (\k. &(binom(p,k)) * (&2 *
       ((if EVEN(p - k) then &1 else &0) * (x pow 2 - &1) pow ((p - k) DIV 2) *
        x pow k)))` SUBST1_TAC THENL
   [REWRITE_TAC[REAL_BINOMIAL_THEOREM; GSYM SUM_ADD_NUMSEG] THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN REPEAT STRIP_TAC THEN BETA_TAC THEN
    REWRITE_TAC[REAL_ARITH `b * u * v + b * u * w = (b * u) * (v + w:real)`;
                NV_PAL_POWPM] THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RING;
    ALL_TAC] THEN
  ASM_SIMP_TAC[NV_PAL_BINOM_SUMSPLIT] THEN
  REWRITE_TAC[REAL_ARITH `a * &2 * b = &2 * (a * b:real)`; SUM_LMUL] THEN
  ASM_REWRITE_TAC[SUB_0; SUB_REFL; EVEN] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[real_pow] THEN REAL_ARITH_TAC);;

let NV_PAL_FROB_S_GT = prove
 (`forall p x. prime p /\ ~(p = 2) /\ &1 < x
     ==> nv_pal_S p x =
         (x pow 2 - &1) pow ((p - 1) DIV 2) +
         &p * sum(0..p) (\k. &(nv_pal_q p k) *
           ((if EVEN(p - k) then &0 else &1) * (x pow 2 - &1) pow ((p - k) DIV 2) *
            x pow k))`,
  GEN_TAC THEN GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN DISCH_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `~EVEN p /\ p DIV 2 = (p - 1) DIV 2` STRIP_ASSUME_TAC THENL
   [MP_TAC(SPEC `p:num` PRIME_ODD) THEN ASM_REWRITE_TAC[] THEN
    SIMP_TAC[NV_PAL_ODD_DIV2]; ALL_TAC] THEN
  NV_PAL_GT_START0_TAC THEN
  SUBGOAL_THEN `&2 * y * nv_pal_S p x = (x + y) pow p - (x + --y) pow p` MP_TAC THENL
   [NV_PAL_BINET_TAC [`p:num`] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(x + y) pow p - (x + --y) pow p =
     y * sum(0..p) (\k. &(binom(p,k)) * (&2 *
       ((if EVEN(p - k) then &0 else &1) * (x pow 2 - &1) pow ((p - k) DIV 2) *
        x pow k)))` SUBST1_TAC THENL
   [REWRITE_TAC[REAL_BINOMIAL_THEOREM; GSYM SUM_SUB_NUMSEG; GSYM SUM_LMUL] THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN REPEAT STRIP_TAC THEN BETA_TAC THEN
    REWRITE_TAC[REAL_ARITH `b * u * v - b * u * w = (b * u) * (v - w:real)`;
                NV_PAL_POWPM] THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RING;
    ALL_TAC] THEN
  ASM_SIMP_TAC[NV_PAL_BINOM_SUMSPLIT] THEN
  REWRITE_TAC[REAL_ARITH `a * &2 * b = &2 * (a * b:real)`; SUM_LMUL] THEN
  ASM_REWRITE_TAC[SUB_0; SUB_REFL; EVEN] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[real_pow] THEN
  ABBREV_TAC `ss = sum (0..p) (\k. &(nv_pal_q p k) *
           ((if EVEN(p - k) then &0 else &1) * (x pow 2 - &1) pow ((p - k) DIV 2) *
            x pow k))` THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `y * (nv_pal_S p x - ((x pow 2 - &1) pow ((p - 1) DIV 2) + &p * ss)) = &0`
  MP_TAC THENL
   [POP_ASSUM MP_TAC THEN CONV_TAC REAL_RING;
    ASM_REWRITE_TAC[REAL_ENTIRE] THEN REAL_ARITH_TAC]);;

let NV_PAL_FROB_T = prove
 (`forall p. prime p /\ ~(p = 2) ==> nv_pal_pc p (\x. nv_pal_T p x) (\x. x pow p)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[nv_pal_pc] THEN
  ABBREV_TAC `h = \x. sum(0..p) (\k. &(nv_pal_q p k) *
           ((if EVEN(p - k) then &1 else &0) * (x pow 2 - &1) pow ((p - k) DIV 2) *
            x pow k))` THEN
  SUBGOAL_THEN `nv_pal_ip p h` ASSUME_TAC THENL
   [EXPAND_TAC "h" THEN NV_PAL_IP_TAC; ALL_TAC] THEN
  EXISTS_TAC `h:real->real` THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`p:num`; `\x. nv_pal_T p x`; `\x. x pow p + &p * (h:real->real) x`]
    NV_PAL_IP_EXT) THEN
  BETA_TAC THEN DISCH_THEN MATCH_MP_TAC THEN REPEAT CONJ_TAC THENL
   [NV_PAL_IP_TAC; NV_PAL_IP_TAC;
    EXPAND_TAC "h" THEN ASM_SIMP_TAC[NV_PAL_FROB_T_GT]]);;

let NV_PAL_FROB_S = prove
 (`forall p. prime p /\ ~(p = 2)
       ==> nv_pal_pc p (\x. nv_pal_S p x) (\x. (x pow 2 - &1) pow ((p - 1) DIV 2))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[nv_pal_pc] THEN
  ABBREV_TAC `h = \x. sum(0..p) (\k. &(nv_pal_q p k) *
           ((if EVEN(p - k) then &0 else &1) * (x pow 2 - &1) pow ((p - k) DIV 2) *
            x pow k))` THEN
  SUBGOAL_THEN `nv_pal_ip p h` ASSUME_TAC THENL
   [EXPAND_TAC "h" THEN NV_PAL_IP_TAC; ALL_TAC] THEN
  EXISTS_TAC `h:real->real` THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`p:num`; `\x. nv_pal_S p x`;
    `\x. (x pow 2 - &1) pow ((p - 1) DIV 2) + &p * (h:real->real) x`]
    NV_PAL_IP_EXT) THEN
  BETA_TAC THEN DISCH_THEN MATCH_MP_TAC THEN REPEAT CONJ_TAC THENL
   [NV_PAL_IP_TAC; NV_PAL_IP_TAC;
    EXPAND_TAC "h" THEN ASM_SIMP_TAC[NV_PAL_FROB_S_GT]]);;
