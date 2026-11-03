(* ========================================================================= *)
(* CAT_NONVANISHING: basic p-local arithmetic on the reals.                  *)
(*   nv_pint p x   : x is p-integral (x * n is an integer for some n with    *)
(*                   p not dividing n)                                       *)
(*   nv_cong p x y : (x - y) / p is p-integral, i.e. x == y (mod p)          *)
(* ========================================================================= *)

needs "src/catalan_defs.ml";;

let nv_pint = new_definition
 `nv_pint p x <=> exists n. ~(p divides n) /\ integer(&n * x)`;;

let nv_cong = new_definition
 `nv_cong p x y <=> nv_pint p ((x - y) / &p)`;;

(* Data used in the interface statements of the sub-parts.                   *)

let nv_a = new_definition
 `nv_a p l i = cheb_U (p - 1 - i) (p - 1 - l)`;;

let nv_b = new_definition
 `nv_b p l i = if i = 0 then &0 else cheb_U (i - 1) (p - 1 - l)`;;

let nv_E = new_definition
 `nv_E d = if EVEN d then cat_c (d DIV 2) else &0`;;

let nv_Ecoef = new_definition
 `nv_Ecoef p d = if EVEN d then (--(&1)) pow (d DIV 2) * &(binom((p - 1) DIV 2,d DIV 2))
                 else &0`;;

(* ------------------------------------------------------------------------- *)
(* p-integrality.                                                            *)
(* ------------------------------------------------------------------------- *)

let NV_PINT_INTEGER = prove
 (`forall p x. prime p /\ integer x ==> nv_pint p x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[nv_pint] THEN EXISTS_TAC `1` THEN
  ASM_REWRITE_TAC[DIVIDES_ONE; REAL_MUL_LID] THEN
  ASM_MESON_TAC[PRIME_1]);;

let NV_PINT_NUM = prove
 (`forall p n. prime p ==> nv_pint p (&n)`,
  MESON_TAC[NV_PINT_INTEGER; INTEGER_CLOSED]);;

let NV_PINT_0 = prove
 (`forall p. prime p ==> nv_pint p (&0)`,
  MESON_TAC[NV_PINT_NUM]);;

let NV_PINT_1 = prove
 (`forall p. prime p ==> nv_pint p (&1)`,
  MESON_TAC[NV_PINT_NUM]);;

let NV_PINT_NEG = prove
 (`forall p x. nv_pint p x ==> nv_pint p (--x)`,
  REWRITE_TAC[nv_pint] THEN MESON_TAC[REAL_MUL_RNEG; INTEGER_NEG]);;

let NV_PINT_NEG_EQ = prove
 (`forall p x. nv_pint p (--x) <=> nv_pint p x`,
  MESON_TAC[NV_PINT_NEG; REAL_NEG_NEG]);;

let NV_PINT_ADD = prove
 (`forall p x y. prime p /\ nv_pint p x /\ nv_pint p y ==> nv_pint p (x + y)`,
  REWRITE_TAC[nv_pint] THEN REPEAT STRIP_TAC THEN
  EXISTS_TAC `n * n':num` THEN
  ASM_SIMP_TAC[PRIME_DIVPROD_EQ; GSYM REAL_OF_NUM_MUL] THEN
  SUBGOAL_THEN `(&n * &n') * (x + y) = &n' * (&n * x) + &n * (&n' * y)`
  SUBST1_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_MESON_TAC[INTEGER_CLOSED]);;

let NV_PINT_SUB = prove
 (`forall p x y. prime p /\ nv_pint p x /\ nv_pint p y ==> nv_pint p (x - y)`,
  MESON_TAC[real_sub; NV_PINT_ADD; NV_PINT_NEG]);;

let NV_PINT_MUL = prove
 (`forall p x y. prime p /\ nv_pint p x /\ nv_pint p y ==> nv_pint p (x * y)`,
  REWRITE_TAC[nv_pint] THEN REPEAT STRIP_TAC THEN
  EXISTS_TAC `n * n':num` THEN
  ASM_SIMP_TAC[PRIME_DIVPROD_EQ; GSYM REAL_OF_NUM_MUL] THEN
  SUBGOAL_THEN `(&n * &n') * (x * y) = (&n * x) * (&n' * y)`
  SUBST1_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_MESON_TAC[INTEGER_CLOSED]);;

let NV_PINT_POW = prove
 (`forall p x k. prime p /\ nv_pint p x ==> nv_pint p (x pow k)`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN
  ASM_SIMP_TAC[real_pow; NV_PINT_1; NV_PINT_MUL]);;

let NV_PINT_INV_NUM = prove
 (`forall p n. prime p /\ ~(p divides n) ==> nv_pint p (inv(&n))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[nv_pint] THEN EXISTS_TAC `n:num` THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `~(n = 0)` ASSUME_TAC THENL
   [ASM_MESON_TAC[DIVIDES_0]; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_MUL_RINV; REAL_OF_NUM_EQ; INTEGER_CLOSED]);;

let NV_PINT_DIV_NUM = prove
 (`forall p x n. prime p /\ nv_pint p x /\ ~(p divides n) ==> nv_pint p (x / &n)`,
  SIMP_TAC[real_div; NV_PINT_MUL; NV_PINT_INV_NUM]);;

let NV_PINT_SUM = prove
 (`forall p (f:A->real) s. prime p /\ FINITE s /\ (forall i. i IN s ==> nv_pint p (f i))
           ==> nv_pint p (sum s f)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN DISCH_TAC THEN
  SPEC_TAC(`s:A->bool`,`s:A->bool`) THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  ASM_SIMP_TAC[SUM_CLAUSES; NV_PINT_0; IN_INSERT] THEN
  ASM_MESON_TAC[NV_PINT_ADD]);;

let NV_PINT_PRODUCT = prove
 (`forall p (f:A->real) s. prime p /\ FINITE s /\ (forall i. i IN s ==> nv_pint p (f i))
           ==> nv_pint p (product s f)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN DISCH_TAC THEN
  SPEC_TAC(`s:A->bool`,`s:A->bool`) THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  ASM_SIMP_TAC[PRODUCT_CLAUSES; NV_PINT_1; IN_INSERT] THEN
  ASM_MESON_TAC[NV_PINT_MUL]);;

let NV_INTEGER_DIV_PRIME = prove
 (`forall p n. prime p /\ integer(&n / &p) ==> p divides n`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `exists m. &n / &p = &m` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[INTEGER_POS; REAL_LE_DIV; REAL_POS]; ALL_TAC] THEN
  SUBGOAL_THEN `~(&p = &0)` ASSUME_TAC THENL
   [ASM_MESON_TAC[REAL_OF_NUM_EQ; PRIME_0]; ALL_TAC] THEN
  SUBGOAL_THEN `&n = &p * &m` MP_TAC THENL
   [UNDISCH_TAC `&n / &p = &m` THEN UNDISCH_TAC `~(&p = &0)` THEN CONV_TAC REAL_FIELD;
    REWRITE_TAC[REAL_OF_NUM_MUL; REAL_OF_NUM_EQ; divides] THEN MESON_TAC[]]);;

let NV_PINT_INV_P = prove
 (`forall p. prime p ==> ~(nv_pint p (inv(&p)))`,
  REWRITE_TAC[nv_pint] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE RAND_CONV [GSYM real_div]) THEN
  ASM_MESON_TAC[NV_INTEGER_DIV_PRIME]);;

(* ------------------------------------------------------------------------- *)
(* Rational numbers are p-integral for large p.                              *)
(* ------------------------------------------------------------------------- *)

let NV_PINT_RATIONAL = prove
 (`forall x. rational x ==> exists P. forall p. prime p /\ P <= p ==> nv_pint p x`,
  GEN_TAC THEN REWRITE_TAC[rational] THEN
  DISCH_THEN(X_CHOOSE_THEN `m:real` (X_CHOOSE_THEN `n:real` STRIP_ASSUME_TAC)) THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [integer] o
    check (fun th -> rand(concl th) = `n:real`)) THEN
  DISCH_THEN(X_CHOOSE_TAC `k:num`) THEN EXISTS_TAC `k + 1` THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[nv_pint] THEN EXISTS_TAC `k:num` THEN
  CONJ_TAC THENL
   [DISCH_THEN(MP_TAC o MATCH_MP DIVIDES_LE) THEN
    SUBGOAL_THEN `~(k = 0)` (fun th -> REWRITE_TAC[th]) THENL
     [ASM_MESON_TAC[REAL_ABS_ZERO; REAL_OF_NUM_EQ]; ASM_ARITH_TAC];
    ALL_TAC] THEN
  FIRST_X_ASSUM(DISJ_CASES_TAC o MATCH_MP (REAL_ARITH
   `abs n = &k ==> n = &k \/ n = -- &k`)) THEN
  ASM_REWRITE_TAC[] THENL
   [SUBGOAL_THEN `&k * m / &k = m` (fun th -> ASM_REWRITE_TAC[th]) THEN
    MATCH_MP_TAC REAL_DIV_LMUL THEN ASM_MESON_TAC[];
    SUBGOAL_THEN `&k * m / -- &k = --m` (fun th -> ASM_SIMP_TAC[th; INTEGER_NEG]) THEN
    UNDISCH_TAC `~(n = &0)` THEN ASM_REWRITE_TAC[] THEN CONV_TAC REAL_FIELD]);;

let NV_PUNIT_RATIONAL = prove
 (`forall x. rational x /\ ~(x = &0)
       ==> exists P. forall p. prime p /\ P <= p ==> nv_pint p x /\ nv_pint p (inv x)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `x:real` NV_PINT_RATIONAL) THEN
  MP_TAC(SPEC `inv x:real` NV_PINT_RATIONAL) THEN
  ASM_SIMP_TAC[RATIONAL_INV] THEN
  DISCH_THEN(X_CHOOSE_TAC `P1:num`) THEN DISCH_THEN(X_CHOOSE_TAC `P2:num`) THEN
  EXISTS_TAC `P1 + P2:num` THEN ASM_MESON_TAC[ARITH_RULE `P1 + P2 <= p:num ==> P1 <= p /\ P2 <= p`]);;

(* ------------------------------------------------------------------------- *)
(* Congruences modulo p.                                                     *)
(* ------------------------------------------------------------------------- *)

let NV_PRIME_NZ = prove
 (`forall p. prime p ==> ~(&p = &0)`,
  MESON_TAC[REAL_OF_NUM_EQ; PRIME_0]);;

let NV_CONG_REFL = prove
 (`forall p x. prime p ==> nv_cong p x x`,
  SIMP_TAC[nv_cong; REAL_SUB_REFL; real_div; REAL_MUL_LZERO; NV_PINT_0]);;

let NV_CONG_SYM = prove
 (`forall p x y. nv_cong p x y ==> nv_cong p y x`,
  REWRITE_TAC[nv_cong] THEN REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[REAL_ARITH `y - x:real = --(x - y)`] THEN
  ASM_REWRITE_TAC[real_div; REAL_MUL_LNEG; NV_PINT_NEG_EQ] THEN
  ASM_REWRITE_TAC[GSYM real_div]);;

let NV_CONG_SYM_EQ = prove
 (`forall p x y. nv_cong p x y <=> nv_cong p y x`,
  MESON_TAC[NV_CONG_SYM]);;

let NV_CONG_TRANS = prove
 (`forall p x y z. prime p /\ nv_cong p x y /\ nv_cong p y z ==> nv_cong p x z`,
  REWRITE_TAC[nv_cong] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(x - z) / &p = (x - y) / &p + (y - z) / &p` SUBST1_TAC THENL
   [REAL_ARITH_TAC; ASM_MESON_TAC[NV_PINT_ADD]]);;

let NV_CONG_ADD = prove
 (`forall p x x' y y'. prime p /\ nv_cong p x x' /\ nv_cong p y y'
                 ==> nv_cong p (x + y) (x' + y')`,
  REWRITE_TAC[nv_cong] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `((x + y) - (x' + y')) / &p = (x - x') / &p + (y - y') / &p`
  SUBST1_TAC THENL [REAL_ARITH_TAC; ASM_MESON_TAC[NV_PINT_ADD]]);;

let NV_CONG_NEG = prove
 (`forall p x x'. nv_cong p x x' ==> nv_cong p (--x) (--x')`,
  REWRITE_TAC[nv_cong] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(--x - --x') / &p = --((x - x') / &p)`
  SUBST1_TAC THENL [REAL_ARITH_TAC; ASM_MESON_TAC[NV_PINT_NEG]]);;

let NV_CONG_SUB = prove
 (`forall p x x' y y'. prime p /\ nv_cong p x x' /\ nv_cong p y y'
                 ==> nv_cong p (x - y) (x' - y')`,
  MESON_TAC[real_sub; NV_CONG_ADD; NV_CONG_NEG]);;

let NV_CONG_PINT = prove
 (`forall p x y. prime p /\ nv_cong p x y /\ nv_pint p y ==> nv_pint p x`,
  REWRITE_TAC[nv_cong] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `x = &p * (x - y) / &p + y` SUBST1_TAC THENL
   [UNDISCH_TAC `prime p` THEN DISCH_THEN(MP_TAC o MATCH_MP NV_PRIME_NZ) THEN
    CONV_TAC REAL_FIELD;
    ASM_MESON_TAC[NV_PINT_ADD; NV_PINT_MUL; NV_PINT_NUM]]);;

let NV_CONG_MUL = prove
 (`forall p x x' y y'. prime p /\ nv_pint p x' /\ nv_pint p y' /\
                 nv_cong p x x' /\ nv_cong p y y'
                 ==> nv_cong p (x * y) (x' * y')`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `nv_pint p x` ASSUME_TAC THENL
   [ASM_MESON_TAC[NV_CONG_PINT]; ALL_TAC] THEN
  REPEAT(POP_ASSUM MP_TAC) THEN REWRITE_TAC[nv_cong] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(x * y - x' * y') / &p = x * (y - y') / &p + y' * (x - x') / &p`
  SUBST1_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[real_div; GSYM REAL_MUL_ASSOC] THEN
  REWRITE_TAC[GSYM real_div] THEN ASM_MESON_TAC[NV_PINT_ADD; NV_PINT_MUL]);;

let NV_CONG_LMUL = prove
 (`forall p c x x'. prime p /\ nv_pint p c /\ nv_cong p x x'
              ==> nv_cong p (c * x) (c * x')`,
  REWRITE_TAC[nv_cong] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(c * x - c * x') / &p = c * (x - x') / &p` SUBST1_TAC THENL
   [REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[real_div; GSYM REAL_MUL_ASSOC] THEN
  REWRITE_TAC[GSYM real_div] THEN ASM_MESON_TAC[NV_PINT_MUL]);;

let NV_CONG_EQ_PMUL = prove
 (`forall p x y. prime p /\ nv_pint p y ==> nv_cong p (x + &p * y) x`,
  REWRITE_TAC[nv_cong] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `((x + &p * y) - x) / &p = y` (fun th -> ASM_REWRITE_TAC[th]) THEN
  UNDISCH_TAC `prime p` THEN DISCH_THEN(MP_TAC o MATCH_MP NV_PRIME_NZ) THEN
  CONV_TAC REAL_FIELD);;

let NV_CONG_PMUL_0 = prove
 (`forall p y. prime p /\ nv_pint p y ==> nv_cong p (&p * y) (&0)`,
  MESON_TAC[NV_CONG_EQ_PMUL; REAL_ADD_LID]);;

let NV_CONG_SUM = prove
 (`forall p (f:A->real) g s. prime p /\ FINITE s /\ (forall i. i IN s ==> nv_cong p (f i) (g i))
             ==> nv_cong p (sum s f) (sum s g)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN DISCH_TAC THEN
  SPEC_TAC(`s:A->bool`,`s:A->bool`) THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  ASM_SIMP_TAC[SUM_CLAUSES; NV_CONG_REFL; IN_INSERT] THEN
  ASM_MESON_TAC[NV_CONG_ADD]);;

let NV_CONG_PRODUCT = prove
 (`forall p (f:A->real) g s. prime p /\ FINITE s /\
             (forall i. i IN s ==> nv_pint p (g i) /\ nv_cong p (f i) (g i))
             ==> nv_cong p (product s f) (product s g)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN DISCH_TAC THEN
  SPEC_TAC(`s:A->bool`,`s:A->bool`) THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  ASM_SIMP_TAC[PRODUCT_CLAUSES; NV_CONG_REFL; IN_INSERT] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC NV_CONG_MUL THEN
  ASM_SIMP_TAC[] THEN MATCH_MP_TAC NV_PINT_PRODUCT THEN ASM_SIMP_TAC[]);;

let NV_CONG_0_IMP = prove
 (`forall p x. prime p /\ nv_cong p x (&0) /\ nv_pint p (inv x) ==> x = &0`,
  REWRITE_TAC[nv_cong; REAL_SUB_RZERO] THEN REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `x = &0` THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(SPEC `p:num` NV_PINT_INV_P) THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `inv(&p) = x / &p * inv x` SUBST1_TAC THENL
   [UNDISCH_TAC `~(x = &0)` THEN CONV_TAC REAL_FIELD;
    ASM_MESON_TAC[NV_PINT_MUL]]);;

let NV_CONG_UNIT_NZ = prove
 (`forall p x y. prime p /\ nv_cong p x y /\ nv_pint p (inv y) /\ ~(y = &0)
           ==> ~(x = &0)`,
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
  MP_TAC(SPECL [`p:num`; `y:real`] NV_CONG_0_IMP) THEN
  ASM_MESON_TAC[NV_CONG_SYM]);;

(* ------------------------------------------------------------------------- *)
(* Determinants of congruent arrays are congruent.                           *)
(* ------------------------------------------------------------------------- *)

let NV_SIGN_PINT = prove
 (`forall p q. prime p ==> nv_pint p (sign q)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[sign] THEN COND_CASES_TAC THEN
  ASM_SIMP_TAC[NV_PINT_1; NV_PINT_NEG]);;

let NV_NDET_PINT = prove
 (`forall p s a. prime p /\ FINITE s /\ (forall i j. i IN s /\ j IN s ==> nv_pint p (a i j))
           ==> nv_pint p (ndet s a)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[ndet] THEN
  MATCH_MP_TAC NV_PINT_SUM THEN ASM_SIMP_TAC[FINITE_PERMUTATIONS; IN_ELIM_THM] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC NV_PINT_MUL THEN
  ASM_SIMP_TAC[NV_SIGN_PINT] THEN MATCH_MP_TAC NV_PINT_PRODUCT THEN
  ASM_MESON_TAC[PERMUTES_IN_IMAGE]);;

let NV_NDET_CONG = prove
 (`forall p s a b. prime p /\ FINITE s /\
             (forall i j. i IN s /\ j IN s ==> nv_pint p (b i j) /\ nv_cong p (a i j) (b i j))
             ==> nv_cong p (ndet s a) (ndet s b)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[ndet] THEN
  MATCH_MP_TAC NV_CONG_SUM THEN ASM_SIMP_TAC[FINITE_PERMUTATIONS; IN_ELIM_THM] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC NV_CONG_LMUL THEN
  ASM_SIMP_TAC[NV_SIGN_PINT] THEN MATCH_MP_TAC NV_CONG_PRODUCT THEN
  ASM_MESON_TAC[PERMUTES_IN_IMAGE]);;
