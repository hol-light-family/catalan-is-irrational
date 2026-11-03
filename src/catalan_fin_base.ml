(* ========================================================================= *)
(* CAT_FINITE_PLACE: basic p-adic valuation tools on real numbers.           *)
(*                                                                           *)
(*   fin_zp p x     : x = m / n with m integer and p not dividing n          *)
(*   fin_vge p k x  : v_p(x) >= k (k real), i.e. x in p^ceil(k) Z_(p)        *)
(* ========================================================================= *)

needs "src/catalan_defs.ml";;
needs "Library/ring_det.ml";;

let fin_zp = new_definition
 `fin_zp p x <=> exists m n. integer m /\ ~(p divides n) /\ x = m / &n`;;

let fin_vge = new_definition
 `fin_vge p k x <=> exists a b. k <= &a - &b /\ fin_zp p (x * &p pow b / &p pow a)`;;

(* ------------------------------------------------------------------------- *)
(* Local integers.                                                           *)
(* ------------------------------------------------------------------------- *)

let FIN_NDIV_NZ = prove
 (`forall p n. ~(p divides n) ==> ~(&n = &0)`,
  REWRITE_TAC[REAL_OF_NUM_EQ] THEN MESON_TAC[DIVIDES_0]);;

let FIN_ZP_INTEGER = prove
 (`forall p x. prime p /\ integer x ==> fin_zp p x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[fin_zp] THEN
  MAP_EVERY EXISTS_TAC [`x:real`; `1`] THEN
  ASM_REWRITE_TAC[DIVIDES_ONE; REAL_DIV_1] THEN ASM_MESON_TAC[PRIME_1]);;

let FIN_ZP_NUM = prove
 (`forall p n. prime p ==> fin_zp p (&n)`,
  MESON_TAC[FIN_ZP_INTEGER; INTEGER_CLOSED]);;

let FIN_ZP_0 = prove
 (`forall p. prime p ==> fin_zp p (&0)`,
  MESON_TAC[FIN_ZP_NUM]);;

let FIN_ZP_1 = prove
 (`forall p. prime p ==> fin_zp p (&1)`,
  MESON_TAC[FIN_ZP_NUM]);;

let FIN_ZP_NEG = prove
 (`forall p x. fin_zp p x ==> fin_zp p (--x)`,
  REWRITE_TAC[fin_zp] THEN REPEAT STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`--m:real`; `n:num`] THEN
  ASM_SIMP_TAC[INTEGER_CLOSED] THEN REAL_ARITH_TAC);;

let FIN_ZP_NEG_EQ = prove
 (`forall p x. fin_zp p (--x) <=> fin_zp p x`,
  MESON_TAC[FIN_ZP_NEG; REAL_NEG_NEG]);;

let FIN_ZP_ADD = prove
 (`forall p x y. prime p /\ fin_zp p x /\ fin_zp p y ==> fin_zp p (x + y)`,
  REWRITE_TAC[fin_zp] THEN REPEAT STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`m * &n' + m' * &n:real`; `n * n':num`] THEN
  ASM_SIMP_TAC[INTEGER_CLOSED] THEN CONJ_TAC THENL
   [ASM_MESON_TAC[PRIME_DIVPROD]; ALL_TAC] THEN
  REPEAT(FIRST_X_ASSUM(ASSUME_TAC o MATCH_MP FIN_NDIV_NZ)) THEN
  ASM_REWRITE_TAC[GSYM REAL_OF_NUM_MUL] THEN
  REPEAT(POP_ASSUM MP_TAC) THEN CONV_TAC REAL_FIELD);;

let FIN_ZP_SUB = prove
 (`forall p x y. prime p /\ fin_zp p x /\ fin_zp p y ==> fin_zp p (x - y)`,
  SIMP_TAC[real_sub; FIN_ZP_ADD; FIN_ZP_NEG]);;

let FIN_ZP_MUL = prove
 (`forall p x y. prime p /\ fin_zp p x /\ fin_zp p y ==> fin_zp p (x * y)`,
  REWRITE_TAC[fin_zp] THEN REPEAT STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`m * m':real`; `n * n':num`] THEN
  ASM_SIMP_TAC[INTEGER_CLOSED] THEN CONJ_TAC THENL
   [ASM_MESON_TAC[PRIME_DIVPROD]; ALL_TAC] THEN
  REPEAT(FIRST_X_ASSUM(ASSUME_TAC o MATCH_MP FIN_NDIV_NZ)) THEN
  ASM_REWRITE_TAC[GSYM REAL_OF_NUM_MUL] THEN
  REPEAT(POP_ASSUM MP_TAC) THEN CONV_TAC REAL_FIELD);;

let FIN_ZP_POW = prove
 (`forall p x k. prime p /\ fin_zp p x ==> fin_zp p (x pow k)`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN
  ASM_SIMP_TAC[real_pow; FIN_ZP_1; FIN_ZP_MUL]);;

let FIN_ZP_DIV_NUM = prove
 (`forall p x n. prime p /\ fin_zp p x /\ ~(p divides n) ==> fin_zp p (x / &n)`,
  REWRITE_TAC[fin_zp] THEN REPEAT STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`m:real`; `n' * n:num`] THEN
  ASM_SIMP_TAC[INTEGER_CLOSED] THEN CONJ_TAC THENL
   [ASM_MESON_TAC[PRIME_DIVPROD]; ALL_TAC] THEN
  REPEAT(FIRST_X_ASSUM(ASSUME_TAC o MATCH_MP FIN_NDIV_NZ)) THEN
  ASM_REWRITE_TAC[GSYM REAL_OF_NUM_MUL] THEN
  REPEAT(POP_ASSUM MP_TAC) THEN CONV_TAC REAL_FIELD);;

let FIN_ZP_INV_NUM = prove
 (`forall p n. prime p /\ ~(p divides n) ==> fin_zp p (inv(&n))`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[REAL_ARITH `inv x = &1 / x`] THEN
  ASM_SIMP_TAC[FIN_ZP_DIV_NUM; FIN_ZP_1]);;

let FIN_ZP_SUM = prove
 (`forall p (f:A->real) s. prime p /\ FINITE s /\ (forall i. i IN s ==> fin_zp p (f i))
           ==> fin_zp p (sum s f)`,
  GEN_TAC THEN GEN_TAC THEN REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN DISCH_TAC THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  ASM_SIMP_TAC[SUM_CLAUSES; FIN_ZP_0; FORALL_IN_INSERT; FIN_ZP_ADD]);;

let FIN_ZP_PRODUCT = prove
 (`forall p (f:A->real) s. prime p /\ FINITE s /\ (forall i. i IN s ==> fin_zp p (f i))
           ==> fin_zp p (product s f)`,
  GEN_TAC THEN GEN_TAC THEN REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN DISCH_TAC THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  ASM_SIMP_TAC[PRODUCT_CLAUSES; FIN_ZP_1; FORALL_IN_INSERT; FIN_ZP_MUL]);;

(* A local integer which is not divisible by p is a local unit. *)

let FIN_ZP_DIVIDES_P = prove
 (`forall p x. prime p /\ fin_zp p (x / &p) ==> fin_zp p x`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `x = &p * x / &p` SUBST1_TAC THENL
   [MP_TAC(SPEC `p:num` PRIME_IMP_NZ) THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_EQ] THEN CONV_TAC REAL_FIELD;
    ASM_SIMP_TAC[FIN_ZP_MUL; FIN_ZP_NUM]]);;

(* ------------------------------------------------------------------------- *)
(* Valuation lower bounds.                                                   *)
(* ------------------------------------------------------------------------- *)

let FIN_PPOW_NZ = prove
 (`forall p k. prime p ==> ~(&p pow k = &0)`,
  SIMP_TAC[REAL_POW_EQ_0; REAL_OF_NUM_EQ; PRIME_IMP_NZ]);;

let FIN_VGE_REPR = prove
 (`forall p x a b a' b'.
        prime p /\ fin_zp p (x * &p pow b / &p pow a) /\ &a' - &b' <= &a - &b
        ==> fin_zp p (x * &p pow b' / &p pow a')`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `a' + b <= a + b':num` MP_TAC THENL
   [REWRITE_TAC[GSYM REAL_OF_NUM_LE; GSYM REAL_OF_NUM_ADD] THEN
    ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[LE_EXISTS] THEN DISCH_THEN(X_CHOOSE_TAC `e:num`) THEN
  SUBGOAL_THEN `x * &p pow b' / &p pow a' = (x * &p pow b / &p pow a) * &p pow e`
  SUBST1_TAC THENL
   [MP_TAC(SPECL [`p:num`; `a:num`] FIN_PPOW_NZ) THEN
    MP_TAC(SPECL [`p:num`; `a':num`] FIN_PPOW_NZ) THEN ASM_REWRITE_TAC[] THEN
    REPEAT DISCH_TAC THEN
    SUBGOAL_THEN `&p pow b' * &p pow a = &p pow b * &p pow e * &p pow a'`
    MP_TAC THENL
     [REWRITE_TAC[GSYM REAL_POW_ADD] THEN AP_TERM_TAC THEN
      UNDISCH_TAC `a + b':num = (a' + b) + e` THEN ARITH_TAC;
      POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN CONV_TAC REAL_FIELD];
    ASM_SIMP_TAC[FIN_ZP_MUL; FIN_ZP_POW; FIN_ZP_NUM]]);;

let FIN_VGE_EXACT = prove
 (`forall p x a b. prime p
             ==> (fin_vge p (&a - &b) x <=> fin_zp p (x * &p pow b / &p pow a))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[fin_vge] THEN EQ_TAC THENL
   [ASM_MESON_TAC[FIN_VGE_REPR]; MESON_TAC[REAL_LE_REFL]]);;

let FIN_VGE_ZP = prove
 (`forall p x. prime p ==> (fin_vge p (&0) x <=> fin_zp p x)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`p:num`; `x:real`; `0`; `0`] FIN_VGE_EXACT) THEN
  ASM_REWRITE_TAC[REAL_SUB_REFL; real_pow; REAL_MUL_RID; REAL_DIV_1]);;

let FIN_VGE_POS = prove
 (`forall p x a. prime p ==> (fin_vge p (&a) x <=> fin_zp p (x / &p pow a))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`p:num`; `x:real`; `a:num`; `0`] FIN_VGE_EXACT) THEN
  ASM_REWRITE_TAC[REAL_SUB_RZERO; real_pow; real_div; REAL_MUL_LID]);;

let FIN_VGE_NEGPOW = prove
 (`forall p x b. prime p ==> (fin_vge p (--(&b)) x <=> fin_zp p (x * &p pow b))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`p:num`; `x:real`; `0`; `b:num`] FIN_VGE_EXACT) THEN
  ASM_REWRITE_TAC[REAL_SUB_LZERO; real_pow; REAL_DIV_1]);;

let FIN_VGE_MONO = prove
 (`forall p k l x. l <= k /\ fin_vge p k x ==> fin_vge p l x`,
  REWRITE_TAC[fin_vge] THEN MESON_TAC[REAL_LE_TRANS]);;

let FIN_VGE_0 = prove
 (`forall p k. prime p ==> fin_vge p k (&0)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[fin_vge] THEN
  MP_TAC(SPEC `k:real` REAL_ARCH_SIMPLE) THEN
  DISCH_THEN(X_CHOOSE_TAC `a:num`) THEN
  MAP_EVERY EXISTS_TAC [`a:num`; `0`] THEN
  ASM_REWRITE_TAC[REAL_SUB_RZERO; REAL_MUL_LZERO; real_div] THEN
  ASM_SIMP_TAC[FIN_ZP_0]);;

let FIN_VGE_ZP_IMP = prove
 (`forall p x. prime p /\ fin_zp p x ==> fin_vge p (&0) x`,
  MESON_TAC[FIN_VGE_ZP]);;

let FIN_VGE_IMP_ZP = prove
 (`forall p k x. prime p /\ &0 <= k /\ fin_vge p k x ==> fin_zp p x`,
  MESON_TAC[FIN_VGE_ZP; FIN_VGE_MONO]);;

let FIN_VGE_INTEGER = prove
 (`forall p x. prime p /\ integer x ==> fin_vge p (&0) x`,
  MESON_TAC[FIN_VGE_ZP; FIN_ZP_INTEGER]);;

let FIN_VGE_NUM = prove
 (`forall p n. prime p ==> fin_vge p (&0) (&n)`,
  MESON_TAC[FIN_VGE_ZP; FIN_ZP_NUM]);;

let FIN_VGE_NEG = prove
 (`forall p k x. fin_vge p k x ==> fin_vge p k (--x)`,
  REWRITE_TAC[fin_vge] THEN REPEAT STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`a:num`; `b:num`] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[real_div; REAL_MUL_LNEG] THEN
  ASM_SIMP_TAC[GSYM real_div; FIN_ZP_NEG]);;

let FIN_VGE_NEG_EQ = prove
 (`forall p k x. fin_vge p k (--x) <=> fin_vge p k x`,
  MESON_TAC[FIN_VGE_NEG; REAL_NEG_NEG]);;

let FIN_VGE_ADD = prove
 (`forall p k x y. prime p /\ fin_vge p k x /\ fin_vge p k y ==> fin_vge p k (x + y)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[fin_vge] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2
   (X_CHOOSE_THEN `a:num` (X_CHOOSE_THEN `b:num` STRIP_ASSUME_TAC))
   (X_CHOOSE_THEN `a':num` (X_CHOOSE_THEN `b':num` STRIP_ASSUME_TAC)))) THEN
  DISJ_CASES_TAC(REAL_ARITH `&a - &b <= &a' - &b' \/ &a' - &b' <= &a - &b`)
  THENL
   [MAP_EVERY EXISTS_TAC [`a:num`; `b:num`] THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[REAL_ADD_RDISTRIB] THEN
    MATCH_MP_TAC FIN_ZP_ADD THEN ASM_MESON_TAC[FIN_VGE_REPR];
    MAP_EVERY EXISTS_TAC [`a':num`; `b':num`] THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[REAL_ADD_RDISTRIB] THEN
    MATCH_MP_TAC FIN_ZP_ADD THEN ASM_MESON_TAC[FIN_VGE_REPR]]);;

let FIN_VGE_SUB = prove
 (`forall p k x y. prime p /\ fin_vge p k x /\ fin_vge p k y ==> fin_vge p k (x - y)`,
  SIMP_TAC[real_sub; FIN_VGE_ADD; FIN_VGE_NEG]);;

let FIN_VGE_SUM = prove
 (`forall p k (f:A->real) s. prime p /\ FINITE s /\ (forall i. i IN s ==> fin_vge p k (f i))
             ==> fin_vge p k (sum s f)`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  DISCH_TAC THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  ASM_SIMP_TAC[SUM_CLAUSES; FIN_VGE_0; FORALL_IN_INSERT; FIN_VGE_ADD]);;

let FIN_VGE_MUL = prove
 (`forall p k l x y. prime p /\ fin_vge p k x /\ fin_vge p l y
               ==> fin_vge p (k + l) (x * y)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[fin_vge] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2
   (X_CHOOSE_THEN `a:num` (X_CHOOSE_THEN `b:num` STRIP_ASSUME_TAC))
   (X_CHOOSE_THEN `a':num` (X_CHOOSE_THEN `b':num` STRIP_ASSUME_TAC)))) THEN
  MAP_EVERY EXISTS_TAC [`a + a':num`; `b + b':num`] THEN CONJ_TAC THENL
   [REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `(x * y) * &p pow (b + b') / &p pow (a + a') =
    (x * &p pow b / &p pow a) * (y * &p pow b' / &p pow a')`
  SUBST1_TAC THENL
   [REWRITE_TAC[REAL_POW_ADD] THEN
    MP_TAC(SPECL [`p:num`; `a:num`] FIN_PPOW_NZ) THEN
    MP_TAC(SPECL [`p:num`; `a':num`] FIN_PPOW_NZ) THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC REAL_FIELD;
    ASM_SIMP_TAC[FIN_ZP_MUL]]);;

let FIN_VGE_PRODUCT = prove
 (`forall p k (f:A->real) s. prime p /\ FINITE s /\ (forall i. i IN s ==> fin_vge p (k i) (f i))
             ==> fin_vge p (sum s k) (product s f)`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  DISCH_TAC THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  ASM_SIMP_TAC[SUM_CLAUSES; PRODUCT_CLAUSES; FORALL_IN_INSERT] THEN
  ASM_SIMP_TAC[FIN_VGE_ZP; FIN_ZP_1; FIN_VGE_MUL]);;

let FIN_VGE_ZP_MUL = prove
 (`forall p k c x. prime p /\ fin_zp p c /\ fin_vge p k x ==> fin_vge p k (c * x)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`p:num`; `&0`; `k:real`; `c:real`; `x:real`] FIN_VGE_MUL) THEN
  ASM_SIMP_TAC[FIN_VGE_ZP; REAL_ADD_LID]);;

let FIN_VGE_MUL_ZP = prove
 (`forall p k c x. prime p /\ fin_zp p c /\ fin_vge p k x ==> fin_vge p k (x * c)`,
  MESON_TAC[FIN_VGE_ZP_MUL; REAL_MUL_SYM]);;

let FIN_VGE_PPOW = prove
 (`forall p n. prime p ==> fin_vge p (&n) (&p pow n)`,
  SIMP_TAC[FIN_VGE_POS] THEN SIMP_TAC[REAL_DIV_REFL; FIN_PPOW_NZ; FIN_ZP_1]);;

let FIN_VGE_PPOW_MUL = prove
 (`forall p k n x. prime p ==> (fin_vge p (k + &n) (&p pow n * x) <=> fin_vge p k x)`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL
   [REWRITE_TAC[fin_vge] THEN STRIP_TAC THEN
    MAP_EVERY EXISTS_TAC [`a:num`; `b + n:num`] THEN CONJ_TAC THENL
     [REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN ASM_REAL_ARITH_TAC;
      FIRST_X_ASSUM(MP_TAC o check (is_comb o concl)) THEN
      MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
      REWRITE_TAC[REAL_POW_ADD] THEN REAL_ARITH_TAC];
    DISCH_TAC THEN ONCE_REWRITE_TAC[REAL_ADD_SYM] THEN
    MATCH_MP_TAC FIN_VGE_MUL THEN ASM_SIMP_TAC[FIN_VGE_PPOW]]);;

let FIN_VGE_PPOW_DIV = prove
 (`forall p k n x. prime p ==> (fin_vge p k (x / &p pow n) <=> fin_vge p (k + &n) x)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`p:num`; `k:real`; `n:num`; `x / &p pow n`] FIN_VGE_PPOW_MUL) THEN
  ASM_SIMP_TAC[REAL_DIV_LMUL; FIN_PPOW_NZ] THEN MESON_TAC[]);;

let FIN_VGE_PMUL = prove
 (`forall p k x. prime p ==> (fin_vge p (k + &1) (&p * x) <=> fin_vge p k x)`,
  MESON_TAC[FIN_VGE_PPOW_MUL; REAL_POW_1]);;

let FIN_VGE_DIV_NUM = prove
 (`forall p k x n. prime p /\ ~(p divides n) /\ fin_vge p k x ==> fin_vge p k (x / &n)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[real_div] THEN
  MATCH_MP_TAC FIN_VGE_MUL_ZP THEN ASM_SIMP_TAC[FIN_ZP_INV_NUM]);;

let FIN_VGE_NUM_DIVIDES = prove
 (`forall p k m. prime p ==> (fin_vge p (&k) (&m) <=> (p EXP k) divides m)`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[FIN_VGE_POS] THEN EQ_TAC THENL
   [REWRITE_TAC[fin_zp; LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`u:real`; `n:num`] THEN STRIP_TAC THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP FIN_NDIV_NZ) THEN
    MP_TAC(SPECL [`p:num`; `k:num`] FIN_PPOW_NZ) THEN ASM_REWRITE_TAC[] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `u = (&m * &n) / &p pow k` ASSUME_TAC THENL
     [UNDISCH_TAC `&m / &p pow k = u / &n` THEN
      UNDISCH_TAC `~(&n = &0)` THEN UNDISCH_TAC `~(&p pow k = &0)` THEN
      CONV_TAC REAL_FIELD; ALL_TAC] THEN
    SUBGOAL_THEN `exists q. u = &q` (X_CHOOSE_TAC `q:num`) THENL
     [MP_TAC(SPEC `u:real` INTEGER_POS) THEN ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN
        SIMP_TAC[REAL_LE_DIV; REAL_LE_MUL; REAL_POS; REAL_POW_LE];
        ASM_MESON_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `n * m = p EXP k * q` ASSUME_TAC THENL
     [REWRITE_TAC[GSYM REAL_OF_NUM_EQ; GSYM REAL_OF_NUM_MUL; GSYM REAL_OF_NUM_POW] THEN
      UNDISCH_TAC `u = (&m * &n) / &p pow k` THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `~(&p pow k = &0)` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
    MATCH_MP_TAC COPRIME_DIVPROD THEN EXISTS_TAC `n:num` THEN CONJ_TAC THENL
     [ASM_REWRITE_TAC[] THEN REWRITE_TAC[divides] THEN MESON_TAC[];
      REWRITE_TAC[COPRIME_LEXP] THEN DISJ1_TAC THEN
      ASM_MESON_TAC[PRIME_COPRIME_STRONG]];
    REWRITE_TAC[divides] THEN DISCH_THEN(X_CHOOSE_THEN `q:num` SUBST1_TAC) THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_MUL; GSYM REAL_OF_NUM_POW] THEN
    ASM_SIMP_TAC[REAL_FIELD `~(a = &0) ==> (a * q) / a = q`; FIN_PPOW_NZ] THEN
    ASM_SIMP_TAC[FIN_ZP_NUM]]);;

let FIN_VGE_1_NUM = prove
 (`forall p m. prime p ==> (fin_vge p (&1) (&m) <=> p divides m)`,
  SIMP_TAC[FIN_VGE_NUM_DIVIDES; EXP_1]);;


(* ------------------------------------------------------------------------- *)
(* Determinants: valuation of ndet, and the atom expansion lemma.            *)
(* ------------------------------------------------------------------------- *)

let FIN_NDET_RING = prove
 (`forall s a. ndet s a = ring_det real_ring s a`,
  REWRITE_TAC[ndet; ring_det; REAL_RING_SUM; REAL_RING_PRODUCT; ring_sign;
              sign; REAL_RING_CLAUSES]);;

let FIN_ZP_SIGN = prove
 (`forall p q. prime p ==> fin_zp p (sign q)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[sign] THEN COND_CASES_TAC THEN
  ASM_SIMP_TAC[FIN_ZP_1; FIN_ZP_NEG]);;

let FIN_VGE_NDET_ROWS = prove
 (`forall p s (b:num->num->real) w.
        prime p /\ FINITE s /\
        (forall k i. k IN s /\ i IN s ==> fin_vge p (w k) (b k i))
        ==> fin_vge p (sum s w) (ndet s b)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[ndet] THEN
  MATCH_MP_TAC FIN_VGE_SUM THEN ASM_SIMP_TAC[FINITE_PERMUTATIONS] THEN
  X_GEN_TAC `q:num->num` THEN REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN
  MATCH_MP_TAC FIN_VGE_ZP_MUL THEN ASM_SIMP_TAC[FIN_ZP_SIGN] THEN
  MATCH_MP_TAC FIN_VGE_PRODUCT THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[PERMUTES_IN_IMAGE]);;

let FIN_NDET_TRANSP = prove
 (`forall s (a:num->num->real). FINITE s ==> ndet s (\i j. a j i) = ndet s a`,
  SIMP_TAC[FIN_NDET_RING; RING_DET_TRANSP]);;

let FIN_VGE_NDET_COLS = prove
 (`forall p s (a:num->num->real) w.
        prime p /\ FINITE s /\
        (forall i k. i IN s /\ k IN s ==> fin_vge p (w k) (a i k))
        ==> fin_vge p (sum s w) (ndet s a)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(fun th -> ONCE_REWRITE_TAC[GSYM(MATCH_MP FIN_NDET_TRANSP th)]) THEN
  MATCH_MP_TAC FIN_VGE_NDET_ROWS THEN ASM_SIMP_TAC[]);;

let FIN_VGE_NDET_ATOMS = prove
 (`forall p s t (a:num->num->real) (c:B->num->real) (v:B->num->real) (w:B->num->real) d.
        prime p /\ FINITE s /\ FINITE t /\
        (forall i k. i IN s /\ k IN s ==> a i k = sum t (\x. c x k * v x i)) /\
        (forall x i k. x IN t /\ i IN s /\ k IN s ==> fin_vge p (w x k) (c x k * v x i)) /\
        (forall f. (forall k. k IN s ==> f k IN t) /\
             (forall k1 k2. k1 IN s /\ k2 IN s /\ f k1 = f k2 ==> k1 = k2)
             ==> d <= sum s (\k. w (f k) k))
        ==> fin_vge p d (ndet s a)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(fun th -> ONCE_REWRITE_TAC[GSYM(MATCH_MP FIN_NDET_TRANSP th)]) THEN
  REWRITE_TAC[FIN_NDET_RING] THEN
  MP_TAC(ISPECL [`real_ring`; `s:num->bool`; `(\k. t):num->B->bool`;
                 `(\i j. (a:num->num->real) j i)`;
                 `(\k x i. (c:B->num->real) x k * (v:B->num->real) x i)`]
         RING_DET_MULTILINEAR) THEN
  ASM_SIMP_TAC[REAL_RING_CLAUSES; IN_UNIV; REAL_RING_SUM] THEN
  DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC FIN_VGE_SUM THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ASM_SIMP_TAC[FINITE_CARTESIAN_PRODUCT] THEN DISJ2_TAC THEN
    MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `s:num->bool` THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `mu:num->B` THEN REWRITE_TAC[IN_CARTESIAN_PRODUCT] THEN
  STRIP_TAC THEN
  ASM_CASES_TAC
   `forall k1 k2. k1 IN s /\ k2 IN s /\ (mu:num->B) k1 = mu k2 ==> k1 = k2`
  THENL
   [MATCH_MP_TAC FIN_VGE_MONO THEN
    EXISTS_TAC `sum s (\k. (w:B->num->real) ((mu:num->B) k) k)` THEN
    CONJ_TAC THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[GSYM FIN_NDET_RING] THEN
    MATCH_MP_TAC FIN_VGE_NDET_ROWS THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [NOT_FORALL_THM]) THEN
  DISCH_THEN(X_CHOOSE_THEN `k1:num` MP_TAC) THEN
  REWRITE_TAC[NOT_FORALL_THM; NOT_IMP] THEN
  DISCH_THEN(X_CHOOSE_THEN `k2:num` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`real_ring`; `s:num->bool`;
                 `\k. (c:B->num->real) ((mu:num->B) k) k`;
                 `\k i. (v:B->num->real) ((mu:num->B) k) i`]
         RING_DET_ROWS_MUL) THEN
  ASM_REWRITE_TAC[REAL_RING_CLAUSES; IN_UNIV] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`real_ring`; `s:num->bool`;
                 `\k i. (v:B->num->real) ((mu:num->B) k) i`;
                 `k1:num`; `k2:num`] RING_DET_IDENTICAL_ROWS) THEN
  ASM_REWRITE_TAC[REAL_RING_CLAUSES] THEN DISCH_THEN SUBST1_TAC THEN
  ASM_SIMP_TAC[REAL_MUL_RZERO; FIN_VGE_0]);;

let FIN_SUM_INDICATOR = prove
 (`forall s P. FINITE s
         ==> sum s (\k:A. if P k then &1 else &0) = &(CARD {k | k IN s /\ P k})`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM SUM_RESTRICT_SET] THEN
  ASM_SIMP_TAC[SUM_CONST; FINITE_RESTRICT; REAL_MUL_RID]);;

let FIN_MIN_LEMMA = prove
 (`forall r q n R S. r <= R /\ q <= S /\ r + q <= n
               ==> 2 * r + q <= MIN (2 * n) (MIN (n + R) (2 * R + S))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[MIN] THEN
  REPEAT COND_CASES_TAC THEN ASM_ARITH_TAC);;

let FIN_VGE_NDET_ATOMS_012 = prove
 (`forall p s t (a:num->num->real) (c:B->num->real) (v:B->num->real) t1 t2 R S.
        prime p /\ FINITE s /\ FINITE t /\
        t1 SUBSET t /\ t2 SUBSET t /\ DISJOINT t1 t2 /\
        CARD t1 <= S /\ CARD t2 <= R /\
        (forall i k. i IN s /\ k IN s ==> a i k = sum t (\x. c x k * v x i)) /\
        (forall x k. x IN t /\ k IN s ==> fin_zp p (c x k)) /\
        (forall x i. x IN t2 /\ i IN s ==> fin_vge p (--(&2)) (v x i)) /\
        (forall x i. x IN t1 /\ i IN s ==> fin_vge p (--(&1)) (v x i)) /\
        (forall x i. x IN t /\ ~(x IN t1) /\ ~(x IN t2) /\ i IN s ==> fin_zp p (v x i))
        ==> fin_vge p (--(&(MIN (2 * CARD s) (MIN (CARD s + R) (2 * R + S)))))
                    (ndet s a)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC FIN_VGE_NDET_ATOMS THEN
  MAP_EVERY EXISTS_TAC
   [`t:B->bool`; `c:B->num->real`; `v:B->num->real`;
    `\(x:B) (k:num). --(&2 * (if x IN t2 then &1 else &0) +
                        (if x IN t1 then &1 else &0))`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`x:B`; `i:num`; `k:num`] THEN STRIP_TAC THEN
    MATCH_MP_TAC FIN_VGE_ZP_MUL THEN ASM_SIMP_TAC[] THEN
    ASM_CASES_TAC `(x:B) IN t2` THENL
     [SUBGOAL_THEN `~((x:B) IN t1)` ASSUME_TAC THENL
       [ASM SET_TAC[]; ASM_SIMP_TAC[]] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM_SIMP_TAC[];
      ASM_REWRITE_TAC[]] THEN
    ASM_CASES_TAC `(x:B) IN t1` THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM_SIMP_TAC[FIN_VGE_ZP];
    ALL_TAC] THEN
  X_GEN_TAC `f:num->B` THEN STRIP_TAC THEN
  REWRITE_TAC[SUM_NEG; SUM_ADD_NUMSEG] THEN
  ASM_SIMP_TAC[SUM_ADD; SUM_LMUL; FIN_SUM_INDICATOR] THEN
  REWRITE_TAC[REAL_LE_NEG2; REAL_OF_NUM_MUL; REAL_OF_NUM_ADD; REAL_OF_NUM_LE] THEN
  MATCH_MP_TAC FIN_MIN_LEMMA THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC LE_TRANS THEN
    EXISTS_TAC `CARD(t2:B->bool)` THEN ASM_REWRITE_TAC[] THEN
    W(MP_TAC o PART_MATCH (rand o rand) CARD_IMAGE_INJ o lhand o snd) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[FINITE_RESTRICT; IN_ELIM_THM] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_MP_TAC CARD_SUBSET THEN
    CONJ_TAC THENL [SET_TAC[]; ASM_MESON_TAC[FINITE_SUBSET]];
    MATCH_MP_TAC LE_TRANS THEN
    EXISTS_TAC `CARD(t1:B->bool)` THEN ASM_REWRITE_TAC[] THEN
    W(MP_TAC o PART_MATCH (rand o rand) CARD_IMAGE_INJ o lhand o snd) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[FINITE_RESTRICT; IN_ELIM_THM] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_MP_TAC CARD_SUBSET THEN
    CONJ_TAC THENL [SET_TAC[]; ASM_MESON_TAC[FINITE_SUBSET]];
    W(MP_TAC o PART_MATCH (rand o rand) CARD_UNION o lhand o snd) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[FINITE_RESTRICT] THEN ASM SET_TAC[]; ALL_TAC] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_MP_TAC CARD_SUBSET THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The product formula, in the form of a lower bound for log |x|.            *)
(* ------------------------------------------------------------------------- *)

let FIN_INTEGER_PRODUCT = prove
 (`forall f (s:A->bool). FINITE s /\ (forall i. i IN s ==> integer(f i))
                   ==> integer(product s f)`,
  GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[PRODUCT_CLAUSES; INTEGER_CLOSED; FORALL_IN_INSERT]);;

let FIN_INTEGER_LOCAL_NUM = prove
 (`forall q m. ~(q = 0) /\ (forall r. prime r ==> fin_zp r (&m / &q)) ==> integer(&m / &q)`,
  MATCH_MP_TAC num_WF THEN X_GEN_TAC `q:num` THEN DISCH_TAC THEN
  X_GEN_TAC `m:num` THEN STRIP_TAC THEN
  ASM_CASES_TAC `q = 1` THENL
   [ASM_REWRITE_TAC[REAL_DIV_1; INTEGER_CLOSED]; ALL_TAC] THEN
  FIRST_ASSUM(X_CHOOSE_THEN `r:num` STRIP_ASSUME_TAC o MATCH_MP PRIME_FACTOR) THEN
  SUBGOAL_THEN `fin_zp r (&m / &q)` MP_TAC THENL [ASM_MESON_TAC[]; REWRITE_TAC[fin_zp]] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real` (X_CHOOSE_THEN `w:num` STRIP_ASSUME_TAC)) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP FIN_NDIV_NZ) THEN
  SUBGOAL_THEN `&0 <= u` MP_TAC THENL
   [SUBGOAL_THEN `u = &m / &q * &w` SUBST1_TAC THENL
     [UNDISCH_TAC `&m / &q = u / &w` THEN UNDISCH_TAC `~(&w = &0)` THEN
      CONV_TAC REAL_FIELD;
      SIMP_TAC[REAL_LE_MUL; REAL_LE_DIV; REAL_POS]];
    ALL_TAC] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `exists k. u = &k` (X_CHOOSE_THEN `k:num` SUBST_ALL_TAC) THENL
   [ASM_MESON_TAC[INTEGER_POS]; ALL_TAC] THEN
  SUBGOAL_THEN `m * w = k * q:num` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_OF_NUM_EQ; GSYM REAL_OF_NUM_MUL] THEN
    UNDISCH_TAC `&m / &q = &k / &w` THEN UNDISCH_TAC `~(&w = &0)` THEN
    UNDISCH_TAC `~(q = 0)` THEN REWRITE_TAC[GSYM REAL_OF_NUM_EQ] THEN
    CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  SUBGOAL_THEN `r divides m` MP_TAC THENL
   [MP_TAC(SPECL [`r:num`; `m:num`; `w:num`] PRIME_DIVPROD) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC DIVIDES_LMUL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `r divides q` THEN REWRITE_TAC[divides] THEN
  DISCH_THEN(X_CHOOSE_THEN `q1:num` SUBST_ALL_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `m1:num` SUBST_ALL_TAC) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP PRIME_GE_2) THEN
  SUBGOAL_THEN `&(r * m1) / &(r * q1) = &m1 / &q1` SUBST_ALL_TAC THENL
   [REWRITE_TAC[GSYM REAL_OF_NUM_MUL] THEN
    UNDISCH_TAC `~(r * q1 = 0)` THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_EQ; GSYM REAL_OF_NUM_MUL] THEN
    CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[RIGHT_IMP_FORALL_THM; IMP_IMP]) THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `~(r * q1 = 0)` THEN REWRITE_TAC[MULT_EQ_0; DE_MORGAN_THM] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(ARITH_RULE `1 * q1 < r * q1 ==> q1 < r * q1`) THEN
  REWRITE_TAC[LT_MULT_RCANCEL] THEN ASM_ARITH_TAC);;

let FIN_INTEGER_LOCAL = prove
 (`forall y. rational y /\ (forall p. prime p ==> fin_zp p y) ==> integer y`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[GSYM INTEGER_ABS] THEN
  SUBGOAL_THEN `forall p. prime p ==> fin_zp p (abs y)` MP_TAC THENL
   [REPEAT STRIP_TAC THEN
    DISJ_CASES_TAC(REAL_ARITH `abs y = y \/ abs y = --y`) THEN
    ASM_SIMP_TAC[FIN_ZP_NEG];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [RATIONAL_ALT]) THEN
  DISCH_THEN(X_CHOOSE_THEN `m:num` (X_CHOOSE_THEN `q:num` STRIP_ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MATCH_MP_TAC FIN_INTEGER_LOCAL_NUM THEN ASM_REWRITE_TAC[]);;

let FIN_CEIL_EXISTS = prove
 (`forall r. exists e. abs r <= &e /\ &e <= abs r + &1`,
  GEN_TAC THEN MP_TAC(SPEC `abs r` REAL_ARCH_SIMPLE) THEN
  GEN_REWRITE_TAC LAND_CONV [num_WOP] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:num` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `e:num` THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `e = 0` THEN ASM_REWRITE_TAC[] THENL
   [REAL_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `e - 1`) THEN
  ASM_SIMP_TAC[ARITH_RULE `~(e = 0) ==> e - 1 < e`; GSYM REAL_OF_NUM_SUB;
               LE_1] THEN
  REAL_ARITH_TAC);;

let FIN_LOG_LOWER = prove
 (`forall x M (K:num->real).
        rational x /\ ~(x = &0) /\
        (forall p. prime p /\ p <= M ==> fin_vge p (--(K p)) x) /\
        (forall p. prime p /\ M < p ==> fin_zp p x)
        ==> --(sum {p | prime p /\ p <= M} (\p. (abs(K p) + &1) * log(&p)))
            <= log(abs x)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(GEN `p:num` (SPEC `(K:num->real) p` FIN_CEIL_EXISTS)) THEN
  REWRITE_TAC[SKOLEM_THM] THEN DISCH_THEN(X_CHOOSE_TAC `e:num->num`) THEN
  ABBREV_TAC `P = {p | prime p /\ p <= M}` THEN
  SUBGOAL_THEN `FINITE(P:num->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "P" THEN MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `0..M` THEN REWRITE_TAC[FINITE_NUMSEG; SUBSET; IN_NUMSEG; IN_ELIM_THM] THEN
    ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `D = product P (\p. &p pow (e p))` THEN
  SUBGOAL_THEN `&0 < D` ASSUME_TAC THENL
   [EXPAND_TAC "D" THEN MATCH_MP_TAC PRODUCT_POS_LT THEN ASM_REWRITE_TAC[] THEN
    EXPAND_TAC "P" THEN REWRITE_TAC[IN_ELIM_THM] THEN
    SIMP_TAC[REAL_POW_LT; REAL_OF_NUM_LT; PRIME_IMP_NZ; LT_NZ];
    ALL_TAC] THEN
  SUBGOAL_THEN `integer(D)` ASSUME_TAC THENL
   [EXPAND_TAC "D" THEN MATCH_MP_TAC FIN_INTEGER_PRODUCT THEN
    ASM_SIMP_TAC[INTEGER_CLOSED];
    ALL_TAC] THEN
  SUBGOAL_THEN `integer(x * D)` ASSUME_TAC THENL
   [MATCH_MP_TAC FIN_INTEGER_LOCAL THEN CONJ_TAC THENL
     [ASM_MESON_TAC[RATIONAL_MUL; RATIONAL_INTEGER]; ALL_TAC] THEN
    X_GEN_TAC `q:num` THEN DISCH_TAC THEN
    ASM_CASES_TAC `q:num <= M` THENL
     [SUBGOAL_THEN `(q:num) IN P` ASSUME_TAC THENL
       [EXPAND_TAC "P" THEN REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
      MP_TAC(ISPECL [`\p. &p pow (e p)`; `P:num->bool`; `q:num`] PRODUCT_DELETE) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC FIN_ZP_MUL THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [ASM_SIMP_TAC[GSYM FIN_VGE_NEGPOW] THEN MATCH_MP_TAC FIN_VGE_MONO THEN
        EXISTS_TAC `--((K:num->real) q)` THEN ASM_SIMP_TAC[] THEN
        FIRST_X_ASSUM(MP_TAC o SPEC `q:num`) THEN REAL_ARITH_TAC;
        MATCH_MP_TAC FIN_ZP_INTEGER THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC FIN_INTEGER_PRODUCT THEN
        ASM_SIMP_TAC[INTEGER_CLOSED; FINITE_DELETE]];
      MATCH_MP_TAC FIN_ZP_MUL THEN ASM_SIMP_TAC[FIN_ZP_INTEGER] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `~(q:num <= M)` THEN ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&1 <= abs(x * D)` MP_TAC THENL
   [MATCH_MP_TAC REAL_ABS_INTEGER_LEMMA THEN ASM_REWRITE_TAC[REAL_ENTIRE] THEN
    ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[REAL_ABS_MUL] THEN ASM_SIMP_TAC[REAL_ARITH `&0 < D ==> abs D = D`] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `&0 <= log(abs x * D)` MP_TAC THENL
   [MATCH_MP_TAC LOG_POS THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[LOG_MUL; GSYM REAL_ABS_NZ] THEN
  SUBGOAL_THEN `log D <= sum P (\p. (abs(K p) + &1) * log(&p))` MP_TAC THENL
   [ALL_TAC; REAL_ARITH_TAC] THEN
  EXPAND_TAC "D" THEN
  W(MP_TAC o PART_MATCH (lhand o rand) LOG_PRODUCT o lhand o snd) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN EXPAND_TAC "P" THEN REWRITE_TAC[IN_ELIM_THM] THEN
    SIMP_TAC[REAL_POW_LT; REAL_OF_NUM_LT; PRIME_IMP_NZ; LT_NZ];
    DISCH_THEN SUBST1_TAC] THEN
  MATCH_MP_TAC SUM_LE THEN ASM_REWRITE_TAC[] THEN
  EXPAND_TAC "P" THEN REWRITE_TAC[IN_ELIM_THM] THEN
  X_GEN_TAC `p:num` THEN STRIP_TAC THEN
  ASM_SIMP_TAC[LOG_POW; REAL_OF_NUM_LT; PRIME_IMP_NZ; LT_NZ] THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `p:num`) THEN REAL_ARITH_TAC;
    MATCH_MP_TAC LOG_POS THEN FIRST_ASSUM(MP_TAC o MATCH_MP PRIME_GE_2) THEN
    REWRITE_TAC[REAL_OF_NUM_LE] THEN ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Shared definitions used in the interfaces between the sub-components.     *)
(* ------------------------------------------------------------------------- *)

(* floor(log_p n) for p >= 2, n >= 1 *)
let fin_flog = new_definition
 `fin_flog p n = CARD {e | 1 <= e /\ p EXP e <= n}`;;

(* H*_z of Equation (18) *)
let fin_hstar = new_definition
 `fin_hstar z = if EVEN z then cat_c (z DIV 2)
                else inv(&z * cat_c ((z - 1) DIV 2))`;;

(* Coefficient of t^d in (1 - t^2)^((p-1)/2) (zero for d >= p) *)
let fin_E = new_definition
 `fin_E p d = if EVEN d /\ d < p
              then (--(&1)) pow (d DIV 2) * &(binom((p - 1) DIV 2,d DIV 2))
              else &0`;;

(* M'(a - 1, j) with the convention M'(-1, j) = k^+_(j+1), Equation (15) *)
let fin_M0x = new_definition
 `fin_M0x a j = if a = 0 then cat_kplus (j + 1) else cat_M0 (a - 1) j`;;

(* The odd-prime loss: Equation (38) for 2p <= H, Lemma 3.3 for 2p > H.     *)
(* Natural-number truncated subtraction implements (.)_+.                    *)
let fin_loss = new_definition
 `fin_loss N p =
    if 2 * p <= 65 * N then
      2 * (48 * N) -
      ((MIN p (MIN (59 * N - p) (19 * N)) - MAX (7 * N) (65 * N - 2 * p)) - 4 * N)
    else
      let R = (59 * N - p) + ((59 * N - p) - 19 * N) +
              ((65 * N - p) - MAX (7 * N) (59 * N - p)) in
      let S = (MIN (19 * N) (59 * N - p) - 7 * N) +
              (MIN (7 * N) (65 * N - p) - (59 * N - p)) in
      MIN (2 * (48 * N)) (MIN (48 * N + R) (2 * R + S))`;;
