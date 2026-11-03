(* ========================================================================= *)
(* CAT_NONVANISHING, part La (prefix nv_dig_): standalone copy, with every   *)
(* name renamed fin_ -> nv_dig_fin_ / FIN_ -> NV_DIG_FIN_, of the material   *)
(* used from the finite-place files catalan_fin_base.ml,                    *)
(* catalan_fin_dig_base.ml, catalan_fin_dig_c.ml, catalan_fin_bdry.ml        *)
(* (p-local integrality, c_l digit laws, H*_z, explicit formulas (19)).      *)
(* ========================================================================= *)

needs "src/catalan_nv_base.ml";;
needs "Library/ring_det.ml";;

(* ---- copied from src/catalan_fin_base.ml ---- *)
(* ========================================================================= *)
(* CAT_FINITE_PLACE: basic p-adic valuation tools on real numbers.           *)
(*                                                                           *)
(*   nv_dig_fin_zp p x     : x = m / n with m integer and p not dividing n          *)
(*   nv_dig_fin_vge p k x  : v_p(x) >= k (k real), i.e. x in p^ceil(k) Z_(p)        *)
(* ========================================================================= *)


let nv_dig_fin_zp = new_definition
 `nv_dig_fin_zp p x <=> exists m n. integer m /\ ~(p divides n) /\ x = m / &n`;;

let nv_dig_fin_vge = new_definition
 `nv_dig_fin_vge p k x <=> exists a b. k <= &a - &b /\ nv_dig_fin_zp p (x * &p pow b / &p pow a)`;;

(* ------------------------------------------------------------------------- *)
(* Local integers.                                                           *)
(* ------------------------------------------------------------------------- *)

let NV_DIG_FIN_NDIV_NZ = prove
 (`forall p n. ~(p divides n) ==> ~(&n = &0)`,
  REWRITE_TAC[REAL_OF_NUM_EQ] THEN MESON_TAC[DIVIDES_0]);;

let NV_DIG_FIN_ZP_INTEGER = prove
 (`forall p x. prime p /\ integer x ==> nv_dig_fin_zp p x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[nv_dig_fin_zp] THEN
  MAP_EVERY EXISTS_TAC [`x:real`; `1`] THEN
  ASM_REWRITE_TAC[DIVIDES_ONE; REAL_DIV_1] THEN ASM_MESON_TAC[PRIME_1]);;

let NV_DIG_FIN_ZP_NUM = prove
 (`forall p n. prime p ==> nv_dig_fin_zp p (&n)`,
  MESON_TAC[NV_DIG_FIN_ZP_INTEGER; INTEGER_CLOSED]);;

let NV_DIG_FIN_ZP_0 = prove
 (`forall p. prime p ==> nv_dig_fin_zp p (&0)`,
  MESON_TAC[NV_DIG_FIN_ZP_NUM]);;

let NV_DIG_FIN_ZP_1 = prove
 (`forall p. prime p ==> nv_dig_fin_zp p (&1)`,
  MESON_TAC[NV_DIG_FIN_ZP_NUM]);;

let NV_DIG_FIN_ZP_NEG = prove
 (`forall p x. nv_dig_fin_zp p x ==> nv_dig_fin_zp p (--x)`,
  REWRITE_TAC[nv_dig_fin_zp] THEN REPEAT STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`--m:real`; `n:num`] THEN
  ASM_SIMP_TAC[INTEGER_CLOSED] THEN REAL_ARITH_TAC);;

let NV_DIG_FIN_ZP_NEG_EQ = prove
 (`forall p x. nv_dig_fin_zp p (--x) <=> nv_dig_fin_zp p x`,
  MESON_TAC[NV_DIG_FIN_ZP_NEG; REAL_NEG_NEG]);;

let NV_DIG_FIN_ZP_ADD = prove
 (`forall p x y. prime p /\ nv_dig_fin_zp p x /\ nv_dig_fin_zp p y ==> nv_dig_fin_zp p (x + y)`,
  REWRITE_TAC[nv_dig_fin_zp] THEN REPEAT STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`m * &n' + m' * &n:real`; `n * n':num`] THEN
  ASM_SIMP_TAC[INTEGER_CLOSED] THEN CONJ_TAC THENL
   [ASM_MESON_TAC[PRIME_DIVPROD]; ALL_TAC] THEN
  REPEAT(FIRST_X_ASSUM(ASSUME_TAC o MATCH_MP NV_DIG_FIN_NDIV_NZ)) THEN
  ASM_REWRITE_TAC[GSYM REAL_OF_NUM_MUL] THEN
  REPEAT(POP_ASSUM MP_TAC) THEN CONV_TAC REAL_FIELD);;

let NV_DIG_FIN_ZP_SUB = prove
 (`forall p x y. prime p /\ nv_dig_fin_zp p x /\ nv_dig_fin_zp p y ==> nv_dig_fin_zp p (x - y)`,
  SIMP_TAC[real_sub; NV_DIG_FIN_ZP_ADD; NV_DIG_FIN_ZP_NEG]);;

let NV_DIG_FIN_ZP_MUL = prove
 (`forall p x y. prime p /\ nv_dig_fin_zp p x /\ nv_dig_fin_zp p y ==> nv_dig_fin_zp p (x * y)`,
  REWRITE_TAC[nv_dig_fin_zp] THEN REPEAT STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`m * m':real`; `n * n':num`] THEN
  ASM_SIMP_TAC[INTEGER_CLOSED] THEN CONJ_TAC THENL
   [ASM_MESON_TAC[PRIME_DIVPROD]; ALL_TAC] THEN
  REPEAT(FIRST_X_ASSUM(ASSUME_TAC o MATCH_MP NV_DIG_FIN_NDIV_NZ)) THEN
  ASM_REWRITE_TAC[GSYM REAL_OF_NUM_MUL] THEN
  REPEAT(POP_ASSUM MP_TAC) THEN CONV_TAC REAL_FIELD);;

let NV_DIG_FIN_ZP_POW = prove
 (`forall p x k. prime p /\ nv_dig_fin_zp p x ==> nv_dig_fin_zp p (x pow k)`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN
  ASM_SIMP_TAC[real_pow; NV_DIG_FIN_ZP_1; NV_DIG_FIN_ZP_MUL]);;

let NV_DIG_FIN_ZP_DIV_NUM = prove
 (`forall p x n. prime p /\ nv_dig_fin_zp p x /\ ~(p divides n) ==> nv_dig_fin_zp p (x / &n)`,
  REWRITE_TAC[nv_dig_fin_zp] THEN REPEAT STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`m:real`; `n' * n:num`] THEN
  ASM_SIMP_TAC[INTEGER_CLOSED] THEN CONJ_TAC THENL
   [ASM_MESON_TAC[PRIME_DIVPROD]; ALL_TAC] THEN
  REPEAT(FIRST_X_ASSUM(ASSUME_TAC o MATCH_MP NV_DIG_FIN_NDIV_NZ)) THEN
  ASM_REWRITE_TAC[GSYM REAL_OF_NUM_MUL] THEN
  REPEAT(POP_ASSUM MP_TAC) THEN CONV_TAC REAL_FIELD);;

let NV_DIG_FIN_ZP_INV_NUM = prove
 (`forall p n. prime p /\ ~(p divides n) ==> nv_dig_fin_zp p (inv(&n))`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[REAL_ARITH `inv x = &1 / x`] THEN
  ASM_SIMP_TAC[NV_DIG_FIN_ZP_DIV_NUM; NV_DIG_FIN_ZP_1]);;

let NV_DIG_FIN_ZP_SUM = prove
 (`forall p (f:A->real) s. prime p /\ FINITE s /\ (forall i. i IN s ==> nv_dig_fin_zp p (f i))
           ==> nv_dig_fin_zp p (sum s f)`,
  GEN_TAC THEN GEN_TAC THEN REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN DISCH_TAC THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  ASM_SIMP_TAC[SUM_CLAUSES; NV_DIG_FIN_ZP_0; FORALL_IN_INSERT; NV_DIG_FIN_ZP_ADD]);;

let NV_DIG_FIN_ZP_PRODUCT = prove
 (`forall p (f:A->real) s. prime p /\ FINITE s /\ (forall i. i IN s ==> nv_dig_fin_zp p (f i))
           ==> nv_dig_fin_zp p (product s f)`,
  GEN_TAC THEN GEN_TAC THEN REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN DISCH_TAC THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  ASM_SIMP_TAC[PRODUCT_CLAUSES; NV_DIG_FIN_ZP_1; FORALL_IN_INSERT; NV_DIG_FIN_ZP_MUL]);;

(* A local integer which is not divisible by p is a local unit. *)

let NV_DIG_FIN_ZP_DIVIDES_P = prove
 (`forall p x. prime p /\ nv_dig_fin_zp p (x / &p) ==> nv_dig_fin_zp p x`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `x = &p * x / &p` SUBST1_TAC THENL
   [MP_TAC(SPEC `p:num` PRIME_IMP_NZ) THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_EQ] THEN CONV_TAC REAL_FIELD;
    ASM_SIMP_TAC[NV_DIG_FIN_ZP_MUL; NV_DIG_FIN_ZP_NUM]]);;

(* ------------------------------------------------------------------------- *)
(* Valuation lower bounds.                                                   *)
(* ------------------------------------------------------------------------- *)

let NV_DIG_FIN_PPOW_NZ = prove
 (`forall p k. prime p ==> ~(&p pow k = &0)`,
  SIMP_TAC[REAL_POW_EQ_0; REAL_OF_NUM_EQ; PRIME_IMP_NZ]);;

let NV_DIG_FIN_VGE_REPR = prove
 (`forall p x a b a' b'.
        prime p /\ nv_dig_fin_zp p (x * &p pow b / &p pow a) /\ &a' - &b' <= &a - &b
        ==> nv_dig_fin_zp p (x * &p pow b' / &p pow a')`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `a' + b <= a + b':num` MP_TAC THENL
   [REWRITE_TAC[GSYM REAL_OF_NUM_LE; GSYM REAL_OF_NUM_ADD] THEN
    ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[LE_EXISTS] THEN DISCH_THEN(X_CHOOSE_TAC `e:num`) THEN
  SUBGOAL_THEN `x * &p pow b' / &p pow a' = (x * &p pow b / &p pow a) * &p pow e`
  SUBST1_TAC THENL
   [MP_TAC(SPECL [`p:num`; `a:num`] NV_DIG_FIN_PPOW_NZ) THEN
    MP_TAC(SPECL [`p:num`; `a':num`] NV_DIG_FIN_PPOW_NZ) THEN ASM_REWRITE_TAC[] THEN
    REPEAT DISCH_TAC THEN
    SUBGOAL_THEN `&p pow b' * &p pow a = &p pow b * &p pow e * &p pow a'`
    MP_TAC THENL
     [REWRITE_TAC[GSYM REAL_POW_ADD] THEN AP_TERM_TAC THEN
      UNDISCH_TAC `a + b':num = (a' + b) + e` THEN ARITH_TAC;
      POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN CONV_TAC REAL_FIELD];
    ASM_SIMP_TAC[NV_DIG_FIN_ZP_MUL; NV_DIG_FIN_ZP_POW; NV_DIG_FIN_ZP_NUM]]);;

let NV_DIG_FIN_VGE_EXACT = prove
 (`forall p x a b. prime p
             ==> (nv_dig_fin_vge p (&a - &b) x <=> nv_dig_fin_zp p (x * &p pow b / &p pow a))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[nv_dig_fin_vge] THEN EQ_TAC THENL
   [ASM_MESON_TAC[NV_DIG_FIN_VGE_REPR]; MESON_TAC[REAL_LE_REFL]]);;

let NV_DIG_FIN_VGE_ZP = prove
 (`forall p x. prime p ==> (nv_dig_fin_vge p (&0) x <=> nv_dig_fin_zp p x)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`p:num`; `x:real`; `0`; `0`] NV_DIG_FIN_VGE_EXACT) THEN
  ASM_REWRITE_TAC[REAL_SUB_REFL; real_pow; REAL_MUL_RID; REAL_DIV_1]);;

let NV_DIG_FIN_VGE_POS = prove
 (`forall p x a. prime p ==> (nv_dig_fin_vge p (&a) x <=> nv_dig_fin_zp p (x / &p pow a))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`p:num`; `x:real`; `a:num`; `0`] NV_DIG_FIN_VGE_EXACT) THEN
  ASM_REWRITE_TAC[REAL_SUB_RZERO; real_pow; real_div; REAL_MUL_LID]);;

let NV_DIG_FIN_VGE_NEGPOW = prove
 (`forall p x b. prime p ==> (nv_dig_fin_vge p (--(&b)) x <=> nv_dig_fin_zp p (x * &p pow b))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`p:num`; `x:real`; `0`; `b:num`] NV_DIG_FIN_VGE_EXACT) THEN
  ASM_REWRITE_TAC[REAL_SUB_LZERO; real_pow; REAL_DIV_1]);;

let NV_DIG_FIN_VGE_MONO = prove
 (`forall p k l x. l <= k /\ nv_dig_fin_vge p k x ==> nv_dig_fin_vge p l x`,
  REWRITE_TAC[nv_dig_fin_vge] THEN MESON_TAC[REAL_LE_TRANS]);;

let NV_DIG_FIN_VGE_0 = prove
 (`forall p k. prime p ==> nv_dig_fin_vge p k (&0)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[nv_dig_fin_vge] THEN
  MP_TAC(SPEC `k:real` REAL_ARCH_SIMPLE) THEN
  DISCH_THEN(X_CHOOSE_TAC `a:num`) THEN
  MAP_EVERY EXISTS_TAC [`a:num`; `0`] THEN
  ASM_REWRITE_TAC[REAL_SUB_RZERO; REAL_MUL_LZERO; real_div] THEN
  ASM_SIMP_TAC[NV_DIG_FIN_ZP_0]);;

let NV_DIG_FIN_VGE_ZP_IMP = prove
 (`forall p x. prime p /\ nv_dig_fin_zp p x ==> nv_dig_fin_vge p (&0) x`,
  MESON_TAC[NV_DIG_FIN_VGE_ZP]);;

let NV_DIG_FIN_VGE_IMP_ZP = prove
 (`forall p k x. prime p /\ &0 <= k /\ nv_dig_fin_vge p k x ==> nv_dig_fin_zp p x`,
  MESON_TAC[NV_DIG_FIN_VGE_ZP; NV_DIG_FIN_VGE_MONO]);;

let NV_DIG_FIN_VGE_INTEGER = prove
 (`forall p x. prime p /\ integer x ==> nv_dig_fin_vge p (&0) x`,
  MESON_TAC[NV_DIG_FIN_VGE_ZP; NV_DIG_FIN_ZP_INTEGER]);;

let NV_DIG_FIN_VGE_NUM = prove
 (`forall p n. prime p ==> nv_dig_fin_vge p (&0) (&n)`,
  MESON_TAC[NV_DIG_FIN_VGE_ZP; NV_DIG_FIN_ZP_NUM]);;

let NV_DIG_FIN_VGE_NEG = prove
 (`forall p k x. nv_dig_fin_vge p k x ==> nv_dig_fin_vge p k (--x)`,
  REWRITE_TAC[nv_dig_fin_vge] THEN REPEAT STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`a:num`; `b:num`] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[real_div; REAL_MUL_LNEG] THEN
  ASM_SIMP_TAC[GSYM real_div; NV_DIG_FIN_ZP_NEG]);;

let NV_DIG_FIN_VGE_NEG_EQ = prove
 (`forall p k x. nv_dig_fin_vge p k (--x) <=> nv_dig_fin_vge p k x`,
  MESON_TAC[NV_DIG_FIN_VGE_NEG; REAL_NEG_NEG]);;

let NV_DIG_FIN_VGE_ADD = prove
 (`forall p k x y. prime p /\ nv_dig_fin_vge p k x /\ nv_dig_fin_vge p k y ==> nv_dig_fin_vge p k (x + y)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[nv_dig_fin_vge] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2
   (X_CHOOSE_THEN `a:num` (X_CHOOSE_THEN `b:num` STRIP_ASSUME_TAC))
   (X_CHOOSE_THEN `a':num` (X_CHOOSE_THEN `b':num` STRIP_ASSUME_TAC)))) THEN
  DISJ_CASES_TAC(REAL_ARITH `&a - &b <= &a' - &b' \/ &a' - &b' <= &a - &b`)
  THENL
   [MAP_EVERY EXISTS_TAC [`a:num`; `b:num`] THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[REAL_ADD_RDISTRIB] THEN
    MATCH_MP_TAC NV_DIG_FIN_ZP_ADD THEN ASM_MESON_TAC[NV_DIG_FIN_VGE_REPR];
    MAP_EVERY EXISTS_TAC [`a':num`; `b':num`] THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[REAL_ADD_RDISTRIB] THEN
    MATCH_MP_TAC NV_DIG_FIN_ZP_ADD THEN ASM_MESON_TAC[NV_DIG_FIN_VGE_REPR]]);;

let NV_DIG_FIN_VGE_SUB = prove
 (`forall p k x y. prime p /\ nv_dig_fin_vge p k x /\ nv_dig_fin_vge p k y ==> nv_dig_fin_vge p k (x - y)`,
  SIMP_TAC[real_sub; NV_DIG_FIN_VGE_ADD; NV_DIG_FIN_VGE_NEG]);;

let NV_DIG_FIN_VGE_SUM = prove
 (`forall p k (f:A->real) s. prime p /\ FINITE s /\ (forall i. i IN s ==> nv_dig_fin_vge p k (f i))
             ==> nv_dig_fin_vge p k (sum s f)`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  DISCH_TAC THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  ASM_SIMP_TAC[SUM_CLAUSES; NV_DIG_FIN_VGE_0; FORALL_IN_INSERT; NV_DIG_FIN_VGE_ADD]);;

let NV_DIG_FIN_VGE_MUL = prove
 (`forall p k l x y. prime p /\ nv_dig_fin_vge p k x /\ nv_dig_fin_vge p l y
               ==> nv_dig_fin_vge p (k + l) (x * y)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[nv_dig_fin_vge] THEN
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
    MP_TAC(SPECL [`p:num`; `a:num`] NV_DIG_FIN_PPOW_NZ) THEN
    MP_TAC(SPECL [`p:num`; `a':num`] NV_DIG_FIN_PPOW_NZ) THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC REAL_FIELD;
    ASM_SIMP_TAC[NV_DIG_FIN_ZP_MUL]]);;

let NV_DIG_FIN_VGE_PRODUCT = prove
 (`forall p k (f:A->real) s. prime p /\ FINITE s /\ (forall i. i IN s ==> nv_dig_fin_vge p (k i) (f i))
             ==> nv_dig_fin_vge p (sum s k) (product s f)`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  DISCH_TAC THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  ASM_SIMP_TAC[SUM_CLAUSES; PRODUCT_CLAUSES; FORALL_IN_INSERT] THEN
  ASM_SIMP_TAC[NV_DIG_FIN_VGE_ZP; NV_DIG_FIN_ZP_1; NV_DIG_FIN_VGE_MUL]);;

let NV_DIG_FIN_VGE_ZP_MUL = prove
 (`forall p k c x. prime p /\ nv_dig_fin_zp p c /\ nv_dig_fin_vge p k x ==> nv_dig_fin_vge p k (c * x)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`p:num`; `&0`; `k:real`; `c:real`; `x:real`] NV_DIG_FIN_VGE_MUL) THEN
  ASM_SIMP_TAC[NV_DIG_FIN_VGE_ZP; REAL_ADD_LID]);;

let NV_DIG_FIN_VGE_MUL_ZP = prove
 (`forall p k c x. prime p /\ nv_dig_fin_zp p c /\ nv_dig_fin_vge p k x ==> nv_dig_fin_vge p k (x * c)`,
  MESON_TAC[NV_DIG_FIN_VGE_ZP_MUL; REAL_MUL_SYM]);;

let NV_DIG_FIN_VGE_PPOW = prove
 (`forall p n. prime p ==> nv_dig_fin_vge p (&n) (&p pow n)`,
  SIMP_TAC[NV_DIG_FIN_VGE_POS] THEN SIMP_TAC[REAL_DIV_REFL; NV_DIG_FIN_PPOW_NZ; NV_DIG_FIN_ZP_1]);;

let NV_DIG_FIN_VGE_PPOW_MUL = prove
 (`forall p k n x. prime p ==> (nv_dig_fin_vge p (k + &n) (&p pow n * x) <=> nv_dig_fin_vge p k x)`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL
   [REWRITE_TAC[nv_dig_fin_vge] THEN STRIP_TAC THEN
    MAP_EVERY EXISTS_TAC [`a:num`; `b + n:num`] THEN CONJ_TAC THENL
     [REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN ASM_REAL_ARITH_TAC;
      FIRST_X_ASSUM(MP_TAC o check (is_comb o concl)) THEN
      MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
      REWRITE_TAC[REAL_POW_ADD] THEN REAL_ARITH_TAC];
    DISCH_TAC THEN ONCE_REWRITE_TAC[REAL_ADD_SYM] THEN
    MATCH_MP_TAC NV_DIG_FIN_VGE_MUL THEN ASM_SIMP_TAC[NV_DIG_FIN_VGE_PPOW]]);;

let NV_DIG_FIN_VGE_PPOW_DIV = prove
 (`forall p k n x. prime p ==> (nv_dig_fin_vge p k (x / &p pow n) <=> nv_dig_fin_vge p (k + &n) x)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`p:num`; `k:real`; `n:num`; `x / &p pow n`] NV_DIG_FIN_VGE_PPOW_MUL) THEN
  ASM_SIMP_TAC[REAL_DIV_LMUL; NV_DIG_FIN_PPOW_NZ] THEN MESON_TAC[]);;

let NV_DIG_FIN_VGE_PMUL = prove
 (`forall p k x. prime p ==> (nv_dig_fin_vge p (k + &1) (&p * x) <=> nv_dig_fin_vge p k x)`,
  MESON_TAC[NV_DIG_FIN_VGE_PPOW_MUL; REAL_POW_1]);;

let NV_DIG_FIN_VGE_DIV_NUM = prove
 (`forall p k x n. prime p /\ ~(p divides n) /\ nv_dig_fin_vge p k x ==> nv_dig_fin_vge p k (x / &n)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[real_div] THEN
  MATCH_MP_TAC NV_DIG_FIN_VGE_MUL_ZP THEN ASM_SIMP_TAC[NV_DIG_FIN_ZP_INV_NUM]);;

let NV_DIG_FIN_VGE_NUM_DIVIDES = prove
 (`forall p k m. prime p ==> (nv_dig_fin_vge p (&k) (&m) <=> (p EXP k) divides m)`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[NV_DIG_FIN_VGE_POS] THEN EQ_TAC THENL
   [REWRITE_TAC[nv_dig_fin_zp; LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`u:real`; `n:num`] THEN STRIP_TAC THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP NV_DIG_FIN_NDIV_NZ) THEN
    MP_TAC(SPECL [`p:num`; `k:num`] NV_DIG_FIN_PPOW_NZ) THEN ASM_REWRITE_TAC[] THEN
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
    ASM_SIMP_TAC[REAL_FIELD `~(a = &0) ==> (a * q) / a = q`; NV_DIG_FIN_PPOW_NZ] THEN
    ASM_SIMP_TAC[NV_DIG_FIN_ZP_NUM]]);;

let NV_DIG_FIN_VGE_1_NUM = prove
 (`forall p m. prime p ==> (nv_dig_fin_vge p (&1) (&m) <=> p divides m)`,
  SIMP_TAC[NV_DIG_FIN_VGE_NUM_DIVIDES; EXP_1]);;


(* ------------------------------------------------------------------------- *)
(* Determinants: valuation of ndet, and the atom expansion lemma.            *)
(* ------------------------------------------------------------------------- *)

let NV_DIG_FIN_NDET_RING = prove
 (`forall s a. ndet s a = ring_det real_ring s a`,
  REWRITE_TAC[ndet; ring_det; REAL_RING_SUM; REAL_RING_PRODUCT; ring_sign;
              sign; REAL_RING_CLAUSES]);;

let NV_DIG_FIN_ZP_SIGN = prove
 (`forall p q. prime p ==> nv_dig_fin_zp p (sign q)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[sign] THEN COND_CASES_TAC THEN
  ASM_SIMP_TAC[NV_DIG_FIN_ZP_1; NV_DIG_FIN_ZP_NEG]);;

let NV_DIG_FIN_VGE_NDET_ROWS = prove
 (`forall p s (b:num->num->real) w.
        prime p /\ FINITE s /\
        (forall k i. k IN s /\ i IN s ==> nv_dig_fin_vge p (w k) (b k i))
        ==> nv_dig_fin_vge p (sum s w) (ndet s b)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[ndet] THEN
  MATCH_MP_TAC NV_DIG_FIN_VGE_SUM THEN ASM_SIMP_TAC[FINITE_PERMUTATIONS] THEN
  X_GEN_TAC `q:num->num` THEN REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN
  MATCH_MP_TAC NV_DIG_FIN_VGE_ZP_MUL THEN ASM_SIMP_TAC[NV_DIG_FIN_ZP_SIGN] THEN
  MATCH_MP_TAC NV_DIG_FIN_VGE_PRODUCT THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[PERMUTES_IN_IMAGE]);;

let NV_DIG_FIN_NDET_TRANSP = prove
 (`forall s (a:num->num->real). FINITE s ==> ndet s (\i j. a j i) = ndet s a`,
  SIMP_TAC[NV_DIG_FIN_NDET_RING; RING_DET_TRANSP]);;

let NV_DIG_FIN_VGE_NDET_COLS = prove
 (`forall p s (a:num->num->real) w.
        prime p /\ FINITE s /\
        (forall i k. i IN s /\ k IN s ==> nv_dig_fin_vge p (w k) (a i k))
        ==> nv_dig_fin_vge p (sum s w) (ndet s a)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(fun th -> ONCE_REWRITE_TAC[GSYM(MATCH_MP NV_DIG_FIN_NDET_TRANSP th)]) THEN
  MATCH_MP_TAC NV_DIG_FIN_VGE_NDET_ROWS THEN ASM_SIMP_TAC[]);;

let NV_DIG_FIN_VGE_NDET_ATOMS = prove
 (`forall p s t (a:num->num->real) (c:B->num->real) (v:B->num->real) (w:B->num->real) d.
        prime p /\ FINITE s /\ FINITE t /\
        (forall i k. i IN s /\ k IN s ==> a i k = sum t (\x. c x k * v x i)) /\
        (forall x i k. x IN t /\ i IN s /\ k IN s ==> nv_dig_fin_vge p (w x k) (c x k * v x i)) /\
        (forall f. (forall k. k IN s ==> f k IN t) /\
             (forall k1 k2. k1 IN s /\ k2 IN s /\ f k1 = f k2 ==> k1 = k2)
             ==> d <= sum s (\k. w (f k) k))
        ==> nv_dig_fin_vge p d (ndet s a)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(fun th -> ONCE_REWRITE_TAC[GSYM(MATCH_MP NV_DIG_FIN_NDET_TRANSP th)]) THEN
  REWRITE_TAC[NV_DIG_FIN_NDET_RING] THEN
  MP_TAC(ISPECL [`real_ring`; `s:num->bool`; `(\k. t):num->B->bool`;
                 `(\i j. (a:num->num->real) j i)`;
                 `(\k x i. (c:B->num->real) x k * (v:B->num->real) x i)`]
         RING_DET_MULTILINEAR) THEN
  ASM_SIMP_TAC[REAL_RING_CLAUSES; IN_UNIV; REAL_RING_SUM] THEN
  DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC NV_DIG_FIN_VGE_SUM THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ASM_SIMP_TAC[FINITE_CARTESIAN_PRODUCT] THEN DISJ2_TAC THEN
    MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `s:num->bool` THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `mu:num->B` THEN REWRITE_TAC[IN_CARTESIAN_PRODUCT] THEN
  STRIP_TAC THEN
  ASM_CASES_TAC
   `forall k1 k2. k1 IN s /\ k2 IN s /\ (mu:num->B) k1 = mu k2 ==> k1 = k2`
  THENL
   [MATCH_MP_TAC NV_DIG_FIN_VGE_MONO THEN
    EXISTS_TAC `sum s (\k. (w:B->num->real) ((mu:num->B) k) k)` THEN
    CONJ_TAC THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[GSYM NV_DIG_FIN_NDET_RING] THEN
    MATCH_MP_TAC NV_DIG_FIN_VGE_NDET_ROWS THEN ASM_SIMP_TAC[];
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
  ASM_SIMP_TAC[REAL_MUL_RZERO; NV_DIG_FIN_VGE_0]);;

let NV_DIG_FIN_SUM_INDICATOR = prove
 (`forall s P. FINITE s
         ==> sum s (\k:A. if P k then &1 else &0) = &(CARD {k | k IN s /\ P k})`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM SUM_RESTRICT_SET] THEN
  ASM_SIMP_TAC[SUM_CONST; FINITE_RESTRICT; REAL_MUL_RID]);;

let NV_DIG_FIN_MIN_LEMMA = prove
 (`forall r q n R S. r <= R /\ q <= S /\ r + q <= n
               ==> 2 * r + q <= MIN (2 * n) (MIN (n + R) (2 * R + S))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[MIN] THEN
  REPEAT COND_CASES_TAC THEN ASM_ARITH_TAC);;

let NV_DIG_FIN_VGE_NDET_ATOMS_012 = prove
 (`forall p s t (a:num->num->real) (c:B->num->real) (v:B->num->real) t1 t2 R S.
        prime p /\ FINITE s /\ FINITE t /\
        t1 SUBSET t /\ t2 SUBSET t /\ DISJOINT t1 t2 /\
        CARD t1 <= S /\ CARD t2 <= R /\
        (forall i k. i IN s /\ k IN s ==> a i k = sum t (\x. c x k * v x i)) /\
        (forall x k. x IN t /\ k IN s ==> nv_dig_fin_zp p (c x k)) /\
        (forall x i. x IN t2 /\ i IN s ==> nv_dig_fin_vge p (--(&2)) (v x i)) /\
        (forall x i. x IN t1 /\ i IN s ==> nv_dig_fin_vge p (--(&1)) (v x i)) /\
        (forall x i. x IN t /\ ~(x IN t1) /\ ~(x IN t2) /\ i IN s ==> nv_dig_fin_zp p (v x i))
        ==> nv_dig_fin_vge p (--(&(MIN (2 * CARD s) (MIN (CARD s + R) (2 * R + S)))))
                    (ndet s a)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC NV_DIG_FIN_VGE_NDET_ATOMS THEN
  MAP_EVERY EXISTS_TAC
   [`t:B->bool`; `c:B->num->real`; `v:B->num->real`;
    `\(x:B) (k:num). --(&2 * (if x IN t2 then &1 else &0) +
                        (if x IN t1 then &1 else &0))`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`x:B`; `i:num`; `k:num`] THEN STRIP_TAC THEN
    MATCH_MP_TAC NV_DIG_FIN_VGE_ZP_MUL THEN ASM_SIMP_TAC[] THEN
    ASM_CASES_TAC `(x:B) IN t2` THENL
     [SUBGOAL_THEN `~((x:B) IN t1)` ASSUME_TAC THENL
       [ASM SET_TAC[]; ASM_SIMP_TAC[]] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM_SIMP_TAC[];
      ASM_REWRITE_TAC[]] THEN
    ASM_CASES_TAC `(x:B) IN t1` THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM_SIMP_TAC[NV_DIG_FIN_VGE_ZP];
    ALL_TAC] THEN
  X_GEN_TAC `f:num->B` THEN STRIP_TAC THEN
  REWRITE_TAC[SUM_NEG; SUM_ADD_NUMSEG] THEN
  ASM_SIMP_TAC[SUM_ADD; SUM_LMUL; NV_DIG_FIN_SUM_INDICATOR] THEN
  REWRITE_TAC[REAL_LE_NEG2; REAL_OF_NUM_MUL; REAL_OF_NUM_ADD; REAL_OF_NUM_LE] THEN
  MATCH_MP_TAC NV_DIG_FIN_MIN_LEMMA THEN REPEAT CONJ_TAC THENL
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

let NV_DIG_FIN_INTEGER_PRODUCT = prove
 (`forall f (s:A->bool). FINITE s /\ (forall i. i IN s ==> integer(f i))
                   ==> integer(product s f)`,
  GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[PRODUCT_CLAUSES; INTEGER_CLOSED; FORALL_IN_INSERT]);;

let NV_DIG_FIN_INTEGER_LOCAL_NUM = prove
 (`forall q m. ~(q = 0) /\ (forall r. prime r ==> nv_dig_fin_zp r (&m / &q)) ==> integer(&m / &q)`,
  MATCH_MP_TAC num_WF THEN X_GEN_TAC `q:num` THEN DISCH_TAC THEN
  X_GEN_TAC `m:num` THEN STRIP_TAC THEN
  ASM_CASES_TAC `q = 1` THENL
   [ASM_REWRITE_TAC[REAL_DIV_1; INTEGER_CLOSED]; ALL_TAC] THEN
  FIRST_ASSUM(X_CHOOSE_THEN `r:num` STRIP_ASSUME_TAC o MATCH_MP PRIME_FACTOR) THEN
  SUBGOAL_THEN `nv_dig_fin_zp r (&m / &q)` MP_TAC THENL [ASM_MESON_TAC[]; REWRITE_TAC[nv_dig_fin_zp]] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real` (X_CHOOSE_THEN `w:num` STRIP_ASSUME_TAC)) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP NV_DIG_FIN_NDIV_NZ) THEN
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

let NV_DIG_FIN_INTEGER_LOCAL = prove
 (`forall y. rational y /\ (forall p. prime p ==> nv_dig_fin_zp p y) ==> integer y`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[GSYM INTEGER_ABS] THEN
  SUBGOAL_THEN `forall p. prime p ==> nv_dig_fin_zp p (abs y)` MP_TAC THENL
   [REPEAT STRIP_TAC THEN
    DISJ_CASES_TAC(REAL_ARITH `abs y = y \/ abs y = --y`) THEN
    ASM_SIMP_TAC[NV_DIG_FIN_ZP_NEG];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [RATIONAL_ALT]) THEN
  DISCH_THEN(X_CHOOSE_THEN `m:num` (X_CHOOSE_THEN `q:num` STRIP_ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MATCH_MP_TAC NV_DIG_FIN_INTEGER_LOCAL_NUM THEN ASM_REWRITE_TAC[]);;

let NV_DIG_FIN_CEIL_EXISTS = prove
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

let NV_DIG_FIN_LOG_LOWER = prove
 (`forall x M (K:num->real).
        rational x /\ ~(x = &0) /\
        (forall p. prime p /\ p <= M ==> nv_dig_fin_vge p (--(K p)) x) /\
        (forall p. prime p /\ M < p ==> nv_dig_fin_zp p x)
        ==> --(sum {p | prime p /\ p <= M} (\p. (abs(K p) + &1) * log(&p)))
            <= log(abs x)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(GEN `p:num` (SPEC `(K:num->real) p` NV_DIG_FIN_CEIL_EXISTS)) THEN
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
   [EXPAND_TAC "D" THEN MATCH_MP_TAC NV_DIG_FIN_INTEGER_PRODUCT THEN
    ASM_SIMP_TAC[INTEGER_CLOSED];
    ALL_TAC] THEN
  SUBGOAL_THEN `integer(x * D)` ASSUME_TAC THENL
   [MATCH_MP_TAC NV_DIG_FIN_INTEGER_LOCAL THEN CONJ_TAC THENL
     [ASM_MESON_TAC[RATIONAL_MUL; RATIONAL_INTEGER]; ALL_TAC] THEN
    X_GEN_TAC `q:num` THEN DISCH_TAC THEN
    ASM_CASES_TAC `q:num <= M` THENL
     [SUBGOAL_THEN `(q:num) IN P` ASSUME_TAC THENL
       [EXPAND_TAC "P" THEN REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
      MP_TAC(ISPECL [`\p. &p pow (e p)`; `P:num->bool`; `q:num`] PRODUCT_DELETE) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC NV_DIG_FIN_ZP_MUL THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [ASM_SIMP_TAC[GSYM NV_DIG_FIN_VGE_NEGPOW] THEN MATCH_MP_TAC NV_DIG_FIN_VGE_MONO THEN
        EXISTS_TAC `--((K:num->real) q)` THEN ASM_SIMP_TAC[] THEN
        FIRST_X_ASSUM(MP_TAC o SPEC `q:num`) THEN REAL_ARITH_TAC;
        MATCH_MP_TAC NV_DIG_FIN_ZP_INTEGER THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC NV_DIG_FIN_INTEGER_PRODUCT THEN
        ASM_SIMP_TAC[INTEGER_CLOSED; FINITE_DELETE]];
      MATCH_MP_TAC NV_DIG_FIN_ZP_MUL THEN ASM_SIMP_TAC[NV_DIG_FIN_ZP_INTEGER] THEN
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
let nv_dig_fin_flog = new_definition
 `nv_dig_fin_flog p n = CARD {e | 1 <= e /\ p EXP e <= n}`;;

(* H*_z of Equation (18) *)
let nv_dig_fin_hstar = new_definition
 `nv_dig_fin_hstar z = if EVEN z then cat_c (z DIV 2)
                else inv(&z * cat_c ((z - 1) DIV 2))`;;

(* Coefficient of t^d in (1 - t^2)^((p-1)/2) (zero for d >= p) *)
let nv_dig_fin_E = new_definition
 `nv_dig_fin_E p d = if EVEN d /\ d < p
              then (--(&1)) pow (d DIV 2) * &(binom((p - 1) DIV 2,d DIV 2))
              else &0`;;

(* M'(a - 1, j) with the convention M'(-1, j) = k^+_(j+1), Equation (15) *)
let nv_dig_fin_M0x = new_definition
 `nv_dig_fin_M0x a j = if a = 0 then cat_kplus (j + 1) else cat_M0 (a - 1) j`;;

(* The odd-prime loss: Equation (38) for 2p <= H, Lemma 3.3 for 2p > H.     *)
(* Natural-number truncated subtraction implements (.)_+.                    *)
let nv_dig_fin_loss = new_definition
 `nv_dig_fin_loss N p =
    if 2 * p <= 65 * N then
      2 * (48 * N) -
      ((MIN p (MIN (59 * N - p) (19 * N)) - MAX (7 * N) (65 * N - 2 * p)) - 4 * N)
    else
      let R = (59 * N - p) + ((59 * N - p) - 19 * N) +
              ((65 * N - p) - MAX (7 * N) (59 * N - p)) in
      let S = (MIN (19 * N) (59 * N - p) - 7 * N) +
              (MIN (7 * N) (65 * N - p) - (59 * N - p)) in
      MIN (2 * (48 * N)) (MIN (48 * N + R) (2 * R + S))`;;


(* ---- copied from src/catalan_fin_dig_base.ml ---- *)
(* ========================================================================= *)
(* nv_dig_fin_dig: congruences modulo p between local integers (base library).     *)
(* ========================================================================= *)


prioritize_real();;

let nv_dig_fin_dig_cg = new_definition
 `nv_dig_fin_dig_cg p x y <=> nv_dig_fin_zp p x /\ nv_dig_fin_zp p y /\ nv_dig_fin_vge p (&1) (x - y)`;;

let nv_dig_fin_dig_unit = new_definition
 `nv_dig_fin_dig_unit p u <=> ~(u = &0) /\ nv_dig_fin_zp p u /\ nv_dig_fin_zp p (inv u)`;;

let NV_DIG_FIN_DIG_CG_REFL = prove
 (`forall p x. prime p /\ nv_dig_fin_zp p x ==> nv_dig_fin_dig_cg p x x`,
  SIMP_TAC[nv_dig_fin_dig_cg; REAL_SUB_REFL; NV_DIG_FIN_VGE_0]);;

let NV_DIG_FIN_DIG_CG_SYM = prove
 (`forall p x y. nv_dig_fin_dig_cg p x y ==> nv_dig_fin_dig_cg p y x`,
  REWRITE_TAC[nv_dig_fin_dig_cg] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  ONCE_REWRITE_TAC[REAL_ARITH `y - x = --(x - y)`] THEN
  ASM_REWRITE_TAC[NV_DIG_FIN_VGE_NEG_EQ]);;

let NV_DIG_FIN_DIG_CG_TRANS = prove
 (`forall p x y z. prime p /\ nv_dig_fin_dig_cg p x y /\ nv_dig_fin_dig_cg p y z ==> nv_dig_fin_dig_cg p x z`,
  REWRITE_TAC[nv_dig_fin_dig_cg] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  ONCE_REWRITE_TAC[REAL_ARITH `x - z = (x - y) + (y - z)`] THEN
  ASM_SIMP_TAC[NV_DIG_FIN_VGE_ADD]);;

let NV_DIG_FIN_DIG_CG_ADD = prove
 (`forall p x y x' y'. prime p /\ nv_dig_fin_dig_cg p x y /\ nv_dig_fin_dig_cg p x' y'
                 ==> nv_dig_fin_dig_cg p (x + x') (y + y')`,
  REWRITE_TAC[nv_dig_fin_dig_cg] THEN REPEAT STRIP_TAC THEN ASM_SIMP_TAC[NV_DIG_FIN_ZP_ADD] THEN
  ONCE_REWRITE_TAC[REAL_ARITH `(x + x') - (y + y') = (x - y) + (x' - y')`] THEN
  ASM_SIMP_TAC[NV_DIG_FIN_VGE_ADD]);;

let NV_DIG_FIN_DIG_CG_NEG = prove
 (`forall p x y. nv_dig_fin_dig_cg p x y ==> nv_dig_fin_dig_cg p (--x) (--y)`,
  REWRITE_TAC[nv_dig_fin_dig_cg; NV_DIG_FIN_ZP_NEG_EQ] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[REAL_ARITH `--x - --y = --(x - y)`; NV_DIG_FIN_VGE_NEG_EQ]);;

let NV_DIG_FIN_DIG_CG_SUB = prove
 (`forall p x y x' y'. prime p /\ nv_dig_fin_dig_cg p x y /\ nv_dig_fin_dig_cg p x' y'
                 ==> nv_dig_fin_dig_cg p (x - x') (y - y')`,
  SIMP_TAC[real_sub; NV_DIG_FIN_DIG_CG_ADD; NV_DIG_FIN_DIG_CG_NEG]);;

let NV_DIG_FIN_DIG_CG_MUL = prove
 (`forall p x y x' y'. prime p /\ nv_dig_fin_dig_cg p x y /\ nv_dig_fin_dig_cg p x' y'
                 ==> nv_dig_fin_dig_cg p (x * x') (y * y')`,
  REWRITE_TAC[nv_dig_fin_dig_cg] THEN REPEAT STRIP_TAC THEN ASM_SIMP_TAC[NV_DIG_FIN_ZP_MUL] THEN
  ONCE_REWRITE_TAC[REAL_ARITH `x * x' - y * y' = (x - y) * x' + y * (x' - y')`] THEN
  MATCH_MP_TAC NV_DIG_FIN_VGE_ADD THEN ASM_SIMP_TAC[NV_DIG_FIN_VGE_MUL_ZP; NV_DIG_FIN_VGE_ZP_MUL]);;

let NV_DIG_FIN_DIG_CG_POW = prove
 (`forall p x y n. prime p /\ nv_dig_fin_dig_cg p x y ==> nv_dig_fin_dig_cg p (x pow n) (y pow n)`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN
  ASM_SIMP_TAC[real_pow; NV_DIG_FIN_DIG_CG_REFL; NV_DIG_FIN_ZP_1; NV_DIG_FIN_DIG_CG_MUL]);;

let NV_DIG_FIN_DIG_CG_SUM = prove
 (`forall p (f:A->real) g s. prime p /\ FINITE s /\ (forall i. i IN s ==> nv_dig_fin_dig_cg p (f i) (g i))
             ==> nv_dig_fin_dig_cg p (sum s f) (sum s g)`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN DISCH_TAC THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  ASM_SIMP_TAC[SUM_CLAUSES; FORALL_IN_INSERT; NV_DIG_FIN_DIG_CG_ADD; NV_DIG_FIN_DIG_CG_REFL; NV_DIG_FIN_ZP_0]);;

let NV_DIG_FIN_DIG_CG_EQ = prove
 (`forall p x y x' y'. nv_dig_fin_dig_cg p x y /\ x' = x /\ y' = y ==> nv_dig_fin_dig_cg p x' y'`,
  MESON_TAC[]);;

let NV_DIG_FIN_DIG_CG_0 = prove
 (`forall p x. prime p ==> (nv_dig_fin_dig_cg p x (&0) <=> nv_dig_fin_vge p (&1) x)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[nv_dig_fin_dig_cg; REAL_SUB_RZERO] THEN
  ASM_SIMP_TAC[NV_DIG_FIN_ZP_0] THEN EQ_TAC THEN SIMP_TAC[] THEN
  ASM_MESON_TAC[NV_DIG_FIN_VGE_IMP_ZP; REAL_POS]);;

let NV_DIG_FIN_DIG_CG_PMUL = prove
 (`forall p x. prime p /\ nv_dig_fin_zp p x ==> nv_dig_fin_dig_cg p (&p * x) (&0)`,
  SIMP_TAC[NV_DIG_FIN_DIG_CG_0] THEN REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[REAL_ARITH `&1 = &0 + &1`] THEN
  ASM_SIMP_TAC[NV_DIG_FIN_VGE_PMUL; NV_DIG_FIN_VGE_ZP]);;

let NV_DIG_FIN_DIG_CG_ZP = prove
 (`forall p x y. nv_dig_fin_dig_cg p x y ==> nv_dig_fin_zp p x /\ nv_dig_fin_zp p y`,
  SIMP_TAC[nv_dig_fin_dig_cg]);;

let NV_DIG_FIN_DIG_CG_VGE = prove
 (`forall p x y. nv_dig_fin_dig_cg p x y ==> nv_dig_fin_vge p (&1) (x - y)`,
  SIMP_TAC[nv_dig_fin_dig_cg]);;

let NV_DIG_FIN_DIG_CG_ZERO_MUL = prove
 (`forall p x y. prime p /\ nv_dig_fin_dig_cg p x (&0) /\ nv_dig_fin_zp p y
           ==> nv_dig_fin_dig_cg p (x * y) (&0) /\ nv_dig_fin_dig_cg p (y * x) (&0)`,
  REPEAT STRIP_TAC THENL
   [MP_TAC(SPECL [`p:num`; `x:real`; `&0`; `y:real`; `y:real`] NV_DIG_FIN_DIG_CG_MUL);
    MP_TAC(SPECL [`p:num`; `y:real`; `y:real`; `x:real`; `&0`] NV_DIG_FIN_DIG_CG_MUL)] THEN
  ASM_SIMP_TAC[NV_DIG_FIN_DIG_CG_REFL; REAL_MUL_LZERO; REAL_MUL_RZERO]);;

(* ------------------------------------------------------------------------- *)
(* Units.                                                                    *)
(* ------------------------------------------------------------------------- *)

let NV_DIG_FIN_DIG_UNIT_NUM = prove
 (`forall p n. prime p /\ ~(p divides n) ==> nv_dig_fin_dig_unit p (&n)`,
  SIMP_TAC[nv_dig_fin_dig_unit; NV_DIG_FIN_ZP_NUM; NV_DIG_FIN_ZP_INV_NUM] THEN
  MESON_TAC[NV_DIG_FIN_NDIV_NZ]);;

let NV_DIG_FIN_DIG_UNIT_NUM_LT = prove
 (`forall p n. prime p /\ 0 < n /\ n < p ==> nv_dig_fin_dig_unit p (&n)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC NV_DIG_FIN_DIG_UNIT_NUM THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o MATCH_MP DIVIDES_LE) THEN ASM_ARITH_TAC);;

let NV_DIG_FIN_DIG_UNIT_NZ = prove
 (`forall p u. nv_dig_fin_dig_unit p u ==> ~(u = &0)`,
  SIMP_TAC[nv_dig_fin_dig_unit]);;

let NV_DIG_FIN_DIG_UNIT_ZP = prove
 (`forall p u. nv_dig_fin_dig_unit p u ==> nv_dig_fin_zp p u /\ nv_dig_fin_zp p (inv u)`,
  SIMP_TAC[nv_dig_fin_dig_unit]);;

let NV_DIG_FIN_DIG_UNIT_INV = prove
 (`forall p u. nv_dig_fin_dig_unit p u ==> nv_dig_fin_dig_unit p (inv u)`,
  SIMP_TAC[nv_dig_fin_dig_unit; REAL_INV_INV; REAL_INV_EQ_0]);;

let NV_DIG_FIN_DIG_UNIT_MUL = prove
 (`forall p u v. prime p /\ nv_dig_fin_dig_unit p u /\ nv_dig_fin_dig_unit p v ==> nv_dig_fin_dig_unit p (u * v)`,
  SIMP_TAC[nv_dig_fin_dig_unit; REAL_INV_MUL; NV_DIG_FIN_ZP_MUL; REAL_ENTIRE]);;

let NV_DIG_FIN_DIG_UNIT_DIV = prove
 (`forall p u v. prime p /\ nv_dig_fin_dig_unit p u /\ nv_dig_fin_dig_unit p v ==> nv_dig_fin_dig_unit p (u / v)`,
  SIMP_TAC[real_div; NV_DIG_FIN_DIG_UNIT_MUL; NV_DIG_FIN_DIG_UNIT_INV]);;

let NV_DIG_FIN_DIG_UNIT_NEG = prove
 (`forall p u. nv_dig_fin_dig_unit p u ==> nv_dig_fin_dig_unit p (--u)`,
  SIMP_TAC[nv_dig_fin_dig_unit; REAL_INV_NEG; NV_DIG_FIN_ZP_NEG_EQ; REAL_NEG_EQ_0]);;

let NV_DIG_FIN_DIG_UNIT_POW = prove
 (`forall p u n. prime p /\ nv_dig_fin_dig_unit p u ==> nv_dig_fin_dig_unit p (u pow n)`,
  SIMP_TAC[nv_dig_fin_dig_unit; GSYM REAL_POW_INV; NV_DIG_FIN_ZP_POW; REAL_POW_EQ_0]);;

let NV_DIG_FIN_DIG_UNIT_1 = prove
 (`forall p. prime p ==> nv_dig_fin_dig_unit p (&1)`,
  SIMP_TAC[nv_dig_fin_dig_unit; REAL_INV_1; NV_DIG_FIN_ZP_1] THEN REAL_ARITH_TAC);;

(* A unit is not congruent to 0. *)
let NV_DIG_FIN_DIG_UNIT_NOT_CG0 = prove
 (`forall p u. prime p /\ nv_dig_fin_dig_unit p u ==> ~nv_dig_fin_vge p (&1) u`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `nv_dig_fin_vge p (&1) (u * inv u)` MP_TAC THENL
   [MATCH_MP_TAC NV_DIG_FIN_VGE_MUL_ZP THEN ASM_MESON_TAC[nv_dig_fin_dig_unit];
    SUBGOAL_THEN `u * inv u = &1` SUBST1_TAC THENL
     [ASM_MESON_TAC[REAL_MUL_RINV; NV_DIG_FIN_DIG_UNIT_NZ]; ALL_TAC] THEN
    ASM_SIMP_TAC[NV_DIG_FIN_VGE_1_NUM; DIVIDES_ONE] THEN ASM_MESON_TAC[PRIME_1]]);;

(* A local integer not divisible by p is a unit. *)
let NV_DIG_FIN_DIG_ZP_UNIT = prove
 (`forall p x. prime p /\ nv_dig_fin_zp p x /\ ~nv_dig_fin_vge p (&1) x ==> nv_dig_fin_dig_unit p x`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN DISCH_TAC THEN
  ASM_SIMP_TAC[NV_DIG_FIN_VGE_POS; REAL_POW_1] THEN
  GEN_REWRITE_TAC LAND_CONV [nv_dig_fin_zp] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`m:real`; `n:num`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC (CONJUNCTS_THEN2 ASSUME_TAC SUBST_ALL_TAC)) THEN
  REWRITE_TAC[is_int; LEFT_IMP_EXISTS_THM] THEN X_GEN_TAC `k:num` THEN
  DISCH_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP NV_DIG_FIN_NDIV_NZ) THEN
  MP_TAC(SPEC `p:num` PRIME_IMP_NZ) THEN ASM_REWRITE_TAC[GSYM REAL_OF_NUM_EQ] THEN
  DISCH_TAC THEN
  ASM_CASES_TAC `p divides k` THENL
   [UNDISCH_TAC `~nv_dig_fin_zp p (m / &n / &p)` THEN
    MATCH_MP_TAC(TAUT `a ==> ~a ==> b`) THEN
    UNDISCH_TAC `p divides k` THEN REWRITE_TAC[divides] THEN
    DISCH_THEN(X_CHOOSE_THEN `e:num` SUBST_ALL_TAC) THEN
    REWRITE_TAC[nv_dig_fin_zp] THEN
    FIRST_X_ASSUM(DISJ_CASES_THEN SUBST_ALL_TAC) THENL
     [MAP_EVERY EXISTS_TAC [`&e:real`; `n:num`];
      MAP_EVERY EXISTS_TAC [`--(&e):real`; `n:num`]] THEN
    ASM_SIMP_TAC[INTEGER_CLOSED; GSYM REAL_OF_NUM_MUL] THEN
    UNDISCH_TAC `~(&p = &0)` THEN UNDISCH_TAC `~(&n = &0)` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  SUBGOAL_THEN `~(&k = &0)` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_EQ] THEN DISCH_THEN SUBST_ALL_TAC THEN
    ASM_MESON_TAC[DIVIDES_0]; ALL_TAC] THEN
  REWRITE_TAC[nv_dig_fin_dig_unit] THEN
  FIRST_X_ASSUM(DISJ_CASES_THEN SUBST_ALL_TAC) THEN
  REPEAT CONJ_TAC THEN REWRITE_TAC[nv_dig_fin_zp] THENL
   [ALL_TAC; MAP_EVERY EXISTS_TAC [`&k:real`; `n:num`];
    MAP_EVERY EXISTS_TAC [`&n:real`; `k:num`];
    ALL_TAC; MAP_EVERY EXISTS_TAC [`--(&k):real`; `n:num`];
    MAP_EVERY EXISTS_TAC [`--(&n):real`; `k:num`]] THEN
  ASM_SIMP_TAC[INTEGER_CLOSED] THEN
  UNDISCH_TAC `~(&k = &0)` THEN UNDISCH_TAC `~(&n = &0)` THEN CONV_TAC REAL_FIELD);;

(* Congruent to a unit implies a unit, and inverses are congruent. *)
let NV_DIG_FIN_DIG_CG_INV = prove
 (`forall p u v. prime p /\ nv_dig_fin_dig_unit p u /\ nv_dig_fin_dig_cg p u v
           ==> nv_dig_fin_dig_unit p v /\ nv_dig_fin_dig_cg p (inv u) (inv v)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `nv_dig_fin_dig_unit p v` ASSUME_TAC THENL
   [MATCH_MP_TAC NV_DIG_FIN_DIG_ZP_UNIT THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[nv_dig_fin_dig_cg]; ALL_TAC] THEN DISCH_TAC THEN
    MP_TAC(SPECL [`p:num`; `u:real`] NV_DIG_FIN_DIG_UNIT_NOT_CG0) THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `u = (u - v) + v` SUBST1_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC NV_DIG_FIN_VGE_ADD THEN ASM_MESON_TAC[nv_dig_fin_dig_cg];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[nv_dig_fin_dig_cg] THEN
  REPEAT(CONJ_TAC THENL [ASM_MESON_TAC[nv_dig_fin_dig_unit]; ALL_TAC]) THEN
  SUBGOAL_THEN `inv u - inv v = (u - v) * --(inv u * inv v)` SUBST1_TAC THENL
   [MP_TAC(SPECL [`p:num`; `u:real`] NV_DIG_FIN_DIG_UNIT_NZ) THEN
    MP_TAC(SPECL [`p:num`; `v:real`] NV_DIG_FIN_DIG_UNIT_NZ) THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC REAL_FIELD;
    MATCH_MP_TAC NV_DIG_FIN_VGE_MUL_ZP THEN ASM_REWRITE_TAC[NV_DIG_FIN_ZP_NEG_EQ] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC NV_DIG_FIN_ZP_MUL THEN ASM_MESON_TAC[nv_dig_fin_dig_unit];
      ASM_MESON_TAC[nv_dig_fin_dig_cg]]]);;

let NV_DIG_FIN_DIG_CG_DIV = prove
 (`forall p x y u v. prime p /\ nv_dig_fin_dig_cg p x y /\ nv_dig_fin_dig_unit p u /\ nv_dig_fin_dig_cg p u v
               ==> nv_dig_fin_dig_cg p (x / u) (y / v)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[real_div] THEN
  MATCH_MP_TAC NV_DIG_FIN_DIG_CG_MUL THEN ASM_MESON_TAC[NV_DIG_FIN_DIG_CG_INV]);;

let NV_DIG_FIN_DIG_CG_DIV_NUM = prove
 (`forall p x y n. prime p /\ nv_dig_fin_dig_cg p x y /\ ~(p divides n)
             ==> nv_dig_fin_dig_cg p (x / &n) (y / &n)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC NV_DIG_FIN_DIG_CG_DIV THEN
  ASM_SIMP_TAC[NV_DIG_FIN_DIG_UNIT_NUM; NV_DIG_FIN_DIG_CG_REFL; NV_DIG_FIN_ZP_NUM]);;

(* Congruences of natural numbers. *)
let NV_DIG_FIN_DIG_CG_INTEGER = prove
 (`forall p x y. prime p /\ integer x /\ integer y /\ (exists k. integer k /\ x - y = &p * k)
           ==> nv_dig_fin_dig_cg p x y`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[nv_dig_fin_dig_cg; NV_DIG_FIN_ZP_INTEGER] THEN
  ONCE_REWRITE_TAC[REAL_ARITH `&1 = &0 + &1`] THEN
  ASM_SIMP_TAC[NV_DIG_FIN_VGE_PMUL; NV_DIG_FIN_VGE_INTEGER]);;

let NV_DIG_FIN_DIG_CG_NUM = prove
 (`forall p a b. prime p /\ (a == b) (mod p) ==> nv_dig_fin_dig_cg p (&a) (&b)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC NV_DIG_FIN_DIG_CG_INTEGER THEN
  ASM_REWRITE_TAC[INTEGER_CLOSED] THEN
  FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[CONG_CASES]) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[GSYM REAL_OF_NUM_ADD; GSYM REAL_OF_NUM_MUL] THENL
   [EXISTS_TAC `&q:real`; EXISTS_TAC `--(&q):real`] THEN
  SIMP_TAC[INTEGER_CLOSED] THEN REAL_ARITH_TAC);;


(* ------------------------------------------------------------------------- *)
(* Sums over a range in which only multiples of p survive.                   *)
(* ------------------------------------------------------------------------- *)

let NV_DIG_FIN_DIG_SUM_MULTIPLES = prove
 (`forall p a b f g.
        prime p /\
        (forall k. a <= k /\ k <= b /\ ~(p divides k) ==> nv_dig_fin_dig_cg p (f k) (&0)) /\
        (forall m. a <= m * p /\ m * p <= b ==> nv_dig_fin_dig_cg p (f (m * p)) (g m))
        ==> nv_dig_fin_dig_cg p (sum (a..b) f) (sum {m | a <= m * p /\ m * p <= b} g)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `FINITE {m | a <= m * p /\ m * p <= b:num}` ASSUME_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `0..b` THEN
    REWRITE_TAC[FINITE_NUMSEG; SUBSET; IN_ELIM_THM; IN_NUMSEG; LE_0] THEN
    X_GEN_TAC `m:num` THEN STRIP_TAC THEN
    TRANS_TAC LE_TRANS `m * p:num` THEN ASM_REWRITE_TAC[] THEN
    GEN_REWRITE_TAC LAND_CONV [ARITH_RULE `m = m * 1`] THEN REWRITE_TAC[LE_MULT_LCANCEL] THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP PRIME_GE_2) THEN
    ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `sum (a..b) f =
    sum {k | k IN a..b /\ p divides k} f + sum {k | k IN a..b /\ ~(p divides k)} f`
  SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC SUM_UNION_EQ THEN
    REWRITE_TAC[FINITE_NUMSEG; EXTENSION; IN_INTER; IN_UNION; IN_ELIM_THM;
                NOT_IN_EMPTY] THEN MESON_TAC[];
    ALL_TAC] THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM REAL_ADD_RID] THEN
  MATCH_MP_TAC NV_DIG_FIN_DIG_CG_ADD THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [SUBGOAL_THEN
     `{k | k IN a..b /\ p divides k} = IMAGE (\m. m * p) {m | a <= m * p /\ m * p <= b:num}`
    SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_IMAGE; IN_ELIM_THM; IN_NUMSEG; divides] THEN
      MESON_TAC[MULT_SYM];
      ALL_TAC] THEN
    W(MP_TAC o PART_MATCH (lhand o rand) SUM_IMAGE o lhand o snd) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[IN_ELIM_THM; EQ_MULT_RCANCEL] THEN
      ASM_MESON_TAC[PRIME_IMP_NZ];
      DISCH_THEN SUBST1_TAC] THEN
    MATCH_MP_TAC NV_DIG_FIN_DIG_CG_SUM THEN ASM_REWRITE_TAC[o_THM; IN_ELIM_THM];
    SUBGOAL_THEN `&0 = sum {k | k IN a..b /\ ~(p divides k)} (\k. &0)` SUBST1_TAC THENL
     [REWRITE_TAC[SUM_0]; ALL_TAC] THEN
    MATCH_MP_TAC NV_DIG_FIN_DIG_CG_SUM THEN
    ASM_SIMP_TAC[FINITE_RESTRICT; FINITE_NUMSEG; IN_ELIM_THM; IN_NUMSEG]]);;


(* ---- copied from src/catalan_fin_dig_c.ml ---- *)
(* ========================================================================= *)
(* nv_dig_fin_dig_c: Catalan numbers c_l = binom(2l,l)/4^l modulo an odd prime p:   *)
(* E_d congruences, the square sum, and the digit (carry / no-carry) laws.   *)
(* ========================================================================= *)


prioritize_real();;

let NV_DIG_FIN_DIG_C_ODD = prove
 (`forall p. prime p /\ ~(p = 2) ==> exists s. p = 2 * s + 1`,
  REPEAT STRIP_TAC THEN MP_TAC(SPEC `p:num` PRIME_ODD) THEN
  ASM_REWRITE_TAC[ODD_EXISTS] THEN STRIP_TAC THEN EXISTS_TAC `m:num` THEN
  ASM_REWRITE_TAC[] THEN ARITH_TAC);;

let NV_DIG_FIN_DIG_C_S = prove
 (`forall s. ((2 * s + 1) - 1) DIV 2 = s /\ (2 * s + 1) - 1 = 2 * s`,
  REWRITE_TAC[ARITH_RULE `(2 * s + 1) - 1 = 2 * s:num`] THEN
  SIMP_TAC[DIV_MULT; ARITH_EQ]);;

let NV_DIG_FIN_DIG_C_NDIV4 = prove
 (`forall p l. prime p /\ ~(p = 2) ==> ~(p divides 4 EXP l)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `p divides 2` MP_TAC THENL
   [MATCH_MP_TAC PRIME_DIVEXP THEN EXISTS_TAC `2 * l` THEN
    ASM_REWRITE_TAC[EXP_MULT] THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[];
    DISCH_THEN(MP_TAC o MATCH_MP DIVIDES_LE) THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP PRIME_GE_2) THEN ASM_ARITH_TAC]);;

let NV_DIG_FIN_DIG_E_INTEGER = prove
 (`forall p d. integer (nv_dig_fin_E p d)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[nv_dig_fin_E] THEN COND_CASES_TAC THEN
  SIMP_TAC[INTEGER_CLOSED]);;

let NV_DIG_FIN_DIG_C_ZP = prove
 (`forall p l. prime p /\ ~(p = 2) ==> nv_dig_fin_zp p (cat_c l)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[cat_c; REAL_OF_NUM_POW] THEN
  MATCH_MP_TAC NV_DIG_FIN_ZP_DIV_NUM THEN ASM_SIMP_TAC[NV_DIG_FIN_ZP_NUM; NV_DIG_FIN_DIG_C_NDIV4]);;

let NV_DIG_FIN_DIG_C_UNIT = prove
 (`forall p l. prime p /\ ~(p = 2) /\ 2 * l < p ==> nv_dig_fin_dig_unit p (cat_c l)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[cat_c; REAL_OF_NUM_POW] THEN
  MATCH_MP_TAC NV_DIG_FIN_DIG_UNIT_DIV THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THEN
  MATCH_MP_TAC NV_DIG_FIN_DIG_UNIT_NUM THEN ASM_SIMP_TAC[NV_DIG_FIN_DIG_C_NDIV4] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `p divides FACT(2 * l)` MP_TAC THENL
   [MP_TAC(SPECL [`l:num`; `l:num`] BINOM_FACT) THEN
    REWRITE_TAC[GSYM MULT_2] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    ASM_SIMP_TAC[DIVIDES_LMUL];
    ASM_SIMP_TAC[DIVIDES_FACT_PRIME] THEN ASM_ARITH_TAC]);;

let NV_DIG_FIN_DIG_C_REC0 = prove
 (`forall l. &(2 * l + 2) * cat_c (l + 1) = &(2 * l + 1) * cat_c l`,
  GEN_TAC THEN REWRITE_TAC[cat_c] THEN
  SUBGOAL_THEN `2 * (l + 1) = (2 * l + 1) + 1` SUBST1_TAC THENL
   [ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[BINOM_BOTH_STEP_REAL; BINOM_TOP_STEP_REAL;
              ARITH_RULE `~(l = 2 * l + 1:num)`] THEN
  REWRITE_TAC[REAL_POW_ADD; REAL_POW_1; GSYM REAL_OF_NUM_ADD;
              GSYM REAL_OF_NUM_MUL] THEN
  SUBGOAL_THEN `~(&4 pow l = &0) /\ ~(&l + &1 = &0) /\ ~(&2 * &l + &1 - &l = &0)`
  MP_TAC THENL
   [REWRITE_TAC[REAL_POW_EQ_0] THEN REAL_ARITH_TAC; CONV_TAC REAL_FIELD]);;


let NV_DIG_FIN_DIG_E_CG0 = prove
 (`forall s k. prime(2 * s + 1) /\ k <= s
         ==> nv_dig_fin_dig_cg (2 * s + 1) ((--(&1)) pow k * &(binom(s,k))) (cat_c k)`,
  GEN_TAC THEN INDUCT_TAC THENL
   [REWRITE_TAC[real_pow; binom; cat_c; MULT_CLAUSES; REAL_MUL_LID; REAL_DIV_1] THEN
    SIMP_TAC[NV_DIG_FIN_DIG_CG_REFL; NV_DIG_FIN_ZP_1];
    ALL_TAC] THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; DISCH_TAC] THEN
  SUBGOAL_THEN `(--(&1)) pow (SUC k) * &(binom(s,SUC k)) =
                ((--(&1)) pow k * &(binom(s,k))) * (--(&s - &k) / &(k + 1))`
  SUBST1_TAC THENL
   [REWRITE_TAC[ADD1; BINOM_BOTTOM_STEP_REAL; REAL_POW_ADD; REAL_POW_1] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN
    SUBGOAL_THEN `~(&k + &1 = &0)` MP_TAC THENL
     [REAL_ARITH_TAC; CONV_TAC REAL_FIELD];
    ALL_TAC] THEN
  SUBGOAL_THEN `cat_c (SUC k) = cat_c k * ((&(2 * k + 1) / &2) / &(k + 1))`
  SUBST1_TAC THENL
   [MP_TAC(SPEC `k:num` NV_DIG_FIN_DIG_C_REC0) THEN
    REWRITE_TAC[ADD1; GSYM REAL_OF_NUM_ADD; GSYM REAL_OF_NUM_MUL] THEN
    SUBGOAL_THEN `~(&k + &1 = &0)` MP_TAC THENL
     [REAL_ARITH_TAC; CONV_TAC REAL_FIELD];
    ALL_TAC] THEN
  MATCH_MP_TAC NV_DIG_FIN_DIG_CG_MUL THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC NV_DIG_FIN_DIG_CG_DIV_NUM THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ALL_TAC;
    DISCH_THEN(MP_TAC o MATCH_MP DIVIDES_LE) THEN ASM_ARITH_TAC] THEN
  REWRITE_TAC[nv_dig_fin_dig_cg] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC NV_DIG_FIN_ZP_INTEGER THEN ASM_SIMP_TAC[INTEGER_CLOSED];
    MATCH_MP_TAC NV_DIG_FIN_ZP_DIV_NUM THEN ASM_SIMP_TAC[NV_DIG_FIN_ZP_NUM] THEN
    DISCH_THEN(MP_TAC o MATCH_MP DIVIDES_LE) THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `--(&s - &k) - &(2 * k + 1) / &2 = &(2 * s + 1) * --(&1 / &2)`
  SUBST1_TAC THENL
   [REWRITE_TAC[GSYM REAL_OF_NUM_ADD; GSYM REAL_OF_NUM_MUL] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`2 * s + 1`; `&0`; `--(&1 / &2)`] NV_DIG_FIN_VGE_PMUL) THEN
  ASM_SIMP_TAC[REAL_ADD_LID; NV_DIG_FIN_VGE_ZP] THEN DISCH_THEN(K ALL_TAC) THEN
  MATCH_MP_TAC NV_DIG_FIN_ZP_NEG THEN MATCH_MP_TAC NV_DIG_FIN_ZP_DIV_NUM THEN
  ASM_SIMP_TAC[NV_DIG_FIN_ZP_1] THEN
  DISCH_THEN(MP_TAC o MATCH_MP DIVIDES_LE) THEN ASM_ARITH_TAC);;

let NV_DIG_FIN_DIG_E_CG = prove
 (`forall p d. prime p /\ ~(p = 2) /\ EVEN d /\ d < p
         ==> nv_dig_fin_dig_cg p (nv_dig_fin_E p d) (cat_c (d DIV 2))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `p:num` NV_DIG_FIN_DIG_C_ODD) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `s:num` SUBST_ALL_TAC) THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `k:num` SUBST_ALL_TAC o REWRITE_RULE[EVEN_EXISTS]) THEN
  ASM_REWRITE_TAC[nv_dig_fin_E; NV_DIG_FIN_DIG_C_S; EVEN_DOUBLE] THEN
  SIMP_TAC[DIV_MULT; ARITH_EQ] THEN MATCH_MP_TAC NV_DIG_FIN_DIG_E_CG0 THEN
  ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

let NV_DIG_FIN_DIG_C_HALF = prove
 (`forall p. prime p /\ ~(p = 2)
       ==> nv_dig_fin_dig_cg p (cat_c ((p - 1) DIV 2)) ((--(&1)) pow ((p - 1) DIV 2))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`p:num`; `p - 1`] NV_DIG_FIN_DIG_E_CG) THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(SPEC `p:num` NV_DIG_FIN_DIG_C_ODD) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `s:num` SUBST_ALL_TAC) THEN
  REWRITE_TAC[NV_DIG_FIN_DIG_C_S; EVEN_DOUBLE; ARITH_RULE `2 * s < 2 * s + 1:num`] THEN
  REWRITE_TAC[nv_dig_fin_E; NV_DIG_FIN_DIG_C_S; EVEN_DOUBLE; ARITH_RULE `2 * s < 2 * s + 1:num`] THEN
  SIMP_TAC[DIV_MULT; ARITH_EQ; BINOM_REFL; REAL_MUL_RID; NV_DIG_FIN_DIG_CG_SYM]);;

let NV_DIG_FIN_DIG_E_REFL = prove
 (`forall p d. prime p /\ ~(p = 2) /\ d < p
         ==> nv_dig_fin_E p ((p - 1) - d) = (--(&1)) pow ((p - 1) DIV 2) * nv_dig_fin_E p d`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `p:num` NV_DIG_FIN_DIG_C_ODD) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `s:num` SUBST_ALL_TAC) THEN
  REWRITE_TAC[NV_DIG_FIN_DIG_C_S] THEN
  ASM_CASES_TAC `EVEN d` THENL
   [FIRST_X_ASSUM(X_CHOOSE_THEN `k:num` SUBST_ALL_TAC o REWRITE_RULE[EVEN_EXISTS]) THEN
    SUBGOAL_THEN `exists m. s = k + m:num` (X_CHOOSE_THEN `m:num` SUBST_ALL_TAC) THENL
     [REWRITE_TAC[GSYM LE_EXISTS] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[ARITH_RULE `2 * (k + m) - 2 * k = 2 * m:num`] THEN
    REWRITE_TAC[nv_dig_fin_E; NV_DIG_FIN_DIG_C_S; EVEN_DOUBLE] THEN
    ASM_REWRITE_TAC[ARITH_RULE `2 * m < 2 * (k + m) + 1:num`] THEN
    SIMP_TAC[DIV_MULT; ARITH_EQ] THEN
    SUBGOAL_THEN `binom(k + m,m) = binom(k + m,k)` SUBST1_TAC THENL
     [MP_TAC(SPECL [`k + m:num`; `k:num`] BINOM_SYM) THEN
      REWRITE_TAC[ADD_SUB2; LE_ADD];
      ALL_TAC] THEN
    SUBGOAL_THEN `(--(&1)) pow k * (--(&1)) pow k = &1` MP_TAC THENL
     [REWRITE_TAC[GSYM REAL_POW_MUL] THEN
      REWRITE_TAC[REAL_ARITH `--(&1) * --(&1) = &1`; REAL_POW_ONE];
      REWRITE_TAC[REAL_POW_ADD] THEN CONV_TAC REAL_RING];
    ALL_TAC] THEN
  SUBGOAL_THEN `~EVEN(2 * s - d)` ASSUME_TAC THENL
   [REWRITE_TAC[EVEN_SUB; EVEN_MULT; ARITH_EVEN] THEN ASM_REWRITE_TAC[] THEN
    DISCH_TAC THEN SUBGOAL_THEN `d = 2 * s` SUBST_ALL_TAC THENL
     [ASM_ARITH_TAC; ASM_MESON_TAC[EVEN_DOUBLE]];
    ASM_REWRITE_TAC[nv_dig_fin_E; REAL_MUL_RZERO]]);;

let NV_DIG_FIN_DIG_C_SPLIT = prove
 (`forall f k. sum(0..SUC k) f = f 0 + sum(0..k) (\i. f(i + 1))`,
  REPEAT GEN_TAC THEN
  SIMP_TAC[SPECL [`f:num->real`; `0`; `SUC k`] SUM_CLAUSES_LEFT; LE_0] THEN AP_TERM_TAC THEN
  REWRITE_TAC[GSYM SUM_OFFSET] THEN REWRITE_TAC[ADD1; ADD_CLAUSES]);;

let NV_DIG_FIN_DIG_C_VDM = prove
 (`forall m n k. &(binom(m + n,k)) =
           sum(0..k) (\j. &(binom(m,j)) * &(binom(n,k - j)))`,
  INDUCT_TAC THENL
   [REPEAT GEN_TAC THEN REWRITE_TAC[ADD_CLAUSES] THEN
    SIMP_TAC[SUM_CLAUSES_LEFT; LE_0] THEN
    REWRITE_TAC[binom; SUB_0; REAL_MUL_LID] THEN
    MATCH_MP_TAC(REAL_ARITH `s = &0 ==> b = b + s`) THEN
    MATCH_MP_TAC SUM_EQ_0_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    SUBGOAL_THEN `binom(0,i) = 0` (fun th -> REWRITE_TAC[th; REAL_MUL_LZERO]) THEN
    MATCH_MP_TAC BINOM_LT THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  GEN_TAC THEN INDUCT_TAC THENL
   [REWRITE_TAC[binom; SUM_SING_NUMSEG; SUB_0; REAL_MUL_LID]; POP_ASSUM(K ALL_TAC)] THEN
  REWRITE_TAC[ADD_CLAUSES; binom; GSYM REAL_OF_NUM_ADD] THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[NV_DIG_FIN_DIG_C_SPLIT] THEN
  REWRITE_TAC[GSYM ADD1; SUB_SUC; SUB_0; binom; GSYM REAL_OF_NUM_ADD;
              REAL_ADD_RDISTRIB; SUM_ADD_NUMSEG; REAL_MUL_LID] THEN
  MATCH_MP_TAC(REAL_ARITH `c = c' ==> (a + b) + c = a + b + c'`) THEN
  REFL_TAC);;

let NV_DIG_FIN_DIG_C_BSQ = prove
 (`forall s. sum(0..s) (\j. &(binom(s,j)) pow 2) = &(binom(2 * s,s))`,
  GEN_TAC THEN REWRITE_TAC[MULT_2; NV_DIG_FIN_DIG_C_VDM] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN
  ASM_SIMP_TAC[REAL_POW_2; BINOM_SYM]);;

let NV_DIG_FIN_DIG_C_FERMAT4 = prove
 (`forall p n. prime p /\ ~(p = 2) ==> (4 EXP (n * p) == 4 EXP n) (mod p)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`4 EXP n`; `p:num`] FERMAT_LITTLE_PRIME) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[COPRIME_SYM] THEN
    ASM_SIMP_TAC[PRIME_COPRIME_EQ; NV_DIG_FIN_DIG_C_NDIV4];
    ALL_TAC] THEN
  SUBGOAL_THEN `4 EXP (n * p) = 4 EXP n * (4 EXP n) EXP (p - 1)` SUBST1_TAC THENL
   [REWRITE_TAC[EXP_EXP; GSYM EXP_ADD] THEN AP_TERM_TAC THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP PRIME_GE_2) THEN DISCH_TAC THEN
    SUBGOAL_THEN `exists q. p = q + 1:num` (CHOOSE_THEN SUBST1_TAC) THENL
     [EXISTS_TAC `p - 1:num` THEN ASM_ARITH_TAC;
      REWRITE_TAC[ADD_SUB] THEN CONV_TAC NUM_RING];
    DISCH_TAC THEN MATCH_MP_TAC(NUMBER_RULE
     `forall x a p:num. (a == 1) (mod p) ==> (x * a == x) (mod p)`) THEN
    ASM_REWRITE_TAC[]]);;

let NV_DIG_FIN_DIG_C_FOUR2 = prove
 (`forall p. prime p /\ ~(p = 2) ==> (4 EXP ((p - 1) DIV 2) == 1) (mod p)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP PRIME_GE_2) THEN
  MP_TAC(SPEC `p:num` NV_DIG_FIN_DIG_C_ODD) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `s:num` SUBST_ALL_TAC) THEN
  MP_TAC(SPECL [`2`; `2 * s + 1`] FERMAT_LITTLE_PRIME) THEN
  REWRITE_TAC[NV_DIG_FIN_DIG_C_S] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[COPRIME_SYM] THEN
    ASM_SIMP_TAC[PRIME_COPRIME_EQ] THEN
    DISCH_THEN(MP_TAC o MATCH_MP DIVIDES_LE) THEN ASM_ARITH_TAC;
    REWRITE_TAC[EXP_MULT] THEN CONV_TAC NUM_REDUCE_CONV]);;

let NV_DIG_FIN_DIG_C_SQSUM = prove
 (`forall p. prime p /\ ~(p = 2)
       ==> nv_dig_fin_dig_cg p (sum (0..(p - 1) DIV 2) (\j. cat_c j pow 2))
                        ((--(&1)) pow ((p - 1) DIV 2))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `p:num` NV_DIG_FIN_DIG_C_ODD) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `s:num` SUBST_ALL_TAC) THEN
  REWRITE_TAC[NV_DIG_FIN_DIG_C_S] THEN
  MATCH_MP_TAC NV_DIG_FIN_DIG_CG_TRANS THEN
  EXISTS_TAC `sum (0..s) (\j. &(binom(s,j)) pow 2)` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC NV_DIG_FIN_DIG_CG_SUM THEN ASM_REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
    X_GEN_TAC `j:num` THEN STRIP_TAC THEN
    MATCH_MP_TAC NV_DIG_FIN_DIG_CG_EQ THEN
    EXISTS_TAC `cat_c j pow 2` THEN
    EXISTS_TAC `((--(&1)) pow j * &(binom(s,j))) pow 2` THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC NV_DIG_FIN_DIG_CG_POW THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC NV_DIG_FIN_DIG_CG_SYM THEN MATCH_MP_TAC NV_DIG_FIN_DIG_E_CG0 THEN
      ASM_REWRITE_TAC[];
      REWRITE_TAC[];
      REWRITE_TAC[REAL_POW_MUL; REAL_POW_POW; REAL_POW_NEG; EVEN_MULT;
                  ARITH_EVEN; REAL_POW_ONE; REAL_MUL_LID]];
    ALL_TAC] THEN
  REWRITE_TAC[NV_DIG_FIN_DIG_C_BSQ] THEN
  MATCH_MP_TAC NV_DIG_FIN_DIG_CG_EQ THEN
  EXISTS_TAC `&4 pow s * cat_c s` THEN EXISTS_TAC `&1 * (--(&1)) pow s` THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC NV_DIG_FIN_DIG_CG_MUL THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_POW] THEN MATCH_MP_TAC NV_DIG_FIN_DIG_CG_NUM THEN
      ASM_REWRITE_TAC[] THEN
      MP_TAC(SPEC `2 * s + 1` NV_DIG_FIN_DIG_C_FOUR2) THEN ASM_REWRITE_TAC[NV_DIG_FIN_DIG_C_S];
      MP_TAC(SPEC `2 * s + 1` NV_DIG_FIN_DIG_C_HALF) THEN ASM_REWRITE_TAC[NV_DIG_FIN_DIG_C_S]];
    REWRITE_TAC[cat_c] THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC REAL_DIV_LMUL THEN
    REWRITE_TAC[REAL_POW_EQ_0] THEN REAL_ARITH_TAC;
    REWRITE_TAC[REAL_MUL_LID]]);;

let nv_dig_fin_dig_c_u = define
 `(forall p. (nv_dig_fin_dig_c_u:num->num->num) p 0 = 1) /\
  (forall p n. nv_dig_fin_dig_c_u p (SUC n) =
         (if p divides SUC n then 1 else SUC n) * nv_dig_fin_dig_c_u p n)`;;

let NV_DIG_FIN_DIG_C_U_NDIV = prove
 (`forall p n. prime p ==> ~(p divides nv_dig_fin_dig_c_u p n)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN SPEC_TAC(`n:num`,`n:num`) THEN INDUCT_TAC THEN REWRITE_TAC[nv_dig_fin_dig_c_u] THENL
   [ASM_MESON_TAC[DIVIDES_ONE; PRIME_1]; ALL_TAC] THEN
  COND_CASES_TAC THEN ASM_SIMP_TAC[PRIME_DIVPROD_EQ; DIVIDES_ONE] THEN
  ASM_MESON_TAC[PRIME_1]);;

let NV_DIG_FIN_DIG_C_DIVSTEP = prove
 (`forall p n. ~(p = 0)
         ==> if p divides SUC n
             then SUC n = p * (n DIV p + 1) /\ (SUC n) DIV p = n DIV p + 1 /\
                  (SUC n) MOD p = 0 /\ n MOD p = p - 1
             else (SUC n) DIV p = n DIV p /\ (SUC n) MOD p = n MOD p + 1`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`n:num`; `p:num`] DIVISION) THEN ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `q = n DIV p` THEN ABBREV_TAC `r = n MOD p` THEN STRIP_TAC THEN
  COND_CASES_TAC THENL
   [SUBGOAL_THEN `r + 1 = p` ASSUME_TAC THENL
     [SUBGOAL_THEN `p divides r + 1` MP_TAC THENL
       [MATCH_MP_TAC DIVIDES_ADD_REVR THEN EXISTS_TAC `q * p:num` THEN
        CONJ_TAC THENL
         [MATCH_MP_TAC DIVIDES_LMUL THEN REWRITE_TAC[DIVIDES_REFL];
          UNDISCH_TAC `p divides SUC n` THEN ASM_REWRITE_TAC[ADD1; ADD_ASSOC]];
        DISCH_THEN(MP_TAC o MATCH_MP DIVIDES_LE) THEN ASM_ARITH_TAC];
      ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[LEFT_ADD_DISTRIB; MULT_CLAUSES] THEN ASM_ARITH_TAC;
      MATCH_MP_TAC DIV_UNIQ THEN EXISTS_TAC `0`;
      MATCH_MP_TAC MOD_UNIQ THEN EXISTS_TAC `q + 1:num`;
      ALL_TAC] THEN
    ASM_REWRITE_TAC[RIGHT_ADD_DISTRIB; MULT_CLAUSES] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `~(r + 1 = p)` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `~(p divides SUC n)` THEN REWRITE_TAC[] THEN
    SUBGOAL_THEN `SUC n = (q + 1) * p` SUBST1_TAC THENL
     [ASM_REWRITE_TAC[RIGHT_ADD_DISTRIB; MULT_CLAUSES] THEN ASM_ARITH_TAC;
      MESON_TAC[DIVIDES_LMUL; DIVIDES_REFL]];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC DIV_UNIQ THEN EXISTS_TAC `r + 1:num`;
    MATCH_MP_TAC MOD_UNIQ THEN EXISTS_TAC `q:num`] THEN
  ASM_ARITH_TAC);;

let NV_DIG_FIN_DIG_C_FACT = prove
 (`forall p n. ~(p = 0) ==> FACT n = p EXP (n DIV p) * FACT (n DIV p) * nv_dig_fin_dig_c_u p n`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN SPEC_TAC(`n:num`,`n:num`) THEN INDUCT_TAC THENL
   [ASM_SIMP_TAC[DIV_0; FACT; EXP; nv_dig_fin_dig_c_u; MULT_CLAUSES]; ALL_TAC] THEN
  MP_TAC(SPECL [`p:num`; `n:num`] NV_DIG_FIN_DIG_C_DIVSTEP) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[nv_dig_fin_dig_c_u; FACT] THEN COND_CASES_TAC THENL
   [DISCH_THEN(CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[GSYM ADD1; FACT; EXP] THEN
    CONV_TAC NUM_RING;
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_RING]);;

let NV_DIG_FIN_DIG_C_UCONG = prove
 (`forall p n. prime p
         ==> (nv_dig_fin_dig_c_u p n == FACT(p - 1) EXP (n DIV p) * FACT(n MOD p)) (mod p)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `~(p = 0)` ASSUME_TAC THENL [ASM_MESON_TAC[PRIME_IMP_NZ]; ALL_TAC] THEN
  SPEC_TAC(`n:num`,`n:num`) THEN INDUCT_TAC THENL
   [ASM_SIMP_TAC[DIV_0; MOD_0; FACT; EXP; nv_dig_fin_dig_c_u; MULT_CLAUSES; CONG_REFL];
    ALL_TAC] THEN
  MP_TAC(SPECL [`p:num`; `n:num`] NV_DIG_FIN_DIG_C_DIVSTEP) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[nv_dig_fin_dig_c_u] THEN COND_CASES_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC
   `(nv_dig_fin_dig_c_u p n == FACT(p - 1) EXP (n DIV p) * FACT(n MOD p)) (mod p)` THENL
   [ASM_REWRITE_TAC[EXP_ADD; EXP_1; FACT; MULT_CLAUSES];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`n:num`; `p:num`] DIVISION) THEN ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `q = n DIV p` THEN ABBREV_TAC `r = n MOD p` THEN
  DISCH_THEN(SUBST1_TAC o CONJUNCT1) THEN
  REWRITE_TAC[GSYM ADD1; FACT] THEN REWRITE_TAC[ADD1] THEN
  CONV_TAC NUMBER_RULE);;

let NV_DIG_FIN_DIG_C_DECOMP = prove
 (`forall p l. prime p
         ==> &(binom(2 * l,l)) *
             (&(nv_dig_fin_dig_c_u p l) * &p pow (l DIV p) * &(FACT(l DIV p))) pow 2 =
             &p pow ((2 * l) DIV p) * &(FACT((2 * l) DIV p)) *
             &(nv_dig_fin_dig_c_u p (2 * l))`,
  REPEAT STRIP_TAC THEN FIRST_ASSUM(ASSUME_TAC o MATCH_MP PRIME_IMP_NZ) THEN
  MP_TAC(SPECL [`p:num`; `l:num`] NV_DIG_FIN_DIG_C_FACT) THEN
  MP_TAC(SPECL [`p:num`; `2 * l:num`] NV_DIG_FIN_DIG_C_FACT) THEN
  MP_TAC(SPECL [`l:num`; `l:num`] BINOM_FACT) THEN
  REWRITE_TAC[GSYM MULT_2] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_EQ; GSYM REAL_OF_NUM_MUL; GSYM REAL_OF_NUM_POW] THEN
  CONV_TAC REAL_RING);;

let NV_DIG_FIN_DIG_C_NZ = prove
 (`forall p n. prime p
         ==> ~(&(nv_dig_fin_dig_c_u p n) = &0) /\ ~(&(FACT n) = &0) /\
             ~(&p pow n = &0) /\ ~(&4 pow n = &0) /\ ~(&p = &0)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  ASM_SIMP_TAC[REAL_OF_NUM_EQ; FACT_NZ; NV_DIG_FIN_PPOW_NZ; REAL_POW_EQ_0; PRIME_IMP_NZ] THEN
  CONJ_TAC THENL
   [DISCH_TAC THEN MP_TAC(SPECL [`p:num`; `n:num`] NV_DIG_FIN_DIG_C_U_NDIV) THEN
    ASM_REWRITE_TAC[DIVIDES_0];
    ARITH_TAC]);;

let NV_DIG_FIN_DIG_C_ALG1 = prove
 (`forall B U1 P G G2 U2 b.
        B * (U1 * P * G) pow 2 = (P * P) * G2 * U2
        ==> (G * G * b = G2 /\ ~(U1 = &0) /\ ~(P = &0) /\ ~(G = &0))
        ==> B = b * U2 / U1 pow 2`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `B * (U1 * P * G) pow 2 = (P * P) * G2 * U2` THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  REPEAT(POP_ASSUM MP_TAC) THEN CONV_TAC REAL_FIELD);;

let NV_DIG_FIN_DIG_C_ALG3 = prove
 (`forall f b f2 A. f * f * b = f2 ==> (~(A = &0) /\ ~(f = &0))
              ==> b = ((A * A) * f2) / (A * f) pow 2`,
  REPEAT GEN_TAC THEN DISCH_THEN(SUBST1_TAC o SYM) THEN CONV_TAC REAL_FIELD);;

let NV_DIG_FIN_DIG_C_ALG4 = prove
 (`forall B U1 P G p G21 U2 x.
        B * (U1 * P * G) pow 2 = (P * P * p) * G21 * U2
        ==> (~(U1 = &0) /\ ~(P = &0) /\ ~(G = &0) /\ ~(p = &0) /\ ~(x = &0))
        ==> B / x / p = (G21 * U2) / ((U1 * G) pow 2 * x)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `B = ((P * P * p) * G21 * U2) / (U1 * P * G) pow 2` SUBST1_TAC THENL
   [UNDISCH_TAC `B * (U1 * P * G) pow 2 = (P * P * p) * G21 * U2` THEN
    REPEAT(POP_ASSUM MP_TAC) THEN CONV_TAC REAL_FIELD;
    REPEAT(POP_ASSUM MP_TAC) THEN CONV_TAC REAL_FIELD]);;

let NV_DIG_FIN_DIG_C_NOCARRY = prove
 (`forall p L s. prime p /\ ~(p = 2) /\ 2 * s < p /\ 2 * L < p
           ==> nv_dig_fin_dig_cg p (cat_c (L * p + s)) (cat_c L * cat_c s)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP PRIME_IMP_NZ) THEN
  ABBREV_TAC `l = L * p + s:num` THEN
  SUBGOAL_THEN `l DIV p = L /\ l MOD p = s /\ (2 * l) DIV p = 2 * L /\
                (2 * l) MOD p = 2 * s` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "l" THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC DIV_UNIQ THEN EXISTS_TAC `s:num`;
      MATCH_MP_TAC MOD_UNIQ THEN EXISTS_TAC `L:num`;
      MATCH_MP_TAC DIV_UNIQ THEN EXISTS_TAC `2 * s:num`;
      MATCH_MP_TAC MOD_UNIQ THEN EXISTS_TAC `2 * L:num`] THEN
    REWRITE_TAC[LEFT_ADD_DISTRIB; RIGHT_ADD_DISTRIB; MULT_ASSOC; MULT_CLAUSES] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `cat_c l = (&(binom(2 * L,L)) *
               (&(nv_dig_fin_dig_c_u p (2 * l)) / &(nv_dig_fin_dig_c_u p l) pow 2)) / &4 pow l`
  SUBST1_TAC THENL
   [REWRITE_TAC[cat_c] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    MP_TAC(SPECL [`p:num`; `l:num`] NV_DIG_FIN_DIG_C_DECOMP) THEN
    MP_TAC(SPECL [`L:num`; `L:num`] BINOM_FACT) THEN
    ASM_REWRITE_TAC[GSYM MULT_2] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_EQ; GSYM REAL_OF_NUM_MUL] THEN
    SUBGOAL_THEN `&p pow (2 * L) = &p pow L * &p pow L` SUBST1_TAC THENL
     [REWRITE_TAC[MULT_2; REAL_POW_ADD]; ALL_TAC] THEN
    MP_TAC(SPECL [`p:num`; `l:num`] NV_DIG_FIN_DIG_C_NZ) THEN
    MP_TAC(SPECL [`p:num`; `L:num`] NV_DIG_FIN_DIG_C_NZ) THEN
    ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o MATCH_MP NV_DIG_FIN_DIG_C_ALG1) THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC NV_DIG_FIN_DIG_CG_EQ THEN
  EXISTS_TAC `(&(binom(2 * L,L)) *
               (&(nv_dig_fin_dig_c_u p (2 * l)) / &(nv_dig_fin_dig_c_u p l) pow 2)) / &4 pow l` THEN
  EXISTS_TAC `(&(binom(2 * L,L)) * &(binom(2 * s,s))) / (&4 pow L * &4 pow s)` THEN
  REPEAT CONJ_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[];
    REWRITE_TAC[cat_c; real_div; REAL_INV_MUL; REAL_MUL_AC]] THEN
  MATCH_MP_TAC NV_DIG_FIN_DIG_CG_DIV THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC NV_DIG_FIN_DIG_CG_MUL THEN ASM_SIMP_TAC[NV_DIG_FIN_DIG_CG_REFL; NV_DIG_FIN_ZP_NUM] THEN
    MATCH_MP_TAC NV_DIG_FIN_DIG_CG_EQ THEN
    EXISTS_TAC `&(nv_dig_fin_dig_c_u p (2 * l)) / &(nv_dig_fin_dig_c_u p l) pow 2` THEN
    EXISTS_TAC `&(FACT(p - 1) EXP (2 * L) * FACT(2 * s)) /
                &(FACT(p - 1) EXP L * FACT s) pow 2` THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC NV_DIG_FIN_DIG_CG_DIV THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC NV_DIG_FIN_DIG_CG_NUM THEN ASM_REWRITE_TAC[] THEN
        MP_TAC(SPECL [`p:num`; `2 * l:num`] NV_DIG_FIN_DIG_C_UCONG) THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC NV_DIG_FIN_DIG_UNIT_POW THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC NV_DIG_FIN_DIG_UNIT_NUM THEN ASM_SIMP_TAC[NV_DIG_FIN_DIG_C_U_NDIV];
        MATCH_MP_TAC NV_DIG_FIN_DIG_CG_POW THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC NV_DIG_FIN_DIG_CG_NUM THEN ASM_REWRITE_TAC[] THEN
        MP_TAC(SPECL [`p:num`; `l:num`] NV_DIG_FIN_DIG_C_UCONG) THEN ASM_REWRITE_TAC[]];
      REWRITE_TAC[];
      SUBGOAL_THEN `FACT(p - 1) EXP (2 * L) = FACT(p - 1) EXP L * FACT(p - 1) EXP L`
      SUBST1_TAC THENL [REWRITE_TAC[MULT_2; EXP_ADD]; ALL_TAC] THEN
      MP_TAC(SPECL [`s:num`; `s:num`] BINOM_FACT) THEN
      REWRITE_TAC[GSYM MULT_2] THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_EQ; GSYM REAL_OF_NUM_MUL] THEN
      DISCH_THEN(MATCH_MP_TAC o MATCH_MP NV_DIG_FIN_DIG_C_ALG3) THEN
      REWRITE_TAC[REAL_OF_NUM_EQ; EXP_EQ_0; FACT_NZ]];
    REWRITE_TAC[REAL_OF_NUM_POW] THEN MATCH_MP_TAC NV_DIG_FIN_DIG_UNIT_NUM THEN
    ASM_SIMP_TAC[NV_DIG_FIN_DIG_C_NDIV4];
    REWRITE_TAC[REAL_OF_NUM_POW; REAL_OF_NUM_MUL] THEN
    MATCH_MP_TAC NV_DIG_FIN_DIG_CG_NUM THEN ASM_REWRITE_TAC[] THEN
    EXPAND_TAC "l" THEN REWRITE_TAC[EXP_ADD] THEN
    MATCH_MP_TAC CONG_MULT THEN ASM_SIMP_TAC[NV_DIG_FIN_DIG_C_FERMAT4; CONG_REFL]]);;

let NV_DIG_FIN_DIG_C_CARRY = prove
 (`forall p L s. prime p /\ ~(p = 2) /\ p <= 2 * s /\ s < p /\ 2 * L + 1 < p
           ==> nv_dig_fin_dig_unit p (cat_c (L * p + s) / &p)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP PRIME_IMP_NZ) THEN
  ABBREV_TAC `l = L * p + s:num` THEN
  SUBGOAL_THEN `l DIV p = L /\ (2 * l) DIV p = 2 * L + 1` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "l" THEN CONJ_TAC THENL
     [MATCH_MP_TAC DIV_UNIQ THEN EXISTS_TAC `s:num`;
      MATCH_MP_TAC DIV_UNIQ THEN EXISTS_TAC `2 * s - p:num`] THEN
    REWRITE_TAC[LEFT_ADD_DISTRIB; RIGHT_ADD_DISTRIB; MULT_ASSOC; MULT_CLAUSES] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `cat_c l / &p =
    (&(FACT(2 * L + 1)) * &(nv_dig_fin_dig_c_u p (2 * l))) /
    ((&(nv_dig_fin_dig_c_u p l) * &(FACT L)) pow 2 * &4 pow l)`
  SUBST1_TAC THENL
   [REWRITE_TAC[cat_c] THEN
    MP_TAC(SPECL [`p:num`; `l:num`] NV_DIG_FIN_DIG_C_DECOMP) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `&p pow (2 * L + 1) = &p pow L * &p pow L * &p` SUBST1_TAC THENL
     [REWRITE_TAC[MULT_2; REAL_POW_ADD; REAL_POW_1; REAL_MUL_ASSOC]; ALL_TAC] THEN
    MP_TAC(SPECL [`p:num`; `l:num`] NV_DIG_FIN_DIG_C_NZ) THEN
    MP_TAC(SPECL [`p:num`; `L:num`] NV_DIG_FIN_DIG_C_NZ) THEN
    ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o MATCH_MP NV_DIG_FIN_DIG_C_ALG4) THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC NV_DIG_FIN_DIG_UNIT_DIV THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC NV_DIG_FIN_DIG_UNIT_MUL THEN ASM_REWRITE_TAC[] THEN CONJ_TAC;
    MATCH_MP_TAC NV_DIG_FIN_DIG_UNIT_MUL THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC NV_DIG_FIN_DIG_UNIT_POW THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC NV_DIG_FIN_DIG_UNIT_MUL THEN ASM_REWRITE_TAC[] THEN CONJ_TAC;
      REWRITE_TAC[REAL_OF_NUM_POW]]] THEN
  MATCH_MP_TAC NV_DIG_FIN_DIG_UNIT_NUM THEN
  ASM_SIMP_TAC[NV_DIG_FIN_DIG_C_U_NDIV; NV_DIG_FIN_DIG_C_NDIV4; DIVIDES_FACT_PRIME] THEN
  ASM_ARITH_TAC);;


(* ---- copied from src/catalan_fin_bdry.ml ---- *)
(* ========================================================================= *)
(* CAT_FINITE_PLACE: boundary formulas (Equations (18), (19)) and the basic  *)
(* valuation bounds for 1/n, 1/binom(2l,l) and floor(log_p n).               *)
(* ========================================================================= *)


(* ------------------------------------------------------------------------- *)
(* Elementary facts on c_l, m_i, H*_z.                                       *)
(* ------------------------------------------------------------------------- *)

let nv_dig_fin_bdry_nz_tac tms =
  MAP_EVERY (fun t -> SUBGOAL_THEN t MP_TAC THENL
    [REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_MUL; REAL_OF_NUM_EQ] THEN
     ARITH_TAC; ALL_TAC]) tms;;

let NV_DIG_FIN_BDRY_BINOM_STEP = prove
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
  nv_dig_fin_bdry_nz_tac [`~(&l + &1 = &0)`] THEN
  CONV_TAC REAL_FIELD);;

let NV_DIG_FIN_BDRY_C_REC = prove
 (`forall l. &(2 * l + 2) * cat_c (l + 1) = &(2 * l + 1) * cat_c l`,
  GEN_TAC THEN REWRITE_TAC[cat_c] THEN
  MP_TAC(SPEC `l:num` NV_DIG_FIN_BDRY_BINOM_STEP) THEN
  REWRITE_TAC[REAL_POW_ADD; REAL_POW_1; GSYM REAL_OF_NUM_ADD;
              GSYM REAL_OF_NUM_MUL] THEN
  SUBGOAL_THEN `~(&4 pow l = &0)` MP_TAC THENL
   [REWRITE_TAC[REAL_POW_EQ_0] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  CONV_TAC REAL_FIELD);;

let NV_DIG_FIN_BDRY_C_POS = prove
 (`forall l. &0 < cat_c l`,
  GEN_TAC THEN REWRITE_TAC[cat_c] THEN MATCH_MP_TAC REAL_LT_DIV THEN
  SIMP_TAC[REAL_POW_LT; REAL_OF_NUM_LT; ARITH] THEN
  REWRITE_TAC[LT_NZ; BINOM_EQ_0] THEN ARITH_TAC);;

let NV_DIG_FIN_BDRY_C_0 = prove
 (`cat_c 0 = &1`,
  REWRITE_TAC[cat_c; MULT_CLAUSES; binom; real_pow] THEN REAL_ARITH_TAC);;

let NV_DIG_FIN_BDRY_C_STEP = prove
 (`forall l. cat_c (l + 1) = cat_c l * &(2 * l + 1) / &(2 * l + 2)`,
  GEN_TAC THEN MP_TAC(SPEC `l:num` NV_DIG_FIN_BDRY_C_REC) THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_ADD; GSYM REAL_OF_NUM_MUL] THEN
  nv_dig_fin_bdry_nz_tac [`~(&2 * &l + &2 = &0)`] THEN CONV_TAC REAL_FIELD);;

let NV_DIG_FIN_BDRY_M_EVEN2 = prove
 (`forall a. cat_m (2 * a) = &2 / (&(2 * a + 1) * cat_c a)`,
  GEN_TAC THEN REWRITE_TAC[cat_m; EVEN_MULT; ARITH] THEN
  SIMP_TAC[DIV_MULT; ARITH_EQ]);;

let NV_DIG_FIN_BDRY_M_ODD2 = prove
 (`forall a. cat_m (2 * a + 1) = &0`,
  REWRITE_TAC[cat_m; EVEN_ADD; EVEN_MULT; ARITH]);;

let NV_DIG_FIN_BDRY_M_REC = prove
 (`forall i. &(i + 3) * cat_m (i + 2) = &(i + 2) * cat_m i`,
  GEN_TAC THEN DISJ_CASES_TAC(SPEC `i:num` EVEN_OR_ODD) THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `a:num` SUBST1_TAC o
    REWRITE_RULE[EVEN_EXISTS; ODD_EXISTS; ADD1]) THENL
   [REWRITE_TAC[ARITH_RULE `2 * a + 2 = 2 * (a + 1)`; NV_DIG_FIN_BDRY_M_EVEN2] THEN
    REWRITE_TAC[NV_DIG_FIN_BDRY_C_STEP] THEN
    MP_TAC(SPEC `a:num` NV_DIG_FIN_BDRY_C_POS) THEN
    DISCH_THEN(MP_TAC o MATCH_MP REAL_LT_IMP_NZ) THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_ADD; GSYM REAL_OF_NUM_MUL] THEN
    nv_dig_fin_bdry_nz_tac [`~(&2 * &a + &1 = &0)`; `~(&2 * &a + &2 = &0)`;
                     `~(&2 * &a + &3 = &0)`] THEN
    CONV_TAC REAL_FIELD;
    REWRITE_TAC[ARITH_RULE `(2 * a + 1) + 2 = 2 * (a + 1) + 1`;
                NV_DIG_FIN_BDRY_M_ODD2; REAL_MUL_RZERO]]);;

let NV_DIG_FIN_BDRY_HSTAR_EVEN2 = prove
 (`forall a. nv_dig_fin_hstar (2 * a) = cat_c a`,
  GEN_TAC THEN REWRITE_TAC[nv_dig_fin_hstar; EVEN_MULT; ARITH] THEN
  SIMP_TAC[DIV_MULT; ARITH_EQ]);;

let NV_DIG_FIN_BDRY_HSTAR_ODD2 = prove
 (`forall a. nv_dig_fin_hstar (2 * a + 1) = inv(&(2 * a + 1) * cat_c a)`,
  GEN_TAC THEN REWRITE_TAC[nv_dig_fin_hstar; EVEN_ADD; EVEN_MULT; ARITH; ADD_SUB] THEN
  SIMP_TAC[DIV_MULT; ARITH_EQ]);;

let NV_DIG_FIN_BDRY_HSTAR_POS = prove
 (`forall z. &0 < nv_dig_fin_hstar z`,
  GEN_TAC THEN DISJ_CASES_TAC(SPEC `z:num` EVEN_OR_ODD) THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `a:num` SUBST1_TAC o
    REWRITE_RULE[EVEN_EXISTS; ODD_EXISTS; ADD1]) THEN
  REWRITE_TAC[NV_DIG_FIN_BDRY_HSTAR_EVEN2; NV_DIG_FIN_BDRY_HSTAR_ODD2; NV_DIG_FIN_BDRY_C_POS] THEN
  MATCH_MP_TAC REAL_LT_INV THEN MATCH_MP_TAC REAL_LT_MUL THEN
  REWRITE_TAC[NV_DIG_FIN_BDRY_C_POS; REAL_OF_NUM_LT] THEN ARITH_TAC);;

let NV_DIG_FIN_BDRY_HSTAR_NZ = prove
 (`forall z. ~(nv_dig_fin_hstar z = &0)`,
  MESON_TAC[NV_DIG_FIN_BDRY_HSTAR_POS; REAL_LT_IMP_NZ]);;

let NV_DIG_FIN_BDRY_HSTAR_1 = prove
 (`nv_dig_fin_hstar 1 = &1`,
  MP_TAC(SPEC `0` NV_DIG_FIN_BDRY_HSTAR_ODD2) THEN
  REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; NV_DIG_FIN_BDRY_C_0] THEN
  DISCH_THEN SUBST1_TAC THEN CONV_TAC REAL_RAT_REDUCE_CONV);;

let NV_DIG_FIN_BDRY_HSTAR_STEP = prove
 (`forall z. nv_dig_fin_hstar (z + 2) = nv_dig_fin_hstar z * &(z + 1) / &(z + 2)`,
  GEN_TAC THEN DISJ_CASES_TAC(SPEC `z:num` EVEN_OR_ODD) THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `a:num` SUBST1_TAC o
    REWRITE_RULE[EVEN_EXISTS; ODD_EXISTS; ADD1]) THENL
   [REWRITE_TAC[ARITH_RULE `2 * a + 2 = 2 * (a + 1)`; NV_DIG_FIN_BDRY_HSTAR_EVEN2] THEN
    REWRITE_TAC[NV_DIG_FIN_BDRY_C_STEP; ARITH_RULE `2 * (a + 1) = 2 * a + 2`] THEN
    REWRITE_TAC[REAL_MUL_ASSOC];
    REWRITE_TAC[ARITH_RULE `(2 * a + 1) + 2 = 2 * (a + 1) + 1`;
                NV_DIG_FIN_BDRY_HSTAR_ODD2] THEN
    REWRITE_TAC[NV_DIG_FIN_BDRY_C_STEP] THEN
    MP_TAC(SPEC `a:num` NV_DIG_FIN_BDRY_C_POS) THEN
    DISCH_THEN(MP_TAC o MATCH_MP REAL_LT_IMP_NZ) THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_ADD; GSYM REAL_OF_NUM_MUL] THEN
    nv_dig_fin_bdry_nz_tac [`~(&2 * &a + &1 = &0)`; `~(&2 * &a + &2 = &0)`;
                     `~(&2 * &a + &3 = &0)`] THEN
    CONV_TAC REAL_FIELD]);;

let NV_DIG_FIN_BDRY_M_ODD = prove
 (`forall z. ODD z ==> cat_m (z - 1) = &2 * nv_dig_fin_hstar z`,
  GEN_TAC THEN REWRITE_TAC[ODD_EXISTS; ADD1] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:num` SUBST1_TAC) THEN
  REWRITE_TAC[ADD_SUB; NV_DIG_FIN_BDRY_M_EVEN2; NV_DIG_FIN_BDRY_HSTAR_ODD2; real_div]);;

(* parity-pair forms used in the boundary recurrences *)

let NV_DIG_FIN_BDRY_M_EVEN_PAIR = prove
 (`forall d. EVEN d ==> cat_m d = &2 / (&(d + 1) * nv_dig_fin_hstar d) /\ cat_m (d + 1) = &0`,
  GEN_TAC THEN REWRITE_TAC[EVEN_EXISTS] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:num` SUBST1_TAC) THEN
  REWRITE_TAC[NV_DIG_FIN_BDRY_M_EVEN2; NV_DIG_FIN_BDRY_M_ODD2; NV_DIG_FIN_BDRY_HSTAR_EVEN2]);;

let NV_DIG_FIN_BDRY_M_ODD_PAIR = prove
 (`forall d. ODD d ==> cat_m d = &0 /\ cat_m (d + 1) = &2 * nv_dig_fin_hstar (d + 2)`,
  GEN_TAC THEN REWRITE_TAC[ODD_EXISTS; ADD1] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:num` SUBST1_TAC) THEN
  REWRITE_TAC[NV_DIG_FIN_BDRY_M_ODD2] THEN
  MP_TAC(SPEC `(2 * a + 1) + 2` NV_DIG_FIN_BDRY_M_ODD) THEN
  REWRITE_TAC[ODD_ADD; ODD_MULT; ARITH] THEN
  REWRITE_TAC[ARITH_RULE `((2 * a + 1) + 2) - 1 = (2 * a + 1) + 1`]);;

(* ------------------------------------------------------------------------- *)
(* Boundary recurrences solved explicitly, Equation (19).                    *)
(* ------------------------------------------------------------------------- *)

let NV_DIG_FIN_BDRY_IND2 = prove
 (`forall P. P 0 /\ P 1 /\ (forall d. P d ==> P (d + 2)) ==> forall n. P n`,
  GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `forall n. P n /\ P (n + 1)` (fun th -> MESON_TAC[th]) THEN
  INDUCT_TAC THENL
   [ASM_REWRITE_TAC[ADD_CLAUSES];
    ASM_REWRITE_TAC[ADD1; ARITH_RULE `(n + 1) + 1 = n + 2`] THEN
    ASM_MESON_TAC[]]);;

let NV_DIG_FIN_BDRY_SUM_STEP2 = prove
 (`forall f n. sum(1..n + 2) f = sum(1..n) f + f(n + 1) + f(n + 2)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[ARITH_RULE `n + 2 = SUC(SUC n)`; SUM_CLAUSES_NUMSEG;
              ARITH_RULE `1 <= SUC n`] THEN
  REWRITE_TAC[ADD1; REAL_ADD_ASSOC]);;

let NV_DIG_FIN_BDRY_KMINUS_STEP = prove
 (`forall d. cat_kminus (d + 2) =
       (&(d + 1) * cat_kminus d + cat_m d + cat_m (d + 1)) / &(d + 2)`,
  GEN_TAC THEN REWRITE_TAC[GSYM(el 2 (CONJUNCTS cat_kminus))] THEN
  AP_TERM_TAC THEN ARITH_TAC);;

let NV_DIG_FIN_BDRY_KPLUS_STEP = prove
 (`forall d. cat_kplus (d + 2) = (&d * cat_kplus d + &2 / &(d + 1)) / &(d + 1)`,
  GEN_TAC THEN REWRITE_TAC[GSYM(el 2 (CONJUNCTS cat_kplus))] THEN
  AP_TERM_TAC THEN ARITH_TAC);;

let NV_DIG_FIN_BDRY_KMINUS_1 = prove
 (`cat_kminus 1 = &2`,
  REWRITE_TAC[num_CONV `1`; cat_kminus]);;

let NV_DIG_FIN_BDRY_KPLUS_1 = prove
 (`cat_kplus 1 = &0`,
  REWRITE_TAC[num_CONV `1`; cat_kplus]);;

let NV_DIG_FIN_BDRY_KPLUS_2 = prove
 (`cat_kplus 2 = &2`,
  MP_TAC(SPEC `0` NV_DIG_FIN_BDRY_KPLUS_STEP) THEN
  REWRITE_TAC[ADD_CLAUSES; cat_kplus] THEN DISCH_THEN SUBST1_TAC THEN
  CONV_TAC REAL_RAT_REDUCE_CONV);;

let NV_DIG_FIN_BDRY_KMINUS_BOTH = prove
 (`forall u. (EVEN u ==> cat_kminus u = nv_dig_fin_hstar u * sum (1..u)
          (\z. if EVEN z then &2 / (&z pow 2 * nv_dig_fin_hstar z pow 2) else &0)) /\
       (ODD u ==> cat_kminus u = nv_dig_fin_hstar u * sum (1..u)
          (\z. if ODD z then &2 / &z else &0))`,
  MATCH_MP_TAC NV_DIG_FIN_BDRY_IND2 THEN BETA_TAC THEN CONJ_TAC THENL
   [REWRITE_TAC[ARITH; cat_kminus; SUM_CLAUSES_NUMSEG; REAL_MUL_RZERO];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[ARITH; NV_DIG_FIN_BDRY_KMINUS_1; SUM_SING_NUMSEG; NV_DIG_FIN_BDRY_HSTAR_1;
                BETA_THM] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV;
    X_GEN_TAC `d:num` THEN STRIP_TAC THEN CONJ_TAC THEN DISCH_TAC THENL
     [SUBGOAL_THEN `EVEN d` ASSUME_TAC THENL
       [UNDISCH_TAC `EVEN(d + 2)` THEN REWRITE_TAC[EVEN_ADD; ARITH]; ALL_TAC] THEN
      FIRST_X_ASSUM(MP_TAC o C MATCH_MP (ASSUME `EVEN d`)) THEN
      MP_TAC(SPEC `d:num` NV_DIG_FIN_BDRY_M_EVEN_PAIR) THEN ASM_REWRITE_TAC[] THEN
      REPEAT STRIP_TAC THEN
      ASM_REWRITE_TAC[NV_DIG_FIN_BDRY_KMINUS_STEP; NV_DIG_FIN_BDRY_SUM_STEP2;
                      NV_DIG_FIN_BDRY_HSTAR_STEP; EVEN_ADD; ARITH; BETA_THM] THEN
      MP_TAC(SPEC `d:num` NV_DIG_FIN_BDRY_HSTAR_NZ) THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN
      nv_dig_fin_bdry_nz_tac [`~(&d + &1 = &0)`; `~(&d + &2 = &0)`] THEN
      CONV_TAC REAL_FIELD;
      SUBGOAL_THEN `ODD d` ASSUME_TAC THENL
       [UNDISCH_TAC `ODD(d + 2)` THEN REWRITE_TAC[ODD_ADD; ARITH]; ALL_TAC] THEN
      FIRST_X_ASSUM(MP_TAC o C MATCH_MP (ASSUME `ODD d`)) THEN
      MP_TAC(SPEC `d:num` NV_DIG_FIN_BDRY_M_ODD_PAIR) THEN ASM_REWRITE_TAC[] THEN
      REPEAT STRIP_TAC THEN
      ASM_REWRITE_TAC[NV_DIG_FIN_BDRY_KMINUS_STEP; NV_DIG_FIN_BDRY_SUM_STEP2;
                      NV_DIG_FIN_BDRY_HSTAR_STEP; ODD_ADD; ARITH; BETA_THM] THEN
      MP_TAC(SPEC `d:num` NV_DIG_FIN_BDRY_HSTAR_NZ) THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN
      nv_dig_fin_bdry_nz_tac [`~(&d + &1 = &0)`; `~(&d + &2 = &0)`] THEN
      CONV_TAC REAL_FIELD]]);;

let NV_DIG_FIN_BDRY_KMINUS_EVEN = prove
 (`forall u. EVEN u ==> cat_kminus u = nv_dig_fin_hstar u * sum (1..u)
          (\z. if EVEN z then &2 / (&z pow 2 * nv_dig_fin_hstar z pow 2) else &0)`,
  MESON_TAC[NV_DIG_FIN_BDRY_KMINUS_BOTH]);;

let NV_DIG_FIN_BDRY_KMINUS_ODD = prove
 (`forall u. ODD u ==> cat_kminus u = nv_dig_fin_hstar u * sum (1..u)
          (\z. if ODD z then &2 / &z else &0)`,
  MESON_TAC[NV_DIG_FIN_BDRY_KMINUS_BOTH]);;

let NV_DIG_FIN_BDRY_KPLUS = prove
 (`forall u. cat_kplus (u + 1) = nv_dig_fin_hstar u * sum (1..u)
          (\z. if (EVEN z <=> EVEN u) then &2 / (&z pow 2 * nv_dig_fin_hstar z) else &0)`,
  MATCH_MP_TAC NV_DIG_FIN_BDRY_IND2 THEN BETA_TAC THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[ADD_CLAUSES; NV_DIG_FIN_BDRY_KPLUS_1; SUM_CLAUSES_NUMSEG; ARITH;
                REAL_MUL_RZERO];
    REWRITE_TAC[ARITH; NV_DIG_FIN_BDRY_KPLUS_2; SUM_SING_NUMSEG; NV_DIG_FIN_BDRY_HSTAR_1;
                BETA_THM] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV;
    X_GEN_TAC `d:num` THEN DISCH_TAC THEN
    REWRITE_TAC[ARITH_RULE `(d + 2) + 1 = (d + 1) + 2`] THEN
    REWRITE_TAC[NV_DIG_FIN_BDRY_KPLUS_STEP] THEN
    REWRITE_TAC[ARITH_RULE `(d + 1) + 1 = d + 2`] THEN
    REWRITE_TAC[NV_DIG_FIN_BDRY_SUM_STEP2; EVEN_ADD; ARITH; BETA_THM;
                TAUT `(~p <=> p) <=> false`] THEN
    ASM_REWRITE_TAC[NV_DIG_FIN_BDRY_HSTAR_STEP] THEN
    MP_TAC(SPEC `d:num` NV_DIG_FIN_BDRY_HSTAR_NZ) THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN
    nv_dig_fin_bdry_nz_tac [`~(&d + &1 = &0)`; `~(&d + &2 = &0)`] THEN
    CONV_TAC REAL_FIELD]);;

(* ------------------------------------------------------------------------- *)
(* floor(log_p n).                                                           *)
(* ------------------------------------------------------------------------- *)

let NV_DIG_FIN_BDRY_FLOG_GE = prove
 (`forall p n e. 2 <= p /\ p EXP e <= n ==> e <= nv_dig_fin_flog p n`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[nv_dig_fin_flog] THEN
  MP_TAC(ISPECL [`1..e`; `{j | 1 <= j /\ p EXP j <= n}`] CARD_SUBSET) THEN
  ASM_SIMP_TAC[FINITE_EXP_LE; CARD_NUMSEG_1] THEN DISCH_THEN MATCH_MP_TAC THEN
  REWRITE_TAC[SUBSET; IN_NUMSEG; IN_ELIM_THM] THEN
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  TRANS_TAC LE_TRANS `p EXP e` THEN ASM_REWRITE_TAC[LE_EXP] THEN
  ASM_ARITH_TAC);;

let NV_DIG_FIN_BDRY_FLOG_EXP = prove
 (`forall p n. 2 <= p /\ 1 <= n ==> p EXP (nv_dig_fin_flog p n) <= n`,
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
  SUBGOAL_THEN `nv_dig_fin_flog p n = k` (fun th -> ASM_REWRITE_TAC[th]) THEN
  REWRITE_TAC[nv_dig_fin_flog] THEN
  SUBGOAL_THEN `{e | 1 <= e /\ p EXP e <= n} = 1..k` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_NUMSEG] THEN
    X_GEN_TAC `e:num` THEN EQ_TAC THEN STRIP_TAC THEN ASM_SIMP_TAC[] THEN
    TRANS_TAC LE_TRANS `p EXP k` THEN ASM_REWRITE_TAC[LE_EXP] THEN
    ASM_ARITH_TAC;
    REWRITE_TAC[CARD_NUMSEG_1]]);;

let NV_DIG_FIN_BDRY_FLOG_ZERO = prove
 (`forall p n. n < p ==> nv_dig_fin_flog p n = 0`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[nv_dig_fin_flog] THEN
  SUBGOAL_THEN `{e | 1 <= e /\ p EXP e <= n} = {}` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY] THEN
    X_GEN_TAC `e:num` THEN STRIP_TAC THEN
    SUBGOAL_THEN `p EXP 1 <= p EXP e` MP_TAC THENL
     [REWRITE_TAC[LE_EXP] THEN COND_CASES_TAC THEN ASM_ARITH_TAC;
      REWRITE_TAC[EXP_1] THEN ASM_ARITH_TAC];
    REWRITE_TAC[CARD_CLAUSES]]);;

let NV_DIG_FIN_BDRY_FLOG_MONO = prove
 (`forall p m n. m <= n ==> nv_dig_fin_flog p m <= nv_dig_fin_flog p n`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[nv_dig_fin_flog] THEN
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

let NV_DIG_FIN_BDRY_FLOG_LOG = prove
 (`forall p n. 2 <= p /\ 1 <= n ==> &(nv_dig_fin_flog p n) * log(&p) <= log(&n)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < &p` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[GSYM LOG_POW] THEN MATCH_MP_TAC LOG_MONO_LE_IMP THEN
  ASM_SIMP_TAC[REAL_POW_LT; REAL_OF_NUM_POW; REAL_OF_NUM_LE;
               NV_DIG_FIN_BDRY_FLOG_EXP]);;

(* ------------------------------------------------------------------------- *)
(* Valuations of 1/n and 1/binom(2l,l).                                      *)
(* ------------------------------------------------------------------------- *)

let NV_DIG_FIN_BDRY_INV_INDEX = prove
 (`forall p n b. prime p /\ ~(n = 0) /\ index p n <= b
           ==> nv_dig_fin_vge p (--(&b)) (inv(&n))`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[NV_DIG_FIN_VGE_NEGPOW] THEN
  ABBREV_TAC `e = index p n` THEN
  MP_TAC(SPECL [`n:num`; `p:num`] INDEX_DECOMPOSITION) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `m:num` STRIP_ASSUME_TAC) THENL
   [ASM_MESON_TAC[PRIME_1]; ALL_TAC] THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `f:num` SUBST1_TAC o REWRITE_RULE[LE_EXISTS]) THEN
  REWRITE_TAC[nv_dig_fin_zp] THEN MAP_EVERY EXISTS_TAC [`&p pow f`; `m:num`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [SIMP_TAC[INTEGER_CLOSED]; ALL_TAC] THEN
  SUBGOAL_THEN `~(m = 0)` ASSUME_TAC THENL
   [ASM_MESON_TAC[MULT_CLAUSES]; ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (is_eq o concl) o
    check (fun th -> rand(concl th) = `n:num`)) THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_MUL; GSYM REAL_OF_NUM_POW; REAL_POW_ADD] THEN
  MP_TAC(SPECL [`p:num`; `e:num`] NV_DIG_FIN_PPOW_NZ) THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `~(m = 0)` THEN REWRITE_TAC[GSYM REAL_OF_NUM_EQ] THEN
  CONV_TAC REAL_FIELD);;

let NV_DIG_FIN_BDRY_NUM_VAL = prove
 (`forall p n H. prime p /\ 1 <= n /\ n <= H
           ==> nv_dig_fin_vge p (--(&(nv_dig_fin_flog p H))) (inv(&n))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC NV_DIG_FIN_BDRY_INV_INDEX THEN
  ASM_REWRITE_TAC[ARITH_RULE `~(n = 0) <=> 1 <= n`] THEN
  MATCH_MP_TAC NV_DIG_FIN_BDRY_FLOG_GE THEN ASM_SIMP_TAC[PRIME_GE_2] THEN
  TRANS_TAC LE_TRANS `n:num` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC DIVIDES_LE_IMP THEN
  ASM_REWRITE_TAC[EXP_INDEX_DIVIDES] THEN ASM_ARITH_TAC);;

let NV_DIG_FIN_BDRY_DIV2_LEMMA = prove
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

let NV_DIG_FIN_BDRY_INDEX_BINOM = prove
 (`forall p l. prime p ==> index p (binom(2 * l,l)) <= nv_dig_fin_flog p (2 * l)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `2 <= p` ASSUME_TAC THENL [ASM_SIMP_TAC[PRIME_GE_2]; ALL_TAC] THEN
  MP_TAC(SPECL [`l:num`; `l:num`] BINOM_FACT) THEN
  REWRITE_TAC[GSYM MULT_2] THEN
  DISCH_THEN(MP_TAC o AP_TERM `index p`) THEN
  ASM_SIMP_TAC[INDEX_MUL; FACT_NZ; MULT_EQ_0; BINOM_EQ_0;
               ARITH_RULE `~(2 * l < l)`] THEN
  ASM_SIMP_TAC[INDEX_FACT_ALT] THEN
  REWRITE_TAC[nv_dig_fin_flog] THEN
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
    REWRITE_TAC[] THEN MATCH_MP_TAC NV_DIG_FIN_BDRY_DIV2_LEMMA THEN
    REWRITE_TAC[EXP_EQ_0] THEN ASM_ARITH_TAC;
    ASM_SIMP_TAC[NSUM_ADD; NSUM_LMUL; NSUM_CONST; MULT_CLAUSES; LE_REFL]]);;

let NV_DIG_FIN_BDRY_BINOM_VAL = prove
 (`forall p l H. prime p /\ 2 * l <= H
           ==> nv_dig_fin_vge p (--(&(nv_dig_fin_flog p H))) (inv(&(binom(2 * l,l))))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC NV_DIG_FIN_BDRY_INV_INDEX THEN
  ASM_REWRITE_TAC[BINOM_EQ_0; ARITH_RULE `~(2 * l < l)`] THEN
  TRANS_TAC LE_TRANS `nv_dig_fin_flog p (2 * l)` THEN
  ASM_SIMP_TAC[NV_DIG_FIN_BDRY_INDEX_BINOM; NV_DIG_FIN_BDRY_FLOG_MONO]);;

