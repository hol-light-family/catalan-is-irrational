(* ========================================================================= *)
(* fin_dig: congruences modulo p between local integers (base library).     *)
(* ========================================================================= *)

needs "src/catalan_fin_base.ml";;

prioritize_real();;

let fin_dig_cg = new_definition
 `fin_dig_cg p x y <=> fin_zp p x /\ fin_zp p y /\ fin_vge p (&1) (x - y)`;;

let fin_dig_unit = new_definition
 `fin_dig_unit p u <=> ~(u = &0) /\ fin_zp p u /\ fin_zp p (inv u)`;;

let FIN_DIG_CG_REFL = prove
 (`forall p x. prime p /\ fin_zp p x ==> fin_dig_cg p x x`,
  SIMP_TAC[fin_dig_cg; REAL_SUB_REFL; FIN_VGE_0]);;

let FIN_DIG_CG_SYM = prove
 (`forall p x y. fin_dig_cg p x y ==> fin_dig_cg p y x`,
  REWRITE_TAC[fin_dig_cg] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  ONCE_REWRITE_TAC[REAL_ARITH `y - x = --(x - y)`] THEN
  ASM_REWRITE_TAC[FIN_VGE_NEG_EQ]);;

let FIN_DIG_CG_TRANS = prove
 (`forall p x y z. prime p /\ fin_dig_cg p x y /\ fin_dig_cg p y z ==> fin_dig_cg p x z`,
  REWRITE_TAC[fin_dig_cg] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  ONCE_REWRITE_TAC[REAL_ARITH `x - z = (x - y) + (y - z)`] THEN
  ASM_SIMP_TAC[FIN_VGE_ADD]);;

let FIN_DIG_CG_ADD = prove
 (`forall p x y x' y'. prime p /\ fin_dig_cg p x y /\ fin_dig_cg p x' y'
                 ==> fin_dig_cg p (x + x') (y + y')`,
  REWRITE_TAC[fin_dig_cg] THEN REPEAT STRIP_TAC THEN ASM_SIMP_TAC[FIN_ZP_ADD] THEN
  ONCE_REWRITE_TAC[REAL_ARITH `(x + x') - (y + y') = (x - y) + (x' - y')`] THEN
  ASM_SIMP_TAC[FIN_VGE_ADD]);;

let FIN_DIG_CG_NEG = prove
 (`forall p x y. fin_dig_cg p x y ==> fin_dig_cg p (--x) (--y)`,
  REWRITE_TAC[fin_dig_cg; FIN_ZP_NEG_EQ] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[REAL_ARITH `--x - --y = --(x - y)`; FIN_VGE_NEG_EQ]);;

let FIN_DIG_CG_SUB = prove
 (`forall p x y x' y'. prime p /\ fin_dig_cg p x y /\ fin_dig_cg p x' y'
                 ==> fin_dig_cg p (x - x') (y - y')`,
  SIMP_TAC[real_sub; FIN_DIG_CG_ADD; FIN_DIG_CG_NEG]);;

let FIN_DIG_CG_MUL = prove
 (`forall p x y x' y'. prime p /\ fin_dig_cg p x y /\ fin_dig_cg p x' y'
                 ==> fin_dig_cg p (x * x') (y * y')`,
  REWRITE_TAC[fin_dig_cg] THEN REPEAT STRIP_TAC THEN ASM_SIMP_TAC[FIN_ZP_MUL] THEN
  ONCE_REWRITE_TAC[REAL_ARITH `x * x' - y * y' = (x - y) * x' + y * (x' - y')`] THEN
  MATCH_MP_TAC FIN_VGE_ADD THEN ASM_SIMP_TAC[FIN_VGE_MUL_ZP; FIN_VGE_ZP_MUL]);;

let FIN_DIG_CG_POW = prove
 (`forall p x y n. prime p /\ fin_dig_cg p x y ==> fin_dig_cg p (x pow n) (y pow n)`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN
  ASM_SIMP_TAC[real_pow; FIN_DIG_CG_REFL; FIN_ZP_1; FIN_DIG_CG_MUL]);;

let FIN_DIG_CG_SUM = prove
 (`forall p (f:A->real) g s. prime p /\ FINITE s /\ (forall i. i IN s ==> fin_dig_cg p (f i) (g i))
             ==> fin_dig_cg p (sum s f) (sum s g)`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN DISCH_TAC THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  ASM_SIMP_TAC[SUM_CLAUSES; FORALL_IN_INSERT; FIN_DIG_CG_ADD; FIN_DIG_CG_REFL; FIN_ZP_0]);;

let FIN_DIG_CG_EQ = prove
 (`forall p x y x' y'. fin_dig_cg p x y /\ x' = x /\ y' = y ==> fin_dig_cg p x' y'`,
  MESON_TAC[]);;

let FIN_DIG_CG_0 = prove
 (`forall p x. prime p ==> (fin_dig_cg p x (&0) <=> fin_vge p (&1) x)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[fin_dig_cg; REAL_SUB_RZERO] THEN
  ASM_SIMP_TAC[FIN_ZP_0] THEN EQ_TAC THEN SIMP_TAC[] THEN
  ASM_MESON_TAC[FIN_VGE_IMP_ZP; REAL_POS]);;

let FIN_DIG_CG_PMUL = prove
 (`forall p x. prime p /\ fin_zp p x ==> fin_dig_cg p (&p * x) (&0)`,
  SIMP_TAC[FIN_DIG_CG_0] THEN REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[REAL_ARITH `&1 = &0 + &1`] THEN
  ASM_SIMP_TAC[FIN_VGE_PMUL; FIN_VGE_ZP]);;

let FIN_DIG_CG_ZP = prove
 (`forall p x y. fin_dig_cg p x y ==> fin_zp p x /\ fin_zp p y`,
  SIMP_TAC[fin_dig_cg]);;

let FIN_DIG_CG_VGE = prove
 (`forall p x y. fin_dig_cg p x y ==> fin_vge p (&1) (x - y)`,
  SIMP_TAC[fin_dig_cg]);;

let FIN_DIG_CG_ZERO_MUL = prove
 (`forall p x y. prime p /\ fin_dig_cg p x (&0) /\ fin_zp p y
           ==> fin_dig_cg p (x * y) (&0) /\ fin_dig_cg p (y * x) (&0)`,
  REPEAT STRIP_TAC THENL
   [MP_TAC(SPECL [`p:num`; `x:real`; `&0`; `y:real`; `y:real`] FIN_DIG_CG_MUL);
    MP_TAC(SPECL [`p:num`; `y:real`; `y:real`; `x:real`; `&0`] FIN_DIG_CG_MUL)] THEN
  ASM_SIMP_TAC[FIN_DIG_CG_REFL; REAL_MUL_LZERO; REAL_MUL_RZERO]);;

(* ------------------------------------------------------------------------- *)
(* Units.                                                                    *)
(* ------------------------------------------------------------------------- *)

let FIN_DIG_UNIT_NUM = prove
 (`forall p n. prime p /\ ~(p divides n) ==> fin_dig_unit p (&n)`,
  SIMP_TAC[fin_dig_unit; FIN_ZP_NUM; FIN_ZP_INV_NUM] THEN
  MESON_TAC[FIN_NDIV_NZ]);;

let FIN_DIG_UNIT_NUM_LT = prove
 (`forall p n. prime p /\ 0 < n /\ n < p ==> fin_dig_unit p (&n)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC FIN_DIG_UNIT_NUM THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o MATCH_MP DIVIDES_LE) THEN ASM_ARITH_TAC);;

let FIN_DIG_UNIT_NZ = prove
 (`forall p u. fin_dig_unit p u ==> ~(u = &0)`,
  SIMP_TAC[fin_dig_unit]);;

let FIN_DIG_UNIT_ZP = prove
 (`forall p u. fin_dig_unit p u ==> fin_zp p u /\ fin_zp p (inv u)`,
  SIMP_TAC[fin_dig_unit]);;

let FIN_DIG_UNIT_INV = prove
 (`forall p u. fin_dig_unit p u ==> fin_dig_unit p (inv u)`,
  SIMP_TAC[fin_dig_unit; REAL_INV_INV; REAL_INV_EQ_0]);;

let FIN_DIG_UNIT_MUL = prove
 (`forall p u v. prime p /\ fin_dig_unit p u /\ fin_dig_unit p v ==> fin_dig_unit p (u * v)`,
  SIMP_TAC[fin_dig_unit; REAL_INV_MUL; FIN_ZP_MUL; REAL_ENTIRE]);;

let FIN_DIG_UNIT_DIV = prove
 (`forall p u v. prime p /\ fin_dig_unit p u /\ fin_dig_unit p v ==> fin_dig_unit p (u / v)`,
  SIMP_TAC[real_div; FIN_DIG_UNIT_MUL; FIN_DIG_UNIT_INV]);;

let FIN_DIG_UNIT_NEG = prove
 (`forall p u. fin_dig_unit p u ==> fin_dig_unit p (--u)`,
  SIMP_TAC[fin_dig_unit; REAL_INV_NEG; FIN_ZP_NEG_EQ; REAL_NEG_EQ_0]);;

let FIN_DIG_UNIT_POW = prove
 (`forall p u n. prime p /\ fin_dig_unit p u ==> fin_dig_unit p (u pow n)`,
  SIMP_TAC[fin_dig_unit; GSYM REAL_POW_INV; FIN_ZP_POW; REAL_POW_EQ_0]);;

let FIN_DIG_UNIT_1 = prove
 (`forall p. prime p ==> fin_dig_unit p (&1)`,
  SIMP_TAC[fin_dig_unit; REAL_INV_1; FIN_ZP_1] THEN REAL_ARITH_TAC);;

(* A unit is not congruent to 0. *)
let FIN_DIG_UNIT_NOT_CG0 = prove
 (`forall p u. prime p /\ fin_dig_unit p u ==> ~fin_vge p (&1) u`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `fin_vge p (&1) (u * inv u)` MP_TAC THENL
   [MATCH_MP_TAC FIN_VGE_MUL_ZP THEN ASM_MESON_TAC[fin_dig_unit];
    SUBGOAL_THEN `u * inv u = &1` SUBST1_TAC THENL
     [ASM_MESON_TAC[REAL_MUL_RINV; FIN_DIG_UNIT_NZ]; ALL_TAC] THEN
    ASM_SIMP_TAC[FIN_VGE_1_NUM; DIVIDES_ONE] THEN ASM_MESON_TAC[PRIME_1]]);;

(* A local integer not divisible by p is a unit. *)
let FIN_DIG_ZP_UNIT = prove
 (`forall p x. prime p /\ fin_zp p x /\ ~fin_vge p (&1) x ==> fin_dig_unit p x`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN DISCH_TAC THEN
  ASM_SIMP_TAC[FIN_VGE_POS; REAL_POW_1] THEN
  GEN_REWRITE_TAC LAND_CONV [fin_zp] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`m:real`; `n:num`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC (CONJUNCTS_THEN2 ASSUME_TAC SUBST_ALL_TAC)) THEN
  REWRITE_TAC[is_int; LEFT_IMP_EXISTS_THM] THEN X_GEN_TAC `k:num` THEN
  DISCH_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP FIN_NDIV_NZ) THEN
  MP_TAC(SPEC `p:num` PRIME_IMP_NZ) THEN ASM_REWRITE_TAC[GSYM REAL_OF_NUM_EQ] THEN
  DISCH_TAC THEN
  ASM_CASES_TAC `p divides k` THENL
   [UNDISCH_TAC `~fin_zp p (m / &n / &p)` THEN
    MATCH_MP_TAC(TAUT `a ==> ~a ==> b`) THEN
    UNDISCH_TAC `p divides k` THEN REWRITE_TAC[divides] THEN
    DISCH_THEN(X_CHOOSE_THEN `e:num` SUBST_ALL_TAC) THEN
    REWRITE_TAC[fin_zp] THEN
    FIRST_X_ASSUM(DISJ_CASES_THEN SUBST_ALL_TAC) THENL
     [MAP_EVERY EXISTS_TAC [`&e:real`; `n:num`];
      MAP_EVERY EXISTS_TAC [`--(&e):real`; `n:num`]] THEN
    ASM_SIMP_TAC[INTEGER_CLOSED; GSYM REAL_OF_NUM_MUL] THEN
    UNDISCH_TAC `~(&p = &0)` THEN UNDISCH_TAC `~(&n = &0)` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  SUBGOAL_THEN `~(&k = &0)` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_EQ] THEN DISCH_THEN SUBST_ALL_TAC THEN
    ASM_MESON_TAC[DIVIDES_0]; ALL_TAC] THEN
  REWRITE_TAC[fin_dig_unit] THEN
  FIRST_X_ASSUM(DISJ_CASES_THEN SUBST_ALL_TAC) THEN
  REPEAT CONJ_TAC THEN REWRITE_TAC[fin_zp] THENL
   [ALL_TAC; MAP_EVERY EXISTS_TAC [`&k:real`; `n:num`];
    MAP_EVERY EXISTS_TAC [`&n:real`; `k:num`];
    ALL_TAC; MAP_EVERY EXISTS_TAC [`--(&k):real`; `n:num`];
    MAP_EVERY EXISTS_TAC [`--(&n):real`; `k:num`]] THEN
  ASM_SIMP_TAC[INTEGER_CLOSED] THEN
  UNDISCH_TAC `~(&k = &0)` THEN UNDISCH_TAC `~(&n = &0)` THEN CONV_TAC REAL_FIELD);;

(* Congruent to a unit implies a unit, and inverses are congruent. *)
let FIN_DIG_CG_INV = prove
 (`forall p u v. prime p /\ fin_dig_unit p u /\ fin_dig_cg p u v
           ==> fin_dig_unit p v /\ fin_dig_cg p (inv u) (inv v)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `fin_dig_unit p v` ASSUME_TAC THENL
   [MATCH_MP_TAC FIN_DIG_ZP_UNIT THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[fin_dig_cg]; ALL_TAC] THEN DISCH_TAC THEN
    MP_TAC(SPECL [`p:num`; `u:real`] FIN_DIG_UNIT_NOT_CG0) THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `u = (u - v) + v` SUBST1_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC FIN_VGE_ADD THEN ASM_MESON_TAC[fin_dig_cg];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[fin_dig_cg] THEN
  REPEAT(CONJ_TAC THENL [ASM_MESON_TAC[fin_dig_unit]; ALL_TAC]) THEN
  SUBGOAL_THEN `inv u - inv v = (u - v) * --(inv u * inv v)` SUBST1_TAC THENL
   [MP_TAC(SPECL [`p:num`; `u:real`] FIN_DIG_UNIT_NZ) THEN
    MP_TAC(SPECL [`p:num`; `v:real`] FIN_DIG_UNIT_NZ) THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC REAL_FIELD;
    MATCH_MP_TAC FIN_VGE_MUL_ZP THEN ASM_REWRITE_TAC[FIN_ZP_NEG_EQ] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC FIN_ZP_MUL THEN ASM_MESON_TAC[fin_dig_unit];
      ASM_MESON_TAC[fin_dig_cg]]]);;

let FIN_DIG_CG_DIV = prove
 (`forall p x y u v. prime p /\ fin_dig_cg p x y /\ fin_dig_unit p u /\ fin_dig_cg p u v
               ==> fin_dig_cg p (x / u) (y / v)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[real_div] THEN
  MATCH_MP_TAC FIN_DIG_CG_MUL THEN ASM_MESON_TAC[FIN_DIG_CG_INV]);;

let FIN_DIG_CG_DIV_NUM = prove
 (`forall p x y n. prime p /\ fin_dig_cg p x y /\ ~(p divides n)
             ==> fin_dig_cg p (x / &n) (y / &n)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC FIN_DIG_CG_DIV THEN
  ASM_SIMP_TAC[FIN_DIG_UNIT_NUM; FIN_DIG_CG_REFL; FIN_ZP_NUM]);;

(* Congruences of natural numbers. *)
let FIN_DIG_CG_INTEGER = prove
 (`forall p x y. prime p /\ integer x /\ integer y /\ (exists k. integer k /\ x - y = &p * k)
           ==> fin_dig_cg p x y`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[fin_dig_cg; FIN_ZP_INTEGER] THEN
  ONCE_REWRITE_TAC[REAL_ARITH `&1 = &0 + &1`] THEN
  ASM_SIMP_TAC[FIN_VGE_PMUL; FIN_VGE_INTEGER]);;

let FIN_DIG_CG_NUM = prove
 (`forall p a b. prime p /\ (a == b) (mod p) ==> fin_dig_cg p (&a) (&b)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC FIN_DIG_CG_INTEGER THEN
  ASM_REWRITE_TAC[INTEGER_CLOSED] THEN
  FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[CONG_CASES]) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[GSYM REAL_OF_NUM_ADD; GSYM REAL_OF_NUM_MUL] THENL
   [EXISTS_TAC `&q:real`; EXISTS_TAC `--(&q):real`] THEN
  SIMP_TAC[INTEGER_CLOSED] THEN REAL_ARITH_TAC);;


(* ------------------------------------------------------------------------- *)
(* Sums over a range in which only multiples of p survive.                   *)
(* ------------------------------------------------------------------------- *)

let FIN_DIG_SUM_MULTIPLES = prove
 (`forall p a b f g.
        prime p /\
        (forall k. a <= k /\ k <= b /\ ~(p divides k) ==> fin_dig_cg p (f k) (&0)) /\
        (forall m. a <= m * p /\ m * p <= b ==> fin_dig_cg p (f (m * p)) (g m))
        ==> fin_dig_cg p (sum (a..b) f) (sum {m | a <= m * p /\ m * p <= b} g)`,
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
  MATCH_MP_TAC FIN_DIG_CG_ADD THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
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
    MATCH_MP_TAC FIN_DIG_CG_SUM THEN ASM_REWRITE_TAC[o_THM; IN_ELIM_THM];
    SUBGOAL_THEN `&0 = sum {k | k IN a..b /\ ~(p divides k)} (\k. &0)` SUBST1_TAC THENL
     [REWRITE_TAC[SUM_0]; ALL_TAC] THEN
    MATCH_MP_TAC FIN_DIG_CG_SUM THEN
    ASM_SIMP_TAC[FINITE_RESTRICT; FINITE_NUMSEG; IN_ELIM_THM; IN_NUMSEG]]);;
