(* ========================================================================= *)
(* CAT_NONVANISHING, part La (prefix nv_dig_): digit/carry facts for c_l and *)
(* H*_z (paper Equations (32), (33)) at an odd prime p = 2s+1.               *)
(* Works in the nv_dig_fin_zp / nv_dig_fin_dig_cg / nv_dig_fin_dig_unit     *)
(* framework of src/catalan_nv_dig_fin.ml (a renamed standalone copy of the  *)
(* finite-place component's lemmas) and bridges to nv_pint / nv_cong.       *)
(* ========================================================================= *)

needs "src/catalan_nv_base.ml";;
needs "src/catalan_nv_dig_fin.ml";;

(* ------------------------------------------------------------------------- *)
(* Bridge.                                                                   *)
(* ------------------------------------------------------------------------- *)

let NV_DIG_ZP_PINT = prove
 (`forall p x. nv_dig_fin_zp p x <=> nv_pint p x`,
  REPEAT GEN_TAC THEN REWRITE_TAC[nv_dig_fin_zp; nv_pint] THEN EQ_TAC THEN STRIP_TAC THENL
   [EXISTS_TAC `n:num` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `~(&n = &0)` ASSUME_TAC THENL [ASM_MESON_TAC[NV_DIG_FIN_NDIV_NZ]; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_DIV_LMUL];
    MAP_EVERY EXISTS_TAC [`&n * x`; `n:num`] THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `~(&n = &0)` MP_TAC THENL
     [ASM_MESON_TAC[NV_DIG_FIN_NDIV_NZ]; CONV_TAC REAL_FIELD]]);;

let NV_DIG_CG_CONG = prove
 (`forall p x y. prime p /\ nv_dig_fin_dig_cg p x y ==> nv_cong p x y`,
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o MATCH_MP NV_DIG_FIN_DIG_CG_VGE) THEN
  ASM_SIMP_TAC[NV_DIG_FIN_VGE_POS; REAL_POW_1; nv_cong; NV_DIG_ZP_PINT]);;

(* ------------------------------------------------------------------------- *)
(* Small helpers.                                                            *)
(* ------------------------------------------------------------------------- *)

let NV_DIG_PS = prove
 (`forall s p. 2 * s + 1 = p ==> (p - 1) DIV 2 = s /\ p - 1 = 2 * s /\ ~(p = 2)`,
  REPEAT GEN_TAC THEN DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[NV_DIG_FIN_DIG_C_S] THEN
  DISCH_THEN(MP_TAC o AP_TERM `EVEN`) THEN REWRITE_TAC[EVEN_ADD; EVEN_MULT; ARITH]);;

let NV_DIG_PS_TAC = FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP NV_DIG_PS th]);;

let NV_DIG_UNIT_CG = prove
 (`forall p x y. prime p /\ nv_dig_fin_dig_unit p y /\ nv_dig_fin_dig_cg p x y ==> nv_dig_fin_dig_unit p x`,
  MESON_TAC[NV_DIG_FIN_DIG_CG_INV; NV_DIG_FIN_DIG_CG_SYM]);;

let NV_DIG_EPS2 = prove
 (`forall s. (--(&1)) pow s * (--(&1)) pow s = &1`,
  REWRITE_TAC[GSYM REAL_POW_MUL] THEN
  REWRITE_TAC[REAL_ARITH `--(&1) * --(&1) = &1`; REAL_POW_ONE]);;

let NV_DIG_EPS_UNIT = prove
 (`forall p s. prime p ==> nv_dig_fin_dig_unit p ((--(&1)) pow s)`,
  MESON_TAC[NV_DIG_FIN_DIG_UNIT_POW; NV_DIG_FIN_DIG_UNIT_NEG; NV_DIG_FIN_DIG_UNIT_1]);;

let NV_DIG_EPS_INV = prove
 (`forall s. inv((--(&1)) pow s) = (--(&1)) pow s`,
  GEN_TAC THEN MATCH_MP_TAC REAL_MUL_RINV_UNIQ THEN REWRITE_TAC[NV_DIG_EPS2]);;

let NV_DIG_NDIV = prove
 (`forall p P r. 0 < r /\ r < p ==> ~(p divides P * p + r)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `p divides r` MP_TAC THENL
   [MATCH_MP_TAC DIVIDES_ADD_REVR THEN EXISTS_TAC `P * p:num` THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[DIVIDES_LMUL; DIVIDES_REFL];
    DISCH_THEN(MP_TAC o MATCH_MP DIVIDES_LE) THEN ASM_ARITH_TAC]);;

let NV_DIG_NDIV_LT = prove
 (`forall p r. 0 < r /\ r < p ==> ~(p divides r)`,
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o MATCH_MP DIVIDES_LE) THEN
  ASM_ARITH_TAC);;

let NV_DIG_CG_QUOT = prove
 (`forall p a b c d. prime p /\ ~(p divides b) /\ ~(p divides d) /\
               (a * d == c * b) (mod p)
               ==> nv_dig_fin_dig_cg p (&a / &b) (&c / &d)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(&b = &0) /\ ~(&d = &0)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[NV_DIG_FIN_NDIV_NZ]; ALL_TAC] THEN
  MATCH_MP_TAC NV_DIG_FIN_DIG_CG_EQ THEN
  MAP_EVERY EXISTS_TAC [`&(a * d) / &(b * d)`; `&(c * b) / &(b * d)`] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC NV_DIG_FIN_DIG_CG_DIV_NUM THEN ASM_SIMP_TAC[NV_DIG_FIN_DIG_CG_NUM] THEN
    ASM_SIMP_TAC[PRIME_DIVPROD_EQ];
    REWRITE_TAC[GSYM REAL_OF_NUM_MUL] THEN
    REPEAT(POP_ASSUM MP_TAC) THEN CONV_TAC REAL_FIELD;
    REWRITE_TAC[GSYM REAL_OF_NUM_MUL] THEN
    REPEAT(POP_ASSUM MP_TAC) THEN CONV_TAC REAL_FIELD]);;

let NV_DIG_CG_SHIFT = prove
 (`forall p P a b. prime p /\ 0 < b /\ b < p
             ==> nv_dig_fin_dig_cg p (&(P * p + a) / &(P * p + b)) (&a / &b)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC NV_DIG_CG_QUOT THEN
  ASM_SIMP_TAC[NV_DIG_NDIV; NV_DIG_NDIV_LT] THEN CONV_TAC NUMBER_RULE);;

let NV_DIG_C_UNIT2 = prove
 (`forall p A B. prime p /\ ~(p = 2) /\ 2 * A < p /\ 2 * B < p
           ==> nv_dig_fin_dig_unit p (cat_c (A * p + B)) /\
               nv_dig_fin_dig_cg p (cat_c (A * p + B)) (cat_c A * cat_c B)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `nv_dig_fin_dig_cg p (cat_c (A * p + B)) (cat_c A * cat_c B)` ASSUME_TAC THENL
   [MATCH_MP_TAC NV_DIG_FIN_DIG_C_NOCARRY THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC NV_DIG_UNIT_CG THEN
  EXISTS_TAC `cat_c A * cat_c B` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC NV_DIG_FIN_DIG_UNIT_MUL THEN ASM_SIMP_TAC[NV_DIG_FIN_DIG_C_UNIT]);;

let NV_DIG_HSTAR_SMALL = prove
 (`forall p z. prime p /\ ~(p = 2) /\ z < p ==> nv_dig_fin_dig_unit p (nv_dig_fin_hstar z)`,
  REPEAT STRIP_TAC THEN DISJ_CASES_TAC(SPEC `z:num` EVEN_OR_ODD) THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `a:num` SUBST_ALL_TAC o
    REWRITE_RULE[EVEN_EXISTS; ODD_EXISTS; ADD1]) THEN
  REWRITE_TAC[NV_DIG_FIN_BDRY_HSTAR_EVEN2; NV_DIG_FIN_BDRY_HSTAR_ODD2] THENL
   [MATCH_MP_TAC NV_DIG_FIN_DIG_C_UNIT THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC NV_DIG_FIN_DIG_UNIT_INV THEN MATCH_MP_TAC NV_DIG_FIN_DIG_UNIT_MUL THEN
    ASM_SIMP_TAC[NV_DIG_FIN_DIG_UNIT_NUM_LT; ARITH_RULE `0 < 2 * a + 1`] THEN
    MATCH_MP_TAC NV_DIG_FIN_DIG_C_UNIT THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC]);;

let NV_DIG_HSTAR_PAIR = prove
 (`forall K. nv_dig_fin_hstar (2 * K + 1) = inv(&(2 * K + 2) * nv_dig_fin_hstar (2 * K + 2))`,
  GEN_TAC THEN
  REWRITE_TAC[NV_DIG_FIN_BDRY_HSTAR_ODD2; ARITH_RULE `2 * K + 2 = 2 * (K + 1)`;
              NV_DIG_FIN_BDRY_HSTAR_EVEN2; NV_DIG_FIN_BDRY_C_STEP] THEN
  AP_TERM_TAC THEN MP_TAC(SPEC `K:num` NV_DIG_FIN_BDRY_C_POS) THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_ADD; GSYM REAL_OF_NUM_MUL] THEN
  CONV_TAC REAL_FIELD);;

(* ------------------------------------------------------------------------- *)
(* Digit laws for H*_z, z = P p + r, P + 2 < p, p = 2 s + 1.                 *)
(* ------------------------------------------------------------------------- *)

let NV_DIG_HA = prove
 (`forall p s P r. prime p /\ 2 * s + 1 = p /\ P + 2 < p /\ r < p /\ EVEN P /\ EVEN r
             ==> nv_dig_fin_dig_unit p (nv_dig_fin_hstar (P * p + r)) /\
                 nv_dig_fin_dig_cg p (nv_dig_fin_hstar (P * p + r)) (nv_dig_fin_hstar P * cat_c (r DIV 2))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `B:num` SUBST_ALL_TAC o REWRITE_RULE[EVEN_EXISTS]) THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `A:num` SUBST_ALL_TAC o REWRITE_RULE[EVEN_EXISTS]) THEN
  REWRITE_TAC[NUM_RING `(2 * A) * p + 2 * B = 2 * (A * p + B)`; NV_DIG_FIN_BDRY_HSTAR_EVEN2] THEN
  SIMP_TAC[DIV_MULT; ARITH_EQ] THEN
  MATCH_MP_TAC NV_DIG_C_UNIT2 THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

let NV_DIG_HB = prove
 (`forall p s P r. prime p /\ 2 * s + 1 = p /\ P + 2 < p /\ r < p /\ EVEN P /\ ODD r
             ==> nv_dig_fin_dig_unit p (nv_dig_fin_hstar (P * p + r))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `B:num` SUBST_ALL_TAC o REWRITE_RULE[ODD_EXISTS; ADD1]) THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `A:num` SUBST_ALL_TAC o REWRITE_RULE[EVEN_EXISTS]) THEN
  REWRITE_TAC[NUM_RING `(2 * A) * p + 2 * B + 1 = 2 * (A * p + B) + 1`;
              NV_DIG_FIN_BDRY_HSTAR_ODD2] THEN
  MATCH_MP_TAC NV_DIG_FIN_DIG_UNIT_INV THEN MATCH_MP_TAC NV_DIG_FIN_DIG_UNIT_MUL THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC NV_DIG_FIN_DIG_UNIT_NUM THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[NUM_RING `2 * (A * p + B) + 1 = (2 * A) * p + (2 * B + 1)`] THEN
    MATCH_MP_TAC NV_DIG_NDIV THEN ASM_ARITH_TAC;
    MP_TAC(SPECL [`p:num`; `A:num`; `B:num`] NV_DIG_C_UNIT2) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_ARITH_TAC; SIMP_TAC[]]]);;

(* c_(A p + s) == c_A * eps and its consequence for inv(m c_(A p + s)) *)
let NV_DIG_CHALF = prove
 (`forall p s A m. prime p /\ 2 * s + 1 = p /\ 2 * A < p /\ 0 < m /\ m < p
             ==> nv_dig_fin_dig_cg p (inv(&m * cat_c (A * p + s)))
                              ((--(&1)) pow s * inv(&m * cat_c A))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(p = 2) /\ 2 * s < p:num` STRIP_ASSUME_TAC THENL
   [NV_DIG_PS_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `nv_dig_fin_dig_cg p (cat_c s) ((--(&1)) pow s)` ASSUME_TAC THENL
   [MP_TAC(SPEC `p:num` NV_DIG_FIN_DIG_C_HALF) THEN ASM_REWRITE_TAC[] THEN
    NV_DIG_PS_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`p:num`; `A:num`; `s:num`] NV_DIG_C_UNIT2) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `nv_dig_fin_dig_cg p (&m * cat_c (A * p + s))
                             (&m * (cat_c A * (--(&1)) pow s))` ASSUME_TAC THENL
   [MATCH_MP_TAC NV_DIG_FIN_DIG_CG_MUL THEN ASM_SIMP_TAC[NV_DIG_FIN_DIG_CG_REFL; NV_DIG_FIN_ZP_NUM] THEN
    MATCH_MP_TAC NV_DIG_FIN_DIG_CG_TRANS THEN EXISTS_TAC `cat_c A * cat_c s` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC NV_DIG_FIN_DIG_CG_MUL THEN
    ASM_SIMP_TAC[NV_DIG_FIN_DIG_CG_REFL; NV_DIG_FIN_DIG_C_ZP];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`p:num`; `&m * cat_c (A * p + s)`;
                 `&m * (cat_c A * (--(&1)) pow s)`] NV_DIG_FIN_DIG_CG_INV) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC NV_DIG_FIN_DIG_UNIT_MUL THEN
    ASM_SIMP_TAC[NV_DIG_FIN_DIG_UNIT_NUM_LT];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o CONJUNCT2) THEN
  MATCH_MP_TAC(TAUT `(a <=> b) ==> a ==> b`) THEN AP_TERM_TAC THEN
  REWRITE_TAC[REAL_INV_MUL; NV_DIG_EPS_INV] THEN REAL_ARITH_TAC);;

let NV_DIG_HC = prove
 (`forall p s P. prime p /\ 2 * s + 1 = p /\ P + 2 < p /\ ODD P
           ==> forall k. 2 * k < p
                   ==> nv_dig_fin_dig_cg p (&p * nv_dig_fin_hstar (P * p + 2 * k))
                                    ((--(&1)) pow s * cat_c k * nv_dig_fin_hstar P)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `A:num` SUBST_ALL_TAC o REWRITE_RULE[ODD_EXISTS; ADD1]) THEN
  SUBGOAL_THEN `~(p = 2) /\ 2 * A < p /\ 2 * A + 1 < p:num /\ ~(&p = &0)`
  STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[REAL_OF_NUM_EQ] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  INDUCT_TAC THENL
   [DISCH_TAC THEN
    SUBGOAL_THEN `(2 * A + 1) * p + 2 * 0 = 2 * (A * p + s) + 1` SUBST1_TAC THENL
     [UNDISCH_TAC `2 * s + 1 = p:num` THEN CONV_TAC NUM_RING; ALL_TAC] THEN
    REWRITE_TAC[NV_DIG_FIN_BDRY_HSTAR_ODD2; NV_DIG_FIN_BDRY_C_0; REAL_MUL_LID] THEN
    SUBGOAL_THEN `&p * inv(&(2 * (A * p + s) + 1) * cat_c (A * p + s)) =
                  inv(&(2 * A + 1) * cat_c (A * p + s))` SUBST1_TAC THENL
     [SUBGOAL_THEN `2 * (A * p + s) + 1 = (2 * A + 1) * p` SUBST1_TAC THENL
       [UNDISCH_TAC `2 * s + 1 = p:num` THEN CONV_TAC NUM_RING; ALL_TAC] THEN
      MP_TAC(SPEC `A * p + s:num` NV_DIG_FIN_BDRY_C_POS) THEN
      UNDISCH_TAC `~(&p = &0)` THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_MUL; GSYM REAL_OF_NUM_ADD] THEN
      CONV_TAC REAL_FIELD;
      ALL_TAC] THEN
    MATCH_MP_TAC NV_DIG_CHALF THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_TAC] THEN
  MP_TAC(SPEC `(2 * A + 1) * p + 2 * k` NV_DIG_FIN_BDRY_HSTAR_STEP) THEN
  REWRITE_TAC[GSYM ADD_ASSOC; ARITH_RULE `2 * k + 2 = 2 * SUC k`] THEN
  DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[ADD1; NV_DIG_FIN_BDRY_C_STEP; ARITH_RULE `2 * (k + 1) = 2 * k + (2:num)`] THEN
  MATCH_MP_TAC NV_DIG_FIN_DIG_CG_EQ THEN
  MAP_EVERY EXISTS_TAC
   [`(&p * nv_dig_fin_hstar ((2 * A + 1) * p + 2 * k)) *
     (&((2 * A + 1) * p + 2 * k + 1) / &((2 * A + 1) * p + 2 * k + 2))`;
    `((--(&1)) pow s * cat_c k * nv_dig_fin_hstar (2 * A + 1)) *
     (&(2 * k + 1) / &(2 * k + 2))`] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC NV_DIG_FIN_DIG_CG_MUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC NV_DIG_CG_SHIFT THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    REWRITE_TAC[real_div] THEN REAL_ARITH_TAC;
    REWRITE_TAC[real_div] THEN REAL_ARITH_TAC]);;

let NV_DIG_CONG_WIT = prove
 (`forall x y p q:num. y = x + p * q ==> (x == y) (mod p)`,
  REPEAT GEN_TAC THEN DISCH_THEN SUBST1_TAC THEN CONV_TAC NUMBER_RULE);;

let NV_DIG_Q_STEP = prove
 (`forall p z. ~(z = 0)
         ==> &p / (&(z + 2) * nv_dig_fin_hstar (z + 2)) =
             (&p / (&z * nv_dig_fin_hstar z)) * (&z / &(z + 1))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[NV_DIG_FIN_BDRY_HSTAR_STEP] THEN
  MP_TAC(SPEC `z:num` NV_DIG_FIN_BDRY_HSTAR_NZ) THEN
  UNDISCH_TAC `~(z = 0)` THEN REWRITE_TAC[GSYM REAL_OF_NUM_EQ] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN
  SUBGOAL_THEN `&0 <= &z` MP_TAC THENL [REWRITE_TAC[REAL_POS]; ALL_TAC] THEN
  CONV_TAC REAL_FIELD);;

let NV_DIG_FIELD1 = prove
 (`forall P c a b d. a = d * P /\ ~(P = &0) /\ ~(b = &0) /\ ~(d = &0) /\ &0 < c
               ==> P / (b * (c * a / b)) = inv(d * c)`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `&0 < c` THEN REPEAT(POP_ASSUM MP_TAC) THEN CONV_TAC REAL_FIELD);;

let NV_DIG_HD0 = prove
 (`forall p s P. prime p /\ 2 * s + 1 = p /\ P + 2 < p /\ ODD P
           ==> forall k j. s = k + j
                 ==> nv_dig_fin_dig_cg p
                      (&p / (&(P * p + 2 * k + 1) * nv_dig_fin_hstar (P * p + 2 * k + 1)))
                      (cat_c j * nv_dig_fin_hstar P)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `A:num` SUBST_ALL_TAC o REWRITE_RULE[ODD_EXISTS; ADD1]) THEN
  SUBGOAL_THEN `~(p = 2) /\ 2 * A < p /\ 2 * A + 1 < p:num /\ ~(&p = &0) /\ 2 * s < p`
  STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[REAL_OF_NUM_EQ] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `nv_dig_fin_dig_cg p (cat_c s) ((--(&1)) pow s)` ASSUME_TAC THENL
   [MP_TAC(SPEC `p:num` NV_DIG_FIN_DIG_C_HALF) THEN ASM_REWRITE_TAC[] THEN
    NV_DIG_PS_TAC;
    ALL_TAC] THEN
  INDUCT_TAC THENL
   [REWRITE_TAC[ADD_CLAUSES] THEN GEN_TAC THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES] THEN
    SUBGOAL_THEN `&p / (&((2 * A + 1) * p + 1) * nv_dig_fin_hstar ((2 * A + 1) * p + 1)) =
                  inv(&(2 * A + 1) * cat_c (A * p + s))` SUBST1_TAC THENL
     [SUBGOAL_THEN `(2 * A + 1) * p + 1 = 2 * ((A * p + s) + 1)` SUBST1_TAC THENL
       [UNDISCH_TAC `2 * s + 1 = p:num` THEN CONV_TAC NUM_RING; ALL_TAC] THEN
      REWRITE_TAC[NV_DIG_FIN_BDRY_HSTAR_EVEN2; NV_DIG_FIN_BDRY_C_STEP] THEN
      REWRITE_TAC[ARITH_RULE `2 * ((x:num) + 1) = 2 * x + 2`] THEN
      MATCH_MP_TAC NV_DIG_FIELD1 THEN
      ASM_REWRITE_TAC[NV_DIG_FIN_BDRY_C_POS; REAL_OF_NUM_EQ; REAL_OF_NUM_MUL] THEN
      CONJ_TAC THENL
       [UNDISCH_TAC `2 * s + 1 = p:num` THEN CONV_TAC NUM_RING; ARITH_TAC];
      ALL_TAC] THEN
    MATCH_MP_TAC NV_DIG_FIN_DIG_CG_TRANS THEN
    EXISTS_TAC `(--(&1)) pow s * inv(&(2 * A + 1) * cat_c A)` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC NV_DIG_CHALF THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[NV_DIG_FIN_BDRY_HSTAR_ODD2] THEN MATCH_MP_TAC NV_DIG_FIN_DIG_CG_SYM THEN
    MATCH_MP_TAC NV_DIG_FIN_DIG_CG_MUL THEN ASM_SIMP_TAC[NV_DIG_FIN_DIG_CG_SYM] THEN
    MATCH_MP_TAC NV_DIG_FIN_DIG_CG_REFL THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(SPECL [`p:num`; `2 * A + 1`] NV_DIG_HSTAR_SMALL) THEN
    ASM_SIMP_TAC[NV_DIG_FIN_BDRY_HSTAR_ODD2; NV_DIG_FIN_DIG_UNIT_ZP];
    ALL_TAC] THEN
  X_GEN_TAC `j:num` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `j + 1`) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_TAC] THEN
  ABBREV_TAC `x = (2 * A + 1) * p` THEN
  SUBGOAL_THEN `x + 2 * SUC k + 1 = (x + 2 * k + 1) + 2` SUBST1_TAC THENL
   [ARITH_TAC; ALL_TAC] THEN
  SIMP_TAC[NV_DIG_Q_STEP; ARITH_RULE `~(x + 2 * k + 1 = 0)`] THEN
  REWRITE_TAC[ARITH_RULE `(x + 2 * k + 1) + 1 = x + 2 * k + 2`] THEN
  MATCH_MP_TAC NV_DIG_FIN_DIG_CG_EQ THEN
  MAP_EVERY EXISTS_TAC
   [`(&p / (&(x + 2 * k + 1) * nv_dig_fin_hstar (x + 2 * k + 1))) *
     (&(x + 2 * k + 1) / &(x + 2 * k + 2))`;
    `(cat_c (j + 1) * nv_dig_fin_hstar (2 * A + 1)) * (&(2 * j + 2) / &(2 * j + 1))`] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC NV_DIG_FIN_DIG_CG_MUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC NV_DIG_CG_QUOT THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [EXPAND_TAC "x" THEN MATCH_MP_TAC NV_DIG_NDIV THEN ASM_ARITH_TAC;
      MATCH_MP_TAC NV_DIG_NDIV_LT THEN ASM_ARITH_TAC;
      MATCH_MP_TAC NV_DIG_CONG_WIT THEN EXISTS_TAC `2 * A + 2` THEN
      EXPAND_TAC "x" THEN
      UNDISCH_TAC `s = SUC k + j` THEN UNDISCH_TAC `2 * s + 1 = p:num` THEN
      REWRITE_TAC[ADD1] THEN CONV_TAC NUM_RING];
    REFL_TAC;
    REWRITE_TAC[NV_DIG_FIN_BDRY_C_STEP] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_ADD; GSYM REAL_OF_NUM_MUL] THEN
    SUBGOAL_THEN `~(&2 * &j + &1 = &0)` MP_TAC THENL
     [MP_TAC(SPEC `j:num` REAL_POS) THEN REAL_ARITH_TAC; CONV_TAC REAL_FIELD]]);;

let NV_DIG_PAR = prove
 (`forall s p P r. 2 * s + 1 = p ==> (EVEN (P * p + r) <=> (EVEN P <=> EVEN r))`,
  REPEAT GEN_TAC THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[EVEN_ADD; EVEN_MULT; ARITH] THEN CONV_TAC TAUT);;

let NV_DIG_HCR = prove
 (`forall p s P r. prime p /\ 2 * s + 1 = p /\ P + 2 < p /\ ODD P /\ r < p /\ EVEN r
     ==> nv_dig_fin_dig_cg p (&p * nv_dig_fin_hstar (P * p + r))
                      ((--(&1)) pow s * cat_c (r DIV 2) * nv_dig_fin_hstar P) /\
         nv_dig_fin_dig_unit p (&p * nv_dig_fin_hstar (P * p + r))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `k:num` SUBST_ALL_TAC o REWRITE_RULE[EVEN_EXISTS]) THEN
  SIMP_TAC[DIV_MULT; ARITH_EQ] THEN
  SUBGOAL_THEN `nv_dig_fin_dig_cg p (&p * nv_dig_fin_hstar (P * p + 2 * k))
                             ((--(&1)) pow s * cat_c k * nv_dig_fin_hstar P)` ASSUME_TAC THENL
   [MP_TAC(SPECL [`p:num`; `s:num`; `P:num`] NV_DIG_HC) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC NV_DIG_UNIT_CG THEN
  EXISTS_TAC `(--(&1)) pow s * cat_c k * nv_dig_fin_hstar P` THEN ASM_REWRITE_TAC[] THEN
  REPEAT(MATCH_MP_TAC NV_DIG_FIN_DIG_UNIT_MUL THEN ASM_REWRITE_TAC[] THEN CONJ_TAC) THEN
  ASM_SIMP_TAC[NV_DIG_EPS_UNIT] THENL
   [MATCH_MP_TAC NV_DIG_FIN_DIG_C_UNIT; MATCH_MP_TAC NV_DIG_HSTAR_SMALL] THEN
  ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

let NV_DIG_HD = prove
 (`forall p s P r. prime p /\ 2 * s + 1 = p /\ P + 2 < p /\ ODD P /\ r < p /\ ODD r
     ==> nv_dig_fin_dig_cg p (&p / (&(P * p + r) * nv_dig_fin_hstar (P * p + r)))
                      (cat_c ((p - r) DIV 2) * nv_dig_fin_hstar P) /\
         nv_dig_fin_dig_unit p (&p / (&(P * p + r) * nv_dig_fin_hstar (P * p + r))) /\
         nv_dig_fin_dig_unit p (nv_dig_fin_hstar (P * p + r) / &p)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `k:num` SUBST_ALL_TAC o REWRITE_RULE[ODD_EXISTS; ADD1]) THEN
  SUBGOAL_THEN `(p - (2 * k + 1)) DIV 2 = s - k` SUBST1_TAC THENL
   [SUBGOAL_THEN `p - (2 * k + 1) = 2 * (s - k)` SUBST1_TAC THENL
     [ASM_ARITH_TAC; SIMP_TAC[DIV_MULT; ARITH_EQ]];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(p = 2) /\ 2 * (s - k) < p /\ P < p:num /\ ~(&p = &0)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_EQ] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `nv_dig_fin_dig_cg p (&p / (&(P * p + 2 * k + 1) * nv_dig_fin_hstar (P * p + 2 * k + 1)))
                             (cat_c (s - k) * nv_dig_fin_hstar P)` ASSUME_TAC THENL
   [MP_TAC(SPECL [`p:num`; `s:num`; `P:num`] NV_DIG_HD0) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `nv_dig_fin_dig_unit p (&p / (&(P * p + 2 * k + 1) * nv_dig_fin_hstar (P * p + 2 * k + 1)))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC NV_DIG_UNIT_CG THEN
    EXISTS_TAC `cat_c (s - k) * nv_dig_fin_hstar P` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC NV_DIG_FIN_DIG_UNIT_MUL THEN ASM_SIMP_TAC[NV_DIG_HSTAR_SMALL; NV_DIG_FIN_DIG_C_UNIT];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `nv_dig_fin_hstar (P * p + 2 * k + 1) / &p =
                inv(&(P * p + 2 * k + 1) *
                    &p / (&(P * p + 2 * k + 1) * nv_dig_fin_hstar (P * p + 2 * k + 1)))`
  SUBST1_TAC THENL
   [MP_TAC(SPEC `P * p + 2 * k + 1` NV_DIG_FIN_BDRY_HSTAR_NZ) THEN
    UNDISCH_TAC `~(&p = &0)` THEN
    SUBGOAL_THEN `~(&(P * p + 2 * k + 1) = &0)` MP_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_EQ] THEN ARITH_TAC; CONV_TAC REAL_FIELD];
    ALL_TAC] THEN
  MATCH_MP_TAC NV_DIG_FIN_DIG_UNIT_INV THEN MATCH_MP_TAC NV_DIG_FIN_DIG_UNIT_MUL THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC NV_DIG_FIN_DIG_UNIT_NUM THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC NV_DIG_NDIV THEN ASM_ARITH_TAC);;

let NV_DIG_QA = prove
 (`forall p s m. prime p /\ 2 * s + 1 = p /\ m + 2 < p /\ EVEN m /\ 0 < m
           ==> nv_dig_fin_dig_cg p (&p / (&(m * p) * nv_dig_fin_hstar (m * p))) (nv_dig_fin_hstar (m - 1))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`p:num`; `s:num`; `m:num`; `0`] NV_DIG_HA) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[EVEN] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[ADD_CLAUSES; NUM_REDUCE_CONV `0 DIV 2`; NV_DIG_FIN_BDRY_C_0; REAL_MUL_RID] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `exists K. m = 2 * K + 2:num` (X_CHOOSE_THEN `K:num` SUBST_ALL_TAC) THENL
   [UNDISCH_TAC `EVEN m` THEN REWRITE_TAC[EVEN_EXISTS] THEN
    DISCH_THEN(X_CHOOSE_TAC `n:num`) THEN EXISTS_TAC `n - 1` THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[ARITH_RULE `(2 * K + 2) - 1 = 2 * K + (1:num)`; NV_DIG_HSTAR_PAIR] THEN
  SUBGOAL_THEN `&p / (&((2 * K + 2) * p) * nv_dig_fin_hstar ((2 * K + 2) * p)) =
                inv(&(2 * K + 2) * nv_dig_fin_hstar ((2 * K + 2) * p))` SUBST1_TAC THENL
   [MP_TAC(SPEC `(2 * K + 2) * p` NV_DIG_FIN_BDRY_HSTAR_NZ) THEN
    SUBGOAL_THEN `~(&p = &0) /\ ~(&(2 * K + 2) = &0)` MP_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_EQ] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_MUL] THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`p:num`; `&(2 * K + 2) * nv_dig_fin_hstar ((2 * K + 2) * p)`;
                 `&(2 * K + 2) * nv_dig_fin_hstar (2 * K + 2)`] NV_DIG_FIN_DIG_CG_INV) THEN
  ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC NV_DIG_FIN_DIG_UNIT_MUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC NV_DIG_FIN_DIG_UNIT_NUM_LT THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    MATCH_MP_TAC NV_DIG_FIN_DIG_CG_MUL THEN ASM_SIMP_TAC[NV_DIG_FIN_DIG_CG_REFL; NV_DIG_FIN_ZP_NUM]]);;

let NV_DIG_Q0 = prove
 (`forall p s P r. prime p /\ 2 * s + 1 = p /\ P + 2 < p /\ EVEN P /\ EVEN r /\ 0 < r /\ r < p
     ==> nv_dig_fin_dig_cg p (&p / (&(P * p + r) * nv_dig_fin_hstar (P * p + r))) (&0)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[real_div] THEN MATCH_MP_TAC NV_DIG_FIN_DIG_CG_PMUL THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `nv_dig_fin_dig_unit p (&(P * p + r) * nv_dig_fin_hstar (P * p + r))`
   (fun th -> MESON_TAC[th; NV_DIG_FIN_DIG_UNIT_ZP; NV_DIG_FIN_DIG_UNIT_INV]) THEN
  MATCH_MP_TAC NV_DIG_FIN_DIG_UNIT_MUL THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC NV_DIG_FIN_DIG_UNIT_NUM THEN ASM_SIMP_TAC[NV_DIG_NDIV];
    MP_TAC(SPECL [`p:num`; `s:num`; `P:num`; `r:num`] NV_DIG_HA) THEN
    ASM_SIMP_TAC[]]);;

let NV_DIG_QZP = prove
 (`forall p s z. prime p /\ 2 * s + 1 = p /\ z DIV p + 2 < p /\ EVEN z /\ 0 < z
           ==> nv_dig_fin_zp p (&p / (&z * nv_dig_fin_hstar z))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(p = 0)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`z:num`; `p:num`] DIVISION) THEN ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `P = z DIV p` THEN ABBREV_TAC `r = z MOD p` THEN
  DISCH_THEN(CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC) THEN
  FIRST_ASSUM(MP_TAC o SPECL [`P:num`; `r:num`] o MATCH_MP NV_DIG_PAR) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ASM_CASES_TAC `r = 0` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[ADD_CLAUSES; EVEN]) THEN
    REWRITE_TAC[ADD_CLAUSES] THEN
    SUBGOAL_THEN `~(P = 0)` ASSUME_TAC THENL
     [DISCH_THEN SUBST_ALL_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[MULT_CLAUSES]) THEN
      ASM_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(SPECL [`p:num`; `s:num`; `P:num`] NV_DIG_QA) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; MESON_TAC[NV_DIG_FIN_DIG_CG_ZP]];
    ALL_TAC] THEN
  ASM_CASES_TAC `EVEN r` THENL
   [MP_TAC(SPECL [`p:num`; `s:num`; `P:num`; `r:num`] NV_DIG_Q0) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[LT_NZ]; MESON_TAC[NV_DIG_FIN_DIG_CG_ZP]];
    MP_TAC(SPECL [`p:num`; `s:num`; `P:num`; `r:num`] NV_DIG_HD) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[NOT_EVEN]; MESON_TAC[NV_DIG_FIN_DIG_UNIT_ZP]]]);;
