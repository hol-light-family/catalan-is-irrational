(* rp_hol_gla_: general lemmas (segment Cauchy integrals, primitives, triangle) *)
needs "src/catalan_rp_hol_base.ml";;

let RP_HOL_GLA_DIV_CONT = prove
 (`forall f:complex->complex p q z.
     f continuous_on segment[p,q] /\ ~(z IN segment[p,q])
     ==> (\w. f w / (w - z)) continuous_on segment[p,q]`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CONTINUOUS_ON_COMPLEX_DIV THEN
  ASM_SIMP_TAC[CONTINUOUS_ON_SUB; CONTINUOUS_ON_ID; CONTINUOUS_ON_CONST] THEN
  REWRITE_TAC[COMPLEX_SUB_0] THEN ASM_MESON_TAC[]);;

let RP_HOL_GLA_CINT_DIFF = prove
 (`forall f:complex->complex p q z.
     f continuous_on segment[p,q] /\ ~(z IN segment[p,q])
     ==> (\z. rp_hol_cint f z p q) complex_differentiable at z`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`f:complex->complex`; `\w. rp_hol_cint f w p q`;
                 `linepath(p:complex,q)`; `(:complex)`; `1`;
                 `norm(q - p:complex)`] CAUCHY_NEXT_DERIVATIVE) THEN
  REWRITE_TAC[ARITH_EQ; OPEN_UNIV; VALID_PATH_LINEPATH;
              VECTOR_DERIVATIVE_LINEPATH_AT; REAL_LE_REFL; PATH_IMAGE_LINEPATH;
              IN_DIFF; IN_UNIV; COMPLEX_POW_1] THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[rp_hol_cint] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC HAS_PATH_INTEGRAL_INTEGRAL THEN
    MATCH_MP_TAC PATH_INTEGRABLE_CONTINUOUS_LINEPATH THEN
    MATCH_MP_TAC RP_HOL_GLA_DIV_CONT THEN ASM_REWRITE_TAC[];
    DISCH_THEN(MP_TAC o SPEC `z:complex`) THEN
    ASM_REWRITE_TAC[complex_differentiable] THEN MESON_TAC[]]);;

let RP_HOL_GLA_CINT_REV = prove
 (`forall f:complex->complex p q z.
     f continuous_on segment[p,q] /\ ~(z IN segment[p,q])
     ==> rp_hol_cint f z p q = --(rp_hol_cint f z q p)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[rp_hol_cint] THEN
  MATCH_MP_TAC PATH_INTEGRAL_REVERSE_LINEPATH THEN
  MATCH_MP_TAC RP_HOL_GLA_DIV_CONT THEN ASM_REWRITE_TAC[]);;

let RP_HOL_GLA_PRIM = prove
 (`forall g:complex->complex s.
     convex s /\ open s /\ g holomorphic_on s
     ==> exists Phi. forall p q. p IN s /\ q IN s
                     ==> path_integral (linepath(p,q)) g = Phi q - Phi p`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`g:complex->complex`; `s:complex->bool`; `{}:complex->bool`]
    HOLOMORPHIC_CONVEX_PRIMITIVE) THEN
  ASM_SIMP_TAC[FINITE_EMPTY; DIFF_EMPTY; INTERIOR_OPEN;
               HOLOMORPHIC_ON_IMP_CONTINUOUS_ON] THEN
  ANTS_TAC THENL [ASM_MESON_TAC[HOLOMORPHIC_ON_IMP_DIFFERENTIABLE_AT];
                  ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `Phi:complex->complex`) THEN
  EXISTS_TAC `Phi:complex->complex` THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC PATH_INTEGRAL_UNIQUE THEN
  MP_TAC(ISPECL [`Phi:complex->complex`; `g:complex->complex`;
                 `linepath(p:complex,q)`; `s:complex->bool`]
    PATH_INTEGRAL_PRIMITIVE) THEN
  REWRITE_TAC[PATHSTART_LINEPATH; PATHFINISH_LINEPATH; VALID_PATH_LINEPATH;
              PATH_IMAGE_LINEPATH] THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[CONVEX_CONTAINS_SEGMENT]);;

let RP_HOL_GLA_CINT_HAS = prove
 (`forall f:complex->complex p q z.
     f continuous_on segment[p,q] /\ ~(z IN segment[p,q])
     ==> ((\w. f w / (w - z)) has_path_integral rp_hol_cint f z p q)
         (linepath(p,q))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[rp_hol_cint] THEN
  MATCH_MP_TAC HAS_PATH_INTEGRAL_INTEGRAL THEN
  MATCH_MP_TAC PATH_INTEGRABLE_CONTINUOUS_LINEPATH THEN
  MATCH_MP_TAC RP_HOL_GLA_DIV_CONT THEN ASM_REWRITE_TAC[]);;

let RP_HOL_GLA_TRI = prove
 (`forall f:complex->complex s a b c z.
     convex s /\ open s /\ f holomorphic_on s /\
     a IN s /\ b IN s /\ c IN s /\
     z IN interior(convex hull {a,b,c}) /\
     ~(z IN segment[a,b]) /\ ~(z IN segment[b,c]) /\ ~(z IN segment[c,a])
     ==> rp_hol_cint f z a b + rp_hol_cint f z b c + rp_hol_cint f z c a =
         Cx(&2) * Cx pi * ii *
         (if &0 < Im((b - a) * cnj (b - z)) then Cx(&1) else --Cx(&1)) * f z`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `convex hull {a:complex,b,c} SUBSET s` ASSUME_TAC THENL
   [MATCH_MP_TAC HULL_MINIMAL THEN
    ASM_REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `(z:complex) IN s` ASSUME_TAC THENL
   [ASM_MESON_TAC[INTERIOR_SUBSET; SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `segment[a:complex,b] SUBSET s /\ segment[b,c] SUBSET s /\
                segment[c,a] SUBSET s` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[CONVEX_CONTAINS_SEGMENT]; ALL_TAC] THEN
  SUBGOAL_THEN `(f:complex->complex) continuous_on segment[a,b] /\
                f continuous_on segment[b,c] /\ f continuous_on segment[c,a]`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[HOLOMORPHIC_ON_IMP_CONTINUOUS_ON; CONTINUOUS_ON_SUBSET];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`f:complex->complex`; `s:complex->bool`;
                 `linepath(a:complex,b) ++ linepath(b,c) ++ linepath(c,a)`;
                 `z:complex`] CAUCHY_INTEGRAL_FORMULA_CONVEX_SIMPLE) THEN
  ASM_SIMP_TAC[INTERIOR_OPEN; VALID_PATH_JOIN; VALID_PATH_LINEPATH;
               PATHSTART_JOIN; PATHFINISH_JOIN; PATHSTART_LINEPATH;
               PATHFINISH_LINEPATH; PATH_IMAGE_JOIN; PATH_IMAGE_LINEPATH;
               UNION_SUBSET; SUBSET_DELETE; WINDING_NUMBER_TRIANGLE] THEN
  ASM_REWRITE_TAC[IN_UNION] THEN DISCH_TAC THEN MATCH_MP_TAC HAS_PATH_INTEGRAL_UNIQUE THEN
  EXISTS_TAC `\w:complex. f w / (w - z)` THEN
  EXISTS_TAC `linepath(a:complex,b) ++ linepath(b,c) ++ linepath(c,a)` THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC HAS_PATH_INTEGRAL_JOIN THEN
  ASM_SIMP_TAC[VALID_PATH_JOIN; VALID_PATH_LINEPATH;
               PATHSTART_JOIN; PATHFINISH_JOIN; PATHSTART_LINEPATH;
               PATHFINISH_LINEPATH; RP_HOL_GLA_CINT_HAS] THEN
  MATCH_MP_TAC HAS_PATH_INTEGRAL_JOIN THEN
  ASM_SIMP_TAC[VALID_PATH_LINEPATH; RP_HOL_GLA_CINT_HAS]);;

let RP_HOL_GLA_HALFPLANE = prove
 (`forall a b c. convex {w | a * Re w + b * Im w < c} /\
           open {w | a * Re w + b * Im w < c}`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `{w | a * Re w + b * Im w < c} = {w | complex(a,b) dot w < c}`
   SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; DOT_2; GSYM RE_DEF; GSYM IM_DEF;
                RE; IM];
    REWRITE_TAC[CONVEX_HALFSPACE_LT; OPEN_HALFSPACE_LT]]);;

let RP_HOL_GLA_MINMAX = prove
 (`forall a b u. &0 <= u /\ u <= &1
           ==> min a b <= (&1 - u) * a + u * b /\
               (&1 - u) * a + u * b <= max a b`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  DISJ_CASES_TAC(REAL_ARITH `a <= b \/ b <= a`) THENL
   [MP_TAC(ISPECL [`u:real`; `b - a:real`] REAL_LE_MUL) THEN
    MP_TAC(ISPECL [`&1 - u:real`; `b - a:real`] REAL_LE_MUL);
    MP_TAC(ISPECL [`u:real`; `a - b:real`] REAL_LE_MUL) THEN
    MP_TAC(ISPECL [`&1 - u:real`; `a - b:real`] REAL_LE_MUL)] THEN
  ASM_REAL_ARITH_TAC);;

let RP_HOL_GLA_SEGBOX = prove
 (`forall p q w. w IN segment[p,q]
           ==> min (Re p) (Re q) <= Re w /\ Re w <= max (Re p) (Re q) /\
               min (Im p) (Im q) <= Im w /\ Im w <= max (Im p) (Im q)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IN_SEGMENT] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[RE_ADD; IM_ADD; RE_CMUL; IM_CMUL] THEN
  ASM_SIMP_TAC[RP_HOL_GLA_MINMAX]);;

let RP_HOL_GLA_INV_N = prove
 (`forall n. 48 <= n ==> &0 < inv(&n) /\ inv(&n) <= &1 / &48 /\
                   &2 / &n = &2 * inv(&n)`,
  GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[real_div] THEN
  SUBGOAL_THEN `&48 <= &n` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[REAL_OF_NUM_LE]; ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LT_INV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[REAL_MUL_LID] THEN MATCH_MP_TAC REAL_LE_INV2 THEN
  ASM_REAL_ARITH_TAC);;

let RP_HOL_GLA_CONTOUR = prove
 (`forall n d s k w.
     48 <= n /\ &0 < d /\ &2 * d <= inv(&n) /\ (s = &1 \/ s = --(&1)) /\
     k <= 6 /\ w IN segment[rp_hol_v n d s k, rp_hol_v n d s (k + 1)]
     ==> (s * Re w <= --d \/ abs(Im w) = &1 + &2 / &n) /\
         (~(Im w = &0) \/ abs(Re w) = d)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o MATCH_MP (ARITH_RULE
   `k <= 6 ==> k = 0 \/ k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6`)) THEN
  REPEAT(FIRST_X_ASSUM SUBST_ALL_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP RP_HOL_GLA_SEGBOX) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP RP_HOL_GLA_INV_N) THEN
  ASM_REWRITE_TAC[rp_hol_v] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[RE; IM] THEN
  POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
  SPEC_TAC(`inv(&n)`,`e:real`) THEN REAL_ARITH_TAC);;

let RP_HOL_GLA_C_EXPAND = prove
 (`forall n d s f z.
     rp_hol_C n d s f z =
     rp_hol_cint f z (rp_hol_v n d s 0) (rp_hol_v n d s 1) +
     rp_hol_cint f z (rp_hol_v n d s 1) (rp_hol_v n d s 2) +
     rp_hol_cint f z (rp_hol_v n d s 2) (rp_hol_v n d s 3) +
     rp_hol_cint f z (rp_hol_v n d s 3) (rp_hol_v n d s 4) +
     rp_hol_cint f z (rp_hol_v n d s 4) (rp_hol_v n d s 5) +
     rp_hol_cint f z (rp_hol_v n d s 5) (rp_hol_v n d s 6) +
     rp_hol_cint f z (rp_hol_v n d s 6) (rp_hol_v n d s 7)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[rp_hol_C] THEN
  CONV_TAC(ONCE_DEPTH_CONV EXPAND_VSUM_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV);;

let RP_HOL_GLA_C_DIFF = prove
 (`forall n d s f z.
     (forall k. k <= 6
          ==> f continuous_on
                segment[rp_hol_v n d s k, rp_hol_v n d s (k + 1)] /\
              ~(z IN segment[rp_hol_v n d s k, rp_hol_v n d s (k + 1)]))
     ==> rp_hol_C n d s f complex_differentiable at z`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> MAP_EVERY (fun k ->
    STRIP_ASSUME_TAC(REWRITE_RULE[] (CONV_RULE NUM_REDUCE_CONV
       (SPEC (mk_small_numeral k) th)))) (0--6)) THEN
  SUBGOAL_THEN `rp_hol_C n d s f =
     \z. rp_hol_cint f z (rp_hol_v n d s 0) (rp_hol_v n d s 1) +
     rp_hol_cint f z (rp_hol_v n d s 1) (rp_hol_v n d s 2) +
     rp_hol_cint f z (rp_hol_v n d s 2) (rp_hol_v n d s 3) +
     rp_hol_cint f z (rp_hol_v n d s 3) (rp_hol_v n d s 4) +
     rp_hol_cint f z (rp_hol_v n d s 4) (rp_hol_v n d s 5) +
     rp_hol_cint f z (rp_hol_v n d s 5) (rp_hol_v n d s 6) +
     rp_hol_cint f z (rp_hol_v n d s 6) (rp_hol_v n d s 7)`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; RP_HOL_GLA_C_EXPAND]; ALL_TAC] THEN
  REPEAT(MATCH_MP_TAC COMPLEX_DIFFERENTIABLE_ADD THEN CONJ_TAC) THEN
  MATCH_MP_TAC RP_HOL_GLA_CINT_DIFF THEN ASM_REWRITE_TAC[]);;

let RP_HOL_GLA_G_DIFF0 = prove
 (`forall n D d s B f z.
     B complex_differentiable at z /\
     rp_hol_C n d s f complex_differentiable at z
     ==> rp_hol_G n D d s B f complex_differentiable at z`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `rp_hol_G n D d s B f =
     \z. Cx(if s = &1 then --(&5) else &1) * z pow D -
         B z * (Cx(&6) / (Cx(&2) * Cx pi * ii) * rp_hol_C n d s f z)`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; rp_hol_G]; ALL_TAC] THEN
  MATCH_MP_TAC COMPLEX_DIFFERENTIABLE_SUB THEN CONJ_TAC THENL
   [MATCH_MP_TAC COMPLEX_DIFFERENTIABLE_MUL_AT THEN
    REWRITE_TAC[COMPLEX_DIFFERENTIABLE_CONST] THEN
    MATCH_MP_TAC COMPLEX_DIFFERENTIABLE_POW_AT THEN
    REWRITE_TAC[COMPLEX_DIFFERENTIABLE_ID];
    MATCH_MP_TAC COMPLEX_DIFFERENTIABLE_MUL_AT THEN
    ASM_REWRITE_TAC[ETA_AX] THEN
    MATCH_MP_TAC COMPLEX_DIFFERENTIABLE_MUL_AT THEN
    ASM_REWRITE_TAC[ETA_AX; COMPLEX_DIFFERENTIABLE_CONST]]);;

let RP_HOL_GLA_G_DIFF = prove
 (`forall n D d s B f z.
     48 <= n /\ &0 < d /\ &2 * d <= inv(&n) /\ (s = &1 \/ s = --(&1)) /\
     (forall w. ~(Im w = &0) \/ abs(Re w) < &2 * d
          ==> f complex_differentiable at w) /\
     B complex_differentiable at z /\
     norm z < &1 + &2 / &n /\ --d < s * Re z
     ==> rp_hol_G n D d s B f complex_differentiable at z`,
  REPEAT GEN_TAC THEN INTRO_TAC "n d dn s f B z1 z2" THEN
  MATCH_MP_TAC RP_HOL_GLA_G_DIFF0 THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC RP_HOL_GLA_C_DIFF THEN X_GEN_TAC `k:num` THEN DISCH_TAC THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_AT_IMP_CONTINUOUS_ON THEN
    X_GEN_TAC `w:complex` THEN DISCH_TAC THEN
    MATCH_MP_TAC COMPLEX_DIFFERENTIABLE_IMP_CONTINUOUS_AT THEN
    REMOVE_THEN "f" MATCH_MP_TAC THEN
    MP_TAC(SPECL [`n:num`; `d:real`; `s:real`; `k:num`; `w:complex`]
      RP_HOL_GLA_CONTOUR) THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    DISCH_TAC THEN
    MP_TAC(SPECL [`n:num`; `d:real`; `s:real`; `k:num`; `z:complex`]
      RP_HOL_GLA_CONTOUR) THEN
    MP_TAC(SPEC `z:complex` COMPLEX_NORM_GE_RE_IM) THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]);;

let RP_HOL_GLA_HOL_FROM_DIFF = prove
 (`forall f:complex->complex s.
     (forall w. w IN s ==> f complex_differentiable at w) ==> f holomorphic_on s`,
  REWRITE_TAC[HOLOMORPHIC_ON_DIFFERENTIABLE] THEN
  MESON_TAC[COMPLEX_DIFFERENTIABLE_AT_WITHIN]);;

let RP_HOL_GLA_PRIM_CINT = prove
 (`forall f:complex->complex z s.
     convex s /\ open s /\ (forall w. w IN s ==> f complex_differentiable at w) /\
     ~(z IN s)
     ==> exists Phi. forall p q. p IN s /\ q IN s
                     ==> rp_hol_cint f z p q = Phi q - Phi p`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[rp_hol_cint] THEN
  MATCH_MP_TAC RP_HOL_GLA_PRIM THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC RP_HOL_GLA_HOL_FROM_DIFF THEN
  X_GEN_TAC `w:complex` THEN DISCH_TAC THEN
  MATCH_MP_TAC COMPLEX_DIFFERENTIABLE_DIV_AT THEN
  ASM_SIMP_TAC[ETA_AX] THEN CONJ_TAC THENL
   [MATCH_MP_TAC COMPLEX_DIFFERENTIABLE_SUB THEN
    REWRITE_TAC[COMPLEX_DIFFERENTIABLE_ID; COMPLEX_DIFFERENTIABLE_CONST];
    REWRITE_TAC[COMPLEX_SUB_0] THEN ASM_MESON_TAC[]]);;

let RP_HOL_GLA_INT_TRI = prove
 (`forall d rho z.
     &0 < d /\ &0 < rho /\ --d < Re z /\ abs(Im z) < rho /\
     &0 < d * Im z - rho * Re z
     ==> z IN interior(convex hull {complex(--d,--rho), complex(--d,rho),
                                    complex(d,rho)})`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < d * rho` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_MUL]; ALL_TAC] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) INTERIOR_CONVEX_HULL_3_MINIMAL o
    rand o snd) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[COLLINEAR_3_2D; GSYM RE_DEF; GSYM IM_DEF; RE; IM] THEN
    ASM_REAL_ARITH_TAC;
    DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[IN_ELIM_THM] THEN
  EXISTS_TAC `(rho - Im z) / (&2 * rho)` THEN
  EXISTS_TAC `(d * Im z - rho * Re z) / (&2 * d * rho)` THEN
  EXISTS_TAC `(d + Re z) / (&2 * d)` THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC;
    UNDISCH_TAC `&0 < d` THEN UNDISCH_TAC `&0 < rho` THEN
    CONV_TAC REAL_FIELD;
    REWRITE_TAC[COMPLEX_EQ; RE_ADD; RE_CMUL; IM_ADD; IM_CMUL; RE; IM] THEN
    UNDISCH_TAC `&0 < d` THEN UNDISCH_TAC `&0 < rho` THEN
    CONV_TAC REAL_FIELD]);;

let rp_hol_gla_mem_tac =
  ASM_REWRITE_TAC[IN_ELIM_THM; IN_INTER; RE; IM] THEN ASM_REAL_ARITH_TAC;;

let rp_hol_gla_convex_tac =
  REPEAT((MATCH_MP_TAC CONVEX_INTER ORELSE MATCH_MP_TAC OPEN_INTER) THEN
         CONJ_TAC) THEN
  REWRITE_TAC[RP_HOL_GLA_HALFPLANE];;

let rp_hol_gla_inst lbl (p,q) =
  USE_THEN lbl (fun th -> MP_TAC(SPECL [p;q] th)) THEN
  ANTS_TAC THENL [rp_hol_gla_mem_tac; ALL_TAC];;

let RP_HOL_GLA_DIFF_ABS = prove
 (`forall e rho R d (f:complex->complex) z a0 a1 a2 a3 a4 a5 a6 a7 b1 b2 b3 b4 b5 b6.
   &0 < d /\ &2 * d <= e /\ e <= &1 / &48 /\ rho + e = &1 /\
   R - &2 * e = &1 /\
   a0 = complex(&0,--R) /\ a1 = complex(--e,--R) /\ a2 = complex(--e,--rho) /\
   a3 = complex(--d,--rho) /\ a4 = complex(--d,rho) /\ a5 = complex(--e,rho) /\
   a6 = complex(--e,R) /\ a7 = complex(&0,R) /\
   b1 = complex(e,--R) /\ b2 = complex(e,--rho) /\ b3 = complex(d,--rho) /\
   b4 = complex(d,rho) /\ b5 = complex(e,rho) /\ b6 = complex(e,R) /\
   (forall w. ~(Im w = &0) \/ abs(Re w) < &2 * d ==> f complex_differentiable at w) /\
   abs(Re z + d / &2) < d / &8 /\ abs(Im z) < d / &8
   ==> (rp_hol_cint f z a0 a1 + rp_hol_cint f z a1 a2 + rp_hol_cint f z a2 a3 +
        rp_hol_cint f z a3 a4 + rp_hol_cint f z a4 a5 + rp_hol_cint f z a5 a6 +
        rp_hol_cint f z a6 a7) -
       (rp_hol_cint f z a0 b1 + rp_hol_cint f z b1 b2 + rp_hol_cint f z b2 b3 +
        rp_hol_cint f z b3 b4 + rp_hol_cint f z b4 b5 + rp_hol_cint f z b5 b6 +
        rp_hol_cint f z b6 a7) =
       --(Cx(&2) * Cx pi * ii * f z)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < rho` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < d * rho` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_MUL]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < rho * (Re z + d)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `d * rho / &4 < (--rho) * Re z + d * Im z` ASSUME_TAC THENL
   [SUBGOAL_THEN `rho * Re z < rho * --(&3 * d / &8)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LT_LMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `d * --(d / &8) < d * Im z` MP_TAC THENL
     [MATCH_MP_TAC REAL_LT_LMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&0 < d * (rho - d)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REAL_ARITH_TAC; ALL_TAC] THEN
  (* bottom region *)
  MP_TAC(ISPECL [`f:complex->complex`; `z:complex`;
                 `{w | &0 * Re w + &1 * Im w < --(&1 / &2)}`]
         RP_HOL_GLA_PRIM_CINT) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[RP_HOL_GLA_HALFPLANE; IN_ELIM_THM] THEN CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    DISCH_THEN(X_CHOOSE_THEN `Pb:complex->complex` (LABEL_TAC "pb"))] THEN
  (* top region *)
  MP_TAC(ISPECL [`f:complex->complex`; `z:complex`;
                 `{w | &0 * Re w + --(&1) * Im w < --(&1 / &2)}`]
         RP_HOL_GLA_PRIM_CINT) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[RP_HOL_GLA_HALFPLANE; IN_ELIM_THM] THEN CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    DISCH_THEN(X_CHOOSE_THEN `Pt:complex->complex` (LABEL_TAC "pt"))] THEN
  (* lower right triangle region *)
  MP_TAC(ISPECL [`f:complex->complex`; `z:complex`;
    `{w | &1 * Re w + &0 * Im w < &2 * d} INTER
     {w | --(&1) * Re w + &0 * Im w < &2 * d} INTER
     {w | &0 * Re w + &1 * Im w < &1} INTER
     {w | &0 * Re w + --(&1) * Im w < &1} INTER
     {w | (--rho) * Re w + d * Im w < d * rho / &4}`]
         RP_HOL_GLA_PRIM_CINT) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [rp_hol_gla_convex_tac; rp_hol_gla_convex_tac;
      REWRITE_TAC[IN_ELIM_THM; IN_INTER] THEN REPEAT STRIP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[IN_ELIM_THM; IN_INTER] THEN ASM_REAL_ARITH_TAC];
    DISCH_THEN(X_CHOOSE_THEN `P2:complex->complex` (LABEL_TAC "p2"))] THEN
  MAP_EVERY (rp_hol_gla_inst "pb")
   [`a0:complex`,`a1:complex`; `a1:complex`,`a2:complex`;
    `a2:complex`,`a3:complex`; `a0:complex`,`b1:complex`;
    `b1:complex`,`b2:complex`; `b2:complex`,`b3:complex`;
    `b3:complex`,`a3:complex`] THEN
  MAP_EVERY (rp_hol_gla_inst "pt")
   [`a4:complex`,`a5:complex`; `a5:complex`,`a6:complex`;
    `a6:complex`,`a7:complex`; `b4:complex`,`b5:complex`;
    `b5:complex`,`b6:complex`; `b6:complex`,`a7:complex`;
    `a4:complex`,`b4:complex`] THEN
  MAP_EVERY (rp_hol_gla_inst "p2")
   [`b3:complex`,`b4:complex`; `b3:complex`,`a3:complex`;
    `b4:complex`,`a3:complex`] THEN
  (* the triangle containing z *)
  MP_TAC(ISPECL [`f:complex->complex`;
    `{w | &1 * Re w + &0 * Im w < &2 * d} INTER
     {w | --(&1) * Re w + &0 * Im w < &2 * d} INTER
     {w | &0 * Re w + &1 * Im w < &1} INTER
     {w | &0 * Re w + --(&1) * Im w < &1}`;
    `a3:complex`; `a4:complex`; `b4:complex`; `z:complex`]
    RP_HOL_GLA_TRI) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [rp_hol_gla_convex_tac; rp_hol_gla_convex_tac;
      MATCH_MP_TAC RP_HOL_GLA_HOL_FROM_DIFF THEN
      REWRITE_TAC[IN_ELIM_THM; IN_INTER] THEN
      REPEAT STRIP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      rp_hol_gla_mem_tac;
      rp_hol_gla_mem_tac;
      rp_hol_gla_mem_tac;
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC RP_HOL_GLA_INT_TRI THEN
      ASM_REAL_ARITH_TAC;
      DISCH_THEN(MP_TAC o MATCH_MP RP_HOL_GLA_SEGBOX) THEN
      ASM_REWRITE_TAC[RE; IM] THEN ASM_REAL_ARITH_TAC;
      DISCH_THEN(MP_TAC o MATCH_MP RP_HOL_GLA_SEGBOX) THEN
      ASM_REWRITE_TAC[RE; IM] THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[IN_SEGMENT] THEN
      DISCH_THEN(X_CHOOSE_THEN `u:real` STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN `(--rho) * Re z + d * Im z = &0` MP_TAC THENL
       [ASM_REWRITE_TAC[RE_ADD; IM_ADD; RE_CMUL; IM_CMUL; RE; IM] THEN
        CONV_TAC REAL_RING;
        ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(&0 < Im((a4 - a3) * cnj(a4 - z)))`
   (fun th -> REWRITE_TAC[th]) THENL
   [ASM_REWRITE_TAC[complex_mul; RE_SUB; IM_SUB; RE_CNJ; IM_CNJ; RE; IM] THEN
    ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  CONV_TAC COMPLEX_RING);;

let RP_HOL_GLA_DIFF = prove
 (`forall n d (f:complex->complex) z.
     48 <= n /\ &0 < d /\ &2 * d <= inv(&n) /\
     (forall w. ~(Im w = &0) \/ abs(Re w) < &2 * d ==> f complex_differentiable at w) /\
     norm(z - Cx(--(d / &2))) < d / &8
     ==> rp_hol_C n d (&1) f z - rp_hol_C n d (--(&1)) f z =
         --(Cx(&2) * Cx pi * ii * f z)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP RP_HOL_GLA_INV_N) THEN
  MP_TAC(SPEC `z - Cx(--(d / &2))` COMPLEX_NORM_GE_RE_IM) THEN
  REWRITE_TAC[RE_SUB; IM_SUB; RE_CX; IM_CX] THEN DISCH_TAC THEN
  REWRITE_TAC[RP_HOL_GLA_C_EXPAND; rp_hol_v] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[REAL_MUL_LNEG; REAL_MUL_LID; REAL_NEG_NEG] THEN
  MATCH_MP_TAC RP_HOL_GLA_DIFF_ABS THEN
  MAP_EVERY EXISTS_TAC [`inv(&n)`; `&1 - inv(&n)`; `&1 + &2 / &n`; `d:real`] THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

let RP_HOL_GLA_NBHD = prove
 (`forall z r a s. norm z < r /\ a < s * Re z /\ (s = &1 \/ s = --(&1))
             ==> exists e. &0 < e /\
                     forall w. dist(w,z) < e ==> norm w < r /\ a < s * Re w`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  EXISTS_TAC `min (r - norm(z:complex)) (s * Re z - a)` THEN
  ASM_REWRITE_TAC[REAL_LT_MIN; REAL_SUB_LT; dist] THEN
  X_GEN_TAC `w:complex` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`w:complex`; `z:complex`] NORM_TRIANGLE_SUB) THEN
  MP_TAC(SPEC `w - z:complex` COMPLEX_NORM_GE_RE_IM) THEN
  REWRITE_TAC[RE_SUB] THEN ASM_REAL_ARITH_TAC);;
