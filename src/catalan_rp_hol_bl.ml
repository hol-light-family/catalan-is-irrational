(* ========================================================================= *)
(* rp_hol_bl_: conjunct 8 of RP_HOL_BL_STMT (bound on a thin strip around   *)
(* the imaginary axis, by uniform continuity) and the final theorem         *)
(*   RP_HOL_BL_THM : |- RP_HOL_BL_STMT                                       *)
(* Files: catalan_rp_hol_bl_a.ml (1-6), _b.ml (7), _c.ml (axis bound), this. *)
(* ========================================================================= *)

needs "src/catalan_rp_hol_bl_c.ml";;

let RP_HOL_BL_MINABS = prove
 (`forall n (x:num->real). (forall i. i < n ==> ~(x i = &0))
         ==> exists d. &0 < d /\ forall i. i < n ==> d < abs(x i)`,
  GEN_TAC THEN GEN_TAC THEN SPEC_TAC(`n:num`,`n:num`) THEN INDUCT_TAC THENL
   [DISCH_TAC THEN EXISTS_TAC `&1` THEN REWRITE_TAC[LT] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[ARITH_RULE `i < n ==> i < SUC n`]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `&0 < abs(x(n:num))` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_ABS_NZ] THEN ASM_MESON_TAC[ARITH_RULE `n < SUC n`];
    ALL_TAC] THEN
  EXISTS_TAC `min d (abs(x(n:num)) / &2)` THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `i:num` THEN REWRITE_TAC[LT] THEN STRIP_TAC THENL
   [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC(REAL_ARITH `d < a ==> min d b < a`) THEN ASM_SIMP_TAC[]]);;

let RP_HOL_BL_RE_IM = prove
 (`forall w. w - ii * Cx(Im w) = Cx(Re w)`,
  REWRITE_TAC[COMPLEX_EQ; RE_SUB; IM_SUB; RE_MUL_II; IM_MUL_II; RE_CX; IM_CX] THEN
  REAL_ARITH_TAC);;

let RP_HOL_BL_K_COMPACT = prove
 (`forall d0. compact {w | abs(Re w) <= d0 /\ abs(Im w) <= &1}`,
  GEN_TAC THEN REWRITE_TAC[COMPACT_EQ_BOUNDED_CLOSED] THEN CONJ_TAC THENL
   [MATCH_MP_TAC BOUNDED_SUBSET THEN
    EXISTS_TAC `cball(vec 0:complex, abs d0 + &1)` THEN
    REWRITE_TAC[BOUNDED_CBALL; SUBSET; IN_ELIM_THM; IN_CBALL; DIST_0] THEN
    X_GEN_TAC `w:complex` THEN STRIP_TAC THEN
    MP_TAC(SPEC `w:complex` COMPLEX_NORM_LE_RE_IM) THEN ASM_REAL_ARITH_TAC;
    SUBGOAL_THEN `{w | abs(Re w) <= d0 /\ abs(Im w) <= &1} =
                  {w | Re w <= d0} INTER {w | Re w >= --d0} INTER
                  {w | Im w <= &1} INTER {w | Im w >= --(&1)}`
    SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_INTER; IN_ELIM_THM] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    REPEAT(MATCH_MP_TAC CLOSED_INTER THEN CONJ_TAC) THEN
    REWRITE_TAC[CLOSED_HALFSPACE_RE_LE; CLOSED_HALFSPACE_RE_GE;
                CLOSED_HALFSPACE_IM_LE; CLOSED_HALFSPACE_IM_GE]]);;

let RP_HOL_BL_STRIP = prove
 (`forall n D (x:num->real). 48 <= n /\ D < n /\ rp_nodes n x /\
     sum {i | i < n} (\i. (&1 - x i pow 2) / (&1 + x i pow 2)) <= &D
     ==> exists d. &0 < d /\ &2 * d <= inv(&n) /\
             (forall i. i < n ==> &2 * d < abs(x i)) /\
             (forall w. abs(Re w) <= d /\ abs(Im w) <= &1 - inv(&n)
                  ==> norm(rp_hol_F n D x w) <= exp(&12))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[rp_nodes] THEN STRIP_TAC THEN
  SUBGOAL_THEN `forall i. i < n ==> ~((x:num->real) i = &0) /\ abs(x i) < &1`
  ASSUME_TAC THENL
   [ASM_MESON_TAC[REAL_ARITH `--(&1) < x /\ x < &1 ==> abs x < &1`];
    ALL_TAC] THEN
  ABBREV_TAC `S = sum {i | i < n} (\i. (&1 - (x:num->real) i pow 2) /
                                       (&1 + x i pow 2))` THEN
  SUBGOAL_THEN `&0 < S` ASSUME_TAC THENL
   [EXPAND_TAC "S" THEN MATCH_MP_TAC SUM_POS_LT THEN
    REWRITE_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM] THEN
    SUBGOAL_THEN `forall i. i < n ==> &0 < (&1 - (x:num->real) i pow 2) /
                                     (&1 + x i pow 2)` ASSUME_TAC THENL
     [X_GEN_TAC `i:num` THEN DISCH_TAC THEN MATCH_MP_TAC REAL_LT_DIV THEN
      MP_TAC(SPEC `(x:num->real) i` REAL_LE_POW_2) THEN
      SUBGOAL_THEN `(x:num->real) i pow 2 < &1` MP_TAC THENL
       [ONCE_REWRITE_TAC[GSYM REAL_POW2_ABS] THEN
        GEN_REWRITE_TAC RAND_CONV [GSYM(SPEC `2` REAL_POW_ONE)] THEN
        MATCH_MP_TAC REAL_POW_LT2 THEN ASM_SIMP_TAC[REAL_ABS_POS] THEN
        ARITH_TAC;
        REAL_ARITH_TAC];
      ALL_TAC] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
    EXISTS_TAC `0` THEN ASM_SIMP_TAC[ARITH_RULE `48 <= n ==> 0 < n`];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(D = 0)` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `S <= &D` THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`n:num`; `x:num->real`] RP_HOL_BL_MINABS) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d0:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`rp_hol_F n D x`;
                 `{w | abs(Re w) <= d0 /\ abs(Im w) <= &1}`]
         COMPACT_UNIFORMLY_CONTINUOUS) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[RP_HOL_BL_K_COMPACT] THEN
    MATCH_MP_TAC CONTINUOUS_AT_IMP_CONTINUOUS_ON THEN
    X_GEN_TAC `w:complex` THEN REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
    MATCH_MP_TAC COMPLEX_DIFFERENTIABLE_IMP_CONTINUOUS_AT THEN
    MATCH_MP_TAC RP_HOL_BL_FDIFF THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC `abs(Re(Cx((x:num->real) i))) <= d0` THEN
    REWRITE_TAC[RE_CX; REAL_NOT_LE] THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[uniformly_continuous_on] THEN
  DISCH_THEN(MP_TAC o SPEC `&1`) THEN REWRITE_TAC[REAL_LT_01] THEN
  DISCH_THEN(X_CHOOSE_THEN `d1:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `&0 < inv(&n)` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_LT_INV_EQ; REAL_OF_NUM_LT] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  EXISTS_TAC `min (d1 / &2) (min (d0 / &2) (inv(&n) / &2))` THEN
  REPEAT CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC;
    REAL_ARITH_TAC;
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN ASM_REWRITE_TAC[] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  X_GEN_TAC `w:complex` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`ii * Cx(Im w)`; `w:complex`]) THEN
  REWRITE_TAC[IN_ELIM_THM; RE_MUL_II; IM_MUL_II; RE_CX; IM_CX; dist;
              RP_HOL_BL_RE_IM; COMPLEX_NORM_CX] THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`n:num`; `D:num`; `x:num->real`; `Im w`] RP_HOL_BL_AXIS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL [`rp_hol_F n D x w`; `rp_hol_F n D x (ii * Cx(Im w))`]
         NORM_TRIANGLE_SUB) THEN
  MP_TAC(SPEC `&12` REAL_EXP_LE_X) THEN ASM_REAL_ARITH_TAC);;

let RP_HOL_BL_THM = prove
 (`RP_HOL_BL_STMT`,
  REWRITE_TAC[RP_HOL_BL_STMT] THEN REPEAT CONJ_TAC THEN
  FIRST(map MATCH_ACCEPT_TAC
   [RP_HOL_BL_FDIFF; RP_HOL_BL_BDIFF; RP_HOL_BL_BF; RP_HOL_BL_BZERO;
    RP_HOL_BL_BNORM; RP_HOL_BL_RADIUS; RP_HOL_BL_NEAR_I; RP_HOL_BL_STRIP]));;
