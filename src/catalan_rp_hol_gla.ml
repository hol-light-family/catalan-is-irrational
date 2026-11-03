(* ========================================================================= *)
(* rp_hol_gla_: holomorphic gluing of the two local formulas and            *)
(* interpolation at the nodes:  RP_HOL_GLA_THM : |- RP_HOL_GLA_STMT.         *)
(* ========================================================================= *)

needs "src/catalan_rp_hol_base.ml";;
needs "src/catalan_rp_hol_gla_a.ml";;

let RP_HOL_GLA_THM = prove
 (`RP_HOL_GLA_STMT`,
  REWRITE_TAC[RP_HOL_GLA_STMT] THEN REPEAT GEN_TAC THEN
  INTRO_TAC "n nodes r d dn xd Bd fd Bf B0" THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP RP_HOL_GLA_INV_N) THEN
  SUBGOAL_THEN
   `forall w. ~(Im w = &0) \/ abs(Re w) < &2 * d ==> f complex_differentiable at w`
   (LABEL_TAC "fd2") THENL
   [X_GEN_TAC `w:complex` THEN DISCH_TAC THEN USE_THEN "fd" MATCH_MP_TAC THEN
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN DISCH_THEN SUBST_ALL_TAC THEN
    USE_THEN "xd" (fun th -> MP_TAC(MP (SPEC `i:num` th) (ASSUME `(i:num) < n`))) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[RE_CX; IM_CX]) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `q = min r (&1 + inv(&n))` THEN
  SUBGOAL_THEN `&1 < q /\ q <= r /\ q < &1 + &2 / &n` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "q" THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `forall z. norm z < q /\ --d < Re z
                    ==> rp_hol_G n D d (&1) B f complex_differentiable at z`
   (LABEL_TAC "g1d") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC RP_HOL_GLA_G_DIFF THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
    TRY(FIRST_ASSUM ACCEPT_TAC) THEN TRY(USE_THEN "Bd" MATCH_MP_TAC) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `forall z. norm z < q /\ Re z < d
                    ==> rp_hol_G n D d (--(&1)) B f complex_differentiable at z`
   (LABEL_TAC "g2d") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC RP_HOL_GLA_G_DIFF THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
    TRY(FIRST_ASSUM ACCEPT_TAC) THEN TRY(USE_THEN "Bd" MATCH_MP_TAC) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* identity theorem on the strip *)
  SUBGOAL_THEN `forall z. norm z < q /\ abs(Re z) < d
                    ==> rp_hol_G n D d (&1) B f z =
                        rp_hol_G n D d (--(&1)) B f z`
   (LABEL_TAC "eqw") THENL
   [MP_TAC(ISPECL
     [`\z. rp_hol_G n D d (&1) B f z - rp_hol_G n D d (--(&1)) B f z`;
      `ball(Cx(&0),q) INTER {w | &1 * Re w + &0 * Im w < d} INTER
       {w | --(&1) * Re w + &0 * Im w < d}`;
      `ball(Cx(--(d / &2)),d / &8)`; `Cx(--(d / &2))`]
     ANALYTIC_CONTINUATION) THEN
    REWRITE_TAC[COMPLEX_SUB_0] THEN ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL
       [REPEAT(MATCH_MP_TAC OPEN_INTER THEN CONJ_TAC) THEN
        REWRITE_TAC[OPEN_BALL; RP_HOL_GLA_HALFPLANE];
        MATCH_MP_TAC CONVEX_CONNECTED THEN
        REPEAT(MATCH_MP_TAC CONVEX_INTER THEN CONJ_TAC) THEN
        REWRITE_TAC[CONVEX_BALL; RP_HOL_GLA_HALFPLANE];
        MATCH_MP_TAC RP_HOL_GLA_HOL_FROM_DIFF THEN
        REWRITE_TAC[IN_INTER; IN_ELIM_THM; GSYM COMPLEX_VEC_0; IN_BALL_0] THEN
        X_GEN_TAC `w:complex` THEN STRIP_TAC THEN
        MATCH_MP_TAC COMPLEX_DIFFERENTIABLE_SUB THEN REWRITE_TAC[ETA_AX] THEN
        CONJ_TAC THENL
         [USE_THEN "g1d" MATCH_MP_TAC; USE_THEN "g2d" MATCH_MP_TAC] THEN
        ASM_REAL_ARITH_TAC;
        REWRITE_TAC[SUBSET; IN_INTER; IN_ELIM_THM; GSYM COMPLEX_VEC_0;
                    IN_BALL_0] THEN
        X_GEN_TAC `w:complex` THEN REWRITE_TAC[IN_BALL; dist] THEN
        ONCE_REWRITE_TAC[NORM_SUB] THEN DISCH_TAC THEN
        MP_TAC(ISPECL [`w:complex`; `Cx(--(d / &2))`] NORM_TRIANGLE_SUB) THEN
        MP_TAC(SPEC `w - Cx(--(d / &2))` COMPLEX_NORM_GE_RE_IM) THEN
        REWRITE_TAC[RE_SUB; RE_CX; COMPLEX_NORM_CX] THEN ASM_REAL_ARITH_TAC;
        REWRITE_TAC[IN_INTER; IN_ELIM_THM; GSYM COMPLEX_VEC_0; IN_BALL_0;
                    COMPLEX_NORM_CX; RE_CX; IM_CX] THEN
        ASM_REAL_ARITH_TAC;
        REWRITE_TAC[LIMPT_BALL; CENTRE_IN_CBALL] THEN ASM_REAL_ARITH_TAC;
        X_GEN_TAC `w:complex` THEN REWRITE_TAC[IN_BALL; dist] THEN
        ONCE_REWRITE_TAC[NORM_SUB] THEN DISCH_TAC THEN
        MP_TAC(SPECL [`n:num`; `d:real`; `f:complex->complex`; `w:complex`]
          RP_HOL_GLA_DIFF) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
        MP_TAC(ISPECL [`w:complex`; `Cx(--(d / &2))`] NORM_TRIANGLE_SUB) THEN
        MP_TAC(SPEC `w - Cx(--(d / &2))` COMPLEX_NORM_GE_RE_IM) THEN
        REWRITE_TAC[RE_SUB; RE_CX; COMPLEX_NORM_CX] THEN
        REPEAT DISCH_TAC THEN
        USE_THEN "Bf" (MP_TAC o SPEC `w:complex`) THEN ANTS_TAC THENL
         [CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
          X_GEN_TAC `i:num` THEN DISCH_TAC THEN DISCH_THEN SUBST_ALL_TAC THEN
          USE_THEN "xd"
           (fun th -> MP_TAC(MP (SPEC `i:num` th) (ASSUME `(i:num) < n`))) THEN
          RULE_ASSUM_TAC(REWRITE_RULE[RE_CX; IM_CX]) THEN ASM_REAL_ARITH_TAC;
          ALL_TAC] THEN
        UNDISCH_TAC
         `rp_hol_C n d (&1) f w - rp_hol_C n d (--(&1)) f w =
          --(Cx(&2) * Cx pi * ii * f w)` THEN
        REWRITE_TAC[rp_hol_G; REAL_ARITH `~(--(&1) = &1)`; CX_NEG] THEN
        MP_TAC PI_NZ THEN REWRITE_TAC[GSYM CX_INJ] THEN
        MP_TAC II_NZ THEN CONV_TAC COMPLEX_FIELD];
      DISCH_TAC THEN X_GEN_TAC `z:complex` THEN STRIP_TAC THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN
      REWRITE_TAC[IN_INTER; IN_ELIM_THM; GSYM COMPLEX_VEC_0; IN_BALL_0] THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `forall z. norm z < q /\ --d < Re z
                    ==> rp_hol_h n D d B f z = rp_hol_G n D d (&1) B f z`
   (LABEL_TAC "h1") THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[rp_hol_h] THEN
    COND_CASES_TAC THEN REWRITE_TAC[] THEN CONV_TAC SYM_CONV THEN
    USE_THEN "eqw" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `forall z. norm z < q /\ Re z < d
                    ==> rp_hol_h n D d B f z = rp_hol_G n D d (--(&1)) B f z`
   (LABEL_TAC "h2") THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[rp_hol_h] THEN
    COND_CASES_TAC THEN REWRITE_TAC[] THEN
    USE_THEN "eqw" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  EXISTS_TAC `q:real` THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC RP_HOL_GLA_HOL_FROM_DIFF THEN
    REWRITE_TAC[GSYM COMPLEX_VEC_0; IN_BALL_0] THEN
    X_GEN_TAC `z:complex` THEN DISCH_TAC THEN
    ASM_CASES_TAC `--d < Re z` THENL
     [MP_TAC(SPECL [`z:complex`; `q:real`; `--(d:real)`; `&1:real`] RP_HOL_GLA_NBHD) THEN
      ASM_REWRITE_TAC[REAL_MUL_LID] THEN
      DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
      MATCH_MP_TAC COMPLEX_DIFFERENTIABLE_TRANSFORM_AT THEN
      MAP_EVERY EXISTS_TAC [`rp_hol_G n D d (&1) B f`; `e:real`] THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [X_GEN_TAC `w:complex` THEN DISCH_TAC THEN CONV_TAC SYM_CONV THEN
        USE_THEN "h1" MATCH_MP_TAC THEN ASM_MESON_TAC[];
        USE_THEN "g1d" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
      MP_TAC(SPECL [`z:complex`; `q:real`; `--(d:real)`; `--(&1):real`]
        RP_HOL_GLA_NBHD) THEN
      REWRITE_TAC[REAL_MUL_LNEG; REAL_MUL_LID; REAL_LT_NEG2] THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
      MATCH_MP_TAC COMPLEX_DIFFERENTIABLE_TRANSFORM_AT THEN
      MAP_EVERY EXISTS_TAC [`rp_hol_G n D d (--(&1)) B f`; `e:real`] THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [X_GEN_TAC `w:complex` THEN DISCH_TAC THEN CONV_TAC SYM_CONV THEN
        USE_THEN "h2" MATCH_MP_TAC THEN ASM_MESON_TAC[];
        USE_THEN "g2d" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC]];
    REPEAT STRIP_TAC THEN USE_THEN "h1" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    REPEAT STRIP_TAC THEN USE_THEN "h2" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    USE_THEN "nodes" (MP_TAC o CONJUNCT1 o REWRITE_RULE[rp_nodes]) THEN
    DISCH_THEN(MP_TAC o SPEC `i:num`) THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN
    USE_THEN "xd" (fun th -> ASSUME_TAC(MP (SPEC `i:num` th) (ASSUME `(i:num) < n`))) THEN
    ASM_SIMP_TAC[rp_hol_h; rp_hol_G; RE_CX; rp_hval; COMPLEX_MUL_LZERO;
                 COMPLEX_SUB_RZERO; CX_MUL; CX_POW;
                 REAL_ARITH `~(--(&1) = &1)`] THEN
    ASM_CASES_TAC `(x:num->real) i < &0` THEN ASM_REWRITE_TAC[] THENL
     [SUBGOAL_THEN `~(--(d / &2) < (x:num->real) i)` (fun th -> REWRITE_TAC[th]) THEN
      ASM_REAL_ARITH_TAC;
      SUBGOAL_THEN `--(d / &2) < (x:num->real) i` (fun th -> REWRITE_TAC[th]) THEN
      ASM_REAL_ARITH_TAC]]);;
