needs "src/catalan_rp_hol_base.ml";;

(* rp_hol_: assembly of RP_PICK_STMT from the four internal interfaces. *)

let rp_hol_pick_tac bl gla glb ck =
  let [BL_FD; BL_BD; BL_BF; BL_B0; BL_BC; BL_RAD; BL_NI; BL_STRIP] =
    CONJUNCTS (REWRITE_RULE[RP_HOL_BL_STMT] bl) in
  let GLA = REWRITE_RULE[RP_HOL_GLA_STMT] gla
  and GLB = REWRITE_RULE[RP_HOL_GLB_STMT] glb
  and CK = REWRITE_RULE[RP_HOL_CK_STMT] ck in
  REWRITE_TAC[RP_PICK_STMT] THEN
  MAP_EVERY X_GEN_TAC [`n:num`; `D:num`; `x:num->real`; `a:num->real`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `forall i. i < n ==> abs((x:num->real) i) < &1` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [rp_nodes]) THEN
    DISCH_THEN(MP_TAC o CONJUNCT1) THEN
    DISCH_TAC THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN ASM_REWRITE_TAC[] THEN
    REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`n:num`; `D:num`; `x:num->real`] BL_STRIP) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(SPECL [`n:num`; `x:num->real`] BL_RAD) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(SPECL [`n:num`; `D:num`; `x:num->real`; `d:real`; `r:real`;
     `rp_hol_B n x`; `rp_hol_F n D x`] GLA) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[BL_FD; BL_B0] THEN CONJ_TAC THEN REPEAT STRIP_TAC THENL
     [MATCH_MP_TAC BL_BD THEN ASM_MESON_TAC[];
      MATCH_MP_TAC BL_BF THEN ASM_MESON_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `r':real` STRIP_ASSUME_TAC) THEN
  MP_TAC(SPECL
   [`n:num`; `x:num->real`; `\i:num. rp_hval D ((x:num->real) i)`;
    `rp_hol_h n D d (rp_hol_B n x) (rp_hol_F n D x)`; `rp_K0 * &n`; `a:num->real`] CK) THEN
  REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC HOLOMORPHIC_ON_IMP_CONTINUOUS_ON THEN
    MATCH_MP_TAC HOLOMORPHIC_ON_SUBSET THEN EXISTS_TAC `ball(Cx(&0),r')` THEN
    ASM_REWRITE_TAC[SUBSET; IN_CBALL; IN_BALL; DIST_0] THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC HOLOMORPHIC_ON_SUBSET THEN EXISTS_TAC `ball(Cx(&0),r')` THEN
    ASM_REWRITE_TAC[SUBSET; IN_BALL; DIST_0] THEN ASM_REAL_ARITH_TAC;
    X_GEN_TAC `z:complex` THEN DISCH_TAC THEN
    SUBGOAL_THEN `norm(z:complex) < r'` ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN
     `exists s. (s = &1 \/ s = --(&1)) /\ &0 <= s * Re z /\
          rp_hol_h n D d (rp_hol_B n x) (rp_hol_F n D x) z =
          rp_hol_G n D d s (rp_hol_B n x) (rp_hol_F n D x) z`
    (X_CHOOSE_THEN `s:real` (CONJUNCTS_THEN2 ASSUME_TAC
       (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC))) THENL
     [ASM_CASES_TAC `&0 <= Re z` THENL
       [EXISTS_TAC `&1` THEN REWRITE_TAC[REAL_MUL_LID] THEN ASM_REWRITE_TAC[] THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        EXISTS_TAC `--(&1)` THEN
        SUBGOAL_THEN `Re z <= &0` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC GLB THEN
    EXISTS_TAC `x:num->real` THEN ASM_REWRITE_TAC[BL_FD] THEN CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN MATCH_MP_TAC BL_NI THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_EQ_IMP_LE THEN MATCH_MP_TAC BL_BC THEN ASM_REWRITE_TAC[]]];;

let RP_HOL_PICK_FROM_PARTS = prove
 (`RP_HOL_BL_STMT /\ RP_HOL_GLA_STMT /\ RP_HOL_GLB_STMT /\ RP_HOL_CK_STMT
   ==> RP_PICK_STMT`,
  DISCH_THEN(fun th ->
    let a,b = CONJ_PAIR th in let b,c = CONJ_PAIR b in let c,d = CONJ_PAIR c in
    rp_hol_pick_tac a b c d));;
