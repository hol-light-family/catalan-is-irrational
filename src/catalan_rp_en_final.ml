(* ========================================================================= *)
(* EN part, final: Proposition 6.1 in the form RP_EN1_STMT, RP_EN2_STMT.    *)
(* ========================================================================= *)

needs "src/catalan_rp_en_fin.ml";;

let RP_EN_DC_POS = prove
 (`forall kappa p v. &0 <= kappa /\ rp_summable p /\ rp_summable v
               ==> &0 <= rp_en_Dc kappa p v`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[rp_en_Dc] THEN
  MP_TAC(SPEC `p:num->real` RP_EN_INFSUM_ABS_POS) THEN
  MP_TAC(SPEC `v:num->real` RP_EN_INFSUM_ABS_POS) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= kappa * real_infsum (from 1) (\k. abs(p k))` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

let RP_EN_UNIFORM = prove
 (`forall kappa lam p v Bx Bs d.
     &0 <= kappa /\ &0 <= lam /\ rp_summable p /\ rp_summable v /\
     (forall x. --(&1) <= x /\ x < &1 /\ ~(x = &0) ==> rp_X kappa lam p v x <= Bx) /\
     (forall s. &0 < s /\ s < &1 ==> rp_Y v s <= Bs) /\
     &0 < d
     ==> exists N0. forall N x s.
           N0 <= N /\ 1 <= N /\ rp_config N x s /\
           (lam = &0 \/
            &(40 * N - 1) <
            sum {i | i < 48 * N} (\i. (&1 - x i pow 2) / (&1 + x i pow 2)))
           ==> rp_en_F kappa N x s <= rp_dual kappa p v Bx Bs + d`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `D = rp_en_Dc kappa p v` THEN
  SUBGOAL_THEN `&0 <= D` ASSUME_TAC THENL
   [EXPAND_TAC "D" THEN MATCH_MP_TAC RP_EN_DC_POS THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `e = min (&1 / &16) (d / (&2 * (D + &1)))` THEN
  SUBGOAL_THEN `&0 < e /\ e < &1 / &8 /\ e * D < d / &2` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < &2 * (D + &1)` ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&0 < d / (&2 * (D + &1))` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `e <= d / (&2 * (D + &1)) /\ e <= &1 / &16 /\ &0 < e`
    STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "e" THEN REWRITE_TAC[REAL_MIN_LE; REAL_LT_MIN; REAL_LE_REFL] THEN
      ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `e * (&2 * (D + &1)) <= d` MP_TAC THENL
     [ASM_MESON_TAC[REAL_LE_RDIV_EQ]; ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `C = rp_en_Cf kappa e lam p v Bx Bs` THEN
  MP_TAC(SPEC `(&2 * abs C) / d` REAL_ARCH_SIMPLE) THEN
  DISCH_THEN(X_CHOOSE_TAC `M:num`) THEN EXISTS_TAC `M:num` THEN
  MAP_EVERY X_GEN_TAC [`N:num`; `x:num->real`; `s:num->real`] THEN STRIP_TAC THEN
  (MP_TAC(SPECL [`kappa:real`; `lam:real`; `p:num->real`; `v:num->real`;
                 `Bx:real`; `Bs:real`; `e:real`; `N:num`; `x:num->real`;
                 `s:num->real`] RP_EN_FIN_BOUND) THEN
   ASM_REWRITE_TAC[] THEN
   SUBGOAL_THEN `C / &(48 * N) <= d / &2` MP_TAC THENL
    [SUBGOAL_THEN `&0 < &(48 * N)` ASSUME_TAC THENL
      [REWRITE_TAC[REAL_OF_NUM_LT] THEN UNDISCH_TAC `1 <= N` THEN ARITH_TAC;
       ALL_TAC] THEN
     ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
     SUBGOAL_THEN `(&2 * abs C) / d <= &(48 * N)` MP_TAC THENL
      [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&M` THEN ASM_REWRITE_TAC[] THEN
       REWRITE_TAC[REAL_OF_NUM_LE] THEN UNDISCH_TAC `M:num <= N` THEN ARITH_TAC;
       ALL_TAC] THEN
     ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN REAL_ARITH_TAC;
     ALL_TAC] THEN
   ASM_REAL_ARITH_TAC));;

(* from the normalised logarithmic bound to the exponential form *)
let RP_EN_EXP_FORM = prove
 (`forall a y K d m. &0 < a /\ &0 < m /\ log a / m pow 2 - log(&2) / &2 = y /\
             y <= K + d
             ==> a <= exp(m pow 2 * (K + d + log(&2) / &2))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < (m:real) pow 2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `log a <= (m:real) pow 2 * (K + d + log(&2) / &2)` ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN ASM_SIMP_TAC[GSYM REAL_LE_LDIV_EQ] THEN
    ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `exp(log a)` THEN CONJ_TAC THENL
   [ASM_SIMP_TAC[EXP_LOG; REAL_LE_REFL]; ASM_REWRITE_TAC[REAL_EXP_MONO_LE]]);;

let RP_EN2_THM = prove
 (`RP_EN2_STMT`,
  REWRITE_TAC[RP_EN2_STMT] THEN REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`&2`; `&0`; `p:num->real`; `v:num->real`; `Bx:real`; `Bs:real`;
                `d:real`] RP_EN_UNIFORM) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `N0:num`) THEN EXISTS_TAC `N0:num` THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC RP_EN_EXP_FORM THEN
  EXISTS_TAC `rp_en_F (&2) N x s` THEN
  ASM_SIMP_TAC[RP_EN_X_I2_POS; RP_EN_X_I2] THEN
  REWRITE_TAC[REAL_OF_NUM_LT] THEN REPEAT CONJ_TAC THEN
  TRY(UNDISCH_TAC `1 <= N` THEN ARITH_TAC) THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

let RP_EN1_THM = prove
 (`RP_EN1_STMT`,
  REWRITE_TAC[RP_EN1_STMT] THEN REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`&1`; `lam:real`; `p:num->real`; `v:num->real`; `Bx:real`; `Bs:real`;
                `d:real`] RP_EN_UNIFORM) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `N0:num`) THEN EXISTS_TAC `N0:num` THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC RP_EN_EXP_FORM THEN
  EXISTS_TAC `rp_en_F (&1) N x s` THEN
  ASM_SIMP_TAC[RP_EN_X_I1_POS; RP_EN_X_I1] THEN
  REWRITE_TAC[REAL_OF_NUM_LT] THEN REPEAT CONJ_TAC THEN
  TRY(UNDISCH_TAC `1 <= N` THEN ARITH_TAC) THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;
