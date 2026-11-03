(* ========================================================================= *)
(* CAT_NONVANISHING, part P: the interface theorems NV_PAL_P, NV_PAL_D,     *)
(* NV_PAL_BINOM (Frobenius / palindromic extraction, Section 4 of the paper) *)
(* ========================================================================= *)

needs "src/catalan_nv_pal_cong.ml";;
needs "src/catalan_nv_iface.ml";;

let NV_PAL_RP_ADD = prove
 (`forall D u v x. nv_pal_rp D u x + nv_pal_rp D v x = nv_pal_rp D (\K. u K + v K) x`,
  REWRITE_TAC[nv_pal_rp; GSYM SUM_ADD_NUMSEG; REAL_ADD_RDISTRIB]);;

let NV_PAL_DM2 = prove
 (`forall p u l. l < p ==> (u * p + l) DIV p = u /\ (u * p + l) MOD p = l`,
  REPEAT STRIP_TAC THENL
   [MATCH_MP_TAC DIV_UNIQ THEN EXISTS_TAC `l:num`;
    MATCH_MP_TAC MOD_UNIQ THEN EXISTS_TAC `u:num`] THEN
  ASM_REWRITE_TAC[]);;

let NV_PAL_ECOEF_ZERO = prove
 (`forall p a. ODD p /\ p - 1 < a ==> nv_Ecoef p a = &0`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ODD_EXISTS] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `m:num` ASSUME_TAC) MP_TAC) THEN
  FIRST_X_ASSUM SUBST1_TAC THEN
  REWRITE_TAC[nv_Ecoef; SUC_SUB1; NV_PAL_DIV2] THEN DISCH_TAC THEN
  COND_CASES_TAC THEN REWRITE_TAC[] THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `k:num` SUBST_ALL_TAC o REWRITE_RULE[EVEN_EXISTS]) THEN
  REWRITE_TAC[NV_PAL_DIV2] THEN
  SUBGOAL_THEN `binom(m,k) = 0` (fun th -> REWRITE_TAC[th; REAL_MUL_RZERO]) THEN
  MATCH_MP_TAC BINOM_LT THEN UNDISCH_TAC `2 * m < 2 * k:num` THEN ARITH_TAC);;

let NV_PAL_RHS_RP = prove
 (`forall p i c c' x. 1 <= p /\ i < p
     ==> nv_pal_S (p - i) x * nv_pal_rp 64 c (x pow p) +
         nv_pal_S i x * nv_pal_rp 64 c' (x pow p) =
         nv_pal_rp (65 * p - 1)
           (\K. nv_a p (K MOD p) i * c (K DIV p) + nv_b p (K MOD p) i * c' (K DIV p)) x`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[NV_PAL_SA_RP; NV_PAL_SB_RP; LT_IMP_LE; NV_PAL_RP_DIGIT] THEN
  REWRITE_TAC[ARITH_RULE `p * (64 + 1) - 1 = 65 * p - 1:num`; NV_PAL_RP_ADD]);;

let NV_PAL_P = prove
 (`forall p r0 i l u. prime p /\ 260 < p /\ r0 < 48 /\ i < p /\ l < p
     ==> nv_cong p
          (sum (0..p - 1) (\d. nv_Ecoef p d *
              cat_pcoef p (p * r0 + i) (((u + 1) * p + l) - 1 - d)))
          (nv_a p l i * cat_pcoef 1 r0 u + nv_b p l i * cat_pcoef 1 (r0 + 1) u)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(p = 2:num)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPEC `p:num` NV_PAL_ODD) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_CASES_TAC `65 <= u:num` THENL
   [SUBGOAL_THEN `forall d. d <= p - 1 ==> 65 * p <= ((u + 1) * p + l) - 1 - d:num`
    ASSUME_TAC THENL
     [REPEAT STRIP_TAC THEN
      SUBGOAL_THEN `66 * p <= (u + 1) * p:num` MP_TAC THENL
       [REWRITE_TAC[LE_MULT_RCANCEL] THEN UNDISCH_TAC `65 <= u:num` THEN ARITH_TAC;
        UNDISCH_TAC `d <= p - 1:num` THEN ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `65 * 1 <= u:num` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[NV_PCOEF_HIGH; REAL_MUL_RZERO; REAL_ADD_RID] THEN
    REWRITE_TAC[SUM_0] THEN ASM_SIMP_TAC[NV_CONG_REFL];
    ALL_TAC] THEN
  MP_TAC(SPECL [`p:num`; `r0:num`; `i:num`] NV_PAL_CONG_P) THEN
  ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[NV_PAL_RHS_RP; NV_PAL_G_RP] THEN
  SUBGOAL_THEN `(forall a. p - 1 < a ==> nv_Ecoef p a = &0) /\
                (forall b. 65 * p - 1 < b ==> cat_pcoef p (p * r0 + i) b = &0)` MP_TAC THENL
   [ASM_SIMP_TAC[NV_PAL_ECOEF_ZERO] THEN X_GEN_TAC `b:num` THEN DISCH_TAC THEN
    MP_TAC(SPECL [`p:num`; `p * r0 + i:num`; `b:num`] NV_PCOEF_HIGH) THEN
    ANTS_TAC THENL [UNDISCH_TAC `65 * p - 1 < b:num` THEN ARITH_TAC; SIMP_TAC[]];
    DISCH_THEN(fun th -> REWRITE_TAC[REWRITE_RULE[ETA_AX] (MATCH_MP NV_PAL_RP_MUL th)])] THEN
  ONCE_REWRITE_TAC[SPECL [`65 * p - 1`; `p - 1`] NV_PAL_RP_PAD] THEN
  SUBGOAL_THEN `(65 * p - 1) + (p - 1) = (p - 1) + (65 * p - 1):num` SUBST1_TAC THENL
   [ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o MATCH_MP NV_PAL_RP_COEFF o CONJ (ASSUME `prime p`)) THEN
  DISCH_THEN(MP_TAC o SPEC `((u + 1) * p + l) - 1:num`) THEN
  SUBGOAL_THEN `(u + 1) * p <= 65 * p:num` ASSUME_TAC THENL
   [REWRITE_TAC[LE_MULT_RCANCEL] THEN UNDISCH_TAC `~(65 <= u:num)` THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `p <= (u + 1) * p:num` ASSUME_TAC THENL
   [GEN_REWRITE_TAC LAND_CONV [ARITH_RULE `p = 1 * p:num`] THEN
    REWRITE_TAC[LE_MULT_RCANCEL] THEN ARITH_TAC;
    ALL_TAC] THEN
  ANTS_TAC THENL [UNDISCH_TAC `l < p:num` THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `p - 1 <= ((u + 1) * p + l) - 1:num /\
                ((u + 1) * p + l) - 1 - (p - 1) = u * p + l`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[RIGHT_ADD_DISTRIB; MULT_CLAUSES] THEN
    UNDISCH_TAC `1 <= p:num` THEN ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[NV_PAL_DM2] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  MATCH_MP_TAC NV_PAL_SUM_ZERO_EXT THEN CONJ_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[NV_PAL_ECOEF_ZERO; REAL_MUL_LZERO]);;

let NV_PAL_D = prove
 (`forall p r0 i l u. prime p /\ 260 < p /\ r0 < 48 /\ i < p /\ l < p
     ==> nv_cong p (cat_dcoef p (p * r0 + i) (u * p + l))
          (nv_a p l i * cat_dcoef 1 r0 u + nv_b p l i * cat_dcoef 1 (r0 + 1) u)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(p = 2:num)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPEC `p:num` NV_PAL_ODD) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_CASES_TAC `65 <= u:num` THENL
   [SUBGOAL_THEN `65 * p <= u * p + l /\ 65 * 1 <= u:num` STRIP_ASSUME_TAC THENL
     [SUBGOAL_THEN `65 * p <= u * p:num` MP_TAC THENL
       [REWRITE_TAC[LE_MULT_RCANCEL] THEN ASM_REWRITE_TAC[];
        UNDISCH_TAC `65 <= u:num` THEN ARITH_TAC];
      ALL_TAC] THEN
    ASM_SIMP_TAC[NV_PCOEF_HIGH; REAL_MUL_RZERO; REAL_ADD_RID; NV_CONG_REFL];
    ALL_TAC] THEN
  MP_TAC(SPECL [`p:num`; `r0:num`; `i:num`] NV_PAL_CONG_D) THEN
  ASM_SIMP_TAC[NV_PAL_RHS_RP] THEN
  DISCH_THEN(MP_TAC o MATCH_MP NV_PAL_RP_COEFF o CONJ (ASSUME `prime p`)) THEN
  DISCH_THEN(MP_TAC o SPEC `u * p + l:num`) THEN
  ASM_SIMP_TAC[NV_PAL_DM2] THEN DISCH_THEN MATCH_MP_TAC THEN
  SUBGOAL_THEN `u * p <= 64 * p:num` MP_TAC THENL
   [REWRITE_TAC[LE_MULT_RCANCEL] THEN UNDISCH_TAC `~(65 <= u:num)` THEN ARITH_TAC;
    UNDISCH_TAC `l < p:num` THEN ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* binom(a p, v) == binom(a, v/p) [p | v]  (mod p).                          *)
(* ------------------------------------------------------------------------- *)

let NV_PAL_FROBSUM = prove
 (`forall p a x. 1 <= p
     ==> (x pow p + &1) pow a =
         sum(0..p * (a + 1) - 1)
           (\v. (if p divides v then &(binom(a,v DIV p)) else &0) * x pow v)`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[NV_PAL_DIGSUM] THEN
  REWRITE_TAC[REAL_BINOMIAL_THEOREM; REAL_POW_ONE; REAL_MUL_RID] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN
  BETA_TAC THEN MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `sum(0..p-1) (\l. if l = 0 then &(binom(a,j)) * x pow (p * j) else &0)` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[SUM_DELTA; IN_NUMSEG; LE_0] THEN REWRITE_TAC[REAL_POW_POW];
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `l:num` THEN STRIP_TAC THEN
    BETA_TAC THEN
    SUBGOAL_THEN `l < p:num` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[DIVIDES_MOD; NV_PAL_DIGIT_DM] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[ADD_CLAUSES; REAL_MUL_LZERO]]);;

let NV_PAL_BINOM = prove
 (`forall p a v. prime p
     ==> nv_cong p (&(binom(a * p,v)))
                   (if p divides v then &(binom(a,v DIV p)) else &0)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `1 <= p:num` ASSUME_TAC THENL
   [ASM_MESON_TAC[PRIME_0; ARITH_RULE `1 <= p <=> ~(p = 0:num)`]; ALL_TAC] THEN
  SUBGOAL_THEN `a * p <= p * (a + 1) - 1:num` ASSUME_TAC THENL
   [REWRITE_TAC[LEFT_ADD_DISTRIB; MULT_CLAUSES] THEN
    UNDISCH_TAC `1 <= p:num` THEN ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `v <= p * (a + 1) - 1:num` THENL
   [ALL_TAC;
    SUBGOAL_THEN `binom(a * p,v) = 0` SUBST1_TAC THENL
     [MATCH_MP_TAC BINOM_LT THEN ASM_ARITH_TAC; ALL_TAC] THEN
    COND_CASES_TAC THEN ASM_SIMP_TAC[NV_CONG_REFL] THEN
    FIRST_X_ASSUM(X_CHOOSE_THEN `q:num` SUBST_ALL_TAC o REWRITE_RULE[divides]) THEN
    SUBGOAL_THEN `~(p = 0:num)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[DIV_MULT] THEN
    SUBGOAL_THEN `binom(a,q) = 0` (fun th -> ASM_SIMP_TAC[th; NV_CONG_REFL]) THEN
    MATCH_MP_TAC BINOM_LT THEN
    SUBGOAL_THEN `~(p * q <= p * a:num)` MP_TAC THENL
     [UNDISCH_TAC `~(p * q <= p * (a + 1) - 1:num)` THEN
      UNDISCH_TAC `1 <= p:num` THEN
      REWRITE_TAC[LEFT_ADD_DISTRIB; MULT_CLAUSES] THEN ARITH_TAC;
      REWRITE_TAC[LE_MULT_LCANCEL] THEN ASM_REWRITE_TAC[] THEN ARITH_TAC]] THEN
  MP_TAC(ISPECL [`p:num`; `p * (a + 1) - 1:num`;
    `\k. &(binom(a * p,k))`;
    `\v. if p divides v then &(binom(a,v DIV p)) else &0`] NV_PAL_PC_COEFF) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ALL_TAC; DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[]] THEN
  MATCH_MP_TAC NV_PAL_PC_EQ_TRANS THEN
  EXISTS_TAC `\x. (x + &1) pow (a * p)` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[REAL_BINOMIAL_THEOREM; REAL_POW_ONE; REAL_MUL_RID] THEN
    MATCH_MP_TAC NV_PAL_TRUNC THEN ASM_REWRITE_TAC[] THEN
    SIMP_TAC[BINOM_LT; REAL_OF_NUM_EQ];
    ALL_TAC] THEN
  MATCH_MP_TAC NV_PAL_PC_TRANS_EQ THEN
  EXISTS_TAC `\x. (x pow p + &1) pow a` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ALL_TAC; ASM_SIMP_TAC[NV_PAL_FROBSUM]] THEN
  NV_PAL_EQCHAIN_TAC `\x. ((x + &1) pow p) pow a` THENL
   [REWRITE_TAC[REAL_POW_POW] THEN REWRITE_TAC[MULT_SYM]; ALL_TAC] THEN
  MATCH_MP_TAC NV_PAL_PC_POW THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC NV_PAL_PC_TRANS_EQ THEN EXISTS_TAC `\x. x pow p + &1 pow p` THEN
    ASM_SIMP_TAC[NV_PAL_FROB_LIN; INTEGER_CLOSED; REAL_POW_ONE];
    NV_PAL_IPG_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The interface constants.                                                  *)
(* ------------------------------------------------------------------------- *)

let NV_PAL_IF_P = prove
 (`nv_if_pal_p`, REWRITE_TAC[nv_if_pal_p; NV_PAL_P]);;

let NV_PAL_IF_D = prove
 (`nv_if_pal_d`, REWRITE_TAC[nv_if_pal_d; NV_PAL_D]);;

let NV_PAL_IF_BINOM = prove
 (`nv_if_binom`, REWRITE_TAC[nv_if_binom; NV_PAL_BINOM]);;
