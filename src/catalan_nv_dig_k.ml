(* ========================================================================= *)
(* CAT_NONVANISHING, part La (prefix nv_dig_): the digit reductions (34),    *)
(* (35) of the paper for m_(z-1), k^-_u and k^+_(u+1), at the nv_dig_fin_dig level. *)
(* ========================================================================= *)

needs "src/catalan_nv_dig_h.ml";;

(* ------------------------------------------------------------------------- *)
(* Sums.                                                                     *)
(* ------------------------------------------------------------------------- *)

let NV_DIG_MSET = prove
 (`forall p P r. 0 < p /\ r < p ==> {m | 1 <= m * p /\ m * p <= P * p + r} = 1..P`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_NUMSEG] THEN
  X_GEN_TAC `m:num` THEN EQ_TAC THEN STRIP_TAC THENL
   [CONJ_TAC THENL
     [REWRITE_TAC[ARITH_RULE `1 <= m <=> ~(m = 0)`] THEN DISCH_THEN SUBST_ALL_TAC THEN
      RULE_ASSUM_TAC(REWRITE_RULE[MULT_CLAUSES]) THEN ASM_ARITH_TAC;
      REWRITE_TAC[GSYM NOT_LT] THEN DISCH_TAC THEN
      SUBGOAL_THEN `(P + 1) * p <= m * p` MP_TAC THENL
       [REWRITE_TAC[LE_MULT_RCANCEL] THEN ASM_ARITH_TAC;
        REWRITE_TAC[RIGHT_ADD_DISTRIB; MULT_CLAUSES] THEN ASM_ARITH_TAC]];
    CONJ_TAC THENL
     [GEN_REWRITE_TAC LAND_CONV [ARITH_RULE `1 = 1 * 1`] THEN
      MATCH_MP_TAC LE_MULT2 THEN ASM_ARITH_TAC;
      TRANS_TAC LE_TRANS `P * p:num` THEN
      ASM_REWRITE_TAC[LE_MULT_RCANCEL; LE_ADD]]]);;

let NV_DIG_SUMM = prove
 (`forall p P r f g.
     prime p /\ r < p /\
     (forall k. 1 <= k /\ k <= P * p + r /\ ~(p divides k) ==> nv_dig_fin_dig_cg p (f k) (&0)) /\
     (forall m. 1 <= m /\ m <= P ==> nv_dig_fin_dig_cg p (f (m * p)) (g m))
     ==> nv_dig_fin_dig_cg p (sum (1..P * p + r) f) (sum (1..P) g)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`p:num`; `1:num`; `P * p + r:num`; `f:num->real`; `g:num->real`]
    NV_DIG_FIN_DIG_SUM_MULTIPLES) THEN
  SUBGOAL_THEN `{m | 1 <= m * p /\ m * p <= P * p + r} = 1..P` SUBST1_TAC THENL
   [MATCH_MP_TAC NV_DIG_MSET THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC[] THEN
  X_GEN_TAC `m:num` THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  MP_TAC(ISPECL [`p:num`; `P:num`; `r:num`] NV_DIG_MSET) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_NUMSEG] THEN ASM_MESON_TAC[]);;

let NV_DIG_EVSUM = prove
 (`forall s w. sum(0..2 * s) (\i. if EVEN i then w (i DIV 2) else &0) = sum(0..s) w`,
  INDUCT_TAC THEN GEN_TAC THENL
   [REWRITE_TAC[MULT_CLAUSES; SUM_SING_NUMSEG; EVEN; NUM_REDUCE_CONV `0 DIV 2`];
    ALL_TAC] THEN
  REWRITE_TAC[ARITH_RULE `2 * SUC s = SUC(SUC(2 * s))`; SUM_CLAUSES_NUMSEG; LE_0] THEN
  ASM_REWRITE_TAC[EVEN; EVEN_DOUBLE] THEN
  REWRITE_TAC[ARITH_RULE `SUC(SUC(2 * s)) = 2 * SUC s`] THEN
  SIMP_TAC[DIV_MULT; ARITH_EQ] THEN REAL_ARITH_TAC);;

let NV_DIG_ODDSUM = prove
 (`forall s w. sum(1..2 * s + 1) (\t. if ODD t then w (((2 * s + 1) - t) DIV 2) else &0) =
         sum(0..s) w`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [SUM_REFLECT] THEN
  REWRITE_TAC[ARITH_RULE `~(2 * s + 1 < 1)`; ADD_SUB] THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM NV_DIG_EVSUM] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  BETA_TAC THEN
  SUBGOAL_THEN `(2 * s + 1) - ((2 * s + 1) - i) = i /\ (ODD((2 * s + 1) - i) <=> EVEN i)`
   (fun th -> REWRITE_TAC[th]) THEN
  CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(2 * s + 1) - i = (2 * s - i) + 1` SUBST1_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[ODD_ADD; ARITH; GSYM NOT_EVEN; EVEN_SUB; EVEN_MULT] THEN
  ASM_REWRITE_TAC[ARITH_RULE `2 * s <= i <=> i = 2 * s \/ 2 * s < i`] THEN
  ASM_CASES_TAC `i = 2 * s` THEN ASM_REWRITE_TAC[EVEN_DOUBLE] THEN
  ASM_SIMP_TAC[ARITH_RULE `i <= 2 * s ==> ~(2 * s < i)`]);;

(* ------------------------------------------------------------------------- *)
(* m_(z-1), E_(p-1-r).                                                       *)
(* ------------------------------------------------------------------------- *)

let NV_DIG_MCASE = prove
 (`forall z. 0 < z ==> cat_m (z - 1) = if ODD z then &2 * nv_dig_fin_hstar z else &0`,
  REPEAT STRIP_TAC THEN COND_CASES_TAC THEN ASM_SIMP_TAC[NV_DIG_FIN_BDRY_M_ODD] THEN
  REWRITE_TAC[cat_m] THEN
  SUBGOAL_THEN `~EVEN(z - 1)` (fun th -> REWRITE_TAC[th]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[NOT_ODD]) THEN
  REWRITE_TAC[EVEN_SUB; ARITH] THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `z = 1` SUBST_ALL_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  UNDISCH_TAC `EVEN 1` THEN REWRITE_TAC[ARITH]);;

let NV_DIG_MP = prove
 (`forall P. (if P = 0 then &0 else cat_m (P - 1)) = if ODD P then &2 * nv_dig_fin_hstar P else &0`,
  GEN_TAC THEN ASM_CASES_TAC `P = 0` THEN ASM_REWRITE_TAC[ARITH] THEN
  MATCH_MP_TAC NV_DIG_MCASE THEN ASM_ARITH_TAC);;

let NV_DIG_EVEN_PM1 = prove
 (`forall s p r. 2 * s + 1 = p /\ r < p ==> (EVEN (p - 1 - r) <=> EVEN r)`,
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (is_eq o concl)) THEN
  REWRITE_TAC[ADD_SUB] THEN REWRITE_TAC[EVEN_SUB; EVEN_MULT; ARITH] THEN
  ASM_CASES_TAC `r = 2 * s` THEN ASM_REWRITE_TAC[EVEN_DOUBLE; LE_REFL] THEN
  ASM_SIMP_TAC[ARITH_RULE `r < 2 * s + 1 /\ ~(r = 2 * s) ==> ~(2 * s <= r)`]);;

let NV_DIG_E_PM1 = prove
 (`forall s p r. 2 * s + 1 = p /\ r < p
           ==> nv_E (p - 1 - r) = if EVEN r then cat_c ((p - 1 - r) DIV 2) else &0`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[nv_E] THEN
  MP_TAC(SPECL [`s:num`; `p:num`; `r:num`] NV_DIG_EVEN_PM1) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REFL_TAC);;

let NV_DIG_CREFL = prove
 (`forall p s r. prime p /\ 2 * s + 1 = p /\ r < p /\ EVEN r
           ==> nv_dig_fin_dig_cg p (cat_c ((p - 1 - r) DIV 2)) ((--(&1)) pow s * cat_c (r DIV 2))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(p = 2) /\ (p - 1) DIV 2 = s` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[NV_DIG_PS]; ALL_TAC] THEN
  MATCH_MP_TAC NV_DIG_FIN_DIG_CG_TRANS THEN EXISTS_TAC `nv_dig_fin_E p (p - 1 - r)` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC NV_DIG_FIN_DIG_CG_SYM THEN MATCH_MP_TAC NV_DIG_FIN_DIG_E_CG THEN
    ASM_MESON_TAC[NV_DIG_EVEN_PM1; ARITH_RULE `r < p ==> p - 1 - r < p`];
    ALL_TAC] THEN
  ASM_SIMP_TAC[NV_DIG_FIN_DIG_E_REFL] THEN MATCH_MP_TAC NV_DIG_FIN_DIG_CG_MUL THEN
  ASM_SIMP_TAC[NV_DIG_FIN_DIG_E_CG] THEN MATCH_MP_TAC NV_DIG_FIN_DIG_CG_REFL THEN
  ASM_MESON_TAC[NV_DIG_EPS_UNIT; NV_DIG_FIN_DIG_UNIT_ZP]);;

let NV_DIG_CG_MUL3 = prove
 (`forall p e c c' h. prime p /\ nv_dig_fin_dig_cg p c' (e * c) /\ nv_dig_fin_zp p h
                ==> nv_dig_fin_dig_cg p (c' * h) (e * c * h)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[REAL_MUL_ASSOC] THEN
  MATCH_MP_TAC NV_DIG_FIN_DIG_CG_MUL THEN ASM_SIMP_TAC[NV_DIG_FIN_DIG_CG_REFL]);;

let NV_DIG_M_FIN = prove
 (`forall p s P r. prime p /\ 2 * s + 1 = p /\ P + 2 < p /\ r < p /\ 0 < P * p + r
     ==> nv_dig_fin_zp p (if P = 0 then &0 else cat_m (P - 1)) /\
         nv_dig_fin_dig_cg p (&p * cat_m ((P * p + r) - 1))
                      (nv_E (p - 1 - r) * (if P = 0 then &0 else cat_m (P - 1)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(p = 2) /\ (p - 1) DIV 2 = s` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[NV_DIG_PS]; ALL_TAC] THEN
  ASM_SIMP_TAC[NV_DIG_MCASE; NV_DIG_MP] THEN
  MP_TAC(SPECL [`s:num`; `p:num`; `r:num`] NV_DIG_E_PM1) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[GSYM NOT_EVEN] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP NV_DIG_PAR th]) THEN
  SUBGOAL_THEN `nv_dig_fin_dig_unit p (nv_dig_fin_hstar P)` ASSUME_TAC THENL
   [MATCH_MP_TAC NV_DIG_HSTAR_SMALL THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `EVEN r` THEN ASM_CASES_TAC `EVEN P` THEN
  ASM_REWRITE_TAC[REAL_MUL_LZERO; REAL_MUL_RZERO] THEN
  ASM_SIMP_TAC[NV_DIG_FIN_ZP_0; NV_DIG_FIN_DIG_CG_REFL; NV_DIG_FIN_ZP_MUL; NV_DIG_FIN_ZP_NUM; NV_DIG_FIN_DIG_UNIT_ZP] THENL
   [MP_TAC(SPECL [`p:num`; `s:num`; `P:num`; `r:num`] NV_DIG_HCR) THEN
    ASM_REWRITE_TAC[GSYM NOT_EVEN] THEN STRIP_TAC THEN
    MP_TAC(SPECL [`p:num`; `s:num`; `r:num`] NV_DIG_CREFL) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MATCH_MP_TAC NV_DIG_FIN_DIG_CG_EQ THEN
    MAP_EVERY EXISTS_TAC [`&2 * (&p * nv_dig_fin_hstar (P * p + r))`;
                          `&2 * (cat_c ((p - 1 - r) DIV 2) * nv_dig_fin_hstar P)`] THEN
    REPEAT CONJ_TAC THENL [ALL_TAC; REAL_ARITH_TAC; REAL_ARITH_TAC] THEN
    MATCH_MP_TAC NV_DIG_FIN_DIG_CG_MUL THEN ASM_SIMP_TAC[NV_DIG_FIN_DIG_CG_REFL; NV_DIG_FIN_ZP_NUM] THEN
    MATCH_MP_TAC NV_DIG_FIN_DIG_CG_TRANS THEN
    EXISTS_TAC `(--(&1)) pow s * cat_c (r DIV 2) * nv_dig_fin_hstar P` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC NV_DIG_FIN_DIG_CG_SYM THEN
    MATCH_MP_TAC NV_DIG_CG_MUL3 THEN ASM_SIMP_TAC[NV_DIG_FIN_DIG_UNIT_ZP];
    REWRITE_TAC[REAL_ARITH `&p * &2 * h = &p * (&2 * h)`] THEN
    MATCH_MP_TAC NV_DIG_FIN_DIG_CG_PMUL THEN ASM_SIMP_TAC[NV_DIG_FIN_ZP_MUL; NV_DIG_FIN_ZP_NUM] THEN
    MP_TAC(SPECL [`p:num`; `s:num`; `P:num`; `r:num`] NV_DIG_HB) THEN
    ASM_REWRITE_TAC[GSYM NOT_EVEN] THEN DISCH_TAC THEN
    MATCH_MP_TAC NV_DIG_FIN_ZP_MUL THEN ASM_SIMP_TAC[NV_DIG_FIN_ZP_NUM; NV_DIG_FIN_DIG_UNIT_ZP]]);;

(* ------------------------------------------------------------------------- *)
(* Further helpers.                                                          *)
(* ------------------------------------------------------------------------- *)

let NV_DIG_UNIT_INV_ZP = prove
 (`forall p u. nv_dig_fin_dig_unit p u ==> nv_dig_fin_zp p (inv u)`,
  MESON_TAC[NV_DIG_FIN_DIG_UNIT_ZP]);;

let NV_DIG_DIVP = prove
 (`forall p k P r. ~(p = 0) /\ r < p /\ k <= P * p + r ==> k DIV p <= P`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(P * p + r) DIV p = P` (fun th -> GEN_REWRITE_TAC RAND_CONV [GSYM th]) THENL
   [MATCH_MP_TAC DIV_UNIQ THEN EXISTS_TAC `r:num` THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC DIV_MONO THEN ASM_REWRITE_TAC[]]);;

let NV_DIG_HMP_EVEN = prove
 (`forall p s m. prime p /\ 2 * s + 1 = p /\ m + 2 < p /\ EVEN m
           ==> nv_dig_fin_dig_unit p (nv_dig_fin_hstar (m * p)) /\
               nv_dig_fin_dig_cg p (nv_dig_fin_hstar (m * p)) (nv_dig_fin_hstar m)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`p:num`; `s:num`; `m:num`; `0`] NV_DIG_HA) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[EVEN] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[ADD_CLAUSES; NUM_REDUCE_CONV `0 DIV 2`; NV_DIG_FIN_BDRY_C_0; REAL_MUL_RID] THEN
  SIMP_TAC[]);;

let NV_DIG_HMP_ODD = prove
 (`forall p s m. prime p /\ 2 * s + 1 = p /\ m + 2 < p /\ ODD m
           ==> nv_dig_fin_dig_unit p (&p * nv_dig_fin_hstar (m * p)) /\
               nv_dig_fin_dig_cg p (&p * nv_dig_fin_hstar (m * p)) ((--(&1)) pow s * nv_dig_fin_hstar m)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`p:num`; `s:num`; `m:num`; `0`] NV_DIG_HCR) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[EVEN] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[ADD_CLAUSES; NUM_REDUCE_CONV `0 DIV 2`; NV_DIG_FIN_BDRY_C_0; REAL_MUL_LID] THEN
  SIMP_TAC[]);;

let NV_DIG_H0 = prove
 (`forall p s P r. prime p /\ 2 * s + 1 = p /\ P + 2 < p /\ ODD P /\ r < p /\ ODD r
     ==> nv_dig_fin_dig_cg p (nv_dig_fin_hstar (P * p + r)) (&0)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`p:num`; `s:num`; `P:num`; `r:num`] NV_DIG_HD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC NV_DIG_FIN_DIG_CG_EQ THEN
  MAP_EVERY EXISTS_TAC [`&p * nv_dig_fin_hstar (P * p + r) / &p`; `&0`] THEN
  ASM_SIMP_TAC[NV_DIG_FIN_DIG_CG_PMUL; NV_DIG_FIN_DIG_UNIT_ZP] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC REAL_DIV_LMUL THEN
  REWRITE_TAC[REAL_OF_NUM_EQ] THEN ASM_ARITH_TAC);;

let NV_DIG_ALG_A = prove
 (`forall P k H. ~(k = &0) /\ ~(H = &0)
           ==> P pow 2 * &2 / (k pow 2 * H) = P * (&2 * (P / (k * H)) * inv k)`,
  REPEAT STRIP_TAC THEN REPEAT(POP_ASSUM MP_TAC) THEN CONV_TAC REAL_FIELD);;

let NV_DIG_ALG_B = prove
 (`forall P m H. ~(P = &0) /\ ~(m = &0)
           ==> P pow 2 * &2 / ((m * P) pow 2 * H) = &2 * inv(m pow 2 * H)`,
  REPEAT STRIP_TAC THEN REPEAT(POP_ASSUM MP_TAC) THEN CONV_TAC REAL_FIELD);;

let NV_DIG_ALG_D = prove
 (`forall P m H. ~(P = &0) /\ ~(m = &0)
           ==> P * &2 / ((m * P) pow 2 * H) = &2 * inv(m pow 2 * (P * H))`,
  REPEAT STRIP_TAC THEN REPEAT(POP_ASSUM MP_TAC) THEN CONV_TAC REAL_FIELD);;

let NV_DIG_ALG_E = prove
 (`forall e m h. e * e = &1 ==> e * &2 / (m * h) = &2 * inv(m * (e * h))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[REAL_INV_MUL; real_div] THEN
  SUBGOAL_THEN `inv e = e` SUBST1_TAC THENL
   [MATCH_MP_TAC REAL_MUL_RINV_UNIQ THEN ASM_REWRITE_TAC[]; REAL_ARITH_TAC]);;

let NV_DIG_ODD_TERM = prove
 (`forall p k. prime p /\ ~(p = 2) /\ ~EVEN k /\ ~(p divides k)
         ==> nv_dig_fin_zp p (&2 / (&k pow 2 * nv_dig_fin_hstar k))`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `a:num` SUBST_ALL_TAC o
    REWRITE_RULE[NOT_EVEN; ODD_EXISTS; ADD1]) THEN
  REWRITE_TAC[NV_DIG_FIN_BDRY_HSTAR_ODD2] THEN
  SUBGOAL_THEN `&2 / (&(2 * a + 1) pow 2 * inv(&(2 * a + 1) * cat_c a)) =
                &2 * cat_c a * inv(&(2 * a + 1))` SUBST1_TAC THENL
   [MP_TAC(SPEC `a:num` NV_DIG_FIN_BDRY_C_POS) THEN
    SUBGOAL_THEN `~(&(2 * a + 1) = &0)` MP_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_EQ] THEN ARITH_TAC; CONV_TAC REAL_FIELD];
    ASM_SIMP_TAC[NV_DIG_FIN_ZP_MUL; NV_DIG_FIN_ZP_NUM; NV_DIG_FIN_DIG_C_ZP; NV_DIG_FIN_ZP_INV_NUM]]);;

(* ------------------------------------------------------------------------- *)
(* The two sums of the plus boundary formula.                                *)
(* ------------------------------------------------------------------------- *)

let NV_DIG_KP_SUM_EVEN = prove
 (`forall p s P r. prime p /\ 2 * s + 1 = p /\ P + 2 < p /\ r < p
   ==> nv_dig_fin_dig_cg p
        (sum(1..P * p + r)
          (\z. &p pow 2 * (if EVEN z then &2 / (&z pow 2 * nv_dig_fin_hstar z) else &0)))
        (sum(1..P) (\m. if EVEN m then &2 / (&m pow 2 * nv_dig_fin_hstar m) else &0))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(p = 0) /\ ~(&p = &0)` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_EQ] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC NV_DIG_SUMM THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THEN X_GEN_TAC `k:num` THEN STRIP_TAC THENL
   [COND_CASES_TAC THEN REWRITE_TAC[REAL_MUL_RZERO] THEN
    ASM_SIMP_TAC[NV_DIG_FIN_DIG_CG_REFL; NV_DIG_FIN_ZP_0] THEN
    SUBGOAL_THEN `~(&k = &0)` ASSUME_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_EQ] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[NV_DIG_ALG_A; NV_DIG_FIN_BDRY_HSTAR_NZ] THEN
    MATCH_MP_TAC NV_DIG_FIN_DIG_CG_PMUL THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `nv_dig_fin_zp p (&p / (&k * nv_dig_fin_hstar k))` ASSUME_TAC THENL
     [MATCH_MP_TAC NV_DIG_QZP THEN EXISTS_TAC `s:num` THEN ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL [ALL_TAC; ASM_ARITH_TAC] THEN
      MP_TAC(SPECL [`p:num`; `k:num`; `P:num`; `r:num`] NV_DIG_DIVP) THEN
      ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
      ASM_SIMP_TAC[NV_DIG_FIN_ZP_MUL; NV_DIG_FIN_ZP_NUM; NV_DIG_FIN_ZP_INV_NUM]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(EVEN (k * p) <=> EVEN k)` SUBST1_TAC THENL
   [REWRITE_TAC[EVEN_MULT] THEN FIRST_X_ASSUM(fun th ->
      REWRITE_TAC[SYM(ASSUME `2 * s + 1 = p`)]) THEN
    REWRITE_TAC[EVEN_ADD; EVEN_MULT; ARITH];
    ALL_TAC] THEN
  COND_CASES_TAC THEN REWRITE_TAC[REAL_MUL_RZERO] THEN
  ASM_SIMP_TAC[NV_DIG_FIN_DIG_CG_REFL; NV_DIG_FIN_ZP_0] THEN
  SUBGOAL_THEN `~(&k = &0)` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_EQ] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[GSYM REAL_OF_NUM_MUL; NV_DIG_ALG_B] THEN
  GEN_REWRITE_TAC RAND_CONV [real_div] THEN
  MATCH_MP_TAC NV_DIG_FIN_DIG_CG_MUL THEN ASM_SIMP_TAC[NV_DIG_FIN_DIG_CG_REFL; NV_DIG_FIN_ZP_NUM] THEN
  MP_TAC(SPECL [`p:num`; `s:num`; `k:num`] NV_DIG_HMP_EVEN) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; STRIP_TAC] THEN
  MP_TAC(ISPECL [`p:num`; `&k pow 2 * nv_dig_fin_hstar (k * p)`;
                 `&k pow 2 * nv_dig_fin_hstar k`] NV_DIG_FIN_DIG_CG_INV) THEN
  ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC NV_DIG_FIN_DIG_UNIT_MUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC NV_DIG_FIN_DIG_UNIT_POW THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC NV_DIG_FIN_DIG_UNIT_NUM_LT THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    MATCH_MP_TAC NV_DIG_FIN_DIG_CG_MUL THEN ASM_SIMP_TAC[NV_DIG_FIN_DIG_CG_REFL; NV_DIG_FIN_ZP_POW; NV_DIG_FIN_ZP_NUM]]);;

let NV_DIG_EVEN_MP = prove
 (`forall s p k. 2 * s + 1 = p ==> (EVEN (k * p) <=> EVEN k)`,
  REPEAT GEN_TAC THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[EVEN_MULT; EVEN_ADD; ARITH]);;

let NV_DIG_KP_SUM_ODD = prove
 (`forall p s P r. prime p /\ 2 * s + 1 = p /\ P + 2 < p /\ r < p
   ==> nv_dig_fin_dig_cg p
        (sum(1..P * p + r)
          (\z. &p * (if ~EVEN z then &2 / (&z pow 2 * nv_dig_fin_hstar z) else &0)))
        (sum(1..P) (\m. (--(&1)) pow s *
                        (if ~EVEN m then &2 / (&m pow 2 * nv_dig_fin_hstar m) else &0)))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(p = 0) /\ ~(&p = &0) /\ ~(p = 2)` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_EQ] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC NV_DIG_SUMM THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THEN X_GEN_TAC `k:num` THEN STRIP_TAC THENL
   [COND_CASES_TAC THEN REWRITE_TAC[REAL_MUL_RZERO] THEN
    ASM_SIMP_TAC[NV_DIG_FIN_DIG_CG_REFL; NV_DIG_FIN_ZP_0] THEN
    MATCH_MP_TAC NV_DIG_FIN_DIG_CG_PMUL THEN ASM_SIMP_TAC[NV_DIG_ODD_TERM];
    ALL_TAC] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP NV_DIG_EVEN_MP th]) THEN
  COND_CASES_TAC THEN REWRITE_TAC[REAL_MUL_RZERO] THEN
  ASM_SIMP_TAC[NV_DIG_FIN_DIG_CG_REFL; NV_DIG_FIN_ZP_0] THEN
  SUBGOAL_THEN `~(&k = &0)` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_EQ] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[GSYM REAL_OF_NUM_MUL; NV_DIG_ALG_D; NV_DIG_ALG_E; NV_DIG_EPS2] THEN
  MATCH_MP_TAC NV_DIG_FIN_DIG_CG_MUL THEN ASM_SIMP_TAC[NV_DIG_FIN_DIG_CG_REFL; NV_DIG_FIN_ZP_NUM] THEN
  MP_TAC(SPECL [`p:num`; `s:num`; `k:num`] NV_DIG_HMP_ODD) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[GSYM NOT_EVEN] THEN ASM_ARITH_TAC; STRIP_TAC] THEN
  MP_TAC(ISPECL [`p:num`; `&k pow 2 * &p * nv_dig_fin_hstar (k * p)`;
                 `&k pow 2 * (--(&1)) pow s * nv_dig_fin_hstar k`] NV_DIG_FIN_DIG_CG_INV) THEN
  ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC NV_DIG_FIN_DIG_UNIT_MUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC NV_DIG_FIN_DIG_UNIT_POW THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC NV_DIG_FIN_DIG_UNIT_NUM_LT THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    MATCH_MP_TAC NV_DIG_FIN_DIG_CG_MUL THEN ASM_SIMP_TAC[NV_DIG_FIN_DIG_CG_REFL; NV_DIG_FIN_ZP_POW; NV_DIG_FIN_ZP_NUM]]);;

let NV_DIG_SMALL_UNITS = prove
 (`forall p z. prime p /\ ~(p = 2) /\ 0 < z /\ z < p
         ==> nv_dig_fin_dig_unit p (&z) /\ nv_dig_fin_dig_unit p (nv_dig_fin_hstar z)`,
  SIMP_TAC[NV_DIG_FIN_DIG_UNIT_NUM_LT; NV_DIG_HSTAR_SMALL]);;

let NV_DIG_ZP_DIV_UNIT = prove
 (`forall p x u. prime p /\ nv_dig_fin_zp p x /\ nv_dig_fin_dig_unit p u ==> nv_dig_fin_zp p (x / u)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[real_div] THEN MATCH_MP_TAC NV_DIG_FIN_ZP_MUL THEN
  ASM_SIMP_TAC[NV_DIG_UNIT_INV_ZP]);;

let NV_DIG_KP_SMALL = prove
 (`forall p P. prime p /\ ~(p = 2) /\ P < p ==> nv_dig_fin_zp p (cat_kplus (P + 1))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[NV_DIG_FIN_BDRY_KPLUS] THEN
  MATCH_MP_TAC NV_DIG_FIN_ZP_MUL THEN ASM_SIMP_TAC[NV_DIG_HSTAR_SMALL; NV_DIG_FIN_DIG_UNIT_ZP] THEN
  MATCH_MP_TAC NV_DIG_FIN_ZP_SUM THEN ASM_REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
  X_GEN_TAC `z:num` THEN STRIP_TAC THEN COND_CASES_TAC THEN ASM_SIMP_TAC[NV_DIG_FIN_ZP_0] THEN
  MP_TAC(SPECL [`p:num`; `z:num`] NV_DIG_SMALL_UNITS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; STRIP_TAC] THEN
  MATCH_MP_TAC NV_DIG_ZP_DIV_UNIT THEN ASM_SIMP_TAC[NV_DIG_FIN_ZP_NUM] THEN
  MATCH_MP_TAC NV_DIG_FIN_DIG_UNIT_MUL THEN ASM_SIMP_TAC[NV_DIG_FIN_DIG_UNIT_POW]);;

let NV_DIG_KP_FIN = prove
 (`forall p s P r. prime p /\ 2 * s + 1 = p /\ P + 2 < p /\ r < p
     ==> nv_dig_fin_zp p (cat_kplus (P + 1)) /\
         nv_dig_fin_dig_cg p (&p pow 2 * cat_kplus ((P * p + r) + 1))
                      (nv_E r * cat_kplus (P + 1))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(p = 2) /\ P < p:num` STRIP_ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [ASM_SIMP_TAC[NV_DIG_KP_SMALL]; ALL_TAC] THEN
  MP_TAC(SPECL [`p:num`; `s:num`; `P:num`; `r:num`] NV_DIG_KP_SUM_EVEN) THEN
  MP_TAC(SPECL [`p:num`; `s:num`; `P:num`; `r:num`] NV_DIG_KP_SUM_ODD) THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
  REWRITE_TAC[NV_DIG_FIN_BDRY_KPLUS; nv_E] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP NV_DIG_PAR th]) THEN
  ASM_CASES_TAC `EVEN r` THEN ASM_CASES_TAC `EVEN P` THEN
  ASM_REWRITE_TAC[REAL_MUL_LZERO] THENL
   [MATCH_MP_TAC NV_DIG_FIN_DIG_CG_EQ THEN
    MAP_EVERY EXISTS_TAC
     [`nv_dig_fin_hstar (P * p + r) *
       sum(1..P * p + r) (\z. &p pow 2 *
           (if EVEN z then &2 / (&z pow 2 * nv_dig_fin_hstar z) else &0))`;
      `(nv_dig_fin_hstar P * cat_c (r DIV 2)) *
       sum(1..P) (\z. if EVEN z then &2 / (&z pow 2 * nv_dig_fin_hstar z) else &0)`] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC NV_DIG_FIN_DIG_CG_MUL THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(SPECL [`p:num`; `s:num`; `P:num`; `r:num`] NV_DIG_HA) THEN
      ASM_SIMP_TAC[];
      REWRITE_TAC[SUM_LMUL] THEN REAL_ARITH_TAC;
      REAL_ARITH_TAC];
    MATCH_MP_TAC NV_DIG_FIN_DIG_CG_EQ THEN
    MAP_EVERY EXISTS_TAC
     [`(&p * nv_dig_fin_hstar (P * p + r)) *
       sum(1..P * p + r) (\z. &p *
           (if ~EVEN z then &2 / (&z pow 2 * nv_dig_fin_hstar z) else &0))`;
      `((--(&1)) pow s * cat_c (r DIV 2) * nv_dig_fin_hstar P) *
       sum(1..P) (\z. (--(&1)) pow s *
           (if ~EVEN z then &2 / (&z pow 2 * nv_dig_fin_hstar z) else &0))`] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC NV_DIG_FIN_DIG_CG_MUL THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(SPECL [`p:num`; `s:num`; `P:num`; `r:num`] NV_DIG_HCR) THEN
      ASM_SIMP_TAC[GSYM NOT_EVEN];
      REWRITE_TAC[SUM_LMUL] THEN REAL_ARITH_TAC;
      REWRITE_TAC[SUM_LMUL] THEN MP_TAC(SPEC `s:num` NV_DIG_EPS2) THEN
      CONV_TAC REAL_RING];
    MATCH_MP_TAC NV_DIG_FIN_DIG_CG_EQ THEN
    MAP_EVERY EXISTS_TAC
     [`(&p * nv_dig_fin_hstar (P * p + r)) *
       sum(1..P * p + r) (\z. &p *
           (if ~EVEN z then &2 / (&z pow 2 * nv_dig_fin_hstar z) else &0))`; `&0`] THEN
    REPEAT CONJ_TAC THENL
     [ALL_TAC; REWRITE_TAC[SUM_LMUL] THEN REAL_ARITH_TAC; REFL_TAC] THEN
    MP_TAC(ISPECL [`p:num`; `&p * nv_dig_fin_hstar (P * p + r)`;
       `sum(1..P * p + r) (\z. &p *
           (if ~EVEN z then &2 / (&z pow 2 * nv_dig_fin_hstar z) else &0))`]
       NV_DIG_FIN_DIG_CG_ZERO_MUL) THEN
    ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC NV_DIG_FIN_DIG_CG_PMUL THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(SPECL [`p:num`; `s:num`; `P:num`; `r:num`] NV_DIG_HB) THEN
      ASM_SIMP_TAC[GSYM NOT_EVEN; NV_DIG_FIN_DIG_UNIT_ZP];
      ASM_MESON_TAC[NV_DIG_FIN_DIG_CG_ZP]];
    MATCH_MP_TAC NV_DIG_FIN_DIG_CG_EQ THEN
    MAP_EVERY EXISTS_TAC
     [`nv_dig_fin_hstar (P * p + r) *
       sum(1..P * p + r) (\z. &p pow 2 *
           (if EVEN z then &2 / (&z pow 2 * nv_dig_fin_hstar z) else &0))`; `&0`] THEN
    REPEAT CONJ_TAC THENL
     [ALL_TAC; REWRITE_TAC[SUM_LMUL] THEN REAL_ARITH_TAC; REFL_TAC] THEN
    MP_TAC(ISPECL [`p:num`; `nv_dig_fin_hstar (P * p + r)`;
       `sum(1..P * p + r) (\z. &p pow 2 *
           (if EVEN z then &2 / (&z pow 2 * nv_dig_fin_hstar z) else &0))`]
       NV_DIG_FIN_DIG_CG_ZERO_MUL) THEN
    ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC NV_DIG_H0 THEN EXISTS_TAC `s:num` THEN
      ASM_REWRITE_TAC[GSYM NOT_EVEN];
      ASM_MESON_TAC[NV_DIG_FIN_DIG_CG_ZP]]]);;

(* ------------------------------------------------------------------------- *)
(* The minus boundary formula.                                               *)
(* ------------------------------------------------------------------------- *)

let nv_dig_fe = new_definition
 `nv_dig_fe z = if EVEN z then &2 / (&z pow 2 * nv_dig_fin_hstar z pow 2) else &0`;;

let nv_dig_g = new_definition
 `nv_dig_g p z = &p pow 2 * nv_dig_fe z`;;

let NV_DIG_KM_EVEN = prove
 (`forall u. EVEN u ==> cat_kminus u = nv_dig_fin_hstar u * sum(1..u) nv_dig_fe`,
  GEN_TAC THEN DISCH_TAC THEN ASM_SIMP_TAC[NV_DIG_FIN_BDRY_KMINUS_EVEN] THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM; nv_dig_fe]);;

let NV_DIG_G_SUM = prove
 (`forall p s. sum s (nv_dig_g p) = &p pow 2 * sum s nv_dig_fe`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM SUM_LMUL] THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM; nv_dig_g]);;

let NV_DIG_G_EVEN = prove
 (`forall p z. EVEN z /\ ~(z = 0)
         ==> nv_dig_g p z = &2 * (&p / (&z * nv_dig_fin_hstar z)) pow 2`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[nv_dig_g; nv_dig_fe] THEN
  MP_TAC(SPEC `z:num` NV_DIG_FIN_BDRY_HSTAR_NZ) THEN
  SUBGOAL_THEN `~(&z = &0)` MP_TAC THENL
   [ASM_REWRITE_TAC[REAL_OF_NUM_EQ]; CONV_TAC REAL_FIELD]);;

let NV_DIG_G_ODD = prove
 (`forall p z. ~EVEN z ==> nv_dig_g p z = &0`,
  SIMP_TAC[nv_dig_g; nv_dig_fe; REAL_MUL_RZERO]);;

let NV_DIG_CG_SQ2 = prove
 (`forall p x y. prime p /\ nv_dig_fin_dig_cg p x y ==> nv_dig_fin_dig_cg p (&2 * x pow 2) (&2 * y pow 2)`,
  SIMP_TAC[NV_DIG_FIN_DIG_CG_MUL; NV_DIG_FIN_DIG_CG_POW; NV_DIG_FIN_DIG_CG_REFL; NV_DIG_FIN_ZP_NUM]);;

let NV_DIG_KM_T0 = prove
 (`forall p s A t. prime p /\ 2 * s + 1 = p /\ A + 2 < p /\ EVEN A /\ 0 < t /\ t < p
             ==> nv_dig_fin_dig_cg p (nv_dig_g p (A * p + t)) (&0)`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `EVEN (A * p + t)` THENL
   [ALL_TAC; ASM_SIMP_TAC[NV_DIG_G_ODD; NV_DIG_FIN_DIG_CG_REFL; NV_DIG_FIN_ZP_0]] THEN
  SUBGOAL_THEN `EVEN t` ASSUME_TAC THENL
   [ASM_MESON_TAC[NV_DIG_PAR]; ALL_TAC] THEN
  ASM_SIMP_TAC[NV_DIG_G_EVEN; ARITH_RULE `0 < t ==> ~(A * p + t = 0)`] THEN
  MATCH_MP_TAC NV_DIG_FIN_DIG_CG_EQ THEN
  MAP_EVERY EXISTS_TAC [`&2 * (&p / (&(A * p + t) * nv_dig_fin_hstar (A * p + t))) pow 2`;
                        `&2 * &0 pow 2`] THEN
  CONJ_TAC THENL [ALL_TAC; REAL_ARITH_TAC] THEN
  MATCH_MP_TAC NV_DIG_CG_SQ2 THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC NV_DIG_Q0 THEN EXISTS_TAC `s:num` THEN ASM_REWRITE_TAC[]);;

let NV_DIG_PAR_K = prove
 (`forall s p K t. 2 * s + 1 = p ==> (EVEN ((2 * K + 1) * p + t) <=> ~EVEN t)`,
  REPEAT GEN_TAC THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[EVEN_ADD; EVEN_MULT; ARITH]);;

let NV_DIG_KM_TB = prove
 (`forall p s K t. prime p /\ 2 * s + 1 = p /\ 2 * K + 4 < p /\ 1 <= t /\ t <= p
     ==> nv_dig_fin_dig_cg p (nv_dig_g p ((2 * K + 1) * p + t))
           (if ODD t then &2 * (cat_c ((p - t) DIV 2) * nv_dig_fin_hstar (2 * K + 1)) pow 2
            else &0)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `EVEN ((2 * K + 1) * p + t) <=> ~EVEN t` ASSUME_TAC THENL
   [ASM_MESON_TAC[NV_DIG_PAR_K]; ALL_TAC] THEN
  REWRITE_TAC[GSYM NOT_EVEN] THEN
  ASM_CASES_TAC `EVEN t` THENL
   [ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `~EVEN ((2 * K + 1) * p + t)` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[NV_DIG_G_ODD; NV_DIG_FIN_DIG_CG_REFL; NV_DIG_FIN_ZP_0];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `EVEN ((2 * K + 1) * p + t)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[NV_DIG_G_EVEN; ARITH_RULE `1 <= t ==> ~(A * p + t = 0)`] THEN
  MATCH_MP_TAC NV_DIG_CG_SQ2 THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `t:num = p` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    REWRITE_TAC[SUB_REFL; NUM_REDUCE_CONV `0 DIV 2`; NV_DIG_FIN_BDRY_C_0; REAL_MUL_LID] THEN
    REWRITE_TAC[ARITH_RULE `(2 * K + 1) * p + p = (2 * K + 2) * p`] THEN
    MP_TAC(SPECL [`p:num`; `s:num`; `2 * K + 2`] NV_DIG_QA) THEN
    ASM_REWRITE_TAC[EVEN_ADD; EVEN_MULT; ARITH] THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[ARITH_RULE `(2 * K + 2) - 1 = 2 * K + 1`];
    MP_TAC(SPECL [`p:num`; `s:num`; `2 * K + 1`; `t:num`] NV_DIG_HD) THEN
    ASM_REWRITE_TAC[ODD_ADD; ODD_MULT; ARITH; GSYM NOT_EVEN] THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; SIMP_TAC[]]]);;

let NV_DIG_SUM_SHIFT = prove
 (`forall f c n. sum(c + 1..c + n) f = sum(1..n) (\i. f(c + i))`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `c + 1 = 1 + (c:num) /\ c + n = n + (c:num)` (fun th -> REWRITE_TAC[th]) THENL
   [ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[SUM_OFFSET] THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[] THEN AP_TERM_TAC THEN ARITH_TAC);;

let NV_DIG_KM_BLOCK = prove
 (`forall p s K. prime p /\ 2 * s + 1 = p /\ 2 * K + 4 < p
   ==> nv_dig_fin_dig_cg p (sum(2 * K * p + 1..2 * K * p + 2 * p) (nv_dig_g p))
                    ((--(&1)) pow s * (&2 * nv_dig_fin_hstar (2 * K + 1) pow 2))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(p = 2) /\ (p - 1) DIV 2 = s` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[NV_DIG_PS]; ALL_TAC] THEN
  REWRITE_TAC[ARITH_RULE `2 * K * p + 2 * p = (2 * K * p + p) + p`] THEN
  MP_TAC(ISPECL [`nv_dig_g p`; `2 * K * p + 1`; `2 * K * p + p:num`; `p:num`]
    SUM_ADD_SPLIT) THEN
  REWRITE_TAC[ARITH_RULE `2 * K * p + 1 <= (2 * K * p + p) + 1`] THEN
  DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC NV_DIG_FIN_DIG_CG_EQ THEN
  MAP_EVERY EXISTS_TAC
   [`sum(2 * K * p + 1..2 * K * p + p) (nv_dig_g p) +
     sum((2 * K * p + p) + 1..(2 * K * p + p) + p) (nv_dig_g p)`;
    `&0 + (--(&1)) pow s * (&2 * nv_dig_fin_hstar (2 * K + 1) pow 2)`] THEN
  REPEAT CONJ_TAC THENL [ALL_TAC; REFL_TAC; REAL_ARITH_TAC] THEN
  MATCH_MP_TAC NV_DIG_FIN_DIG_CG_ADD THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [SUBGOAL_THEN `&0 = sum(2 * K * p + 1..2 * K * p + p) (\z. &0)` SUBST1_TAC THENL
     [REWRITE_TAC[SUM_0]; ALL_TAC] THEN
    MATCH_MP_TAC NV_DIG_FIN_DIG_CG_SUM THEN ASM_REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
    X_GEN_TAC `z:num` THEN STRIP_TAC THEN BETA_TAC THEN
    ASM_CASES_TAC `z = 2 * K * p + p` THENL
     [FIRST_X_ASSUM SUBST1_TAC THEN
      SUBGOAL_THEN `~EVEN (2 * K * p + p)` ASSUME_TAC THENL
       [FIRST_X_ASSUM(fun th -> REWRITE_TAC[SYM(ASSUME `2 * s + 1 = p`)]) THEN
        REWRITE_TAC[EVEN_ADD; EVEN_MULT; ARITH];
        ASM_SIMP_TAC[NV_DIG_G_ODD; NV_DIG_FIN_DIG_CG_REFL; NV_DIG_FIN_ZP_0]];
      ALL_TAC] THEN
    SUBGOAL_THEN `z = (2 * K) * p + (z - 2 * K * p:num)` SUBST1_TAC THENL
     [REWRITE_TAC[GSYM MULT_ASSOC] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC NV_DIG_KM_T0 THEN EXISTS_TAC `s:num` THEN
    ASM_REWRITE_TAC[EVEN_DOUBLE] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[NV_DIG_SUM_SHIFT] THEN
  MATCH_MP_TAC NV_DIG_FIN_DIG_CG_TRANS THEN
  EXISTS_TAC `sum(1..p) (\t. if ODD t
                            then &2 * (cat_c ((p - t) DIV 2) * nv_dig_fin_hstar (2 * K + 1)) pow 2
                            else &0)` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC NV_DIG_FIN_DIG_CG_SUM THEN ASM_REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
    X_GEN_TAC `t:num` THEN STRIP_TAC THEN BETA_TAC THEN
    SUBGOAL_THEN `(2 * K * p + p) + t = (2 * K + 1) * p + t:num` SUBST1_TAC THENL
     [ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC NV_DIG_KM_TB THEN EXISTS_TAC `s:num` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`s:num`; `\j. &2 * (cat_c j * nv_dig_fin_hstar (2 * K + 1)) pow 2`]
    NV_DIG_ODDSUM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN `sum(0..s) (\j. &2 * (cat_c j * nv_dig_fin_hstar (2 * K + 1)) pow 2) =
                (&2 * nv_dig_fin_hstar (2 * K + 1) pow 2) * sum(0..s) (\j. cat_c j pow 2)`
  SUBST1_TAC THENL
   [REWRITE_TAC[GSYM SUM_LMUL] THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN
    REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC NV_DIG_FIN_DIG_CG_EQ THEN
  MAP_EVERY EXISTS_TAC
   [`(&2 * nv_dig_fin_hstar (2 * K + 1) pow 2) * sum(0..s) (\j. cat_c j pow 2)`;
    `(&2 * nv_dig_fin_hstar (2 * K + 1) pow 2) * (--(&1)) pow s`] THEN
  REPEAT CONJ_TAC THENL [ALL_TAC; REFL_TAC; REAL_ARITH_TAC] THEN
  MATCH_MP_TAC NV_DIG_FIN_DIG_CG_MUL THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC NV_DIG_FIN_DIG_CG_REFL THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(SPECL [`p:num`; `2 * K + 1`] NV_DIG_HSTAR_SMALL) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[NV_DIG_FIN_DIG_UNIT_ZP; NV_DIG_FIN_ZP_MUL; NV_DIG_FIN_ZP_POW; NV_DIG_FIN_ZP_NUM];
    MP_TAC(SPEC `p:num` NV_DIG_FIN_DIG_C_SQSUM) THEN ASM_REWRITE_TAC[]]);;

let NV_DIG_FE_ODD = prove
 (`forall K. nv_dig_fe (2 * K + 1) = &0`,
  REWRITE_TAC[nv_dig_fe; EVEN_ADD; EVEN_MULT; ARITH]);;

let NV_DIG_FE_EVEN = prove
 (`forall K. nv_dig_fe (2 * K + 2) = &2 * nv_dig_fin_hstar (2 * K + 1) pow 2`,
  GEN_TAC THEN REWRITE_TAC[nv_dig_fe; EVEN_ADD; EVEN_MULT; ARITH; NV_DIG_HSTAR_PAIR] THEN
  MP_TAC(SPEC `2 * K + 2` NV_DIG_FIN_BDRY_HSTAR_NZ) THEN
  SUBGOAL_THEN `~(&(2 * K + 2) = &0)` MP_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_EQ] THEN ARITH_TAC; CONV_TAC REAL_FIELD]);;

let NV_DIG_KM_IND = prove
 (`forall p s. prime p /\ 2 * s + 1 = p
         ==> forall K. 2 * K + 2 < p
                 ==> nv_dig_fin_dig_cg p (sum(1..2 * K * p) (nv_dig_g p))
                                  ((--(&1)) pow s * sum(1..2 * K) nv_dig_fe)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN INDUCT_TAC THENL
   [DISCH_TAC THEN REWRITE_TAC[MULT_CLAUSES; SUM_CLAUSES_NUMSEG; ARITH; REAL_MUL_RZERO] THEN
    ASM_SIMP_TAC[NV_DIG_FIN_DIG_CG_REFL; NV_DIG_FIN_ZP_0];
    ALL_TAC] THEN
  DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_TAC] THEN
  SUBGOAL_THEN `2 * SUC K * p = 2 * K * p + 2 * p /\ 2 * SUC K = 2 * K + 2`
    (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[ADD1] THEN CONV_TAC NUM_RING; ALL_TAC] THEN
  REWRITE_TAC[NV_DIG_FIN_BDRY_SUM_STEP2; NV_DIG_FE_ODD; NV_DIG_FE_EVEN] THEN
  MP_TAC(ISPECL [`nv_dig_g p`; `1:num`; `2 * K * p:num`; `2 * p:num`] SUM_ADD_SPLIT) THEN
  REWRITE_TAC[ARITH_RULE `1 <= 2 * K * p + 1`] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC NV_DIG_FIN_DIG_CG_EQ THEN
  MAP_EVERY EXISTS_TAC
   [`sum(1..2 * K * p) (nv_dig_g p) + sum(2 * K * p + 1..2 * K * p + 2 * p) (nv_dig_g p)`;
    `(--(&1)) pow s * sum(1..2 * K) nv_dig_fe +
     (--(&1)) pow s * (&2 * nv_dig_fin_hstar (2 * K + 1) pow 2)`] THEN
  REPEAT CONJ_TAC THENL [ALL_TAC; REFL_TAC; REAL_ARITH_TAC] THEN
  MATCH_MP_TAC NV_DIG_FIN_DIG_CG_ADD THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC NV_DIG_KM_BLOCK THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

let NV_DIG_KM_SUM_EVEN = prove
 (`forall p s P r. prime p /\ 2 * s + 1 = p /\ P + 2 < p /\ EVEN P /\ r < p
   ==> nv_dig_fin_dig_cg p (sum(1..P * p + r) (nv_dig_g p))
                    ((--(&1)) pow s * sum(1..P) nv_dig_fe)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`nv_dig_g p`; `1:num`; `P * p:num`; `r:num`] SUM_ADD_SPLIT) THEN
  REWRITE_TAC[ARITH_RULE `1 <= P * p + 1`] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC NV_DIG_FIN_DIG_CG_EQ THEN
  MAP_EVERY EXISTS_TAC
   [`sum(1..P * p) (nv_dig_g p) + sum(P * p + 1..P * p + r) (nv_dig_g p)`;
    `(--(&1)) pow s * sum(1..P) nv_dig_fe + &0`] THEN
  REPEAT CONJ_TAC THENL [ALL_TAC; REFL_TAC; REAL_ARITH_TAC] THEN
  MATCH_MP_TAC NV_DIG_FIN_DIG_CG_ADD THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [FIRST_X_ASSUM(X_CHOOSE_THEN `K:num` SUBST_ALL_TAC o REWRITE_RULE[EVEN_EXISTS]) THEN
    REWRITE_TAC[GSYM MULT_ASSOC] THEN
    MP_TAC(SPECL [`p:num`; `s:num`] NV_DIG_KM_IND) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 = sum(P * p + 1..P * p + r) (\z. &0)` SUBST1_TAC THENL
   [REWRITE_TAC[SUM_0]; ALL_TAC] THEN
  MATCH_MP_TAC NV_DIG_FIN_DIG_CG_SUM THEN ASM_REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
  X_GEN_TAC `z:num` THEN STRIP_TAC THEN BETA_TAC THEN
  SUBGOAL_THEN `z = P * p + (z - P * p:num)` SUBST1_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC NV_DIG_KM_T0 THEN EXISTS_TAC `s:num` THEN
  ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

let NV_DIG_KM_SUM_EVEN_ZP = prove
 (`forall p s P r. prime p /\ 2 * s + 1 = p /\ P + 2 < p /\ r < p
   ==> nv_dig_fin_zp p (sum(1..P * p + r) (nv_dig_g p))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC NV_DIG_FIN_ZP_SUM THEN
  ASM_REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
  X_GEN_TAC `z:num` THEN STRIP_TAC THEN
  ASM_CASES_TAC `EVEN z` THENL [ALL_TAC; ASM_SIMP_TAC[NV_DIG_G_ODD; NV_DIG_FIN_ZP_0]] THEN
  ASM_SIMP_TAC[NV_DIG_G_EVEN; ARITH_RULE `1 <= z ==> ~(z = 0)`] THEN
  MATCH_MP_TAC NV_DIG_FIN_ZP_MUL THEN ASM_SIMP_TAC[NV_DIG_FIN_ZP_NUM] THEN
  MATCH_MP_TAC NV_DIG_FIN_ZP_POW THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC NV_DIG_QZP THEN EXISTS_TAC `s:num` THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [ALL_TAC; ASM_ARITH_TAC] THEN
  MP_TAC(SPECL [`p:num`; `z:num`; `P:num`; `r:num`] NV_DIG_DIVP) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN ASM_ARITH_TAC);;

let NV_DIG_KM_SUM_ODD = prove
 (`forall p s P r. prime p /\ 2 * s + 1 = p /\ P + 2 < p /\ r < p
   ==> nv_dig_fin_dig_cg p (sum(1..P * p + r) (\z. &p * (if ODD z then &2 / &z else &0)))
                    (sum(1..P) (\z. if ODD z then &2 / &z else &0))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(p = 0) /\ ~(&p = &0)` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_EQ] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC NV_DIG_SUMM THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THEN X_GEN_TAC `k:num` THEN STRIP_TAC THENL
   [COND_CASES_TAC THEN REWRITE_TAC[REAL_MUL_RZERO] THEN
    ASM_SIMP_TAC[NV_DIG_FIN_DIG_CG_REFL; NV_DIG_FIN_ZP_0] THEN
    MATCH_MP_TAC NV_DIG_FIN_DIG_CG_PMUL THEN ASM_SIMP_TAC[NV_DIG_FIN_ZP_DIV_NUM; NV_DIG_FIN_ZP_NUM];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM NOT_EVEN] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP NV_DIG_EVEN_MP th]) THEN
  COND_CASES_TAC THEN REWRITE_TAC[REAL_MUL_RZERO] THENL
   [ALL_TAC; ASM_SIMP_TAC[NV_DIG_FIN_DIG_CG_REFL; NV_DIG_FIN_ZP_0]] THEN
  SUBGOAL_THEN `&p * &2 / &(k * p) = &2 / &k` SUBST1_TAC THENL
   [SUBGOAL_THEN `~(&k = &0)` MP_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_EQ] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `~(&p = &0)` THEN REWRITE_TAC[GSYM REAL_OF_NUM_MUL] THEN
    CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  MATCH_MP_TAC NV_DIG_FIN_DIG_CG_REFL THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC NV_DIG_FIN_ZP_DIV_NUM THEN ASM_SIMP_TAC[NV_DIG_FIN_ZP_NUM] THEN
  MATCH_MP_TAC NV_DIG_NDIV_LT THEN ASM_ARITH_TAC);;

let NV_DIG_UNIT_TAC =
  REPEAT(FIRST [FIRST_ASSUM ACCEPT_TAC; CONJ_TAC;
                MATCH_MP_TAC NV_DIG_FIN_DIG_UNIT_MUL; MATCH_MP_TAC NV_DIG_FIN_DIG_UNIT_POW]);;

let NV_DIG_KM_SMALL = prove
 (`forall p P. prime p /\ ~(p = 2) /\ P < p ==> nv_dig_fin_zp p (cat_kminus P)`,
  REPEAT STRIP_TAC THEN DISJ_CASES_TAC(SPEC `P:num` EVEN_OR_ODD) THEN
  ASM_SIMP_TAC[NV_DIG_FIN_BDRY_KMINUS_EVEN; NV_DIG_FIN_BDRY_KMINUS_ODD] THEN
  MATCH_MP_TAC NV_DIG_FIN_ZP_MUL THEN ASM_SIMP_TAC[NV_DIG_HSTAR_SMALL; NV_DIG_FIN_DIG_UNIT_ZP] THEN
  MATCH_MP_TAC NV_DIG_FIN_ZP_SUM THEN ASM_REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
  X_GEN_TAC `z:num` THEN STRIP_TAC THEN COND_CASES_TAC THEN ASM_SIMP_TAC[NV_DIG_FIN_ZP_0] THEN
  MP_TAC(SPECL [`p:num`; `z:num`] NV_DIG_SMALL_UNITS) THEN
  (ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; STRIP_TAC]) THEN
  MATCH_MP_TAC NV_DIG_ZP_DIV_UNIT THEN ASM_SIMP_TAC[NV_DIG_FIN_ZP_NUM] THEN
  NV_DIG_UNIT_TAC);;

let NV_DIG_KM_FIN = prove
 (`forall p s P r. prime p /\ 2 * s + 1 = p /\ P + 2 < p /\ r < p
     ==> nv_dig_fin_zp p (cat_kminus P) /\
         nv_dig_fin_dig_cg p (&p pow 2 * cat_kminus (P * p + r))
                      (nv_E (p - 1 - r) * cat_kminus P)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(p = 2) /\ P < p:num` STRIP_ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `nv_dig_fin_zp p (cat_kminus P)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[NV_DIG_KM_SMALL]; ASM_REWRITE_TAC[]] THEN
  MP_TAC(SPECL [`s:num`; `p:num`; `r:num`] NV_DIG_E_PM1) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN `EVEN (P * p + r) <=> (EVEN P <=> EVEN r)` ASSUME_TAC THENL
   [ASM_MESON_TAC[NV_DIG_PAR]; ALL_TAC] THEN
  ASM_CASES_TAC `EVEN r` THEN ASM_CASES_TAC `EVEN P` THEN
  ASM_REWRITE_TAC[REAL_MUL_LZERO] THENL
   [(* u, P, r even *)
    SUBGOAL_THEN `EVEN (P * p + r)` ASSUME_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `nv_dig_fin_zp p (cat_kminus P)` THEN
    ASM_SIMP_TAC[NV_DIG_KM_EVEN] THEN DISCH_TAC THEN
    MATCH_MP_TAC NV_DIG_FIN_DIG_CG_TRANS THEN
    EXISTS_TAC `(nv_dig_fin_hstar P * cat_c (r DIV 2)) *
                ((--(&1)) pow s * sum(1..P) nv_dig_fe)` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC NV_DIG_FIN_DIG_CG_EQ THEN
      MAP_EVERY EXISTS_TAC
       [`nv_dig_fin_hstar (P * p + r) * sum(1..P * p + r) (nv_dig_g p)`;
        `(nv_dig_fin_hstar P * cat_c (r DIV 2)) * ((--(&1)) pow s * sum(1..P) nv_dig_fe)`] THEN
      REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC NV_DIG_FIN_DIG_CG_MUL THEN ASM_SIMP_TAC[NV_DIG_KM_SUM_EVEN] THEN
        MP_TAC(SPECL [`p:num`; `s:num`; `P:num`; `r:num`] NV_DIG_HA) THEN
        ASM_SIMP_TAC[];
        REWRITE_TAC[NV_DIG_G_SUM] THEN REAL_ARITH_TAC;
        REFL_TAC];
      MATCH_MP_TAC NV_DIG_FIN_DIG_CG_SYM THEN MATCH_MP_TAC NV_DIG_FIN_DIG_CG_EQ THEN
      MAP_EVERY EXISTS_TAC
       [`cat_c ((p - 1 - r) DIV 2) * (nv_dig_fin_hstar P * sum(1..P) nv_dig_fe)`;
        `((--(&1)) pow s * cat_c (r DIV 2)) * (nv_dig_fin_hstar P * sum(1..P) nv_dig_fe)`] THEN
      REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC NV_DIG_FIN_DIG_CG_MUL THEN ASM_SIMP_TAC[NV_DIG_CREFL; NV_DIG_FIN_DIG_CG_REFL];
        REFL_TAC; REAL_ARITH_TAC]];
    (* r even, P odd: u odd *)
    SUBGOAL_THEN `ODD (P * p + r) /\ ODD P` STRIP_ASSUME_TAC THENL
     [ASM_REWRITE_TAC[GSYM NOT_EVEN]; ALL_TAC] THEN
    UNDISCH_TAC `nv_dig_fin_zp p (cat_kminus P)` THEN
    ASM_SIMP_TAC[NV_DIG_FIN_BDRY_KMINUS_ODD] THEN DISCH_TAC THEN
    MATCH_MP_TAC NV_DIG_FIN_DIG_CG_TRANS THEN
    EXISTS_TAC `((--(&1)) pow s * cat_c (r DIV 2) * nv_dig_fin_hstar P) *
                sum(1..P) (\z. if ODD z then &2 / &z else &0)` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC NV_DIG_FIN_DIG_CG_EQ THEN
      MAP_EVERY EXISTS_TAC
       [`(&p * nv_dig_fin_hstar (P * p + r)) *
         sum(1..P * p + r) (\z. &p * (if ODD z then &2 / &z else &0))`;
        `((--(&1)) pow s * cat_c (r DIV 2) * nv_dig_fin_hstar P) *
         sum(1..P) (\z. if ODD z then &2 / &z else &0)`] THEN
      REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC NV_DIG_FIN_DIG_CG_MUL THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
         [MP_TAC(SPECL [`p:num`; `s:num`; `P:num`; `r:num`] NV_DIG_HCR) THEN
          ASM_SIMP_TAC[];
          MP_TAC(SPECL [`p:num`; `s:num`; `P:num`; `r:num`] NV_DIG_KM_SUM_ODD) THEN
          ASM_REWRITE_TAC[]];
        REWRITE_TAC[SUM_LMUL] THEN REAL_ARITH_TAC;
        REFL_TAC];
      MATCH_MP_TAC NV_DIG_FIN_DIG_CG_SYM THEN MATCH_MP_TAC NV_DIG_FIN_DIG_CG_EQ THEN
      MAP_EVERY EXISTS_TAC
       [`cat_c ((p - 1 - r) DIV 2) *
         (nv_dig_fin_hstar P * sum(1..P) (\z. if ODD z then &2 / &z else &0))`;
        `((--(&1)) pow s * cat_c (r DIV 2)) *
         (nv_dig_fin_hstar P * sum(1..P) (\z. if ODD z then &2 / &z else &0))`] THEN
      REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC NV_DIG_FIN_DIG_CG_MUL THEN ASM_SIMP_TAC[NV_DIG_CREFL; NV_DIG_FIN_DIG_CG_REFL];
        REFL_TAC; REAL_ARITH_TAC]];
    (* r odd, P even: u odd *)
    SUBGOAL_THEN `ODD (P * p + r) /\ ODD r` STRIP_ASSUME_TAC THENL
     [ASM_REWRITE_TAC[GSYM NOT_EVEN]; ALL_TAC] THEN
    ASM_SIMP_TAC[NV_DIG_FIN_BDRY_KMINUS_ODD] THEN
    MATCH_MP_TAC NV_DIG_FIN_DIG_CG_EQ THEN
    MAP_EVERY EXISTS_TAC
     [`(&p * nv_dig_fin_hstar (P * p + r)) *
       sum(1..P * p + r) (\z. &p * (if ODD z then &2 / &z else &0))`; `&0`] THEN
    REPEAT CONJ_TAC THENL
     [ALL_TAC; REWRITE_TAC[SUM_LMUL] THEN REAL_ARITH_TAC; REFL_TAC] THEN
    MP_TAC(ISPECL [`p:num`; `&p * nv_dig_fin_hstar (P * p + r)`;
       `sum(1..P * p + r) (\z. &p * (if ODD z then &2 / &z else &0))`]
       NV_DIG_FIN_DIG_CG_ZERO_MUL) THEN
    ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC NV_DIG_FIN_DIG_CG_PMUL THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(SPECL [`p:num`; `s:num`; `P:num`; `r:num`] NV_DIG_HB) THEN
      ASM_SIMP_TAC[NV_DIG_FIN_DIG_UNIT_ZP];
      MP_TAC(SPECL [`p:num`; `s:num`; `P:num`; `r:num`] NV_DIG_KM_SUM_ODD) THEN
      ASM_MESON_TAC[NV_DIG_FIN_DIG_CG_ZP]];
    (* r odd, P odd: u even *)
    SUBGOAL_THEN `EVEN (P * p + r) /\ ODD r /\ ODD P` STRIP_ASSUME_TAC THENL
     [ASM_REWRITE_TAC[GSYM NOT_EVEN]; ALL_TAC] THEN
    ASM_SIMP_TAC[NV_DIG_KM_EVEN] THEN
    MATCH_MP_TAC NV_DIG_FIN_DIG_CG_EQ THEN
    MAP_EVERY EXISTS_TAC
     [`nv_dig_fin_hstar (P * p + r) * sum(1..P * p + r) (nv_dig_g p)`; `&0`] THEN
    REPEAT CONJ_TAC THENL
     [ALL_TAC; REWRITE_TAC[NV_DIG_G_SUM] THEN REAL_ARITH_TAC; REFL_TAC] THEN
    MP_TAC(ISPECL [`p:num`; `nv_dig_fin_hstar (P * p + r)`;
       `sum(1..P * p + r) (nv_dig_g p)`] NV_DIG_FIN_DIG_CG_ZERO_MUL) THEN
    ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC NV_DIG_H0 THEN EXISTS_TAC `s:num` THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC NV_DIG_KM_SUM_EVEN_ZP THEN EXISTS_TAC `s:num` THEN
      ASM_REWRITE_TAC[]]]);;
