(* ========================================================================= *)
(* rp_int: the entries of Delta_N as integrals over x in [-1,1] of           *)
(* rp_row N r x * G(rp_t x), G(t) = int_0^1 psi_k(s) / (1 - t s) ds.          *)
(* ========================================================================= *)

needs "src/catalan_rp_int_g.ml";;
needs "src/catalan_rp_int_cv.ml";;
needs "src/catalan_rp_int_poly.ml";;

let RP_INT_ROW_ALT = prove
 (`forall N r x. 1 <= N /\ r < 48 * N
     ==> rp_row N r x =
         &4 * abs x / (&1 + x pow 2) pow 2 *
         ((&1 - x) pow 2 / (&1 + x pow 2)) pow (2 * N) *
         (&2 / (&1 + x pow 2)) pow (63 * N - 1) *
         ((x / &8 - &3 * abs x / &8) * x pow (67 * N - 2 - r) +
          (&7 * x / &8 + &3 * abs x / &8) * x pow (59 * N - 2 + r))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[rp_row] THEN
  SUBGOAL_THEN `67 * N - 1 - r = SUC(67 * N - 2 - r) /\
                59 * N - 1 + r = SUC(59 * N - 2 + r)`
  (CONJUNCTS_THEN SUBST1_TAC) THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[real_pow] THEN
  REPEAT AP_TERM_TAC THEN
  REWRITE_TAC[rp_xif; rp_xin] THEN COND_CASES_TAC THENL
  [ASM_SIMP_TAC[REAL_ARITH `x < &0 ==> abs x = --x`];
   ASM_SIMP_TAC[REAL_ARITH `~(x < &0) ==> abs x = x`]] THEN
  REAL_ARITH_TAC);;

let RP_INT_ROW_CONT = prove
 (`forall N r s. 1 <= N /\ r < 48 * N ==> (\x. rp_row N r x) real_continuous_on s`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_CONTINUOUS_ON_EQ THEN
  EXISTS_TAC
   `\x. &4 * abs x / (&1 + x pow 2) pow 2 *
        ((&1 - x) pow 2 / (&1 + x pow 2)) pow (2 * N) *
        (&2 / (&1 + x pow 2)) pow (63 * N - 1) *
        ((x / &8 - &3 * abs x / &8) * x pow (67 * N - 2 - r) +
         (&7 * x / &8 + &3 * abs x / &8) * x pow (59 * N - 2 + r))` THEN
  ASM_SIMP_TAC[RP_INT_ROW_ALT] THEN RP_INT_CV_CONT_TAC THEN
  SIMP_TAC[RP_INT_CV_DEN; REAL_OF_NUM_EQ; ARITH_EQ]);;

let RP_INT_POLY_CONT = prove
 (`forall H c s. (\t. cat_poly H c t) real_continuous_on s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[cat_poly] THEN
  MATCH_MP_TAC REAL_CONTINUOUS_ON_SUM THEN REWRITE_TAC[FINITE_NUMSEG] THEN
  REPEAT STRIP_TAC THEN BETA_TAC THEN RP_INT_CONT_TAC);;

let RP_INT_POLY_ROW = prove
 (`forall N r x. 1 <= N /\ r < 48 * N /\ --(&1) <= x /\ x <= &1
   ==> rp_row N r x =
       &4 * abs x / (&1 + x pow 2) pow 2 * cat_rowP N r (rp_t x) -
       (if &0 < x
        then &3 / &2 * (&2 * (&1 - x pow 2) / (&1 + x pow 2) pow 2) *
             cat_rowD N r (rp_t x)
        else &0)`,
  SIMP_TAC[RP_INT_POLY_ID; rp_row]);;

let RP_INT_ROWP_CONT = prove
 (`forall N r s. cat_rowP N r real_continuous_on s /\
           cat_rowD N r real_continuous_on s`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `cat_rowP N r = (\t. cat_poly (65 * N) (cat_pcoef N r) t) /\
                cat_rowD N r = (\t. cat_poly (65 * N) (cat_dcoef N r) t)`
  (CONJUNCTS_THEN SUBST1_TAC) THENL
  [REWRITE_TAC[FUN_EQ_THM; cat_rowP; cat_rowD]; ALL_TAC] THEN
  REWRITE_TAC[RP_INT_POLY_CONT]);;

let RP_INT_GN_CONT = prove
 (`forall N k s. 1 <= N /\ s SUBSET real_interval[--(&1),&1]
           ==> rp_int_G (7 * N + k) (4 * N) real_continuous_on s`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_CONTINUOUS_ON_SUBSET THEN
  EXISTS_TAC `real_interval[--(&1),&1]` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC RP_INT_G_CONT THEN ASM_ARITH_TAC);;

let RP_INT_COMP_CONTS = prove
 (`forall N r k s. 1 <= N /\ IMAGE rp_t s SUBSET s /\ s SUBSET real_interval[--(&1),&1]
     ==> (\x. cat_rowP N r (rp_t x)) real_continuous_on s /\
         (\x. cat_rowD N r (rp_t x)) real_continuous_on s /\
         (\x. rp_int_G (7 * N + k) (4 * N) (rp_t x)) real_continuous_on s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REPEAT CONJ_TAC THEN MATCH_MP_TAC RP_INT_CV_COMP_CONT THEN
  ASM_SIMP_TAC[ETA_AX; RP_INT_ROWP_CONT; RP_INT_GN_CONT]);;

let RP_INT_INTERVALS = prove
 (`IMAGE rp_t (real_interval[--(&1),&1]) SUBSET real_interval[--(&1),&1] /\
   real_interval[--(&1),&1] SUBSET real_interval[--(&1),&1] /\
   IMAGE rp_t (real_interval[&0,&1]) SUBSET real_interval[&0,&1] /\
   real_interval[&0,&1] SUBSET real_interval[--(&1),&1]`,
  REWRITE_TAC[RP_INT_CV_IMAGES; SUBSET_REFL; SUBSET_REAL_INTERVAL] THEN
  REAL_ARITH_TAC);;

let RP_INT_INNER = prove
 (`forall N k c t. 1 <= N /\ abs t <= &1
     ==> real_integral (real_interval[&0,&1])
           (\s. c * rp_int_h (7 * N + k) (4 * N) t s) =
         c * rp_int_G (7 * N + k) (4 * N) t`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[rp_int_G] THEN
  MATCH_MP_TAC REAL_INTEGRAL_LMUL THEN
  MATCH_MP_TAC REAL_INTEGRABLE_CONTINUOUS THEN
  MATCH_MP_TAC RP_INT_H_CONT_S THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

let RP_INT_MIXED_EQ = prove
 (`forall N r k. 1 <= N
     ==> cat_mixed (cat_rowP N r) (cat_psi N k) =
         real_integral (real_interval[--(&1),&1])
          (\x. &4 * abs x / (&1 + x pow 2) pow 2 *
               (cat_rowP N r (rp_t x) * rp_int_G (7 * N + k) (4 * N) (rp_t x)))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[cat_mixed] THEN
  TRANS_TAC EQ_TRANS
   `real_integral (real_interval[--(&1),&1])
     (\t. abs t / sqrt(&1 - t pow 2) *
          (cat_rowP N r t * rp_int_G (7 * N + k) (4 * N) t))` THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC REAL_INTEGRAL_EQ THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN
   X_GEN_TAC `t:real` THEN DISCH_TAC THEN BETA_TAC THEN
   MP_TAC(SPECL [`N:num`; `k:num`;
                 `abs t / sqrt(&1 - t pow 2) * cat_rowP N r t`; `t:real`]
     RP_INT_INNER) THEN
   ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   REWRITE_TAC[REAL_MUL_ASSOC] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
   MATCH_MP_TAC REAL_INTEGRAL_EQ THEN REPEAT STRIP_TAC THEN
   REWRITE_TAC[rp_int_h; cat_psi; real_div] THEN REAL_ARITH_TAC;
   ALL_TAC] THEN
  MATCH_MP_TAC REAL_INTEGRAL_UNIQUE THEN
  MP_TAC(ISPEC `\t. cat_rowP N r t * rp_int_G (7 * N + k) (4 * N) t`
    RP_INT_CV_MIXED) THEN
  REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
  MATCH_MP_TAC REAL_CONTINUOUS_ON_MUL THEN
  REWRITE_TAC[ETA_AX; RP_INT_ROWP_CONT] THEN
  MATCH_MP_TAC RP_INT_GN_CONT THEN ASM_REWRITE_TAC[SUBSET_REFL]);;

let RP_INT_ZETA_EQ = prove
 (`forall N r k. 1 <= N
     ==> cat_zeta (cat_rowD N r) (cat_psi N k) =
         real_integral (real_interval[&0,&1])
          (\x. &2 * (&1 - x pow 2) / (&1 + x pow 2) pow 2 *
               (cat_rowD N r (rp_t x) * rp_int_G (7 * N + k) (4 * N) (rp_t x)))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[cat_zeta] THEN
  TRANS_TAC EQ_TRANS
   `real_integral (real_interval[&0,&1])
     (\t. cat_rowD N r t * rp_int_G (7 * N + k) (4 * N) t)` THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC REAL_INTEGRAL_EQ THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN
   X_GEN_TAC `t:real` THEN DISCH_TAC THEN BETA_TAC THEN
   MP_TAC(SPECL [`N:num`; `k:num`; `cat_rowD N r t`; `t:real`]
     RP_INT_INNER) THEN
   ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   DISCH_THEN(SUBST1_TAC o SYM) THEN
   MATCH_MP_TAC REAL_INTEGRAL_EQ THEN REPEAT STRIP_TAC THEN
   REWRITE_TAC[rp_int_h; cat_psi; real_div] THEN REAL_ARITH_TAC;
   ALL_TAC] THEN
  MATCH_MP_TAC REAL_INTEGRAL_UNIQUE THEN
  MP_TAC(ISPEC `\t. cat_rowD N r t * rp_int_G (7 * N + k) (4 * N) t`
    RP_INT_CV_ZETA) THEN
  REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
  MATCH_MP_TAC REAL_CONTINUOUS_ON_MUL THEN
  REWRITE_TAC[ETA_AX; RP_INT_ROWP_CONT] THEN
  MATCH_MP_TAC RP_INT_GN_CONT THEN ASM_REWRITE_TAC[RP_INT_INTERVALS]);;

let RP_INT_AB_CONT = prove
 (`forall N r k s. 1 <= N /\ r < 48 * N /\ IMAGE rp_t s SUBSET s /\
             s SUBSET real_interval[--(&1),&1]
   ==> (\x. &4 * abs x / (&1 + x pow 2) pow 2 *
            (cat_rowP N r (rp_t x) * rp_int_G (7 * N + k) (4 * N) (rp_t x)))
       real_continuous_on s /\
       (\x. &2 * (&1 - x pow 2) / (&1 + x pow 2) pow 2 *
            (cat_rowD N r (rp_t x) * rp_int_G (7 * N + k) (4 * N) (rp_t x)))
       real_continuous_on s /\
       (\x. rp_row N r x * rp_int_G (7 * N + k) (4 * N) (rp_t x))
       real_continuous_on s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`N:num`; `r:num`; `k:num`; `s:real->bool`] RP_INT_COMP_CONTS) THEN
  MP_TAC(SPECL [`N:num`; `r:num`; `s:real->bool`] RP_INT_ROW_CONT) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN RP_INT_CV_CONT_TAC THEN
  SIMP_TAC[RP_INT_CV_DEN]);;

let RP_INT_ENTRY_INT = prove
 (`forall N r k. 1 <= N /\ r < 48 * N
    ==> cat_entry N r k =
        real_integral (real_interval[--(&1),&1])
          (\x. rp_row N r x * rp_int_G (7 * N + k) (4 * N) (rp_t x))`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[cat_entry; RP_INT_MIXED_EQ; RP_INT_ZETA_EQ] THEN
  MP_TAC(SPECL [`N:num`; `r:num`; `k:num`; `real_interval[--(&1),&1]`]
    RP_INT_AB_CONT) THEN
  MP_TAC(SPECL [`N:num`; `r:num`; `k:num`; `real_interval[&0,&1]`]
    RP_INT_AB_CONT) THEN
  ASM_REWRITE_TAC[RP_INT_INTERVALS] THEN
  DISCH_THEN(STRIP_ASSUME_TAC o MATCH_MP (MESON[REAL_INTEGRABLE_CONTINUOUS]
   `f real_continuous_on real_interval[a,b] /\
    g real_continuous_on real_interval[a,b] /\
    h real_continuous_on real_interval[a,b]
    ==> f real_integrable_on real_interval[a,b] /\
        g real_integrable_on real_interval[a,b] /\
        h real_integrable_on real_interval[a,b]`)) THEN
  DISCH_THEN(STRIP_ASSUME_TAC o MATCH_MP (MESON[REAL_INTEGRABLE_CONTINUOUS]
   `f real_continuous_on real_interval[a,b] /\
    g real_continuous_on real_interval[a,b] /\
    h real_continuous_on real_interval[a,b]
    ==> f real_integrable_on real_interval[a,b] /\
        g real_integrable_on real_interval[a,b] /\
        h real_integrable_on real_interval[a,b]`)) THEN
  ABBREV_TAC `A = \x. &4 * abs x / (&1 + x pow 2) pow 2 *
            (cat_rowP N r (rp_t x) * rp_int_G (7 * N + k) (4 * N) (rp_t x))` THEN
  ABBREV_TAC `B = \x. &2 * (&1 - x pow 2) / (&1 + x pow 2) pow 2 *
            (cat_rowD N r (rp_t x) * rp_int_G (7 * N + k) (4 * N) (rp_t x))` THEN
  ABBREV_TAC `RG = \x. rp_row N r x * rp_int_G (7 * N + k) (4 * N) (rp_t x)` THEN
  MP_TAC(ISPECL [`RG:real->real`; `--(&1)`; `&1`; `&0`] REAL_INTEGRAL_COMBINE) THEN
  MP_TAC(ISPECL [`A:real->real`; `--(&1)`; `&1`; `&0`] REAL_INTEGRAL_COMBINE) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  REPEAT(DISCH_THEN(SUBST1_TAC o SYM)) THEN
  SUBGOAL_THEN
   `real_integral (real_interval[--(&1),&0]) RG =
    real_integral (real_interval[--(&1),&0]) A`
  SUBST1_TAC THENL
  [MATCH_MP_TAC REAL_INTEGRAL_EQ THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN
   X_GEN_TAC `x:real` THEN STRIP_TAC THEN
   MAP_EVERY EXPAND_TAC ["A"; "RG"] THEN BETA_TAC THEN
   MP_TAC(SPECL [`N:num`; `r:num`; `x:real`] RP_INT_POLY_ROW) THEN
   ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   DISCH_THEN SUBST1_TAC THEN
   ASM_SIMP_TAC[REAL_ARITH `x <= &0 ==> ~(&0 < x)`] THEN REAL_ARITH_TAC;
   ALL_TAC] THEN
  SUBGOAL_THEN
   `real_integral (real_interval[&0,&1]) RG =
    real_integral (real_interval[&0,&1]) (\x. A x - &3 / &2 * B x)`
  SUBST1_TAC THENL
  [MATCH_MP_TAC REAL_INTEGRAL_SPIKE THEN EXISTS_TAC `{&0}` THEN
   REWRITE_TAC[REAL_NEGLIGIBLE_SING; IN_DIFF; IN_SING; IN_REAL_INTERVAL] THEN
   X_GEN_TAC `x:real` THEN STRIP_TAC THEN
   MAP_EVERY EXPAND_TAC ["A"; "B"; "RG"] THEN BETA_TAC THEN
   MP_TAC(SPECL [`N:num`; `r:num`; `x:real`] RP_INT_POLY_ROW) THEN
   ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   DISCH_THEN SUBST1_TAC THEN
   ASM_SIMP_TAC[REAL_ARITH `&0 <= x /\ ~(x = &0) ==> &0 < x`] THEN
   REAL_ARITH_TAC;
   ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_INTEGRAL_SUB; REAL_INTEGRABLE_LMUL; REAL_INTEGRAL_LMUL] THEN
  REAL_ARITH_TAC);;
