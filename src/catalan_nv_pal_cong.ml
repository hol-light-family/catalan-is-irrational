(* ========================================================================= *)
(* CAT_NONVANISHING, part P: the row congruences in x-space.                 *)
(* ========================================================================= *)

needs "src/catalan_nv_pal_row.ml";;

let NV_PAL_ODD = prove
 (`forall p. prime p /\ ~(p = 2) ==> ODD p /\ ~EVEN p /\ 1 <= p`,
  GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC `p:num` PRIME_ODD) THEN ASM_REWRITE_TAC[GSYM NOT_EVEN] THEN
  DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[PRIME_0; ARITH_RULE `1 <= p <=> ~(p = 0:num)`]);;

let NV_PAL_PC_NEG = prove
 (`forall p f g. prime p /\ nv_pal_pc p f g ==> nv_pal_pc p (\x. --(f x)) (\x. --(g x))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[nv_pal_pc] THEN STRIP_TAC THEN
  EXISTS_TAC `\x. --((h:real->real) x)` THEN ASM_SIMP_TAC[NV_PAL_IP_NEG] THEN
  REAL_ARITH_TAC);;

let NV_PAL_XM1 = prove
 (`forall p. prime p /\ ~(p = 2)
       ==> nv_pal_pc p (\x. (x - &1) pow (2 * p)) (\x. (x pow p - &1) pow 2)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`p:num`; `--(&1)`] NV_PAL_FROB_LIN) THEN
  ASM_SIMP_TAC[INTEGER_CLOSED] THEN DISCH_TAC THEN
  SUBGOAL_THEN `~EVEN p` ASSUME_TAC THENL [ASM_MESON_TAC[NV_PAL_ODD]; ALL_TAC] THEN
  NV_PAL_EQCHAIN_TAC `\x. ((x + --(&1)) pow p) pow 2` THENL
   [REWRITE_TAC[REAL_POW_POW; real_sub] THEN REWRITE_TAC[MULT_SYM]; ALL_TAC] THEN
  MATCH_MP_TAC NV_PAL_PC_TRANS_EQ THEN
  EXISTS_TAC `\x. (x pow p + --(&1) pow p) pow 2` THEN
  CONJ_TAC THENL [ASM_REWRITE_TAC[]; CONJ_TAC] THENL
   [MATCH_MP_TAC NV_PAL_PC_POW THEN ASM_REWRITE_TAC[] THEN NV_PAL_IPG_TAC;
    ASM_REWRITE_TAC[REAL_POW_NEG; REAL_POW_ONE] THEN REAL_ARITH_TAC]);;

let NV_PAL_SGN_S = prove
 (`forall N r x. cat_sgn N r * nv_pal_S (cat_dist N r) x =
           if 4 * N <= r then nv_pal_S (r - 4 * N) x else --(nv_pal_S (4 * N - r) x)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[cat_sgn; cat_dist] THEN
  ASM_CASES_TAC `r < 4 * N` THEN ASM_REWRITE_TAC[] THENL
   [SUBGOAL_THEN `~(4 * N <= r)` (fun th -> REWRITE_TAC[th]) THENL
     [ASM_ARITH_TAC; REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `4 * N <= r` (fun th -> REWRITE_TAC[th]) THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `r = 4 * N` THEN ASM_REWRITE_TAC[SUB_REFL; NV_PAL_S_0] THEN
  REAL_ARITH_TAC);;

(* G T_d and S_d for the row r = p r0 + i, in terms of the rows r0, r0+1. *)

let NV_PAL_KEY_ROW = prove
 (`forall p r0 i. prime p /\ ~(p = 2) /\ i < p
     ==> nv_pal_pc p (\x. nv_pal_G p x * nv_pal_T (cat_dist p (p * r0 + i)) x)
           (\x. nv_pal_S (p - i) x * nv_pal_T (cat_dist 1 r0) (x pow p) +
                nv_pal_S i x * nv_pal_T (cat_dist 1 (r0 + 1)) (x pow p)) /\
         nv_pal_pc p (\x. cat_sgn p (p * r0 + i) * nv_pal_S (cat_dist p (p * r0 + i)) x)
           (\x. nv_pal_S (p - i) x * (cat_sgn 1 r0 * nv_pal_S (cat_dist 1 r0) (x pow p)) +
                nv_pal_S i x * (cat_sgn 1 (r0 + 1) *
                                nv_pal_S (cat_dist 1 (r0 + 1)) (x pow p)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `4 <= r0:num` THENL
   [FIRST_X_ASSUM(X_CHOOSE_THEN `e:num` SUBST_ALL_TAC o
      REWRITE_RULE[LE_EXISTS]) THEN
    SUBGOAL_THEN
     `(forall y. cat_sgn p (p * (4 + e) + i) * nv_pal_S (cat_dist p (p * (4 + e) + i)) y =
           nv_pal_S (p * e + i) y) /\
      (forall y. cat_sgn 1 (4 + e) * nv_pal_S (cat_dist 1 (4 + e)) y = nv_pal_S e y) /\
      (forall y. cat_sgn 1 ((4 + e) + 1) * nv_pal_S (cat_dist 1 ((4 + e) + 1)) y =
           nv_pal_S (e + 1) y)`
    (fun th -> REWRITE_TAC[th]) THENL
     [REWRITE_TAC[NV_PAL_SGN_S; LEFT_ADD_DISTRIB] THEN
      REPEAT CONJ_TAC THEN GEN_TAC THEN COND_CASES_TAC THENL
       [AP_THM_TAC THEN AP_TERM_TAC THEN POP_ASSUM MP_TAC THEN ARITH_TAC;
        POP_ASSUM MP_TAC THEN MATCH_MP_TAC(TAUT `~a ==> a ==> b`) THEN ARITH_TAC;
        AP_THM_TAC THEN AP_TERM_TAC THEN POP_ASSUM MP_TAC THEN ARITH_TAC;
        POP_ASSUM MP_TAC THEN MATCH_MP_TAC(TAUT `~a ==> a ==> b`) THEN ARITH_TAC;
        AP_THM_TAC THEN AP_TERM_TAC THEN POP_ASSUM MP_TAC THEN ARITH_TAC;
        POP_ASSUM MP_TAC THEN MATCH_MP_TAC(TAUT `~a ==> a ==> b`) THEN ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `cat_dist p (p * (4 + e) + i) = p * e + i /\
                  cat_dist 1 (4 + e) = e /\ cat_dist 1 ((4 + e) + 1) = e + 1`
    (fun th -> REWRITE_TAC[th]) THENL
     [REWRITE_TAC[cat_dist; LEFT_ADD_DISTRIB] THEN ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC NV_PAL_KEY THEN ASM_SIMP_TAC[LT_IMP_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `exists e. r0 + e = 3:num` (X_CHOOSE_TAC `e:num`) THENL
   [EXISTS_TAC `3 - r0:num` THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `p * r0 + p * e = 3 * p:num` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[GSYM LEFT_ADD_DISTRIB] THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `(forall y. cat_sgn p (p * r0 + i) * nv_pal_S (cat_dist p (p * r0 + i)) y =
         --(nv_pal_S (p * e + (p - i)) y)) /\
    (forall y. cat_sgn 1 r0 * nv_pal_S (cat_dist 1 r0) y = --(nv_pal_S (e + 1) y)) /\
    (forall y. cat_sgn 1 (r0 + 1) * nv_pal_S (cat_dist 1 (r0 + 1)) y = --(nv_pal_S e y))`
  (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[NV_PAL_SGN_S] THEN
    SUBGOAL_THEN `~(4 * p <= p * r0 + i:num) /\ 4 * p - (p * r0 + i) = p * e + (p - i) /\
                  ~(4 * 1 <= r0) /\ 4 * 1 - r0 = e + 1`
    (fun th -> REWRITE_TAC[th]) THENL
     [UNDISCH_TAC `p * r0 + p * e = 3 * p:num` THEN UNDISCH_TAC `r0 + e = 3:num` THEN
      UNDISCH_TAC `i < p:num` THEN ARITH_TAC;
      ALL_TAC] THEN
    GEN_TAC THEN COND_CASES_TAC THENL
     [SUBGOAL_THEN `(r0 + 1) - 4 * 1 = 0 /\ e = 0:num` (fun th -> REWRITE_TAC[th]) THENL
       [UNDISCH_TAC `4 * 1 <= r0 + 1:num` THEN UNDISCH_TAC `r0 + e = 3:num` THEN ARITH_TAC;
        REWRITE_TAC[NV_PAL_S_0] THEN REAL_ARITH_TAC];
      SUBGOAL_THEN `4 * 1 - (r0 + 1) = e:num` (fun th -> REWRITE_TAC[th]) THEN
      UNDISCH_TAC `r0 + e = 3:num` THEN ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `cat_dist p (p * r0 + i) = p * e + (p - i) /\
                cat_dist 1 r0 = e + 1 /\ cat_dist 1 (r0 + 1) = e`
  (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[cat_dist] THEN
    UNDISCH_TAC `p * r0 + p * e = 3 * p:num` THEN UNDISCH_TAC `r0 + e = 3:num` THEN
    UNDISCH_TAC `i < p:num` THEN ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`p:num`; `p - i:num`; `e:num`] NV_PAL_KEY) THEN
  ASM_SIMP_TAC[ARITH_RULE `p - i <= p:num`; ARITH_RULE `i < p ==> p - (p - i) = i:num`] THEN
  STRIP_TAC THEN CONJ_TAC THENL
   [MATCH_MP_TAC NV_PAL_PC_TRANS_EQ THEN
    EXISTS_TAC `\x. nv_pal_S i x * nv_pal_T e (x pow p) +
                    nv_pal_S (p - i) x * nv_pal_T (e + 1) (x pow p)` THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    MATCH_MP_TAC NV_PAL_PC_TRANS_EQ THEN
    EXISTS_TAC `\x. --(nv_pal_S i x * nv_pal_S e (x pow p) +
                       nv_pal_S (p - i) x * nv_pal_S (e + 1) (x pow p))` THEN
    ASM_SIMP_TAC[NV_PAL_PC_NEG] THEN REAL_ARITH_TAC]);;

let NV_PAL_ROWP1 = prove
 (`forall r y. r <= 48 ==> nv_pal_rp 64 (cat_pcoef 1 r) y =
                     (y - &1) pow 2 * nv_pal_T (cat_dist 1 r) y`,
  REPEAT STRIP_TAC THEN MP_TAC(SPECL [`1`; `r:num`; `y:real`] NV_PAL_ROWP) THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[]);;

let NV_PAL_ROWD1 = prove
 (`forall r y. r <= 48 ==> nv_pal_rp 64 (cat_dcoef 1 r) y =
                     (y - &1) pow 2 * (cat_sgn 1 r * nv_pal_S (cat_dist 1 r) y)`,
  REPEAT STRIP_TAC THEN MP_TAC(SPECL [`1`; `r:num`; `y:real`] NV_PAL_ROWD) THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

let NV_PAL_CONG_SETUP_TAC =
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `1 <= p:num` ASSUME_TAC THENL [ASM_MESON_TAC[NV_PAL_ODD]; ALL_TAC] THEN
  SUBGOAL_THEN `p * r0 + i <= 48 * p:num` ASSUME_TAC THENL
   [SUBGOAL_THEN `p * r0 <= p * 47:num` MP_TAC THENL
     [REWRITE_TAC[LE_MULT_LCANCEL] THEN UNDISCH_TAC `r0 < 48:num` THEN ARITH_TAC;
      UNDISCH_TAC `i < p:num` THEN ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `r0 <= 48 /\ r0 + 1 <= 48` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `r0 < 48:num` THEN ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`p:num`; `r0:num`; `i:num`] NV_PAL_KEY_ROW) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPEC `p:num` NV_PAL_XM1) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `forall N r. nv_pint p (cat_sgn N r)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[NV_PAL_SGN_PINT]; ALL_TAC];;

let NV_PAL_CONG_P = prove
 (`forall p r0 i. prime p /\ ~(p = 2) /\ r0 < 48 /\ i < p
     ==> nv_pal_pc p
          (\x. nv_pal_G p x * nv_pal_rp (65 * p - 1) (cat_pcoef p (p * r0 + i)) x)
          (\x. nv_pal_S (p - i) x * nv_pal_rp 64 (cat_pcoef 1 r0) (x pow p) +
               nv_pal_S i x * nv_pal_rp 64 (cat_pcoef 1 (r0 + 1)) (x pow p))`,
  NV_PAL_CONG_SETUP_TAC THEN
  NV_PAL_EQCHAIN_TAC `\x. (x - &1) pow (2 * p) *
     (nv_pal_G p x * nv_pal_T (cat_dist p (p * r0 + i)) x)` THENL
   [ASM_SIMP_TAC[NV_PAL_ROWP] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC NV_PAL_PC_TRANS_EQ THEN
  EXISTS_TAC `\x. (x pow p - &1) pow 2 *
     (nv_pal_S (p - i) x * nv_pal_T (cat_dist 1 r0) (x pow p) +
      nv_pal_S i x * nv_pal_T (cat_dist 1 (r0 + 1)) (x pow p))` THEN
  CONJ_TAC THENL [ASM_REWRITE_TAC[]; CONJ_TAC] THENL
   [NV_PAL_PC_TAC [];
    ASM_SIMP_TAC[NV_PAL_ROWP1] THEN REAL_ARITH_TAC]);;

let NV_PAL_CONG_D = prove
 (`forall p r0 i. prime p /\ ~(p = 2) /\ r0 < 48 /\ i < p
     ==> nv_pal_pc p
          (\x. nv_pal_rp (65 * p - 1) (cat_dcoef p (p * r0 + i)) x)
          (\x. nv_pal_S (p - i) x * nv_pal_rp 64 (cat_dcoef 1 r0) (x pow p) +
               nv_pal_S i x * nv_pal_rp 64 (cat_dcoef 1 (r0 + 1)) (x pow p))`,
  NV_PAL_CONG_SETUP_TAC THEN
  NV_PAL_EQCHAIN_TAC `\x. (x - &1) pow (2 * p) *
     (cat_sgn p (p * r0 + i) * nv_pal_S (cat_dist p (p * r0 + i)) x)` THENL
   [ASM_SIMP_TAC[NV_PAL_ROWD] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC NV_PAL_PC_TRANS_EQ THEN
  EXISTS_TAC `\x. (x pow p - &1) pow 2 *
     (nv_pal_S (p - i) x * (cat_sgn 1 r0 * nv_pal_S (cat_dist 1 r0) (x pow p)) +
      nv_pal_S i x * (cat_sgn 1 (r0 + 1) * nv_pal_S (cat_dist 1 (r0 + 1)) (x pow p)))` THEN
  CONJ_TAC THENL [ASM_REWRITE_TAC[]; CONJ_TAC] THENL
   [NV_PAL_PC_TAC [];
    ASM_SIMP_TAC[NV_PAL_ROWD1] THEN REAL_ARITH_TAC]);;
