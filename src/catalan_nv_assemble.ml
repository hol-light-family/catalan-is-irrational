(* ========================================================================= *)
(* CAT_NONVANISHING: assembly from the interfaces of the sub-parts.          *)
(* ========================================================================= *)

needs "src/catalan_nv_gather.ml";;
needs "src/catalan_nv_det.ml";;
needs "src/catalan_components.ml";;

let NV_G_LDET = prove
 (`forall p (B:num->num->real).
     ODD p
     ==> ndet (0..48 * p - 1)
           (\r k. nv_a p (k MOD p) (r MOD p) * B (r DIV p) (k DIV p) +
                  nv_b p (k MOD p) (r MOD p) * B (r DIV p + 1) (k DIV p)) =
         product (0..p - 1) (\i. &2 pow (p - 1 - i)) pow 48 * ndet (0..47) B *
         ndet (0..47) (\i j. B i j + B (i + 1) j) pow ((p - 1) DIV 2) *
         ndet (0..47) (\i j. B i j - B (i + 1) j) pow ((p - 1) DIV 2)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(p = 0)` ASSUME_TAC THENL [ASM_MESON_TAC[ODD]; ALL_TAC] THEN
  MP_TAC(ISPECL [`p:num`; `nv_a p`; `B:num->num->real`; `\r k. (B:num->num->real) (r + 1) k`]
    NV_DET_BLOCK) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[nv_a] THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC NV_CHEB_U_DEG THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[] THEN
  SUBGOAL_THEN `product (0..p - 1) (\i. nv_a p i i) = product (0..p - 1) (\i. &2 pow (p - 1 - i))`
  SUBST1_TAC THENL
   [MATCH_MP_TAC PRODUCT_EQ_NUMSEG THEN REWRITE_TAC[nv_a; NV_CHEB_U_LEAD]; ALL_TAC] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM] THEN MAP_EVERY X_GEN_TAC [`r:num`; `k:num`] THEN
  AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[nv_b; nv_a] THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  MP_TAC(SPECL [`r:num`; `p:num`] DIVISION) THEN ASM_REWRITE_TAC[] THEN ARITH_TAC);;

let NV_G_POW2_UNIT = prove
 (`forall p k. prime p /\ ~(p = 2) ==> nv_pint p (inv(&2 pow k))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[REAL_OF_NUM_POW] THEN
  MATCH_MP_TAC NV_PINT_INV_NUM THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN SUBGOAL_THEN `p divides 2` MP_TAC THENL
   [ASM_MESON_TAC[PRIME_DIVEXP]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP DIVIDES_LE) THEN
  SUBGOAL_THEN `2 <= p` MP_TAC THENL [ASM_MESON_TAC[PRIME_GE_2]; ASM_ARITH_TAC]);;

let NV_G_FINAL = prove
 (`nv_g_ifaces /\ nv_if_cert ==> CAT_NONVANISHING`,
  STRIP_TAC THEN REWRITE_TAC[CAT_NONVANISHING] THEN X_GEN_TAC `z:real` THEN DISCH_TAC THEN
  ABBREV_TAC `B = \r k. cat_entryq (&0) 1 r k` THEN
  ABBREV_TAC `d0 = ndet (0..47) B` THEN
  ABBREV_TAC `d1 = ndet (0..47) (\i j. (B:num->num->real) i j + B (i + 1) j)` THEN
  ABBREV_TAC `d2 = ndet (0..47) (\i j. (B:num->num->real) i j - B (i + 1) j)` THEN
  SUBGOAL_THEN `forall r k. rational((B:num->num->real) r k)` ASSUME_TAC THENL
   [EXPAND_TAC "B" THEN SIMP_TAC[NV_RAT_ENTRYQ; RATIONAL_NUM]; ALL_TAC] THEN
  SUBGOAL_THEN `rational d0 /\ rational d1 /\ rational d2 /\
                ~(d0 = &0) /\ ~(d1 = &0) /\ ~(d2 = &0)` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["d0"; "d1"; "d2"] THEN
    UNDISCH_TAC `nv_if_cert` THEN EXPAND_TAC "B" THEN REWRITE_TAC[nv_if_cert; ETA_AX] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
    MATCH_MP_TAC NV_RAT_NDET THEN REWRITE_TAC[FINITE_NUMSEG] THEN REPEAT STRIP_TAC THEN
    SIMP_TAC[NV_RAT_ENTRYQ; RATIONAL_NUM; RATIONAL_ADD; RATIONAL_SUB];
    ALL_TAC] THEN
  MP_TAC(SPEC `z:real` NV_PINT_RATIONAL) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_TAC `Pz:num`) THEN
  MP_TAC(SPEC `d0:real` NV_PUNIT_RATIONAL) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_TAC `Pd0:num`) THEN
  MP_TAC(SPEC `d1:real` NV_PUNIT_RATIONAL) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_TAC `Pd1:num`) THEN
  MP_TAC(SPEC `d2:real` NV_PUNIT_RATIONAL) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_TAC `Pd2:num`) THEN
  MP_TAC(ISPECL [`\x:num#num. (B:num->num->real) (FST x) (SND x)`;
                 `(0..48) CROSS (0..47)`] NV_PINT_FAMILY) THEN
  ASM_SIMP_TAC[FINITE_CROSS; FINITE_NUMSEG; FORALL_PAIR_THM; IN_CROSS; IN_NUMSEG] THEN
  DISCH_THEN(X_CHOOSE_TAC `PB:num`) THEN
  MP_TAC(ISPECL [`\x:num#num. cat_M0 (FST x) (SND x)`;
                 `(0..65) CROSS (0..64)`] NV_PINT_FAMILY) THEN
  SIMP_TAC[FINITE_CROSS; FINITE_NUMSEG; FORALL_PAIR_THM; IN_CROSS; IN_NUMSEG; NV_RAT_M0] THEN
  DISCH_THEN(X_CHOOSE_TAC `PM:num`) THEN
  MP_TAC(ISPECL [`\x:num#num. cat_Z0 (FST x) (SND x)`;
                 `(0..65) CROSS (0..64)`] NV_PINT_FAMILY) THEN
  SIMP_TAC[FINITE_CROSS; FINITE_NUMSEG; FORALL_PAIR_THM; IN_CROSS; IN_NUMSEG; NV_RAT_Z0] THEN
  DISCH_THEN(X_CHOOSE_TAC `PZ:num`) THEN
  MP_TAC(ISPECL [`\x:num#num. cat_rawq (&0) 1 (FST x) (SND x)`;
                 `(0..48) CROSS (0..64)`] NV_PINT_FAMILY) THEN
  SIMP_TAC[FINITE_CROSS; FINITE_NUMSEG; FORALL_PAIR_THM; IN_CROSS; IN_NUMSEG;
           NV_RAT_RAWQ; RATIONAL_NUM] THEN
  DISCH_THEN(X_CHOOSE_TAC `PR:num`) THEN
  EXISTS_TAC `261 + Pz + Pd0 + Pd1 + Pd2 + PB + PM + PZ + PR` THEN
  X_GEN_TAC `p:num` THEN STRIP_TAC THEN
  SUBGOAL_THEN `260 < p /\ Pz <= p /\ Pd0 <= p /\ Pd1 <= p /\ Pd2 <= p /\ PB <= p /\
                PM <= p /\ PZ <= p /\ PR <= p` STRIP_ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPEC `p:num` NV_G_PRIME_FACTS) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(fun th -> if is_forall(concl th) && can (find_term ((=) `PB:num`)) (concl th) ||
     (is_forall(concl th) && (can (find_term ((=) `PM:num`)) (concl th) ||
       can (find_term ((=) `PZ:num`)) (concl th) || can (find_term ((=) `PR:num`)) (concl th) ||
       can (find_term ((=) `Pz:num`)) (concl th) || can (find_term ((=) `Pd0:num`)) (concl th) ||
       can (find_term ((=) `Pd1:num`)) (concl th) || can (find_term ((=) `Pd2:num`)) (concl th)))
     then MP_TAC(SPEC `p:num` th) else failwith "")) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  (* the scaled matrix and its block form *)
  ABBREV_TAC `L = \r k. nv_a p (k MOD p) (r MOD p) * (B:num->num->real) (r DIV p) (k DIV p) +
                        nv_b p (k MOD p) (r MOD p) * B (r DIV p + 1) (k DIV p)` THEN
  SUBGOAL_THEN `forall r k. r IN 0..48 * p - 1 /\ k IN 0..48 * p - 1
                      ==> nv_pint p ((L:num->num->real) r k) /\
                          nv_cong p (&p pow 2 * cat_entryq z p r k) (L r k)`
  ASSUME_TAC THENL
   [MAP_EVERY X_GEN_TAC [`r:num`; `k:num`] THEN REWRITE_TAC[IN_NUMSEG] THEN STRIP_TAC THEN
    SUBGOAL_THEN `r DIV p < 48 /\ k DIV p < 48 /\ r MOD p < p /\ k MOD p < p`
    STRIP_ASSUME_TAC THENL
     [ASM_SIMP_TAC[RDIV_LT_EQ; DIVISION] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL
     [EXPAND_TAC "L" THEN BETA_TAC THEN
      MATCH_MP_TAC NV_PINT_ADD THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THEN
      MATCH_MP_TAC NV_PINT_MUL THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THEN
      TRY(MATCH_MP_TAC NV_PINT_INTEGER THEN ASM_REWRITE_TAC[nv_a; nv_b] THEN
          TRY COND_CASES_TAC THEN SIMP_TAC[INTEGER_CLOSED; NV_CHEB_INT] THEN NO_TAC) THEN
      FIRST_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `p * r DIV p + r MOD p = r /\ p * k DIV p + k MOD p = k` STRIP_ASSUME_TAC THENL
     [MP_TAC(SPECL [`r:num`; `p:num`] DIVISION) THEN MP_TAC(SPECL [`k:num`; `p:num`] DIVISION) THEN
      ASM_REWRITE_TAC[] THEN ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(SPECL [`p:num`; `z:real`; `r DIV p`; `r MOD p`; `k MOD p`; `k DIV p`]
      (MP NV_G_ENTRY (ASSUME `nv_g_ifaces`))) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [MAP_EVERY X_GEN_TAC [`r1:num`; `m:num`; `J:num`] THEN STRIP_TAC THEN
      REPEAT CONJ_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
      EXPAND_TAC "L" THEN EXPAND_TAC "B" THEN SIMP_TAC[]];
    ALL_TAC] THEN
  (* conclusion *)
  UNDISCH_TAC `cat_detq z p = &0` THEN REWRITE_TAC[cat_detq] THEN DISCH_TAC THEN
  SUBGOAL_THEN `ndet (0..48 * p - 1) (\r k. &p pow 2 * cat_entryq z p r k) = &0` MP_TAC THENL
   [REWRITE_TAC[NV_DET_NDET] THEN
    MP_TAC(NV_DET_RR(ISPECL [`real_ring`; `0..48 * p - 1`; `cat_entryq z p`; `&p pow 2`]
      RING_DET_CMUL)) THEN
    REWRITE_TAC[FINITE_NUMSEG] THEN DISCH_THEN SUBST1_TAC THEN
    ASM_REWRITE_TAC[GSYM NV_DET_NDET; REAL_MUL_RZERO];
    ALL_TAC] THEN
  REWRITE_TAC[] THEN MATCH_MP_TAC NV_CONG_UNIT_NZ THEN EXISTS_TAC `p:num` THEN
  EXISTS_TAC `ndet (0..48 * p - 1) L` THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC NV_NDET_CONG THEN ASM_SIMP_TAC[FINITE_NUMSEG]; ALL_TAC] THEN
  EXPAND_TAC "L" THEN ASM_SIMP_TAC[NV_G_LDET] THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[REAL_INV_MUL; REAL_INV_POW; REAL_ENTIRE; REAL_POW_EQ_0; DE_MORGAN_THM] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC NV_PINT_MUL THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC NV_PINT_POW THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `inv(product (0..p-1) (\i. &2 pow (p-1-i))) =
                    product (0..p-1) (\i. inv(&2 pow (p-1-i)))` SUBST1_TAC THENL
       [CONV_TAC SYM_CONV THEN MATCH_MP_TAC PRODUCT_INV THEN REWRITE_TAC[FINITE_NUMSEG];
        MATCH_MP_TAC NV_PINT_PRODUCT THEN ASM_SIMP_TAC[FINITE_NUMSEG; NV_G_POW2_UNIT]];
      REPEAT(MATCH_MP_TAC NV_PINT_MUL THEN ASM_REWRITE_TAC[] THEN TRY CONJ_TAC) THEN
      MATCH_MP_TAC NV_PINT_POW THEN ASM_REWRITE_TAC[]];
    DISJ1_TAC THEN REWRITE_TAC[PRODUCT_EQ_0_NUMSEG; REAL_POW_EQ_0; REAL_OF_NUM_EQ; ARITH_EQ]]);;
