(* ========================================================================= *)
(* rp_int_cb_: discrete double Andreief / Cauchy-Binet bound and limits of  *)
(* determinants (sub-part of rp_int).                                        *)
(* ========================================================================= *)

needs "src/catalan_rp_defs.ml";;
needs "Library/ring_det.ml";;

(* ------------------------------------------------------------------------- *)
(* Limits of determinants.                                                   *)
(* ------------------------------------------------------------------------- *)

let RP_INT_CB_REALLIM_PRODUCT = prove
 (`forall net (f:A->B->real) l s.
        FINITE s /\ (forall i. i IN s ==> ((\x. f x i) ---> l i) net)
        ==> ((\x. product s (f x)) ---> product s l) net`,
  REPLICATE_TAC 3 GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[PRODUCT_CLAUSES; REALLIM_CONST; IN_INSERT] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REALLIM_MUL THEN ASM_SIMP_TAC[]);;

let RP_INT_CB_NDET_LIM = prove
 (`forall n (A:num->num->num->real) B.
   (forall r k. r < n /\ k < n ==> ((\m. A m r k) ---> B r k) sequentially)
   ==> ((\m. ndet {i | i < n} (A m)) ---> ndet {i | i < n} B) sequentially`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[ndet] THEN
  MATCH_MP_TAC REALLIM_SUM THEN
  SIMP_TAC[FINITE_PERMUTATIONS; FINITE_NUMSEG_LT; IN_ELIM_THM] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REALLIM_LMUL THEN
  MATCH_MP_TAC RP_INT_CB_REALLIM_PRODUCT THEN
  REWRITE_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `i:num` o MATCH_MP PERMUTES_IN_IMAGE) THEN
  ASM_REWRITE_TAC[IN_ELIM_THM]);;

(* ------------------------------------------------------------------------- *)
(* ndet as ring_det over the reals, and the determinant facts we need.      *)
(* ------------------------------------------------------------------------- *)

let RP_INT_CB_NDET_RING = prove
 (`forall s (a:num->num->real). ndet s a = ring_det real_ring s a`,
  REWRITE_TAC[ndet; ring_det; ring_sign; sign; REAL_RING_SUM;
              REAL_RING_PRODUCT; REAL_RING_CLAUSES]);;

let RP_INT_CB_RR th = REWRITE_RULE[GSYM RP_INT_CB_NDET_RING; REAL_RING_SUM;
   REAL_RING_PRODUCT; REAL_RING_CLAUSES; IN_UNIV]
   (INST_TYPE [`:num`,`:A`] th);;

let RP_INT_CB_SIGN = prove
 (`forall p:A->A. ring_sign real_ring p = sign p`,
  REWRITE_TAC[ring_sign; sign; REAL_RING_CLAUSES]);;

let RP_INT_CB_NDET_MULTILINEAR = prove
 (`forall s (t:num->C->bool) (f:num->num->real) g.
        FINITE s /\ (forall i. i IN s ==> FINITE(t i)) /\
        (forall i j. i IN s /\ j IN s ==> f i j = sum (t i) (\x. g i x j))
        ==> ndet s f =
            sum (cartesian_product s t) (\mu. ndet s (\i j. g i (mu i) j))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(RP_INT_CB_RR (ISPECL [`real_ring`; `s:num->bool`; `t:num->C->bool`;
     `f:num->num->real`; `g:num->C->num->real`] RING_DET_MULTILINEAR)) THEN
  ASM_SIMP_TAC[]);;

let RP_INT_CB_NDET_ROWS_MUL = prove
 (`forall s (c:num->real) (f:num->num->real).
        FINITE s ==> ndet s (\i j. c i * f i j) = product s c * ndet s f`,
  SIMP_TAC[RP_INT_CB_RR (ISPEC `real_ring` RING_DET_ROWS_MUL)]);;

let RP_INT_CB_NDET_COLUMNS_MUL = prove
 (`forall s (c:num->real) (f:num->num->real).
        FINITE s ==> ndet s (\i j. f i j * c j) = ndet s f * product s c`,
  SIMP_TAC[RP_INT_CB_RR (ISPEC `real_ring` RING_DET_COLUMNS_MUL)]);;

let RP_INT_CB_NDET_PERMUTE_ROWS = prove
 (`forall s (f:num->num->real) q.
        FINITE s /\ q permutes s
        ==> ndet s (\i j. f (q i) j) = sign q * ndet s f`,
  SIMP_TAC[RP_INT_CB_RR (REWRITE_RULE[RP_INT_CB_SIGN]
    (ISPEC `real_ring` RING_DET_PERMUTE_ROWS))]);;

let RP_INT_CB_NDET_IDENTICAL_ROWS = prove
 (`forall s (f:num->num->real) a b.
        FINITE s /\ a IN s /\ b IN s /\ ~(a = b) /\
        (forall j. j IN s ==> f a j = f b j)
        ==> ndet s f = &0`,
  REWRITE_TAC[RP_INT_CB_RR (ISPEC `real_ring` RING_DET_IDENTICAL_ROWS)]);;

let RP_INT_CB_NDET_IDENTICAL_COLUMNS = prove
 (`forall s (f:num->num->real) a b.
        FINITE s /\ a IN s /\ b IN s /\ ~(a = b) /\
        (forall i. i IN s ==> f i a = f i b)
        ==> ndet s f = &0`,
  REWRITE_TAC[RP_INT_CB_RR (ISPEC `real_ring` RING_DET_IDENTICAL_COLUMNS)]);;

let RP_INT_CB_SUM_PRODUCT_CP = prove
 (`forall (k:K->bool) (t:K->A->bool) (g:K->A->real).
        FINITE k /\ (forall i. i IN k ==> FINITE(t i))
        ==> sum (cartesian_product k t) (\mu. product k (\i. g i (mu i))) =
            product k (\i. sum (t i) (g i))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(REWRITE_RULE[REAL_RING_SUM; REAL_RING_PRODUCT; REAL_RING_CLAUSES;
     IN_UNIV] (ISPECL [`real_ring`; `k:K->bool`; `t:K->A->bool`;
     `g:K->A->real`] RING_SUM_PRODUCT_CARTESIAN_PRODUCT)) THEN
  ASM_SIMP_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Function spaces.                                                          *)
(* ------------------------------------------------------------------------- *)

let RP_INT_CB_IN_CP = prove
 (`forall s (tt:B->bool) (mu:A->B).
        mu IN cartesian_product s (\i. tt) <=>
        (forall i. i IN s ==> mu i IN tt) /\ (forall i. ~(i IN s) ==> mu i = ARB)`,
  REWRITE_TAC[IN_CARTESIAN_PRODUCT; REWRITE_RULE[IN] IN_EXTENSIONAL] THEN
  REWRITE_TAC[IN] THEN MESON_TAC[]);;

let RP_INT_CB_FINITE_CP = prove
 (`forall s (tt:B->bool). FINITE s /\ FINITE tt
        ==> FINITE(cartesian_product s (\i:A. tt))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[FINITE_CARTESIAN_PRODUCT] THEN
  DISJ2_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `s:A->bool` THEN
  ASM_REWRITE_TAC[] THEN SET_TAC[]);;

let RP_INT_CB_SUM_CP_PERMUTE = prove
 (`forall s (tt:B->bool) (q:A->A) h.
        q permutes s
        ==> sum (cartesian_product s (\i. tt)) h =
            sum (cartesian_product s (\i. tt)) (\mu. h (mu o q))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`h:(A->B)->real`; `\mu:A->B. mu o (q:A->A)`;
                 `cartesian_product s (\i:A. (tt:B->bool))`] SUM_BIJECTION) THEN
  REWRITE_TAC[o_DEF] THEN DISCH_THEN MATCH_MP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP PERMUTES_INVERSES) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP PERMUTES_INVERSE) THEN
  REWRITE_TAC[RP_INT_CB_IN_CP] THEN CONJ_TAC THENL
   [X_GEN_TAC `mu:A->B` THEN STRIP_TAC THEN CONJ_TAC THEN
    X_GEN_TAC `i:A` THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_MESON_TAC[PERMUTES_IN_IMAGE; permutes];
    X_GEN_TAC `y:A->B` THEN STRIP_TAC THEN
    REWRITE_TAC[EXISTS_UNIQUE_THM] THEN CONJ_TAC THENL
     [EXISTS_TAC `\i:A. (y:A->B) (inverse (q:A->A) i)` THEN ASM_REWRITE_TAC[ETA_AX] THEN
      CONJ_TAC THEN X_GEN_TAC `i:A` THEN DISCH_TAC THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_MESON_TAC[PERMUTES_IN_IMAGE; permutes];
      MAP_EVERY X_GEN_TAC [`x1:A->B`; `x2:A->B`] THEN STRIP_TAC THEN
      REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `i:A` THEN
      FIRST_X_ASSUM(MP_TAC o C AP_THM `inverse (q:A->A) i`) THEN
      FIRST_X_ASSUM(MP_TAC o C AP_THM `inverse (q:A->A) i`) THEN
      ASM_REWRITE_TAC[] THEN MESON_TAC[]]]);;

(* ------------------------------------------------------------------------- *)
(* Symmetrized Cauchy-Binet over all index maps.                             *)
(* ------------------------------------------------------------------------- *)

let RP_INT_CB_CB = prove
 (`forall n P (A:num->num->real) (Y:num->num->real).
     &(FACT n) * ndet {i | i < n} (\r k. sum {a | a < P} (\a. A r a * Y a k)) =
     sum (cartesian_product {i | i < n} (\i. {a | a < P}))
         (\mu. ndet {i | i < n} (\r i. A r (mu i)) *
               ndet {i | i < n} (\i k. Y (mu i) k))`,
  REPEAT GEN_TAC THEN
  ABBREV_TAC `s = {i:num | i < n}` THEN
  SUBGOAL_THEN `FINITE (s:num->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "s" THEN REWRITE_TAC[FINITE_NUMSEG_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `CARD (s:num->bool) = n` ASSUME_TAC THENL
   [EXPAND_TAC "s" THEN REWRITE_TAC[CARD_NUMSEG_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `FINITE (cartesian_product s (\i:num. {a:num | a < (P:num)}))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC RP_INT_CB_FINITE_CP THEN ASM_REWRITE_TAC[FINITE_NUMSEG_LT];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `ndet s (\r k. sum {a | a < P} (\a. (A:num->num->real) r a * (Y:num->num->real) a k)) =
    sum (cartesian_product s (\i:num. {a:num | a < (P:num)}))
        (\mu. product s (\r. A r (mu r)) * ndet s (\i k. Y (mu i) k))`
  SUBST1_TAC THENL
   [MP_TAC(ISPECL [`s:num->bool`; `\i:num. {a:num | a < (P:num)}`;
      `\r k. sum {a:num | a < (P:num)} (\a. (A:num->num->real) r a * (Y:num->num->real) a k)`;
      `\r a k. (A:num->num->real) r a * (Y:num->num->real) a k`]
      RP_INT_CB_NDET_MULTILINEAR) THEN
    ASM_REWRITE_TAC[FINITE_NUMSEG_LT] THEN DISCH_THEN SUBST1_TAC THEN
    MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `mu:num->num` THEN DISCH_TAC THEN
    MP_TAC(BETA_RULE(ISPECL [`s:num->bool`; `\r. (A:num->num->real) r (mu r)`;
       `\i k. (Y:num->num->real) ((mu:num->num) i) k`] RP_INT_CB_NDET_ROWS_MUL)) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `forall q. q permutes s
        ==> sum (cartesian_product s (\i:num. {a:num | a < (P:num)}))
              (\mu. product s (\r. (A:num->num->real) r (mu r)) *
                    ndet s (\i k. Y (mu i) k)) =
            sign q *
            sum (cartesian_product s (\i:num. {a:num | a < (P:num)}))
              (\mu. product s (\r. A r (mu (q r))) *
                    ndet s (\i k. Y (mu i) k))`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    FIRST_ASSUM(fun th -> GEN_REWRITE_TAC LAND_CONV
      [MATCH_MP RP_INT_CB_SUM_CP_PERMUTE th]) THEN
    REWRITE_TAC[GSYM SUM_LMUL] THEN MATCH_MP_TAC SUM_EQ THEN
    X_GEN_TAC `mu:num->num` THEN DISCH_TAC THEN REWRITE_TAC[o_THM] THEN
    MP_TAC(BETA_RULE(ISPECL [`s:num->bool`; `\i k. (Y:num->num->real) ((mu:num->num) i) k`;
       `q:num->num`] RP_INT_CB_NDET_PERMUTE_ROWS)) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC
   `S = sum (cartesian_product s (\i:num. {a:num | a < (P:num)}))
          (\mu. product s (\r. (A:num->num->real) r (mu r)) *
                ndet s (\i k. Y (mu i) k))` THEN
  TRANS_TAC EQ_TRANS `sum {q | q permutes s} (\q:num->num. S)` THEN
  CONJ_TAC THENL
   [ASM_SIMP_TAC[SUM_CONST; FINITE_PERMUTATIONS; CARD_PERMUTATIONS];
    ALL_TAC] THEN
  TRANS_TAC EQ_TRANS
   `sum {q | q permutes s}
      (\q. sign q *
           sum (cartesian_product s (\i:num. {a:num | a < (P:num)}))
              (\mu. product s (\r. (A:num->num->real) r (mu (q r))) *
                    ndet s (\i k. Y (mu i) k)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_EQ THEN REWRITE_TAC[IN_ELIM_THM] THEN
    X_GEN_TAC `q:num->num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM SUM_LMUL] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) SUM_SWAP o lhand o snd) THEN
  ASM_SIMP_TAC[FINITE_PERMUTATIONS] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `mu:num->num` THEN DISCH_TAC THEN
  REWRITE_TAC[REAL_MUL_ASSOC; SUM_RMUL] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[ndet]);;

(* ------------------------------------------------------------------------- *)
(* The double Andreief bound.                                                *)
(* ------------------------------------------------------------------------- *)

let RP_INT_CB_ABS_LEMMA = prove
 (`forall p q x b. &0 <= p /\ &0 <= q /\ abs x <= b
             ==> abs(p * q * x) <= p * q * b`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[REAL_ABS_MUL] THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 <= x ==> abs x = x`] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]);;

let RP_INT_CB_POINT = prove
 (`forall n P Q (A:num->num->real) (K:num->num->real) (Psi:num->num->real) B.
   &0 <= B /\
   (forall f g. (forall i. i < n ==> f i < P) /\ (forall j. j < n ==> g j < Q) /\
          (forall i j. i < n /\ j < n /\ f i = f j ==> i = j) /\
          (forall i j. i < n /\ j < n /\ g i = g j ==> i = j)
          ==> abs(ndet {i | i < n} (\r i. A r (f i)) *
                  ndet {i | i < n} (\i j. K (f i) (g j)) *
                  ndet {i | i < n} (\j k. Psi (g j) k)) <= B)
   ==> forall f g. f IN cartesian_product {i | i < n} (\i. {a | a < P}) /\
             g IN cartesian_product {i | i < n} (\i. {b | b < Q})
             ==> abs(ndet {i | i < n} (\r i. A r (f i)) *
                     ndet {i | i < n} (\i j. K (f i) (g j)) *
                     ndet {i | i < n} (\j k. Psi (g j) k)) <= B`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[RP_INT_CB_IN_CP; IN_ELIM_THM] THEN
  STRIP_TAC THEN
  ASM_CASES_TAC `exists i j. i < n /\ j < n /\ ~(i = j) /\ (f:num->num) i = f j`
  THENL
   [FIRST_X_ASSUM(CHOOSE_THEN (CHOOSE_THEN STRIP_ASSUME_TAC)) THEN
    MP_TAC(ISPECL [`{i:num | i < n}`;
                   `\r i. (A:num->num->real) r ((f:num->num) i)`;
                   `i:num`; `j:num`] RP_INT_CB_NDET_IDENTICAL_COLUMNS) THEN
    ASM_REWRITE_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM] THEN
    DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[REAL_MUL_LZERO; REAL_ABS_0];
    ALL_TAC] THEN
  ASM_CASES_TAC `exists i j. i < n /\ j < n /\ ~(i = j) /\ (g:num->num) i = g j`
  THENL
   [FIRST_X_ASSUM(CHOOSE_THEN (CHOOSE_THEN STRIP_ASSUME_TAC)) THEN
    MP_TAC(ISPECL [`{i:num | i < n}`;
                   `\j k. (Psi:num->num->real) ((g:num->num) j) k`;
                   `i:num`; `j:num`] RP_INT_CB_NDET_IDENTICAL_ROWS) THEN
    ASM_REWRITE_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM] THEN
    DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[REAL_MUL_RZERO; REAL_ABS_0];
    ALL_TAC] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[]);;

let RP_INT_CB_BOUND = prove
 (`forall n P Q (A:num->num->real) (w:num->real) (K:num->num->real) (v:num->real)
   (Psi:num->num->real) B.
   (forall a. a < P ==> &0 <= w a) /\ (forall b. b < Q ==> &0 <= v b) /\ &0 <= B /\
   (forall f g. (forall i. i < n ==> f i < P) /\ (forall j. j < n ==> g j < Q) /\
          (forall i j. i < n /\ j < n /\ f i = f j ==> i = j) /\
          (forall i j. i < n /\ j < n /\ g i = g j ==> i = j)
          ==> abs(ndet {i | i < n} (\r i. A r (f i)) *
                  ndet {i | i < n} (\i j. K (f i) (g j)) *
                  ndet {i | i < n} (\j k. Psi (g j) k)) <= B)
   ==> abs(ndet {i | i < n}
             (\r k. sum {a | a < P}
                      (\a. sum {b | b < Q}
                             (\b. A r a * w a * K a b * v b * Psi b k)))) <=
       sum {a | a < P} w pow n * sum {b | b < Q} v pow n * B`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`n:num`; `P:num`; `Q:num`; `A:num->num->real`;
    `K:num->num->real`; `Psi:num->num->real`; `B:real`] RP_INT_CB_POINT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `FINITE(cartesian_product {i:num | i < n} (\i. {a:num | a < (P:num)})) /\
    FINITE(cartesian_product {i:num | i < n} (\i. {b:num | b < (Q:num)}))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC RP_INT_CB_FINITE_CP THEN
    REWRITE_TAC[FINITE_NUMSEG_LT];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `&(FACT n) * &(FACT n) *
    ndet {i | i < n}
      (\r k. sum {a | a < P}
        (\a. sum {b | b < Q}
          (\b. (A:num->num->real) r a * (w:num->real) a * (K:num->num->real) a b *
               (v:num->real) b * (Psi:num->num->real) b k))) =
    sum (cartesian_product {i:num | i < n} (\i. {a:num | a < P}))
     (\f. sum (cartesian_product {i:num | i < n} (\i. {b:num | b < Q}))
       (\g. product {i | i < n} (\i. w (f i)) *
            product {i | i < n} (\j. v (g j)) *
            (ndet {i | i < n} (\r i. A r (f i)) *
             ndet {i | i < n} (\i j. K (f i) (g j)) *
             ndet {i | i < n} (\j k. Psi (g j) k))))`
  ASSUME_TAC THENL
   [MP_TAC(BETA_RULE(ISPECL [`n:num`; `P:num`; `A:num->num->real`;
      `\a k. (w:num->real) a * sum {b:num | b < (Q:num)}
               (\b. ((K:num->num->real) a b * (v:num->real) b) *
                    (Psi:num->num->real) b k)`] RP_INT_CB_CB)) THEN
    MATCH_MP_TAC(REAL_RING
     `(e:real) = e' /\ c * s = t ==> c * e' = s ==> c * c * e = t`) THEN
    CONJ_TAC THENL
     [AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN
      MAP_EVERY X_GEN_TAC [`r:num`; `k:num`] THEN
      MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `a:num` THEN DISCH_TAC THEN
      REWRITE_TAC[GSYM SUM_LMUL; REAL_MUL_ASSOC];
      ALL_TAC] THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM SUM_LMUL] THEN MATCH_MP_TAC SUM_EQ THEN
    X_GEN_TAC `f:num->num` THEN DISCH_TAC THEN BETA_TAC THEN
    MP_TAC(BETA_RULE(ISPECL [`{i:num | i < n}`;
      `\i. (w:num->real) ((f:num->num) i)`;
      `\i k. sum {b:num | b < (Q:num)}
               (\b. ((K:num->num->real) ((f:num->num) i) b * (v:num->real) b) *
                    (Psi:num->num->real) b k)`] RP_INT_CB_NDET_ROWS_MUL)) THEN
    REWRITE_TAC[FINITE_NUMSEG_LT] THEN DISCH_THEN SUBST1_TAC THEN
    MP_TAC(BETA_RULE(ISPECL [`n:num`; `Q:num`;
      `\i b. (K:num->num->real) ((f:num->num) i) b * (v:num->real) b`;
      `Psi:num->num->real`] RP_INT_CB_CB)) THEN
    MATCH_MP_TAC(REAL_RING
     `((d:real) * p) * s = t ==> c * x = s ==> c * (d * (p * x)) = t`) THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM SUM_LMUL] THEN MATCH_MP_TAC SUM_EQ THEN
    X_GEN_TAC `g:num->num` THEN DISCH_TAC THEN BETA_TAC THEN
    MP_TAC(BETA_RULE(ISPECL [`{i:num | i < n}`;
      `\j. (v:num->real) ((g:num->num) j)`;
      `\i j. (K:num->num->real) ((f:num->num) i) ((g:num->num) j)`]
      RP_INT_CB_NDET_COLUMNS_MUL)) THEN
    REWRITE_TAC[FINITE_NUMSEG_LT] THEN DISCH_THEN SUBST1_TAC THEN
    MATCH_ACCEPT_TAC(REAL_RING
     `forall a b c p q:real. (a * p) * (b * q) * c = p * q * (a * b * c)`);
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `abs(&(FACT n) * &(FACT n) *
    ndet {i | i < n}
      (\r k. sum {a | a < P}
        (\a. sum {b | b < Q}
          (\b. (A:num->num->real) r a * (w:num->real) a * (K:num->num->real) a b *
               (v:num->real) b * (Psi:num->num->real) b k))))` THEN
  CONJ_TAC THENL
   [SUBGOAL_THEN `&1 <= &(FACT n) * &(FACT n)` MP_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_MUL; REAL_OF_NUM_LE;
                  ARITH_RULE `1 <= x <=> ~(x = 0)`; MULT_EQ_0; FACT_NZ];
      ALL_TAC] THEN
    REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_NUM] THEN
    SPEC_TAC(`&(FACT n)`,`c:real`) THEN GEN_TAC THEN DISCH_TAC THEN
    MATCH_MP_TAC(REAL_ARITH
     `&0 <= (c * c - &1) * x ==> x <= c * c * x`) THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[REAL_ABS_POS; REAL_SUB_LE];
    ALL_TAC] THEN
  POP_ASSUM SUBST1_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `sum (cartesian_product {i:num | i < n} (\i. {a:num | a < P}))
     (\f. sum (cartesian_product {i:num | i < n} (\i. {b:num | b < Q}))
       (\g. product {i | i < n} (\i. (w:num->real) (f i)) *
            product {i | i < n} (\j. (v:num->real) (g j)) * B))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_ABS_LE THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `f:num->num` THEN DISCH_TAC THEN BETA_TAC THEN
    MATCH_MP_TAC SUM_ABS_LE THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `g:num->num` THEN DISCH_TAC THEN BETA_TAC THEN
    MATCH_MP_TAC RP_INT_CB_ABS_LEMMA THEN ASM_SIMP_TAC[] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[RP_INT_CB_IN_CP; IN_ELIM_THM]) THEN
    CONJ_TAC THEN MATCH_MP_TAC PRODUCT_POS_LE THEN
    ASM_SIMP_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM];
    ALL_TAC] THEN
  REWRITE_TAC[SUM_LMUL; SUM_RMUL] THEN
  MP_TAC(BETA_RULE(ISPECL [`{i:num | i < n}`; `\i:num. {a:num | a < (P:num)}`;
     `\i:num. (w:num->real)`] RP_INT_CB_SUM_PRODUCT_CP)) THEN
  MP_TAC(BETA_RULE(ISPECL [`{i:num | i < n}`; `\i:num. {b:num | b < (Q:num)}`;
     `\i:num. (v:num->real)`] RP_INT_CB_SUM_PRODUCT_CP)) THEN
  REWRITE_TAC[FINITE_NUMSEG_LT] THEN
  REPEAT(DISCH_THEN SUBST1_TAC) THEN
  SIMP_TAC[PRODUCT_CONST; FINITE_NUMSEG_LT; CARD_NUMSEG_LT; REAL_LE_REFL]);;
