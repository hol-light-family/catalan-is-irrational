(* ========================================================================= *)
(* CAT_NONVANISHING, part D: the block determinant (paper Eqs. (59)-(60)).   *)
(* ========================================================================= *)

needs "Library/ring_det.ml";;
needs "src/catalan_nv_base.ml";;

let NV_DET_RR = REWRITE_RULE[REAL_RING_CLAUSES; REAL_RING_SUM; REAL_RING_PRODUCT;
                            REAL_RING_POW; IN_UNIV];;

let NV_DET_NDET = prove
 (`forall s a. ndet s a = ring_det real_ring s a`,
  REWRITE_TAC[ndet; ring_det; ring_sign; sign; REAL_RING_SUM;
              REAL_RING_PRODUCT; REAL_RING_CLAUSES]);;

let NV_DET_MUL = prove
 (`forall s (a:A->A->real) b.
        FINITE s
        ==> ring_det real_ring s (\i j. sum s (\k. a i k * b k j)) =
            ring_det real_ring s a * ring_det real_ring s b`,
  REPEAT STRIP_TAC THEN
  MP_TAC(NV_DET_RR(ISPECL [`real_ring`; `s:A->bool`; `a:A->A->real`; `b:A->A->real`]
    RING_DET_MUL)) THEN ASM_REWRITE_TAC[]);;

let NV_DET_KRONECKER = prove
 (`forall s t (a:A->A->real) (b:B->B->real).
        FINITE s /\ FINITE t
        ==> ring_det real_ring (s CROSS t)
              (\x y. a (FST x) (FST y) * b (SND x) (SND y)) =
            ring_det real_ring s a pow (CARD t) * ring_det real_ring t b pow (CARD s)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(NV_DET_RR(ISPECL [`real_ring`; `s:A->bool`; `t:B->bool`;
     `a:A->A->real`; `b:B->B->real`] RING_DET_KRONECKER)) THEN
  ASM_REWRITE_TAC[]);;

let NV_DET_UPPERTRIANGULAR = prove
 (`forall s (f:num->num->real).
        FINITE s /\ (forall i j. i IN s /\ j IN s /\ j < i ==> f i j = &0)
        ==> ring_det real_ring s f = product s (\i. f i i)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(NV_DET_RR(ISPECL [`real_ring`; `s:num->bool`; `f:num->num->real`]
    RING_DET_UPPERTRIANGULAR)) THEN ASM_REWRITE_TAC[]);;

let NV_DET_DIAGONAL = prove
 (`forall s (f:A->A->real).
        FINITE s /\ (forall i j. i IN s /\ j IN s /\ ~(i = j) ==> f i j = &0)
        ==> ring_det real_ring s f = product s (\i. f i i)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(NV_DET_RR(ISPECL [`real_ring`; `s:A->bool`; `f:A->A->real`]
    RING_DET_DIAGONAL)) THEN ASM_REWRITE_TAC[]);;

let NV_DET_ID = prove
 (`forall s:A->bool. FINITE s
       ==> ring_det real_ring s (\i j. if i = j then &1 else &0) = &1`,
  REPEAT STRIP_TAC THEN
  MP_TAC(NV_DET_RR(ISPECL [`real_ring`; `s:A->bool`] RING_DET_I)) THEN
  ASM_REWRITE_TAC[]);;

let NV_DET_REINDEX = prove
 (`forall (g:A->C) s (f:C->C->real).
        FINITE s /\ (forall x y. x IN s /\ y IN s /\ g x = g y ==> x = y)
        ==> ring_det real_ring (IMAGE g s) f =
            ring_det real_ring s (\i j. f (g i) (g j))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`real_ring`; `g:A->C`; `s:A->bool`; `f:C->C->real`]
    RING_DET_REINDEX) THEN ASM_REWRITE_TAC[]);;

let NV_DET_EQ = prove
 (`forall s (f:A->A->real) g.
        (forall i j. i IN s /\ j IN s ==> f i j = g i j)
        ==> ring_det real_ring s f = ring_det real_ring s g`,
  REWRITE_TAC[RING_DET_EQ]);;

let NV_DET_BLOCK_TRIANGULAR = prove
 (`forall s t (f:A->A->real).
        FINITE s /\ FINITE t /\ DISJOINT s t /\
        (forall i j. i IN s /\ j IN t ==> f i j = &0)
        ==> ring_det real_ring (s UNION t) f =
            ring_det real_ring s f * ring_det real_ring t f`,
  REPEAT STRIP_TAC THEN
  MP_TAC(NV_DET_RR(ISPECL [`real_ring`; `s:A->bool`; `t:A->bool`; `f:A->A->real`]
    RING_DET_BLOCK_TRIANGULAR)) THEN ASM_REWRITE_TAC[]);;

let NV_DET_EMPTY = prove
 (`forall f:A->A->real. ring_det real_ring {} f = &1`,
  REWRITE_TAC[NV_DET_RR (ISPEC `real_ring` RING_DET_EMPTY)]);;

(* Block diagonal arrays on s CROSS t.                                       *)

let NV_DET_BLOCKDIAG = prove
 (`forall s t (b:A->B->B->real).
        FINITE s /\ FINITE t
        ==> ring_det real_ring (s CROSS t)
              (\x y. if FST x = FST y then b (FST x) (SND x) (SND y) else &0) =
            product s (\i. ring_det real_ring t (b i))`,
  (GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN
  SPEC_TAC(`s:A->bool`,`s:A->bool`) THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  REWRITE_TAC[CROSS_EMPTY; NV_DET_EMPTY; PRODUCT_CLAUSES] THEN
  MAP_EVERY X_GEN_TAC [`a:A`; `s:A->bool`] THEN
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[PRODUCT_CLAUSES])
  THEN (SUBGOAL_THEN `((a:A) INSERT s) CROSS (t:B->bool) = ({a} CROSS t) UNION (s CROSS t)`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_CROSS; IN_UNION; IN_INSERT; NOT_IN_EMPTY; FORALL_PAIR_THM] THEN
    MESON_TAC[];
    ALL_TAC])
  THEN (W(MP_TAC o PART_MATCH (lhand o rand) NV_DET_BLOCK_TRIANGULAR o lhand o snd))
  THEN (ANTS_TAC THENL
   [ASM_SIMP_TAC[FINITE_CROSS; FINITE_SING] THEN
    REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; IN_CROSS; IN_SING; NOT_IN_EMPTY;
                FORALL_PAIR_THM] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[IN_CROSS; IN_SING; FORALL_PAIR_THM] THEN ASM_MESON_TAC[];
    DISCH_THEN SUBST1_TAC])
  THEN (FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN ASM_SIMP_TAC[] THEN
  DISCH_THEN SUBST1_TAC THEN AP_THM_TAC THEN AP_TERM_TAC)
  THEN (SUBGOAL_THEN `{a:A} CROSS (t:B->bool) = IMAGE (\j. a,j) t` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_CROSS; IN_SING; IN_IMAGE; FORALL_PAIR_THM; PAIR_EQ] THEN
    MESON_TAC[];
    ALL_TAC])
  THEN (W(MP_TAC o PART_MATCH (lhand o rand) NV_DET_REINDEX o lhand o snd) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[PAIR_EQ]; DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[ETA_AX]));;

let NV_DET_SUM_CROSS = prove
 (`forall (s:A->bool) (t:B->bool) (f:A#B->real). FINITE s /\ FINITE t
           ==> sum (s CROSS t) f = sum s (\i. sum t (\j. f(i,j)))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:A->bool`; `\i:A. (t:B->bool)`; `\i j. (f:A#B->real)(i,j)`] SUM_SUM_PRODUCT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[CROSS] THEN MATCH_MP_TAC SUM_EQ THEN
  REWRITE_TAC[FORALL_PAIR_THM]);;
let NV_DET_SUM_DELTA = prove
 (`forall s (a:A) f. sum s (\x. if x = a then f x else &0) = if a IN s then f a else &0`,
  REPEAT GEN_TAC THEN
  TRANS_TAC EQ_TRANS `sum s (\x. if x = a then (f:A->real) a else &0)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_EQ THEN SIMP_TAC[];
    REWRITE_TAC[SUM_DELTA]]);;

let NV_DET_SUM_DELTA_MUL = prove
 (`forall s (a:A) f. sum s (\x. f x * (if x = a then &1 else &0)) = if a IN s then f a else &0`,
  REPEAT GEN_TAC THEN
  TRANS_TAC EQ_TRANS `sum s (\x. if x = a then (f:A->real) x else &0)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_EQ THEN REPEAT STRIP_TAC THEN BETA_TAC THEN COND_CASES_TAC THEN
    REWRITE_TAC[REAL_MUL_RID; REAL_MUL_RZERO];
    REWRITE_TAC[NV_DET_SUM_DELTA]]);;

let nv_det_pi = new_definition `nv_det_pi p i = if i = 0 then p else p - i`;;
let nv_det_sig = new_definition
  `nv_det_sig p j = if (p - 1) DIV 2 < j then --(&1) else &1`;;
let nv_det_lam = new_definition
  `nv_det_lam p j = if j = 0 then &0 else nv_det_sig p j`;;
let nv_det_S = new_definition
  `nv_det_S p i j = (if i = j then nv_det_sig p j else &0) +
                    (if i = nv_det_pi p j then &1 else &0)`;;
let nv_det_M = new_definition
  `nv_det_M p (B0:num->num->real) B1 (x:num#num) (z:num#num) =
     (if FST z = FST x then B0 (SND x) (SND z) else &0) +
     (if FST z = nv_det_pi p (FST x) then B1 (SND x) (SND z) else &0)`;;
let nv_det_K = new_definition
  `nv_det_K (a:num->num->real) (z:num#num) (y:num#num) =
     a (FST y) (FST z) * (if SND z = SND y then &1 else &0)`;;
let nv_det_SI = new_definition
  `nv_det_SI p (z:num#num) (y:num#num) =
     nv_det_S p (FST z) (FST y) * (if SND z = SND y then &1 else &0)`;;
let nv_det_D = new_definition
  `nv_det_D p (B0:num->num->real) B1 (z:num#num) (y:num#num) =
     if FST z = FST y then B0 (SND z) (SND y) + nv_det_lam p (FST z) * B1 (SND z) (SND y)
     else &0`;;

let NV_DET_COND_MUL = prove
 (`(forall b x y. (if b then x else &0) * y = if b then x * y else &0) /\
   (forall b x y. y * (if b then x else &0) = if b then y * x else &0)`,
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[REAL_MUL_LZERO; REAL_MUL_RZERO]);;

let NV_DET_MK = prove
 (`forall p a B0 B1 s t x y.
      FINITE s /\ FINITE t /\ FST x IN s /\ SND y IN t
      ==> sum (s CROSS t) (\z. nv_det_M p B0 B1 x z * nv_det_K a z y) =
          a (FST y) (FST x) * B0 (SND x) (SND y) +
          (if nv_det_pi p (FST x) IN s then a (FST y) (nv_det_pi p (FST x)) else &0) *
          B1 (SND x) (SND y)`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[NV_DET_SUM_CROSS] THEN
  REWRITE_TAC[nv_det_K; REAL_MUL_ASSOC; NV_DET_SUM_DELTA_MUL] THEN
  ASM_REWRITE_TAC[nv_det_M; REAL_ADD_RDISTRIB] THEN
  ASM_SIMP_TAC[SUM_ADD] THEN
  REWRITE_TAC[NV_DET_COND_MUL; NV_DET_SUM_DELTA] THEN
  ASM_REWRITE_TAC[] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

let NV_DET_SUM_DELTA2 = prove
 (`forall s (a:A) f. sum s (\x. if a = x then f x else &0) = if a IN s then f a else &0`,
  REPEAT GEN_TAC THEN
  TRANS_TAC EQ_TRANS `sum s (\x. if x = a then (f:A->real) x else &0)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_EQ THEN REPEAT STRIP_TAC THEN BETA_TAC THEN
    REWRITE_TAC[EQ_SYM_EQ];
    REWRITE_TAC[NV_DET_SUM_DELTA]]);;

let NV_DET_MSI = prove
 (`forall p B0 B1 s t x y.
      FINITE s /\ FINITE t /\ FST x IN s /\ SND y IN t
      ==> sum (s CROSS t) (\z. nv_det_M p B0 B1 x z * nv_det_SI p z y) =
          nv_det_S p (FST x) (FST y) * B0 (SND x) (SND y) +
          (if nv_det_pi p (FST x) IN s then nv_det_S p (nv_det_pi p (FST x)) (FST y)
           else &0) * B1 (SND x) (SND y)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`p:num`; `\u v. nv_det_S p v u`; `B0:num->num->real`; `B1:num->num->real`;
                `s:num->bool`; `t:num->bool`; `x:num#num`; `y:num#num`] NV_DET_MK) THEN
  ASM_REWRITE_TAC[nv_det_K; nv_det_SI]);;

let NV_DET_SID = prove
 (`forall p B0 B1 s t x y.
      FINITE s /\ FINITE t /\ FST y IN s /\ SND x IN t
      ==> sum (s CROSS t) (\z. nv_det_SI p x z * nv_det_D p B0 B1 z y) =
          nv_det_S p (FST x) (FST y) *
          (B0 (SND x) (SND y) + nv_det_lam p (FST y) * B1 (SND x) (SND y))`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[NV_DET_SUM_CROSS] THEN
  REWRITE_TAC[nv_det_SI; nv_det_D; NV_DET_COND_MUL; REAL_MUL_RID; REAL_MUL_LZERO] THEN
  REWRITE_TAC[NV_DET_SUM_DELTA; NV_DET_SUM_DELTA2] THEN
  ASM_REWRITE_TAC[NV_DET_COND_MUL; NV_DET_SUM_DELTA]);;

let NV_DET_PAR = prove
 (`forall m j. ~(SUC(2 * m) - j = j)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  ASM_CASES_TAC `j < SUC(2 * m)` THENL
   [SUBGOAL_THEN `SUC(2 * m) = 2 * j` MP_TAC THENL
     [ASM_ARITH_TAC;
      DISCH_THEN(MP_TAC o AP_TERM `EVEN`) THEN REWRITE_TAC[EVEN; EVEN_MULT; ARITH]];
    SUBGOAL_THEN `j = 0` SUBST_ALL_TAC THEN ASM_ARITH_TAC]);;

let NV_DET_EIG = prove
 (`forall p i j. ODD p /\ i < p /\ j < p
           ==> (if nv_det_pi p i IN 0..p-1 then nv_det_S p (nv_det_pi p i) j else &0) =
               nv_det_S p i j * nv_det_lam p j`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ODD_EXISTS] THEN STRIP_TAC THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  REWRITE_TAC[nv_det_S; nv_det_pi; nv_det_lam; nv_det_sig; IN_NUMSEG;
              ARITH_RULE `(SUC(2 * m) - 1) DIV 2 = m`] THEN
  ASM_CASES_TAC `j = 0` THEN ASM_REWRITE_TAC[] THENL
   [ASM_CASES_TAC `i = 0` THEN ASM_REWRITE_TAC[] THEN
    REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
    REPEAT(POP_ASSUM MP_TAC) THEN ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `i = 0` THEN ASM_REWRITE_TAC[] THENL
   [REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
    REPEAT(POP_ASSUM MP_TAC) THEN ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[ARITH_RULE `~(i = 0) /\ i < SUC(2 * m) ==> 0 <= SUC(2 * m) - i /\ SUC(2 * m) - i <= SUC(2 * m) - 1`] THEN
  ASM_CASES_TAC `i:num = j` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    REWRITE_TAC[NV_DET_PAR] THEN
    COND_CASES_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `i = SUC(2 * m) - j` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    ASM_SIMP_TAC[NV_DET_PAR; ARITH_RULE `~(j = 0) /\ j < SUC(2 * m) ==> SUC(2 * m) - (SUC(2 * m) - j) = j`] THEN
    COND_CASES_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `~(SUC(2 * m) - i = j) /\ ~(SUC(2 * m) - i = SUC(2 * m) - j)` STRIP_ASSUME_TAC THENL
   [ASM_ARITH_TAC; ASM_REWRITE_TAC[]] THEN REAL_ARITH_TAC);;

let NV_DET_STS = prove
 (`forall p i j. ODD p /\ i < p /\ j < p
           ==> sum (0..p-1) (\k. nv_det_S p k i * nv_det_S p k j) =
               if i = j then (if i = 0 then &1 else &2) else &0`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ODD_EXISTS] THEN STRIP_TAC THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  REWRITE_TAC[nv_det_S; REAL_ADD_LDISTRIB; REAL_ADD_RDISTRIB] THEN
  REWRITE_TAC[SUM_ADD_NUMSEG; NV_DET_COND_MUL; REAL_MUL_LID; REAL_MUL_RID] THEN
  REWRITE_TAC[NV_DET_SUM_DELTA; IN_NUMSEG] THEN
  REWRITE_TAC[nv_det_pi; nv_det_sig; ARITH_RULE `(SUC(2 * m) - 1) DIV 2 = m`] THEN
  ASM_CASES_TAC `i = 0` THEN ASM_CASES_TAC `j = 0` THEN ASM_REWRITE_TAC[] THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
  TRY REAL_ARITH_TAC THEN
  REPEAT(POP_ASSUM MP_TAC) THEN REWRITE_TAC[NV_DET_PAR] THEN TRY ARITH_TAC THEN
  REPEAT STRIP_TAC THEN ASM_MESON_TAC[NV_DET_PAR; ARITH_RULE `j < SUC(2 * m) /\ i < SUC(2 * m) /\ SUC(2 * m) - i = SUC(2 * m) - j /\ ~(i = 0) /\ ~(j = 0) ==> i = j`]);;

let NV_DET_S_NZ = prove
 (`forall p. ODD p ==> ~(ring_det real_ring (0..p-1) (nv_det_S p) = &0)`,
  (REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`0..p-1`; `\i k. nv_det_S p k i`; `nv_det_S p`] NV_DET_MUL) THEN
  REWRITE_TAC[FINITE_NUMSEG] THEN
  MP_TAC(NV_DET_RR(ISPECL [`real_ring`; `0..p-1`; `nv_det_S p`] RING_DET_TRANSP)) THEN
  REWRITE_TAC[FINITE_NUMSEG] THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN `ring_det real_ring (0..p-1) (\i j. sum (0..p-1) (\k. nv_det_S p k i * nv_det_S p k j)) =
                ring_det real_ring (0..p-1) (\i j. if i = j then (if i = 0 then &1 else &2) else &0)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC NV_DET_EQ THEN REWRITE_TAC[IN_NUMSEG] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC NV_DET_STS THEN ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP (ARITH_RULE `ODD p ==> 1 <= p`) o check (is_comb o concl)) THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  ALL_TAC)
  THEN (ASM_SIMP_TAC[NV_DET_DIAGONAL; FINITE_NUMSEG])
  THEN (REWRITE_TAC[REAL_MUL_LZERO; PRODUCT_EQ_0_NUMSEG; NOT_EXISTS_THM] THEN
  X_GEN_TAC `k:num` THEN COND_CASES_TAC THEN
  CONV_TAC REAL_RAT_REDUCE_CONV));;

let NV_DET_X = prove
 (`forall p a B0 B1.
      ODD p /\ (forall l i. l < i /\ i < p ==> a l i = &0)
      ==> ring_det real_ring ((0..p-1) CROSS (0..47))
            (\x y. sum ((0..p-1) CROSS (0..47)) (\z. nv_det_M p B0 B1 x z * nv_det_K a z y)) =
          product (0..p-1) (\i. a i i) pow 48 *
          product (0..p-1) (\i. ring_det real_ring (0..47)
                                  (\u v. B0 u v + nv_det_lam p i * B1 u v))`,
  (REPEAT STRIP_TAC THEN
  ABBREV_TAC `X = (0..p-1) CROSS (0..47)` THEN
  SUBGOAL_THEN `FINITE(X:num#num->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "X" THEN SIMP_TAC[FINITE_CROSS; FINITE_NUMSEG]; ALL_TAC] THEN
  ASM_SIMP_TAC[NV_DET_MUL; ETA_AX])
  THEN (SUBGOAL_THEN `ring_det real_ring X (nv_det_K a) = product (0..p-1) (\i. a i i) pow 48`
  SUBST1_TAC THENL
   [EXPAND_TAC "X" THEN
    SUBGOAL_THEN `nv_det_K a = (\x y. (\u v. a v u) (FST x) (FST y) *
                                (\u v. if u = v then &1 else &0) (SND x) (SND y))`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; nv_det_K]; ALL_TAC] THEN
    SIMP_TAC[NV_DET_KRONECKER; FINITE_NUMSEG; NV_DET_ID; REAL_POW_ONE; REAL_MUL_RID] THEN
    REWRITE_TAC[CARD_NUMSEG; ARITH_RULE `(47 + 1) - 0 = 48`] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    W(MP_TAC o PART_MATCH (lhand o rand) NV_DET_UPPERTRIANGULAR o lhand o snd) THEN
    REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN ANTS_TAC THENL
     [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
      SIMP_TAC[]];
    ALL_TAC])
  THEN (MATCH_MP_TAC(REAL_RING `m = d ==> m * k = k * d:real`))
  THEN (SUBGOAL_THEN `~(ring_det real_ring X (nv_det_SI p) = &0)` ASSUME_TAC THENL
   [EXPAND_TAC "X" THEN
    SUBGOAL_THEN `nv_det_SI p = (\x y. nv_det_S p (FST x) (FST y) *
                                (\u v. if u = v then &1 else &0) (SND x) (SND y))`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; nv_det_SI]; ALL_TAC] THEN
    SIMP_TAC[NV_DET_KRONECKER; FINITE_NUMSEG; NV_DET_ID; REAL_POW_ONE; REAL_MUL_RID] THEN
    REWRITE_TAC[REAL_POW_EQ_0; ETA_AX; CARD_NUMSEG] THEN
    ASM_SIMP_TAC[NV_DET_S_NZ] THEN ARITH_TAC;
    ALL_TAC])
  THEN (SUBGOAL_THEN `product (0..p-1) (\i. ring_det real_ring (0..47)
                    (\u v. B0 u v + nv_det_lam p i * B1 u v)) =
                ring_det real_ring X (nv_det_D p B0 B1)` SUBST1_TAC THENL
   [EXPAND_TAC "X" THEN
    SUBGOAL_THEN `nv_det_D p B0 B1 = (\x y. if FST x = FST y then
          (\i u v. B0 u v + nv_det_lam p i * B1 u v) (FST x) (SND x) (SND y) else &0)`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; nv_det_D]; ALL_TAC] THEN
    SIMP_TAC[NV_DET_BLOCKDIAG; FINITE_NUMSEG];
    ALL_TAC])
  THEN (SUBGOAL_THEN `ring_det real_ring X (nv_det_M p B0 B1) * ring_det real_ring X (nv_det_SI p) =
                ring_det real_ring X (nv_det_SI p) * ring_det real_ring X (nv_det_D p B0 B1)`
  MP_TAC THENL
   [ALL_TAC;
    UNDISCH_TAC `~(ring_det real_ring X (nv_det_SI p) = &0)` THEN CONV_TAC REAL_RING])
  THEN (ASM_SIMP_TAC[GSYM NV_DET_MUL])
  THEN (MATCH_MP_TAC NV_DET_EQ THEN EXPAND_TAC "X" THEN
  REWRITE_TAC[FORALL_PAIR_THM; IN_CROSS; IN_NUMSEG] THEN
  MAP_EVERY X_GEN_TAC [`i:num`; `r:num`; `j:num`; `k:num`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `1 <= p:num` ASSUME_TAC THENL
   [ASM_MESON_TAC[ARITH_RULE `ODD p ==> 1 <= p`; ODD]; ALL_TAC])
  THEN (W(MP_TAC o PART_MATCH (lhand o rand) NV_DET_MSI o lhand o snd) THEN
  REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC])
  THEN (W(MP_TAC o PART_MATCH (lhand o rand) NV_DET_SID o rand o snd) THEN
  REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC])
  THEN (MP_TAC(REWRITE_RULE[IN_NUMSEG] (SPECL [`p:num`; `i:num`; `j:num`] NV_DET_EIG)) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `i <= p - 1` THEN UNDISCH_TAC `j <= p - 1` THEN
    UNDISCH_TAC `1 <= p` THEN ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[FST; SND] THEN DISCH_THEN SUBST1_TAC THEN REAL_ARITH_TAC));;


let NV_DET_LAMPROD = prove
 (`forall p f. ODD p
         ==> product (0..p-1) (\i. f (nv_det_lam p i)) =
             f (&0) * f (&1) pow ((p - 1) DIV 2) * f (--(&1)) pow ((p - 1) DIV 2)`,
  (REPEAT GEN_TAC)
  THEN (REWRITE_TAC[ODD_EXISTS])
  THEN (STRIP_TAC)
  THEN (FIRST_X_ASSUM SUBST_ALL_TAC)
  THEN (REWRITE_TAC[ARITH_RULE `(SUC(2 * m) - 1) DIV 2 = m`; ARITH_RULE `SUC(2 * m) - 1 = m + m`])
  THEN (SIMP_TAC[PRODUCT_CLAUSES_LEFT; LE_0])
  THEN (REWRITE_TAC[nv_det_lam; ARITH_RULE `0 + 1 = 1`])
  THEN (MP_TAC(SPECL [`\i. f (if i = 0 then &0 else nv_det_sig (SUC(2 * m)) i):real`; `1`; `m:num`; `m:num`]
    PRODUCT_ADD_SPLIT))
  THEN (REWRITE_TAC[ARITH_RULE `1 <= m + 1`])
  THEN (DISCH_THEN SUBST1_TAC)
  THEN (REWRITE_TAC[GSYM REAL_MUL_ASSOC])
  THEN (AP_TERM_TAC)
  THEN (BINOP_TAC THENL
   [TRANS_TAC EQ_TRANS `product (1..m) (\i. f(&1):real)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC PRODUCT_EQ_NUMSEG THEN REWRITE_TAC[nv_det_sig] THEN
      REPEAT STRIP_TAC THEN BETA_TAC THEN
      REWRITE_TAC[ARITH_RULE `(SUC(2 * m) - 1) DIV 2 = m`] THEN
      SUBGOAL_THEN `~(i = 0) /\ ~(m < i:num)` (fun th -> REWRITE_TAC[th]) THEN ASM_ARITH_TAC;
      REWRITE_TAC[PRODUCT_CONST_NUMSEG_1]];
    TRANS_TAC EQ_TRANS `product (m+1..m+m) (\i. f(--(&1)):real)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC PRODUCT_EQ_NUMSEG THEN REWRITE_TAC[nv_det_sig] THEN
      REPEAT STRIP_TAC THEN BETA_TAC THEN
      REWRITE_TAC[ARITH_RULE `(SUC(2 * m) - 1) DIV 2 = m`] THEN
      SUBGOAL_THEN `~(i = 0) /\ (m < i:num)` (fun th -> REWRITE_TAC[th]) THEN ASM_ARITH_TAC;
      REWRITE_TAC[PRODUCT_CONST_NUMSEG; ARITH_RULE `((m + m) + 1) - (m + 1) = m`]]]));;



let NV_DET_ARITH_TAC =
  let ok tm = try fst(dest_const(rator tm)) <> "ODD" &&
                  not(can (find_term (fun t -> is_abs t || type_of t = `:real`)) tm)
              with Failure _ -> not(can (find_term (fun t -> is_abs t || type_of t = `:real`)) tm) in
  REPEAT(FIRST_X_ASSUM(fun th -> if ok(concl th) then MP_TAC th else ALL_TAC)) THEN
  ARITH_TAC;;

let NV_DET_BLOCK = prove
 (`forall p a B0 B1.
     ODD p /\ (forall l i. l < i /\ i < p ==> a l i = &0)
     ==> ndet (0..48 * p - 1)
           (\r k. a (k MOD p) (r MOD p) * B0 (r DIV p) (k DIV p) +
                  (if r MOD p = 0 then &0 else a (k MOD p) (p - r MOD p)) *
                  B1 (r DIV p) (k DIV p)) =
         product (0..p - 1) (\i. a i i) pow 48 * ndet (0..47) B0 *
         ndet (0..47) (\i j. B0 i j + B1 i j) pow ((p - 1) DIV 2) *
         ndet (0..47) (\i j. B0 i j - B1 i j) pow ((p - 1) DIV 2)`,
  ((REPEAT STRIP_TAC))
  THEN ((SUBGOAL_THEN `~(p = 0:num)` ASSUME_TAC THENL [ASM_MESON_TAC[ODD]; ALL_TAC]))
  THEN ((REWRITE_TAC[NV_DET_NDET]))
  THEN ((SUBGOAL_THEN `0..48 * p - 1 = IMAGE (\x. SND x * p + FST x) ((0..p-1) CROSS (0..47))`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_IMAGE; EXISTS_PAIR_THM; IN_CROSS; IN_NUMSEG] THEN
    X_GEN_TAC `r:num` THEN EQ_TAC THENL
     [STRIP_TAC THEN MAP_EVERY EXISTS_TAC [`r MOD p`; `r DIV p`] THEN
      ASM_SIMP_TAC[DIVISION; LE_0; ARITH_RULE `~(p = 0) ==> (x <= p - 1 <=> x < p)`] THEN
      ASM_SIMP_TAC[GSYM LT_SUC_LE; RDIV_LT_EQ] THEN NV_DET_ARITH_TAC;
      STRIP_TAC THEN ASM_REWRITE_TAC[LE_0] THEN
      SUBGOAL_THEN `p2 * p <= 47 * p` MP_TAC THENL
       [ASM_SIMP_TAC[LE_MULT_RCANCEL]; NV_DET_ARITH_TAC]];
    ALL_TAC]))
  THEN ((W(MP_TAC o PART_MATCH (lhand o rand) NV_DET_REINDEX o lhand o snd)))
  THEN ((ANTS_TAC THENL
   [SIMP_TAC[FINITE_CROSS; FINITE_NUMSEG; FORALL_PAIR_THM; IN_CROSS; IN_NUMSEG; PAIR_EQ] THEN
    MAP_EVERY X_GEN_TAC [`i:num`; `r:num`; `j:num`; `k:num`] THEN STRIP_TAC THEN
    UNDISCH_TAC `r * p + i = k * p + j:num` THEN
    DISCH_THEN(fun th -> MP_TAC(AP_TERM `\x. x MOD p` th) THEN MP_TAC(AP_TERM `\x. x DIV p` th)) THEN
    SUBGOAL_THEN `i < p /\ j < p:num` STRIP_ASSUME_TAC THENL [NV_DET_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[] THEN
    ASM_SIMP_TAC[DIV_MULT_ADD; MOD_MULT_ADD; DIV_LT; MOD_LT;
                 ARITH_RULE `~(p = 0) ==> (x <= p - 1 <=> x < p)`] THEN ARITH_TAC;
    DISCH_THEN SUBST1_TAC]))
  THEN (MP_TAC(ISPECL [`p:num`; `\c. ring_det real_ring (0..47) (\u v. (B0:num->num->real) u v + c * B1 u v)`] NV_DET_LAMPROD) THEN
        ASM_REWRITE_TAC[REAL_MUL_LZERO; REAL_ADD_RID; REAL_MUL_LID; ETA_AX;
              REAL_ARITH `x + --(&1) * y = x - y`] THEN DISCH_THEN(SUBST1_TAC o SYM))
  THEN ((ASM_SIMP_TAC[GSYM NV_DET_X]))
  THEN ((MATCH_MP_TAC NV_DET_EQ))
  THEN ((REWRITE_TAC[FORALL_PAIR_THM; IN_CROSS; IN_NUMSEG]))
  THEN ((MAP_EVERY X_GEN_TAC [`i:num`; `r:num`; `j:num`; `k:num`]))
  THEN ((STRIP_TAC))
  THEN ((W(MP_TAC o PART_MATCH (lhand o rand) NV_DET_MK o rand o snd)))
  THEN ((REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG]))
  THEN ((ANTS_TAC THENL [NV_DET_ARITH_TAC; DISCH_THEN SUBST1_TAC]))
  THEN ((REWRITE_TAC[FST; SND]))
  THEN ((SUBGOAL_THEN `i < p /\ j < p:num` STRIP_ASSUME_TAC THENL [NV_DET_ARITH_TAC; ALL_TAC]))
  THEN ((ASM_SIMP_TAC[DIV_MULT_ADD; MOD_MULT_ADD; DIV_LT; MOD_LT; ADD_CLAUSES]))
  THEN ((REWRITE_TAC[nv_det_pi]))
  THEN ((COND_CASES_TAC))
  THEN ((ASM_REWRITE_TAC[]))
  THEN ((COND_CASES_TAC))
  THEN ((TRY(FIRST_X_ASSUM(MP_TAC o check (is_neg o concl)))))
  THEN ((NV_DET_ARITH_TAC)));;




