(* ========================================================================= *)
(* rp_alg: basic facts about ndet (real determinants over num index sets),   *)
(* obtained from Library/ring_det.ml via real_ring.                          *)
(* ========================================================================= *)

needs "src/catalan_rp_defs.ml";;
needs "Library/ring_det.ml";;

let RP_ALG_NDET_RING = prove
 (`forall s a. ndet s a = ring_det real_ring s a`,
  REWRITE_TAC[ndet; ring_det; ring_sign; REAL_RING_SUM; REAL_RING_PRODUCT;
              REAL_RING_CLAUSES; sign] THEN
  REPEAT GEN_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN
  GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[]);;

let RP_ALG_NDET_TRANSP = prove
 (`forall s a. FINITE s ==> ndet s (\i j. a j i) = ndet s a`,
  SIMP_TAC[RP_ALG_NDET_RING; RING_DET_TRANSP]);;

let RP_ALG_NDET_EQ = prove
 (`forall s a b. (forall i j. i IN s /\ j IN s ==> a i j = b i j)
           ==> ndet s a = ndet s b`,
  REWRITE_TAC[RP_ALG_NDET_RING] THEN MESON_TAC[RING_DET_EQ]);;

let RP_ALG_NDET_ROWS_MUL = prove
 (`forall s c a. FINITE s
           ==> ndet s (\i j. c i * a i j) = product s c * ndet s a`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[RP_ALG_NDET_RING] THEN
  MP_TAC(ISPECL [`real_ring`; `s:num->bool`; `c:num->real`;
                 `a:num->num->real`] RING_DET_ROWS_MUL) THEN
  ASM_REWRITE_TAC[REAL_RING_CLAUSES; IN_UNIV; REAL_RING_PRODUCT]);;

let RP_ALG_NDET_COLUMNS_MUL = prove
 (`forall s c a. FINITE s
           ==> ndet s (\i j. a i j * c j) = ndet s a * product s c`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[RP_ALG_NDET_RING] THEN
  MP_TAC(ISPECL [`real_ring`; `s:num->bool`; `c:num->real`;
                 `a:num->num->real`] RING_DET_COLUMNS_MUL) THEN
  ASM_REWRITE_TAC[REAL_RING_CLAUSES; IN_UNIV; REAL_RING_PRODUCT]);;

let RP_ALG_NDET_ROW_OPERATION = prove
 (`forall s a k l c.
        FINITE s /\ k IN s /\ l IN s /\ ~(k = l)
        ==> ndet s (\i j. if i = k then a k j + c * a l j else a i j) =
            ndet s a`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[RP_ALG_NDET_RING] THEN
  MP_TAC(ISPECL [`real_ring`; `s:num->bool`; `a:num->num->real`;
                 `k:num`; `l:num`; `c:real`] RING_DET_ROW_OPERATION) THEN
  ASM_REWRITE_TAC[REAL_RING_CLAUSES; IN_UNIV]);;

(* subtract multiples of row l from all rows in a set k not containing l *)
let RP_ALG_NDET_ROWS_OPERATION = prove
 (`forall s a l c k.
        FINITE s /\ l IN s /\ k SUBSET s /\ ~(l IN k)
        ==> ndet s (\i j. if i IN k then a i j + c i * a l j else a i j) =
            ndet s a`,
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `FINITE(s:num->bool)` THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `(l:num) IN s` THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `FINITE(k:num->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[FINITE_SUBSET]; ALL_TAC] THEN
  UNDISCH_TAC `k SUBSET (s:num->bool)` THEN UNDISCH_TAC `~((l:num) IN k)` THEN
  UNDISCH_TAC `FINITE(k:num->bool)` THEN
  SPEC_TAC(`k:num->bool`,`k:num->bool`) THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  REWRITE_TAC[NOT_IN_EMPTY; ETA_AX] THEN
  MAP_EVERY X_GEN_TAC [`m:num`; `k:num->bool`] THEN
  REWRITE_TAC[IN_INSERT; INSERT_SUBSET; DE_MORGAN_THM] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  MP_TAC(ISPECL
   [`s:num->bool`;
    `\i j. if i IN k then (a:num->num->real) i j + c i * a l j else a i j`;
    `m:num`; `l:num`; `(c:num->real) m`] RP_ALG_NDET_ROW_OPERATION) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; ASM_REWRITE_TAC[]] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC RP_ALG_NDET_EQ THEN REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `i:num = m` THEN ASM_REWRITE_TAC[]);;

let RP_ALG_NDET_COLUMNS_OPERATION = prove
 (`forall s a l c k.
        FINITE s /\ l IN s /\ k SUBSET s /\ ~(l IN k)
        ==> ndet s (\i j. if j IN k then a i j + c j * a i l else a i j) =
            ndet s a`,
  REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[GSYM(MATCH_MP RP_ALG_NDET_TRANSP
    (ASSUME `FINITE(s:num->bool)`))] THEN
  REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`s:num->bool`; `\i j. (a:num->num->real) j i`;
                 `l:num`; `c:num->real`; `k:num->bool`]
                RP_ALG_NDET_ROWS_OPERATION) THEN
  REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

(* last row is (0,...,0,1) on {i | i < SUC n} *)
let RP_ALG_NUMSEG_LT_SUC = prove
 (`forall n. {i | i < SUC n} = {n} UNION {i | i < n}`,
  REWRITE_TAC[EXTENSION; IN_UNION; IN_SING; IN_ELIM_THM] THEN ARITH_TAC);;

let RP_ALG_NUMSEG_LT_INSERT = prove
 (`forall n. {i | i < SUC n} = n INSERT {i | i < n}`,
  REWRITE_TAC[EXTENSION; IN_INSERT; IN_ELIM_THM] THEN ARITH_TAC);;

let RP_ALG_NDET_LASTROW = prove
 (`forall n a. (forall j. j < n ==> a n j = &0)
         ==> ndet {i | i < SUC n} a = a n n * ndet {i | i < n} a`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[RP_ALG_NDET_RING; RP_ALG_NUMSEG_LT_SUC] THEN
  MP_TAC(ISPECL [`real_ring`; `{n:num}`; `{i:num | i < n}`;
                 `a:num->num->real`] RING_DET_BLOCK_TRIANGULAR) THEN
  REWRITE_TAC[FINITE_SING; FINITE_NUMSEG_LT; REAL_RING_CLAUSES; IN_UNIV] THEN
  ANTS_TAC THENL
   [REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; IN_SING; IN_ELIM_THM;
                NOT_IN_EMPTY] THEN
    REPEAT CONJ_TAC THEN TRY ARITH_TAC THEN ASM_MESON_TAC[];
    DISCH_THEN SUBST1_TAC] THEN
  SIMP_TAC[RING_DET_SING; REAL_RING_CLAUSES; IN_UNIV]);;

let RP_ALG_NDET_VANDERMONDE = prove
 (`forall n x. ndet {i | i < n} (\i j. x i pow j) = rp_vdm n x`,
  REWRITE_TAC[RP_ALG_NDET_RING; rp_vdm] THEN REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`real_ring`; `n:num`; `x:num->real`]
    RING_DET_VANDERMONDE) THEN
  REWRITE_TAC[REAL_RING_CLAUSES; IN_UNIV; REAL_RING_POW; REAL_RING_SUB;
              REAL_RING_PRODUCT]);;

let RP_ALG_PRODUCT_LT_SUC = prove
 (`forall n f. product {i | i < SUC n} f = f n * product {i | i < n} f`,
  REWRITE_TAC[RP_ALG_NUMSEG_LT_INSERT] THEN
  SIMP_TAC[PRODUCT_CLAUSES; FINITE_NUMSEG_LT; IN_ELIM_THM; LT_REFL]);;

let RP_ALG_NDET_EMPTY = prove
 (`forall a. ndet {i | i < 0} a = &1`,
  REWRITE_TAC[LT; EMPTY_GSPEC; RP_ALG_NDET_RING; RING_DET_EMPTY;
              REAL_RING_CLAUSES]);;

let RP_ALG_VDM_SUC = prove
 (`forall n y. rp_vdm (SUC n) y =
         rp_vdm n y * product {i | i < n} (\i. y n - y i)`,
  REWRITE_TAC[rp_vdm; RP_ALG_NUMSEG_LT_INSERT] THEN
  SIMP_TAC[PRODUCT_CLAUSES; FINITE_NUMSEG_LT; IN_ELIM_THM; LT_REFL] THEN
  REPEAT GEN_TAC THEN MATCH_ACCEPT_TAC REAL_MUL_SYM);;

(* generalize all closed-in-context subterms headed by the given constants *)
let rec rp_alg_tsize t =
  match t with
    Comb(a,b) -> 1 + rp_alg_tsize a + rp_alg_tsize b
  | Abs(_,b) -> 1 + rp_alg_tsize b
  | _ -> 1;;

let RP_ALG_GEN_CONSTS_TAC names : tactic =
  fun (asl,w as gl) ->
    let ok t =
      try let h,_ = strip_comb t in is_const h && mem (fst(dest_const h)) names
      with Failure _ -> false in
    let ts = find_terms ok w in
    let ts = sort (fun a b -> rp_alg_tsize a > rp_alg_tsize b) ts in
    MAP_EVERY (fun t -> TRY(SPEC_TAC(t,genvar(type_of t)))) ts gl;;
