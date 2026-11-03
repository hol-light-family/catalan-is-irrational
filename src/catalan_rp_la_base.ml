(* ========================================================================= *)
(* rp_la_: num-indexed real determinants as ring_det over real_ring.         *)
(* ========================================================================= *)

needs "src/catalan_rp_defs.ml";;
needs "Library/ring_det.ml";;

let RP_LA_NDET_RING = prove
 (`forall s (a:num->num->real). ndet s a = ring_det real_ring s a`,
  REWRITE_TAC[ndet; ring_det; ring_sign; sign; REAL_RING_SUM;
              REAL_RING_PRODUCT; REAL_RING_CLAUSES]);;

let RP_LA_RR th = REWRITE_RULE[GSYM RP_LA_NDET_RING; REAL_RING_SUM;
   REAL_RING_PRODUCT; REAL_RING_CLAUSES; REAL_RING_POW; IN_UNIV] (INST_TYPE [`:num`,`:A`] th);;

let RP_LA_NDET_MUL = prove
 (`forall s (a:num->num->real) b.
        FINITE s
        ==> ndet s (\i j. sum s (\k. a i k * b k j)) = ndet s a * ndet s b`,
  SIMP_TAC[RP_LA_RR (ISPEC `real_ring` RING_DET_MUL)]);;

let RP_LA_NDET_TRANSP = prove
 (`forall s (a:num->num->real). FINITE s ==> ndet s (\i j. a j i) = ndet s a`,
  SIMP_TAC[RP_LA_RR (ISPEC `real_ring` RING_DET_TRANSP)]);;

let RP_LA_NDET_CMUL = prove
 (`forall s (a:num->num->real) c.
        FINITE s ==> ndet s (\i j. c * a i j) = c pow (CARD s) * ndet s a`,
  SIMP_TAC[RP_LA_RR (ISPEC `real_ring` RING_DET_CMUL)]);;

let RP_LA_NDET_BLOCK = prove
 (`forall s t (f:num->num->real).
        FINITE s /\ FINITE t /\ DISJOINT s t /\
        (forall i j. i IN s /\ j IN t ==> f i j = &0)
        ==> ndet (s UNION t) f = ndet s f * ndet t f`,
  SIMP_TAC[RP_LA_RR (ISPEC `real_ring` RING_DET_BLOCK_TRIANGULAR)]);;

let RP_LA_NDET_UPPER = prove
 (`forall s (f:num->num->real).
        FINITE s /\ (forall i j. i IN s /\ j IN s /\ j < i ==> f i j = &0)
        ==> ndet s f = product s (\i. f i i)`,
  SIMP_TAC[RP_LA_RR (ISPEC `real_ring` RING_DET_UPPERTRIANGULAR)]);;

let RP_LA_NDET_SING = prove
 (`forall a (f:num->num->real). ndet {a} f = f a a`,
  REWRITE_TAC[RP_LA_RR (ISPEC `real_ring` RING_DET_SING)]);;

let RP_LA_NDET_EMPTY = prove
 (`forall (f:num->num->real). ndet {} f = &1`,
  REWRITE_TAC[RP_LA_RR (ISPEC `real_ring` RING_DET_EMPTY)]);;

let RP_LA_NDET_EQ = prove
 (`forall s (f:num->num->real) g.
        (forall i j. i IN s /\ j IN s ==> f i j = g i j) ==> ndet s f = ndet s g`,
  REWRITE_TAC[RP_LA_RR (ISPEC `real_ring` RING_DET_EQ)]);;

let RP_LA_NDET_VANDERMONDE = prove
 (`forall n (x:num->real).
        ndet {i | i < n} (\i j. x i pow j) = rp_vdm n x`,
  REWRITE_TAC[rp_vdm; RP_LA_RR (ISPEC `real_ring` RING_DET_VANDERMONDE);
              REAL_RING_SUB]);;

let RP_LA_NDET_ROWS_MUL = prove
 (`forall s (c:num->real) (f:num->num->real).
        FINITE s
        ==> ndet s (\i j. c i * f i j) = product s c * ndet s f`,
  SIMP_TAC[RP_LA_RR (ISPEC `real_ring` RING_DET_ROWS_MUL)]);;

let RP_LA_NDET_MULTILINEAR = prove
 (`forall s (t:num->num->bool) (f:num->num->real) (g:num->num->num->real).
        FINITE s /\ (forall i. i IN s ==> FINITE(t i)) /\
        (forall i j. i IN s /\ j IN s ==> f i j = sum (t i) (\c. g i c j))
        ==> ndet s f =
            sum (cartesian_product s t) (\mu. ndet s (\i j. g i (mu i) j))`,
  REWRITE_TAC[RP_LA_RR (INST_TYPE [`:num`,`:C`]
    (ISPEC `real_ring` RING_DET_MULTILINEAR))]);;

let RP_LA_SUM_PRODUCT_CART = prove
 (`forall (k:num->bool) (t:num->num->bool) (g:num->num->real).
        FINITE k /\ (forall i. i IN k ==> FINITE(t i))
        ==> sum (cartesian_product k t) (\mu. product k (\i. g i (mu i))) =
            product k (\i. sum (t i) (g i))`,
  REWRITE_TAC[RP_LA_RR (INST_TYPE [`:num`,`:K`; `:num`,`:A`]
    (ISPEC `real_ring` RING_SUM_PRODUCT_CARTESIAN_PRODUCT))]);;

(* arithmetic on the num-only assumptions (avoids failures on real ones)  *)
let rp_la_numfml tm =
  not (can (find_term (fun t -> is_abs t || type_of t = `:real` ||
                                type_of t = `:complex`)) tm);;

let RP_LA_ARITH_TAC =
  W(fun (asl,w) ->
     MAP_EVERY (fun (_,th) -> if rp_la_numfml (concl th) then MP_TAC th
                              else ALL_TAC) asl THEN ARITH_TAC);;

let RP_LA_CONTR_TAC = MATCH_MP_TAC(TAUT `false ==> p`) THEN RP_LA_ARITH_TAC;;

(* swap the two outermost sums of  sum s (\i. sum t (\j. b))  (s, t finite *)
(* sets of the form {i | i < n} or anything FINITE_NUMSEG_LT/FINITE_* proves) *)
let RP_LA_SWAP_CONV tm =
  let s,lam = dest_comb tm in
  let s = rand s in
  let i,body = dest_abs lam in
  let t,lam2 = dest_comb body in
  let t = rand t in
  let j,b = dest_abs lam2 in
  let f = mk_abs(i,mk_abs(j,b)) in
  let th = ISPECL [f; s; t] SUM_SWAP in
  let th = CONV_RULE (DEPTH_CONV BETA_CONV) th in
  let fin = SIMP_CONV[FINITE_NUMSEG_LT; FINITE_NUMSEG; FINITE_INSERT;
                      FINITE_EMPTY] (lhand(concl th)) in
  MP th (EQT_ELIM fin);;
