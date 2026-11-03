(* ========================================================================= *)
(* CAT_FINITE_PLACE, columns at odd primes (prefix fin_col_): final file.    *)
(* Discharges the scalar digit reductions (fin_dig_) in FIN_COL_ODD_BOUND.   *)
(* ========================================================================= *)

needs "src/catalan_fin_col_odd.ml";;
needs "src/catalan_fin_dig.ml";;

let FIN_COL_DIGHYPS = prove
 (`fin_col_dighyps`,
  REWRITE_TAC[fin_col_dighyps] THEN REPEAT CONJ_TAC THEN
  FIRST (map MATCH_ACCEPT_TAC
    [FIN_DIG_LEMMA31_M; FIN_DIG_LEMMA31_Z; FIN_DIG_CENTRAL_M; FIN_DIG_CENTRAL_Z]));;

let FIN_COL_ODD_BOUND = prove
 (`forall z N p. rational z /\ 1 <= N /\ prime p /\ ~(p = 2) /\ 4 * (65 * N) < p * p /\
           p <= 65 * N /\ fin_zp p z
           ==> fin_vge p (--(&(fin_loss N p))) (cat_detq z N)`,
  MP_TAC FIN_COL_ODD_BOUND_COND THEN REWRITE_TAC[FIN_COL_DIGHYPS]);;
