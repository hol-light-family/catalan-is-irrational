(* ========================================================================= *)
(* CAT_FINITE_PLACE (paper Proposition 3.4 with Proposition 2.2).            *)
(* ========================================================================= *)

needs "src/catalan_fin_asm.ml";;
needs "src/catalan_fin_loss.ml";;
needs "src/catalan_fin_two.ml";;
needs "src/catalan_fin_col.ml";;

let CAT_FINITE_PLACE_THM = prove
 (`CAT_FINITE_PLACE`,
  MATCH_MP_TAC FIN_ASSEMBLY THEN REPEAT CONJ_TAC THENL
   [MATCH_ACCEPT_TAC FIN_TWO_ADIC;
    MATCH_ACCEPT_TAC FIN_COL_ODD_BOUND;
    MATCH_ACCEPT_TAC FIN_LOSS_LE_DFUN]);;
