(* ========================================================================= *)
(* The four components of the proof and their assembly (paper, Section 8).   *)
(*                                                                           *)
(*  CAT_RATIONALITY   Proposition 2.1: with z = G, the rational formula     *)
(*                    cat_detq equals the integral determinant cat_det.     *)
(*  CAT_FINITE_PLACE  Proposition 3.4 (with Proposition 2.2): for every     *)
(*                    rational z, the product formula lower bound.          *)
(*  CAT_NONVANISHING  Proposition 4.1: for every rational z, cat_detq z p   *)
(*                    is nonzero at every sufficiently large prime p.       *)
(*  CAT_REAL_PLACE    Proposition 7.1: the real-place upper bound.          *)
(* ========================================================================= *)

needs "src/catalan_defs.ml";;

let CAT_RATIONALITY = new_definition
 `CAT_RATIONALITY <=>
    forall N. 1 <= N ==> cat_detq catalan_constant N = cat_det N`;;

let CAT_FINITE_PLACE = new_definition
 `CAT_FINITE_PLACE <=>
    forall z. rational z
        ==> exists N0. forall N. N0 <= N /\ ~(cat_detq z N = &0)
                     ==> --(&229084 / &100000) < cat_nlog N (cat_detq z N)`;;

let CAT_NONVANISHING = new_definition
 `CAT_NONVANISHING <=>
    forall z. rational z
        ==> exists P0. forall p. prime p /\ P0 <= p ==> ~(cat_detq z p = &0)`;;

let CAT_REAL_PLACE = new_definition
 `CAT_REAL_PLACE <=>
    exists N0. forall N. N0 <= N /\ ~(cat_det N = &0)
             ==> cat_nlog N (cat_det N) < --(&22909 / &10000)`;;

let CATALAN_FROM_COMPONENTS = prove
 (`CAT_RATIONALITY /\ CAT_FINITE_PLACE /\ CAT_NONVANISHING /\ CAT_REAL_PLACE
   ==> CATALAN_IRRATIONAL_STATEMENT`,
  REWRITE_TAC[CAT_RATIONALITY; CAT_FINITE_PLACE; CAT_NONVANISHING;
              CAT_REAL_PLACE; CATALAN_IRRATIONAL_STATEMENT] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "rat")
   (CONJUNCTS_THEN2 (LABEL_TAC "fin")
   (CONJUNCTS_THEN2 (LABEL_TAC "nv") (X_CHOOSE_TAC `N0:num`)))) THEN
  DISCH_TAC THEN
  REMOVE_THEN "nv" (MP_TAC o SPEC `catalan_constant`) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `P0:num`) THEN
  REMOVE_THEN "fin" (MP_TAC o SPEC `catalan_constant`) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `N1:num`) THEN
  MP_TAC(SPEC `N0 + N1 + P0 + 1` EUCLID) THEN
  DISCH_THEN(X_CHOOSE_THEN `p:num` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `1 <= p /\ N0 <= p /\ N1 <= p /\ P0 <= p`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `p > N0 + N1 + P0 + 1` THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `~(cat_detq catalan_constant p = &0)` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `cat_detq catalan_constant p = cat_det p` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `--(&229084 / &100000) < cat_nlog p (cat_det p) /\
    cat_nlog p (cat_det p) < --(&22909 / &10000)` MP_TAC THENL
   [ASM_MESON_TAC[]; REAL_ARITH_TAC]);;
