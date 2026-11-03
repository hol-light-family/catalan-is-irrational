(* ========================================================================= *)
(* The statement: Catalan's constant is irrational.                         *)
(*                                                                           *)
(* This is the only file that must be read to know what is proved.  It uses *)
(* the standard HOL Light notions real_infsum (Multivariate/realanalysis.ml) *)
(* and rational (Library/floor.ml).                                          *)
(*                                                                           *)
(*   G = sum_{j >= 0} (-1)^j / (2 j + 1)^2                                   *)
(* ========================================================================= *)

needs "Multivariate/realanalysis.ml";;
needs "Library/floor.ml";;

let catalan_constant = new_definition
 `catalan_constant =
    real_infsum (from 0) (\j. --(&1) pow j / &(2 * j + 1) pow 2)`;;

let CATALAN_IRRATIONAL_STATEMENT = new_definition
 `CATALAN_IRRATIONAL_STATEMENT <=> ~(rational catalan_constant)`;;
