(* ========================================================================= *)
(* HOL Light proof that Catalan's constant is irrational.                    *)
(*                                                                           *)
(* Start HOL Light (hol.sh) in this directory, then                          *)
(*   loadt "make.ml";;                                                       *)
(* This loads the development, prints the headline theorems and checks that  *)
(* no axioms beyond HOL Light's three standard ones are used.                *)
(* ========================================================================= *)

needs "100/pnt.ml";;
needs "src/catalan_main.ml";;

(* Expected output:
- : thm =
|- (exists G. ((\j. -- &1 pow j / &(2 * j + 1) pow 2) real_sums G) (from 0)) /\
   (forall G.
        ((\j. -- &1 pow j / &(2 * j + 1) pow 2) real_sums G) (from 0)
        ==> ~(exists m n. integer m /\ integer n /\ ~(n = &0) /\ G = m / n))
*)
CATALAN_CONSTANT_IRRATIONAL_HEADLINE;;

(* Expected output:
- : thm = |- ~rational catalan_constant
*)
CATALAN_CONSTANT_IRRATIONAL;;

(* Expected output:
- : thm = |- CATALAN_IRRATIONAL_STATEMENT
*)
CATALAN_IRRATIONAL;;

check_axioms ();;
