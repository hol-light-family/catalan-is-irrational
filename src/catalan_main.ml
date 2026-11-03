(* ========================================================================= *)
(* The main theorem: Catalan's constant is irrational.                       *)
(*                                                                           *)
(* The headline theorem CATALAN_CONSTANT_IRRATIONAL_HEADLINE, at the end of  *)
(* this file, is stated using only standard HOL Light notions, with nothing  *)
(* from this development unfolded or hidden:                                 *)
(*                                                                           *)
(*   |- (exists G.                                                           *)
(*        ((\j. --(&1) pow j / &(2 * j + 1) pow 2) real_sums G) (from 0))    *)
(*      /\                                                                   *)
(*      (forall G.                                                           *)
(*        ((\j. --(&1) pow j / &(2 * j + 1) pow 2) real_sums G) (from 0)     *)
(*        ==> ~(exists m n. integer m /\ integer n /\ ~(n = &0) /\           *)
(*              G = m / n))                                                  *)
(*                                                                           *)
(* In words: the series  sum_{j >= 0} (-1)^j / (2j + 1)^2  converges, and    *)
(* its sum G (Catalan's constant) is not a quotient m / n of integers with   *)
(* n nonzero.  The notions used are HOL Light's own:                         *)
(*   (f real_sums l) (from 0)  the partial sums f(0) + ... + f(k) tend to l  *)
(*                             (Multivariate/realanalysis.ml);               *)
(*   integer x                 abs(x) = &n for some natural number n         *)
(*                             (int.ml, part of core HOL Light);             *)
(*   &k                        the natural number k as a real number.        *)
(*                                                                           *)
(* The same result, phrased with the definitions of catalan_statement.ml,    *)
(* is CATALAN_IRRATIONAL (|- CATALAN_IRRATIONAL_STATEMENT) and               *)
(* CATALAN_CONSTANT_IRRATIONAL (|- ~(rational catalan_constant)).            *)
(* ========================================================================= *)

(* Each component was developed and checked in a session where Multivariate *)
(* complex analysis had just been loaded, so untyped arithmetic defaults to  *)
(* the complex numbers.  Some components switch the default to the reals     *)
(* with prioritize_real(); restore the original default before each one so   *)
(* that every component is parsed exactly as when it was checked.           *)

prioritize_complex();;
needs "src/catalan_components.ml";;
prioritize_complex();;
needs "src/catalan_rat_final.ml";;
prioritize_complex();;
needs "src/catalan_fin_final.ml";;
prioritize_complex();;
needs "src/catalan_nv_final.ml";;
prioritize_complex();;
needs "src/catalan_rp_final.ml";;
prioritize_real();;

let CATALAN_IRRATIONAL = prove
 (`CATALAN_IRRATIONAL_STATEMENT`,
  MATCH_MP_TAC CATALAN_FROM_COMPONENTS THEN
  REWRITE_TAC[CAT_RATIONALITY_THM; CAT_FINITE_PLACE_THM;
              CAT_NONVANISHING_THM; CAT_REAL_PLACE_THM]);;

let CATALAN_CONSTANT_IRRATIONAL = prove
 (`~(rational catalan_constant)`,
  REWRITE_TAC[GSYM CATALAN_IRRATIONAL_STATEMENT; CATALAN_IRRATIONAL]);;

(* ------------------------------------------------------------------------- *)
(* The headline theorem, with every definition unfolded.                     *)
(* ------------------------------------------------------------------------- *)

let CATALAN_CONSTANT_IRRATIONAL_HEADLINE = prove
 (`(exists G. ((\j. --(&1) pow j / &(2 * j + 1) pow 2) real_sums G) (from 0)) /\
   (forall G. ((\j. --(&1) pow j / &(2 * j + 1) pow 2) real_sums G) (from 0)
        ==> ~(exists m n. integer m /\ integer n /\ ~(n = &0) /\ G = m / n))`,
  CONJ_TAC THENL
   [MESON_TAC[RAT_C_CATSERIES];
    GEN_TAC THEN
    DISCH_THEN(fun th -> ASSUME_TAC(SYM(MATCH_MP REAL_INFSUM_UNIQUE th))) THEN
    MP_TAC CATALAN_CONSTANT_IRRATIONAL THEN
    ASM_REWRITE_TAC[catalan_constant; rational]]);;
