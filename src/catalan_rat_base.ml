(* ========================================================================= *)
(* CAT_RATIONALITY: shared basic definitions (prefix rat).                   *)
(* ========================================================================= *)

needs "src/catalan_defs.ml";;

(* Inner integral g_j(t) = int_0^1 s^j / (1 - t s) ds *)
let rat_g = new_definition
 `rat_g j t = real_integral (real_interval[&0,&1]) (\s. s pow j / (&1 - t * s))`;;

(* Monomial moments M(i,j), Z(i,j) of Equation (6) *)
let rat_M = new_definition
 `rat_M i j = cat_mixed (\t. t pow i) (\s. s pow j)`;;

let rat_Z = new_definition
 `rat_Z i j = cat_zeta (\t. t pow i) (\s. s pow j)`;;

(* zeta(2), realised as Z(0,0) *)
let rat_kappa = new_definition
 `rat_kappa = rat_Z 0 0`;;
