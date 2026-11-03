(* ========================================================================= *)
(* Definitions used inside the proof (not part of the trusted statement).    *)
(*                                                                           *)
(* Notation follows the paper "Catalan's constant is irrational" (OpenAI,    *)
(* 2026-09-24), Equations (2)-(8), (9)-(16).  For a positive integer N:      *)
(*   n = 48N, a = 11N, b = 7N, q = g = 4N, h = 2N, L = 59N, C = 63N,         *)
(*   H = 65N, A = 19N.                                                       *)
(* ========================================================================= *)

needs "src/catalan_statement.ml";;
needs "Library/permutations.ml";;
needs "Library/binomial.ml";;
needs "Library/prime.ml";;

(* ------------------------------------------------------------------------- *)
(* Determinant of a square array indexed by a finite set of numbers.         *)
(* ------------------------------------------------------------------------- *)

let ndet = new_definition
 `ndet (s:num->bool) (a:num->num->real) =
    sum {p | p permutes s} (\p. sign p * product s (\i. a i (p i)))`;;

(* ------------------------------------------------------------------------- *)
(* Chebyshev polynomials T_d and U_d as coefficient arrays: cheb_T d k is    *)
(* the coefficient of x^k in T_d(x).                                         *)
(* ------------------------------------------------------------------------- *)

let cheb_T = define
 `(forall k. cheb_T 0 k = if k = 0 then &1 else &0) /\
  (forall k. cheb_T (SUC 0) k = if k = 1 then &1 else &0) /\
  (forall d k. cheb_T (SUC(SUC d)) k =
         (if k = 0 then &0 else &2 * cheb_T (SUC d) (k - 1)) - cheb_T d k)`;;

let cheb_U = define
 `(forall k. cheb_U 0 k = if k = 0 then &1 else &0) /\
  (forall k. cheb_U (SUC 0) k = if k = 1 then &2 else &0) /\
  (forall d k. cheb_U (SUC(SUC d)) k =
         (if k = 0 then &0 else &2 * cheb_U (SUC d) (k - 1)) - cheb_U d k)`;;

(* ------------------------------------------------------------------------- *)
(* Reversal: coefficients of t^(C-1) F(1/t) for deg F < C.                   *)
(* ------------------------------------------------------------------------- *)

let cat_revc = new_definition
 `cat_revc C (c:num->real) m = if m < C then c (C - 1 - m) else &0`;;

(* ------------------------------------------------------------------------- *)
(* Row data: |r - g| and sgn(r - g).                                         *)
(* ------------------------------------------------------------------------- *)

let cat_dist = new_definition
 `cat_dist N r = if r < 4 * N then 4 * N - r else r - 4 * N`;;

let cat_sgn = new_definition
 `cat_sgn N r = if r < 4 * N then --(&1) else if r = 4 * N then &0 else &1`;;

(* Coefficient of t^i in (1 - t)^h * F(t), F given by coefficients c.        *)

let cat_mulfac = new_definition
 `cat_mulfac h (c:num->real) i =
    sum (0..h) (\v. if v <= i then (--(&1)) pow v * &(binom(h,v)) * c (i - v)
                   else &0)`;;

(* Coefficients of P_r = (1-t)^h t^(C-1) T_d(1/t), D_r = sgn (1-t)^h         *)
(* t^(C-1) U_(d-1)(1/t), d = |r - g|.                                         *)

let cat_pcoef = new_definition
 `cat_pcoef N r i =
    cat_mulfac (2 * N) (cat_revc (63 * N) (cheb_T (cat_dist N r))) i`;;

let cat_dcoef = new_definition
 `cat_dcoef N r i =
    cat_sgn N r *
    cat_mulfac (2 * N) (cat_revc (63 * N) (cheb_U (cat_dist N r - 1))) i`;;

let cat_poly = new_definition
 `cat_poly H (c:num->real) t = sum (0..H) (\i. c i * t pow i)`;;

let cat_rowP = new_definition
 `cat_rowP N r t = cat_poly (65 * N) (cat_pcoef N r) t`;;

let cat_rowD = new_definition
 `cat_rowD N r t = cat_poly (65 * N) (cat_dcoef N r) t`;;

(* Filtered column psi_k(s) = s^(b+k) (1-s)^q.                               *)

let cat_psi = new_definition
 `cat_psi N k s = s pow (7 * N + k) * (&1 - s) pow (4 * N)`;;

(* ------------------------------------------------------------------------- *)
(* The two moment functionals and the determinant Delta_N, Equation (7).    *)
(* ------------------------------------------------------------------------- *)

let cat_mixed = new_definition
 `cat_mixed (P:real->real) (Q:real->real) =
    real_integral (real_interval[--(&1),&1])
     (\t. real_integral (real_interval[&0,&1])
           (\s. abs t / sqrt(&1 - t pow 2) * (P t * Q s) / (&1 - t * s)))`;;

let cat_zeta = new_definition
 `cat_zeta (P:real->real) (Q:real->real) =
    real_integral (real_interval[&0,&1])
     (\t. real_integral (real_interval[&0,&1])
           (\s. (P t * Q s) / (&1 - t * s)))`;;

let cat_entry = new_definition
 `cat_entry N r k =
    cat_mixed (cat_rowP N r) (cat_psi N k) -
    &3 / &2 * cat_zeta (cat_rowD N r) (cat_psi N k)`;;

let cat_det = new_definition
 `cat_det N = ndet (0..48 * N - 1) (cat_entry N)`;;

(* ------------------------------------------------------------------------- *)
(* Rational arrays, Equations (9)-(16).                                      *)
(* ------------------------------------------------------------------------- *)

(* c_l = 4^(-l) binom(2l,l) *)
let cat_c = new_definition
 `cat_c l = &(binom(2 * l,l)) / &4 pow l`;;

(* c_((i-j)/2), zero unless i - j is a nonnegative even integer *)
let cat_ckern = new_definition
 `cat_ckern i j = if j <= i /\ EVEN(i - j) then cat_c ((i - j) DIV 2) else &0`;;

(* m_i = int_{-1}^{1} |t| t^i / sqrt(1 - t^2) dt *)
let cat_m = new_definition
 `cat_m i = if EVEN i then &2 / (&(i + 1) * cat_c (i DIV 2)) else &0`;;

let cat_kminus = define
 `cat_kminus 0 = &0 /\
  cat_kminus (SUC 0) = &2 /\
  (forall d. cat_kminus (SUC(SUC d)) =
       (&(d + 1) * cat_kminus d + cat_m d + cat_m (d + 1)) / &(d + 2))`;;

let cat_kplus = define
 `cat_kplus 0 = &0 /\
  cat_kplus (SUC 0) = &0 /\
  (forall d. cat_kplus (SUC(SUC d)) =
       (&d * cat_kplus d + &2 / &(d + 1)) / &(d + 1))`;;

(* M'(i,j), Equation (14) *)
let cat_M0 = new_definition
 `cat_M0 i j =
    if j <= i then cat_kminus (i - j) - sum (1..j) (\k. cat_m (i - j + k - 1) / &k)
    else cat_kplus (j - i) - sum (1..i) (\k. cat_m (k - 1) / &(j - i + k))`;;

let cat_harm = new_definition
 `cat_harm d n = sum (1..n) (\k. &1 / &k pow d)`;;

(* Z'(i,j), Equation (16) *)
let cat_Z0 = new_definition
 `cat_Z0 i j =
    if i = j then --(cat_harm 2 i)
    else (cat_harm 1 i - cat_harm 1 j) / (&i - &j)`;;

(* Raw entry F_j(r) with G replaced by z, Equation (20) *)
let cat_rawq = new_definition
 `cat_rawq z N r j =
    sum (0..65 * N) (\i. cat_pcoef N r i * (cat_M0 i j + &4 * z * cat_ckern i j)) -
    &3 / &2 * sum (0..65 * N) (\i. cat_dcoef N r i * cat_Z0 i j)`;;

(* Filtered entry: column k of F T, Equation (8) *)
let cat_entryq = new_definition
 `cat_entryq z N r k =
    sum (0..4 * N) (\v. (--(&1)) pow v * &(binom(4 * N,v)) *
                        cat_rawq z N r (7 * N + k + v))`;;

let cat_detq = new_definition
 `cat_detq z N = ndet (0..48 * N - 1) (cat_entryq z N)`;;

(* ------------------------------------------------------------------------- *)
(* The normalized logarithm L_N of Equation (1).                             *)
(* ------------------------------------------------------------------------- *)

let cat_nlog = new_definition
 `cat_nlog N x = log(abs x) / &(48 * N) pow 2 - log(&2) / &2`;;
