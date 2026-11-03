(* ========================================================================= *)
(* EN part (Section 6, Proposition 6.1): internal definitions shared by the *)
(* EN sub-agents.  Owned by the EN worker; FROZEN for EN sub-agents.         *)
(* ========================================================================= *)

needs "src/catalan_rp_defs.ml";;

(* P_r(u,v) = |1 - r e^{i(a+b)}|^2 |1 - r e^{i(a-b)}|^2 for u = cos a,      *)
(* v = cos b, written as a polynomial in u, v                                *)
let rp_en_P = new_definition
 `rp_en_P r u v =
    (&1 + r pow 2) pow 2 - &4 * r * (&1 + r pow 2) * u * v +
    &4 * r pow 2 * (u pow 2 + v pow 2 - &1)`;;

(* damped cosine kernel L_r(u,v), Equation (81) *)
let rp_en_L = new_definition
 `rp_en_L r u v = --log(&2) + log(rp_en_P r u v) / &2`;;

(* damping factors, Equation (83); tau = 1 - e is written inline *)
let rp_en_rho = new_definition
 `rp_en_rho e x = &1 - e * (&1 - x)`;;

let rp_en_sig = new_definition
 `rp_en_sig e s = &1 - e * sqrt(&1 - s)`;;

(* sum over pairs i < j < n *)
let rp_en_psum = new_definition
 `rp_en_psum n (f:num->num->real) =
    sum {j | j < n} (\j. sum {i | i < j} (\i. f i j))`;;

(* one-variable weights W_kappa, W_s of Equation (76) *)
let rp_en_W = new_definition
 `rp_en_W kappa x =
    &19 / &48 * log(abs x) + &1 / &12 * log(&1 - x) -
    (kappa / &2 + &17 / &48) * log(&1 + x pow 2)`;;

let rp_en_Ws = new_definition
 `rp_en_Ws s = &7 / &48 * log s + &1 / &12 * log(&1 - s)`;;

(* right side of the exact identity (80) *)
let rp_en_F = new_definition
 `rp_en_F kappa N (x:num->real) (s:num->real) =
    (&(63 * N) / &(48 * N) + (kappa - &2) / &2 -
     (kappa + &1) / (&2 * &(48 * N))) * log(&2) +
    sum {i | i < 48 * N}
      (\i. rp_en_W kappa (x i) +
           (kappa + &2) / (&2 * &(48 * N)) * log(&1 + x i pow 2)) / &(48 * N) +
    sum {j | j < 48 * N} (\j. rp_en_Ws (s j)) / &(48 * N) +
    kappa * rp_en_psum (48 * N) (\i j. log(abs(x j - x i))) / &(48 * N) pow 2 +
    rp_en_psum (48 * N) (\i j. log(&1 - x i * x j)) / &(48 * N) pow 2 +
    &2 * rp_en_psum (48 * N) (\i j. log(abs(s j - s i))) / &(48 * N) pow 2 -
    sum {i | i < 48 * N}
      (\i. sum {j | j < 48 * N}
             (\j. log(&1 - &2 * x i * s j + x i pow 2))) / &(48 * N) pow 2`;;
