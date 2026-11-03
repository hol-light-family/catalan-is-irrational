(* ========================================================================= *)
(* CAT_REAL_PLACE: shared definitions and interface statements for all      *)
(* sub-parts (paper Sections 5-7).  Owned by the rp lead; FROZEN for         *)
(* sub-agents (propose changes in doc/rp_PLAN.md).                           *)
(*                                                                           *)
(* N >= 1, n = 48N, a = 11N, b = 7N, g = q = 4N, h = 2N, C = 63N,            *)
(* D* = n - 1 - 2g = 40N - 1, A = a + 2g = 19N.                              *)
(* ========================================================================= *)

needs "src/catalan_components.ml";;

(* ------------------------------------------------------------------------- *)
(* Coordinates and configurations.                                           *)
(* ------------------------------------------------------------------------- *)

(* t = 2x/(1+x^2), Equation (64) *)
let rp_t = new_definition
 `rp_t x = &2 * x / (&1 + x pow 2)`;;

(* far / near sheet weights xi_f, xi_n (value at x = 0 immaterial) *)
let rp_xif = new_definition
 `rp_xif x = if x < &0 then &1 / &2 else --(&1 / &4)`;;

let rp_xin = new_definition
 `rp_xin x = if x < &0 then &1 / &2 else &5 / &4`;;

(* distinct nonzero nodes in (-1,1) *)
let rp_nodes = new_definition
 `rp_nodes n (x:num->real) <=>
    (forall i. i < n ==> --(&1) < x i /\ x i < &1 /\ ~(x i = &0)) /\
    (forall i j. i < n /\ j < n /\ x i = x j ==> i = j)`;;

(* interior configuration: x as above, s distinct in (0,1) *)
let rp_config = new_definition
 `rp_config N (x:num->real) (s:num->real) <=>
    rp_nodes (48 * N) x /\
    (forall j. j < 48 * N ==> &0 < s j /\ s j < &1) /\
    (forall i j. i < 48 * N /\ j < 48 * N /\ s i = s j ==> i = j)`;;

(* Vandermonde product V(y) = prod_{i<j<n} (y_j - y_i) *)
let rp_vdm = new_definition
 `rp_vdm n (y:num->real) =
    product {j | j < n} (\j. product {i | i < j} (\i. y j - y i))`;;

(* ------------------------------------------------------------------------- *)
(* Part INT/ALG: the row function in the x coordinate and the integrand of  *)
(* the (discretized) double Andreief expansion.                              *)
(*   rp_row N r x = (4|x|/(1+x^2)^2) (1-t)^h t^(C-1)                          *)
(*                   (xi_f(x) x^(g-r) + xi_n(x) x^(r-g)),  t = rp_t x,        *)
(* written with natural exponents (t^(C-1) = (2/(1+x^2))^(C-1) x^(C-1)):     *)
(* C-1+g-r = 67N-1-r, C-1+r-g = 59N-1+r.  NOTE: in HOL Light num "-" binds   *)
(* tighter than "+", and DIV tighter than "*"; parenthesize accordingly.     *)
(* ------------------------------------------------------------------------- *)

let rp_row = new_definition
 `rp_row N r x =
    &4 * abs x / (&1 + x pow 2) pow 2 *
    ((&1 - x) pow 2 / (&1 + x pow 2)) pow (2 * N) *
    (&2 / (&1 + x pow 2)) pow (63 * N - 1) *
    (rp_xif x * x pow (67 * N - 1 - r) +
     rp_xin x * x pow (59 * N - 1 + r))`;;

let rp_integrand = new_definition
 `rp_integrand N (x:num->real) (s:num->real) =
    ndet {i | i < 48 * N} (\r i. rp_row N r (x i)) *
    ndet {i | i < 48 * N} (\i j. inv(&1 - rp_t (x i) * s j)) *
    ndet {i | i < 48 * N} (\j k. cat_psi N k (s j))`;;

(* sheet determinant R'(x) = det[xi_f x_i^(n-1-r) + xi_n x_i^(r+Dstar)], Dstar = 40N-1 *)
let rp_R = new_definition
 `rp_R N (x:num->real) =
    ndet {i | i < 48 * N}
     (\r i. rp_xif (x i) * x i pow (48 * N - 1 - r) +
            rp_xin (x i) * x i pow (r + 40 * N - 1))`;;

(* ------------------------------------------------------------------------- *)
(* The principal integrand J_n and the two majorants I_1, I_2, Eq. (74).    *)
(* ------------------------------------------------------------------------- *)

let rp_J = new_definition
 `rp_J N (x:num->real) (s:num->real) =
    abs(rp_vdm (48 * N) (\i. rp_t (x i))) * rp_vdm (48 * N) s pow 2 /
    product {i | i < 48 * N}
      (\i. product {j | j < 48 * N} (\j. &1 - rp_t (x i) * s j)) *
    product {j | j < 48 * N} (\j. s j pow (7 * N) * (&1 - s j) pow (4 * N)) *
    product {i | i < 48 * N}
      (\i. abs(rp_t (x i)) pow (63 * N - 1) * (&1 - rp_t (x i)) pow (2 * N))`;;

let rp_I1 = new_definition
 `rp_I1 N x s =
    rp_J N x s * inv(&2) pow (((48 * N) * (48 * N - 1)) DIV 2) *
    product {i | i < 48 * N}
      (\i. sqrt(&1 + x i pow 2) pow (48 * N - 1) *
           inv(abs(x i)) pow (44 * N - 1))`;;

let rp_I2 = new_definition
 `rp_I2 N x s =
    rp_J N x s * abs(rp_vdm (48 * N) (\i. inv(x i))) *
    product {i | i < 48 * N} (\i. abs(x i) pow (4 * N))`;;

(* ------------------------------------------------------------------------- *)
(* Lemma 5.1 / Proposition 5.2 data.                                          *)
(* ------------------------------------------------------------------------- *)

let rp_K0 = new_definition
 `rp_K0 = &10 * exp(&12)`;;

(* interpolation data h_i = c_i x_i^D, c = 1 (x < 0), -5 (x > 0) *)
let rp_hval = new_definition
 `rp_hval D x = (if x < &0 then &1 else --(&5)) * x pow D`;;

(* ------------------------------------------------------------------------- *)
(* Section 6: trial sequences, one-variable functions, dual constant.       *)
(* ------------------------------------------------------------------------- *)

(* Chebyshev polynomial values T_k(x) *)
let rp_cheb = define
 `rp_cheb 0 x = &1 /\
  rp_cheb 1 x = x /\
  (forall k. rp_cheb (k + 2) x = &2 * x * rp_cheb (k + 1) x - rp_cheb k x)`;;

(* T(u,x), S(u,x), ||u||_*^2 of Equation (77) *)
let rp_Tser = new_definition
 `rp_Tser (u:num->real) x =
    real_infsum (from 1) (\k. u k * rp_cheb k x / &k)`;;

let rp_Sser = new_definition
 `rp_Sser (u:num->real) x =
    real_infsum (from 1) (\k. u k * x pow k / &k)`;;

let rp_nsq = new_definition
 `rp_nsq (u:num->real) = real_infsum (from 1) (\k. u k pow 2 / &k)`;;

(* X_kappa(x) = W_kappa(x) + lam D(x) - 2 kappa T(p,x) - S(v,x), Eq. (76),(91) *)
let rp_X = new_definition
 `rp_X kappa lam p v x =
    &19 / &48 * log(abs x) + &1 / &12 * log(&1 - x) -
    (kappa / &2 + &17 / &48) * log(&1 + x pow 2) +
    lam * (&1 / &6 - &2 * x pow 2 / (&1 + x pow 2)) -
    &2 * kappa * rp_Tser p x - rp_Sser v x`;;

(* Y(s) = W_s(s) + 2 T(v,s) *)
let rp_Y = new_definition
 `rp_Y v s = &7 / &48 * log s + &1 / &12 * log(&1 - s) + &2 * rp_Tser v s`;;

(* right side of (78) with the suprema replaced by bounds Bx, Bs *)
let rp_dual = new_definition
 `rp_dual kappa p v Bx Bs =
    --(&11 / &16) * log(&2) + kappa * rp_nsq p + rp_nsq v / &2 + Bx + Bs`;;

let rp_summable = new_definition
 `rp_summable (u:num->real) <=> real_summable (from 1) (\k. abs(u k))`;;

(* ------------------------------------------------------------------------- *)
(* INTERFACE STATEMENTS.  Each sub-part proves |- RP_xxx_STMT; the lead       *)
(* proves RP_ASSEMBLY : all of them ==> CAT_REAL_PLACE.                      *)
(* ------------------------------------------------------------------------- *)

(* (i) rp_int_: discretized double Andreief identity, Section 5.1 *)
let RP_INT_STMT = new_definition
 `RP_INT_STMT <=>
    forall N M. 1 <= N /\
          (forall x s. rp_config N x s ==> abs(rp_integrand N x s) <= M)
          ==> abs(cat_det N) <= &2 pow (48 * N) * M`;;

(* (ii) rp_alg_: Cauchy double alternant, psi Vandermonde, row factoring *)
let RP_ALG_STMT = new_definition
 `RP_ALG_STMT <=>
    forall N x s. 1 <= N /\ rp_config N x s
            ==> abs(rp_integrand N x s) =
                product {i | i < 48 * N}
                  (\i. &4 * abs(x i) / (&1 + x i pow 2) pow 2) *
                product {i | i < 48 * N} (\i. inv(abs(x i)) pow (44 * N - 1)) *
                abs(rp_R N x) * rp_J N x s`;;

(* (iii) rp_la_: Hadamard sheet estimate, Proposition 5.3 *)
let RP_HAD_STMT = new_definition
 `RP_HAD_STMT <=>
    forall N x. 1 <= N /\ rp_nodes (48 * N) x
          ==> abs(rp_R N x) <=
              (&3 / &2) pow (48 * N) * sqrt(&(48 * N)) pow (48 * N) *
              inv(&2) pow (((48 * N) * (48 * N - 1)) DIV 2) *
              product {i | i < 48 * N}
                (\i. sqrt(&1 + x i pow 2) pow (48 * N - 1))`;;

(* (iii') rp_la_: |det A| <= c^n when A has operator norm <= c for the     *)
(* positive definite quadratic form G                                        *)
let RP_LA_STMT = new_definition
 `RP_LA_STMT <=>
    forall n (G:num->num->real) (A:num->num->real) c.
      (forall i j. i < n /\ j < n ==> G i j = G j i) /\
      (forall a. ~(forall i. i < n ==> a i = &0)
           ==> &0 < sum {i | i < n}
                      (\i. sum {j | j < n} (\j. a i * G i j * a j))) /\
      &0 <= c /\
      (forall a. sum {i | i < n}
             (\i. sum {j | j < n}
                    (\j. sum {k | k < n} (\k. A i k * a k) * G i j *
                         sum {l | l < n} (\l. A j l * a l))) <=
           c pow 2 *
           sum {i | i < n} (\i. sum {j | j < n} (\j. a i * G i j * a j)))
      ==> abs(ndet {i | i < n} A) <= c pow n`;;

(* (iv) rp_hol_: Lemma 5.1 in the form needed: the Pick-type form bound    *)
(* for the data h_i = c_i x_i^D (consequence of the holomorphic h* with     *)
(* sup |h*| <= K0 n on the closed disk, via Cauchy's formula on the circle) *)
let RP_PICK_STMT = new_definition
 `RP_PICK_STMT <=>
    forall n D (x:num->real) (a:num->real).
      48 <= n /\ D < n /\ rp_nodes n x /\
      sum {i | i < n} (\i. (&1 - x i pow 2) / (&1 + x i pow 2)) <= &D
      ==> sum {i | i < n}
            (\i. sum {j | j < n}
                   (\j. a i * a j * rp_hval D (x i) * rp_hval D (x j) /
                        (&1 - x i * x j))) <=
          (rp_K0 * &n) pow 2 *
          sum {i | i < n}
            (\i. sum {j | j < n} (\j. a i * a j / (&1 - x i * x j)))`;;

(* (v) rp_ip_: interpolation estimate, Proposition 5.2 (from LA + PICK) *)
let RP_INTERP_STMT = new_definition
 `RP_INTERP_STMT <=>
    forall N x. 1 <= N /\ rp_nodes (48 * N) x /\
          sum {i | i < 48 * N} (\i. (&1 - x i pow 2) / (&1 + x i pow 2))
            <= &(40 * N - 1)
          ==> abs(rp_R N x) <=
              (&1 + rp_K0 * &(48 * N)) pow (48 * N) *
              abs(rp_vdm (48 * N) x)`;;

(* (vi) rp_en_: energy bound, Proposition 6.1, case kappa = 2 *)
let RP_EN2_STMT = new_definition
 `RP_EN2_STMT <=>
    forall p v Bx Bs d.
      rp_summable p /\ rp_summable v /\
      (forall x. --(&1) <= x /\ x < &1 /\ ~(x = &0) ==> rp_X (&2) (&0) p v x <= Bx) /\
      (forall s. &0 < s /\ s < &1 ==> rp_Y v s <= Bs) /\
      &0 < d
      ==> exists N0. forall N x s.
            N0 <= N /\ 1 <= N /\ rp_config N x s
            ==> rp_I2 N x s <=
                exp(&(48 * N) pow 2 *
                    (rp_dual (&2) p v Bx Bs + d + log(&2) / &2))`;;

(* (vi') rp_en_: case kappa = 1, on the complement of Equation (67) *)
let RP_EN1_STMT = new_definition
 `RP_EN1_STMT <=>
    forall lam p v Bx Bs d.
      &0 <= lam /\ rp_summable p /\ rp_summable v /\
      (forall x. --(&1) <= x /\ x < &1 /\ ~(x = &0) ==> rp_X (&1) lam p v x <= Bx) /\
      (forall s. &0 < s /\ s < &1 ==> rp_Y v s <= Bs) /\
      &0 < d
      ==> exists N0. forall N x s.
            N0 <= N /\ 1 <= N /\ rp_config N x s /\
            &(40 * N - 1) <
              sum {i | i < 48 * N} (\i. (&1 - x i pow 2) / (&1 + x i pow 2))
            ==> rp_I1 N x s <=
                exp(&(48 * N) pow 2 *
                    (rp_dual (&1) p v Bx Bs + d + log(&2) / &2))`;;

(* (vii) rp_cert_: exact certificates of Section 7 *)
let RP_CERT2_STMT = new_definition
 `RP_CERT2_STMT <=>
    exists p v Bx Bs.
      rp_summable p /\ rp_summable v /\
      (forall x. --(&1) <= x /\ x < &1 /\ ~(x = &0) ==> rp_X (&2) (&0) p v x <= Bx) /\
      (forall s. &0 < s /\ s < &1 ==> rp_Y v s <= Bs) /\
      rp_dual (&2) p v Bx Bs < --(&22909 / &10000)`;;

let RP_CERT1_STMT = new_definition
 `RP_CERT1_STMT <=>
    exists lam p v Bx Bs.
      &0 <= lam /\ rp_summable p /\ rp_summable v /\
      (forall x. --(&1) <= x /\ x < &1 /\ ~(x = &0) ==> rp_X (&1) lam p v x <= Bx) /\
      (forall s. &0 < s /\ s < &1 ==> rp_Y v s <= Bs) /\
      rp_dual (&1) p v Bx Bs < --(&22909 / &10000)`;;

(* ------------------------------------------------------------------------- *)
(* Small helper.                                                             *)
(* ------------------------------------------------------------------------- *)

let RP_NUMSEG_LT = prove
 (`forall n. 1 <= n ==> 0..n-1 = {i | i < n}`,
  REWRITE_TAC[EXTENSION; IN_NUMSEG; IN_ELIM_THM] THEN ARITH_TAC);;
