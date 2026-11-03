(* ========================================================================= *)
(* rp_hol_: shared definitions and internal interface statements for the     *)
(* proof of RP_PICK_STMT (Lemma 5.1 + Cauchy formula on the circle).          *)
(* Owned by the rp_hol coordinator; FROZEN for rp_hol sub-workers.           *)
(* ========================================================================= *)

needs "src/catalan_rp_defs.ml";;

(* Blaschke product B(z) = prod (z - x_i)/(1 - x_i z) *)
let rp_hol_B = new_definition
 `rp_hol_B n (x:num->real) z =
    cproduct {i | i < n} (\i. (z - Cx(x i)) / (Cx(&1) - Cx(x i) * z))`;;

(* F(z) = z^D / B(z), written so that it is holomorphic off the nodes *)
let rp_hol_F = new_definition
 `rp_hol_F n D (x:num->real) z =
    z pow D * cproduct {i | i < n} (\i. (Cx(&1) - Cx(x i) * z) / (z - Cx(x i)))`;;

(* Vertices v_0..v_7 of the contour from -iR to iR, R = 1 + 2/n,          *)
(* e = 1/n, rho = 1 - 1/n.  s = &1: contour in Re <= 0 (used for Re z >= 0);  *)
(* s = --(&1): mirror image in Re >= 0 (used for Re z <= 0).                  *)
(* Middle vertical side at Re = -s d, d small and node dependent.            *)
let rp_hol_v = new_definition
 `rp_hol_v n d s k =
    if k = 0 then complex(&0, --(&1 + &2 / &n)) else
    if k = 1 then complex(--s * inv(&n), --(&1 + &2 / &n)) else
    if k = 2 then complex(--s * inv(&n), --(&1 - inv(&n))) else
    if k = 3 then complex(--s * d, --(&1 - inv(&n))) else
    if k = 4 then complex(--s * d, &1 - inv(&n)) else
    if k = 5 then complex(--s * inv(&n), &1 - inv(&n)) else
    if k = 6 then complex(--s * inv(&n), &1 + &2 / &n) else
    complex(&0, &1 + &2 / &n)`;;

(* Cauchy integral of f over one segment *)
let rp_hol_cint = new_definition
 `rp_hol_cint (f:complex->complex) z p q =
    path_integral (linepath(p,q)) (\w. f w / (w - z))`;;

(* Cauchy integral over the whole polygonal contour (without 1/(2 pi i)) *)
let rp_hol_C = new_definition
 `rp_hol_C n d s (f:complex->complex) z =
    vsum (0..6) (\k. rp_hol_cint f z (rp_hol_v n d s k) (rp_hol_v n d s (k + 1)))`;;

(* the two local formulas c_s z^D - B(z) C(z), C = (1/(2 pi i)) int 6F/(w-z) *)
let rp_hol_G = new_definition
 `rp_hol_G n D d s (B:complex->complex) (f:complex->complex) z =
    Cx(if s = &1 then --(&5) else &1) * z pow D -
    B z * (Cx(&6) / (Cx(&2) * Cx pi * ii) * rp_hol_C n d s f z)`;;

(* the glued function h* *)
let rp_hol_h = new_definition
 `rp_hol_h n D d (B:complex->complex) (f:complex->complex) z =
    if --(d / &2) < Re z then rp_hol_G n D d (&1) B f z
    else rp_hol_G n D d (--(&1)) B f z`;;

(* ------------------------------------------------------------------------- *)
(* INTERNAL INTERFACES (each proved as |- RP_HOL_xxx_STMT by one worker).   *)
(* ------------------------------------------------------------------------- *)

(* rp_hol_bl_: concrete facts about B and F *)
let RP_HOL_BL_STMT = new_definition
 `RP_HOL_BL_STMT <=>
   (forall n D x w. (forall i. i < n ==> ~(w = Cx(x i)))
              ==> rp_hol_F n D x complex_differentiable at w) /\
   (forall n x w. (forall i. i < n ==> ~(Cx(x i) * w = Cx(&1)))
            ==> rp_hol_B n x complex_differentiable at w) /\
   (forall n D x w. (forall i. i < n ==> ~(w = Cx(x i)) /\ ~(Cx(x i) * w = Cx(&1)))
              ==> rp_hol_B n x w * rp_hol_F n D x w = w pow D) /\
   (forall n x j. j < n ==> rp_hol_B n x (Cx(x j)) = Cx(&0)) /\
   (forall n x z. (forall i. i < n ==> abs(x i) < &1) /\ norm z = &1
            ==> norm(rp_hol_B n x z) = &1) /\
   (forall n (x:num->real). (forall i. i < n ==> abs(x i) < &1)
          ==> exists r. &1 < r /\
                  forall w i. norm w < r /\ i < n ==> ~(Cx(x i) * w = Cx(&1))) /\
   (forall n D x w. 48 <= n /\ D < n /\ (forall i. i < n ==> abs(x i) < &1) /\
              (norm(w - ii) <= &3 / &n \/ norm(w + ii) <= &3 / &n)
              ==> norm(rp_hol_F n D x w) <= exp(&12)) /\
   (forall n D x. 48 <= n /\ D < n /\ rp_nodes n x /\
            sum {i | i < n} (\i. (&1 - x i pow 2) / (&1 + x i pow 2)) <= &D
            ==> exists d. &0 < d /\ &2 * d <= inv(&n) /\
                    (forall i. i < n ==> &2 * d < abs(x i)) /\
                    (forall w. abs(Re w) <= d /\ abs(Im w) <= &1 - inv(&n)
                         ==> norm(rp_hol_F n D x w) <= exp(&12)))`;;

(* rp_hol_gla_: holomorphic gluing and interpolation (abstract B, f) *)
let RP_HOL_GLA_STMT = new_definition
 `RP_HOL_GLA_STMT <=>
   forall n D x d r (B:complex->complex) (f:complex->complex).
     48 <= n /\ rp_nodes n x /\ &1 < r /\
     &0 < d /\ &2 * d <= inv(&n) /\ (forall i. i < n ==> &2 * d < abs(x i)) /\
     (forall w. norm w < r ==> B complex_differentiable at w) /\
     (forall w. (forall i. i < n ==> ~(w = Cx(x i))) ==> f complex_differentiable at w) /\
     (forall w. norm w < r /\ (forall i. i < n ==> ~(w = Cx(x i))) ==> B w * f w = w pow D) /\
     (forall i. i < n ==> B(Cx(x i)) = Cx(&0))
     ==> exists r'. &1 < r' /\
              rp_hol_h n D d B f holomorphic_on ball(Cx(&0),r') /\
              (forall z. norm z < r' /\ &0 <= Re z
                   ==> rp_hol_h n D d B f z = rp_hol_G n D d (&1) B f z) /\
              (forall z. norm z < r' /\ Re z <= &0
                   ==> rp_hol_h n D d B f z = rp_hol_G n D d (--(&1)) B f z) /\
              (forall i. i < n ==> rp_hol_h n D d B f (Cx(x i)) = Cx(rp_hval D (x i)))`;;

(* rp_hol_glb_: bound of the local formulas on the unit circle *)
let RP_HOL_GLB_STMT = new_definition
 `RP_HOL_GLB_STMT <=>
   forall n D x d s (B:complex->complex) (f:complex->complex) z.
     48 <= n /\ &0 < d /\ &2 * d <= inv(&n) /\
     (forall i. i < n ==> &2 * d < abs(x i)) /\ (s = &1 \/ s = --(&1)) /\
     (forall w. (forall i. i < n ==> ~(w = Cx(x i))) ==> f complex_differentiable at w) /\
     (forall w. norm(w - ii) <= &3 / &n \/ norm(w + ii) <= &3 / &n
          ==> norm(f w) <= exp(&12)) /\
     (forall w. abs(Re w) <= d /\ abs(Im w) <= &1 - inv(&n) ==> norm(f w) <= exp(&12)) /\
     norm z = &1 /\ &0 <= s * Re z /\ norm(B z) <= &1
     ==> norm(rp_hol_G n D d s B f z) <= rp_K0 * &n`;;

(* rp_hol_ck_: Step 2, Cauchy formula on the circle + AM-GM *)
let RP_HOL_CK_STMT = new_definition
 `RP_HOL_CK_STMT <=>
   forall n (x:num->real) (hv:num->real) (h:complex->complex) M (a:num->real).
     (forall i. i < n ==> abs(x i) < &1) /\
     h continuous_on cball(Cx(&0),&1) /\ h holomorphic_on ball(Cx(&0),&1) /\
     (forall i. i < n ==> h(Cx(x i)) = Cx(hv i)) /\
     (forall z. norm z = &1 ==> norm(h z) <= M)
     ==> sum {i | i < n}
           (\i. sum {j | j < n}
                  (\j. a i * a j * hv i * hv j / (&1 - x i * x j))) <=
         M pow 2 *
         sum {i | i < n}
           (\i. sum {j | j < n} (\j. a i * a j / (&1 - x i * x j)))`;;
