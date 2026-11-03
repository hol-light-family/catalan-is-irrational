(* ========================================================================= *)
(* CAT_NONVANISHING: the interface statements of the sub-parts, as boolean   *)
(* constants (so that the gathering can be proved before the parts).         *)
(* ========================================================================= *)

needs "src/catalan_nv_base.ml";;

let nv_if_pal_p = new_definition
 `nv_if_pal_p <=>
  forall p r0 i l u. prime p /\ 260 < p /\ r0 < 48 /\ i < p /\ l < p
     ==> nv_cong p
          (sum (0..p - 1) (\d. nv_Ecoef p d *
              cat_pcoef p (p * r0 + i) (((u + 1) * p + l) - 1 - d)))
          (nv_a p l i * cat_pcoef 1 r0 u + nv_b p l i * cat_pcoef 1 (r0 + 1) u)`;;

let nv_if_pal_d = new_definition
 `nv_if_pal_d <=>
  forall p r0 i l u. prime p /\ 260 < p /\ r0 < 48 /\ i < p /\ l < p
     ==> nv_cong p (cat_dcoef p (p * r0 + i) (u * p + l))
          (nv_a p l i * cat_dcoef 1 r0 u + nv_b p l i * cat_dcoef 1 (r0 + 1) u)`;;

let nv_if_binom = new_definition
 `nv_if_binom <=>
  forall p a v. prime p
     ==> nv_cong p (&(binom(a * p,v)))
                   (if p divides v then &(binom(a,v DIV p)) else &0)`;;

let nv_if_c_pint = new_definition
 `nv_if_c_pint <=> forall p l. prime p /\ ~(p = 2) ==> nv_pint p (cat_c l)`;;

let nv_if_ecoef = new_definition
 `nv_if_ecoef <=>
  forall p d. prime p /\ ~(p = 2) /\ d < p ==> nv_cong p (nv_Ecoef p d) (nv_E d)`;;

let nv_if_m0 = new_definition
 `nv_if_m0 <=>
  forall p i j d. prime p /\ 260 < p /\ p <= i /\ i < 65 * p /\ j < 65 * p /\
            d < p /\ (i + 1 + d) MOD p = j MOD p
     ==> nv_pint p (cat_M0 ((i + 1 + d) DIV p - 1) (j DIV p)) /\
         nv_cong p (&p pow 2 * cat_M0 i j)
           (nv_E d * cat_M0 ((i + 1 + d) DIV p - 1) (j DIV p))`;;

let nv_if_z0 = new_definition
 `nv_if_z0 <=>
  forall p i j. prime p /\ 260 < p /\ i < 65 * p /\ j < 65 * p
     ==> nv_pint p (cat_Z0 (i DIV p) (j DIV p)) /\
         nv_cong p (&p pow 2 * cat_Z0 i j)
           (if i MOD p = j MOD p then cat_Z0 (i DIV p) (j DIV p) else &0)`;;

let nv_if_cert = new_definition
 `nv_if_cert <=>
  ~(ndet (0..47) (\r k. cat_entryq (&0) 1 r k) = &0) /\
  ~(ndet (0..47) (\r k. cat_entryq (&0) 1 r k + cat_entryq (&0) 1 (r + 1) k) = &0) /\
  ~(ndet (0..47) (\r k. cat_entryq (&0) 1 r k - cat_entryq (&0) 1 (r + 1) k) = &0)`;;
