(* ========================================================================= *)
(* fin_dig: final file.  Scalar odd-prime congruences of Lemma 3.1 and the  *)
(* scalar part of Lemma 3.2 of the paper:                                    *)
(*   FIN_DIG_LEMMA31_M, FIN_DIG_LEMMA31_Z, FIN_DIG_CENTRAL_M,                *)
(*   FIN_DIG_CENTRAL_Z, FIN_DIG_SMALL_INTEGRAL.                              *)
(* ========================================================================= *)

needs "src/catalan_fin_dig_m.ml";;

prioritize_real();;

(* ------------------------------------------------------------------------- *)
(* Check that the five main results have exactly the requested statements.  *)
(* ------------------------------------------------------------------------- *)

let fin_dig_check (th,tm) =
  if hyp th = [] && aconv (concl th) tm then ()
  else failwith "fin_dig: statement mismatch";;

List.iter fin_dig_check
 [FIN_DIG_LEMMA31_M,
  `forall p H i j. prime p /\ ~(p = 2) /\ 4 * H < p * p /\ p <= H /\ i < H /\ j < H
   ==> fin_zp p (&p pow 2 * cat_M0 i j) /\
       fin_vge p (&1)
        (&p pow 2 * cat_M0 i j -
         fin_E p ((j + (p * (i + 1) - (i + 1))) MOD p) *
         fin_M0x (((i + 1 + ((j + (p * (i + 1) - (i + 1))) MOD p)) - j MOD p) DIV p) (j DIV p))`;
  FIN_DIG_LEMMA31_Z,
  `forall p H i j. prime p /\ ~(p = 2) /\ 4 * H < p * p /\ p <= H /\ i < H /\ j < H
   ==> fin_zp p (&p pow 2 * cat_Z0 i j) /\
       fin_vge p (&1) (&p pow 2 * cat_Z0 i j -
                       (if i MOD p = j MOD p then cat_Z0 (i DIV p) (j DIV p) else &0))`;
  FIN_DIG_CENTRAL_M,
  `forall p H i j. prime p /\ ~(p = 2) /\ H < 2 * p /\ p <= H /\ H <= j + p /\ j < p /\ i < H
   ==> fin_zp p (&p * cat_M0 i j) /\
       fin_vge p (&1) (&p * cat_M0 i j +
          sum {l | l < H - p} (\l. if p + l <= i /\ i < 2 * p + l
                                   then &2 * fin_E p (((2 * p + l) - 1) - i) / (&j - &l) else &0))`;
  FIN_DIG_CENTRAL_Z,
  `forall p H i j. prime p /\ ~(p = 2) /\ H < 2 * p /\ p <= H /\ H <= j + p /\ j < p /\ i < H
   ==> fin_zp p (&p * cat_Z0 i j) /\
       fin_vge p (&1) (&p * cat_Z0 i j -
                       (if p <= i /\ i < H then &1 / (&(i - p) - &j) else &0))`;
  FIN_DIG_SMALL_INTEGRAL,
  `forall p a j. prime p /\ ~(p = 2) /\ a <= p /\ j + 1 < p
   ==> fin_zp p (fin_M0x a j) /\ (a < p ==> fin_zp p (cat_Z0 a j))`];;
