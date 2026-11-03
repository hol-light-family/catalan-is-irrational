(* ========================================================================= *)
(* CERT part (paper Section 7): shared base definitions for all rp_cert_    *)
(* sub-parts.  FROZEN once sub-agents start (owner: rp_cert lead).          *)
(* ========================================================================= *)

needs "src/catalan_rp_defs.ml";;

(* ------------------------------------------------------------------------- *)
(* Trial sequences u_k = l_k + sum_{(c,z) in t} Re(c z^k), Equation (89).    *)
(* l = [l_1; ...; l_d]; t = list of pairs (c,z) of complex numbers.          *)
(* A real base z with coefficient a is (Complex(a,&0), Complex(z,&0)); a     *)
(* nonreal base z with paper entries a, b is (Complex(a,--b), z).            *)
(* ------------------------------------------------------------------------- *)

let rp_cert_fin = new_definition
 `rp_cert_fin (l:real list) k =
    if 1 <= k /\ k <= LENGTH l then EL (k - 1) l else &0`;;

let rp_cert_tail = define
 `(rp_cert_tail [] k = &0) /\
  (rp_cert_tail (CONS (cz:complex#complex) t) k =
     Re(FST cz * SND cz pow k) + rp_cert_tail t k)`;;

let rp_cert_seq = new_definition
 `rp_cert_seq l t k = rp_cert_fin l k + rp_cert_tail t k`;;

let rp_cert_ok = new_definition
 `rp_cert_ok (t:(complex#complex)list) <=> ALL (\cz. norm(SND cz) < &1) t`;;

(* Chebyshev polynomials of the second kind U_k *)
let rp_cert_chebu = define
 `rp_cert_chebu 0 x = &1 /\
  rp_cert_chebu 1 x = &2 * x /\
  (forall k. rp_cert_chebu (k + 2) x =
       &2 * x * rp_cert_chebu (k + 1) x - rp_cert_chebu k x)`;;

(* ------------------------------------------------------------------------- *)
(* Closed forms, Equation (90), and derivative tails, Equation (92).         *)
(* ------------------------------------------------------------------------- *)

let rp_cert_ttail = define
 `(rp_cert_ttail [] (x:real) = &0) /\
  (rp_cert_ttail (CONS (cz:complex#complex) t) x =
     --(Re(FST cz * clog(Cx(&1) - Cx(&2 * x) * SND cz + SND cz pow 2))) / &2 +
     rp_cert_ttail t x)`;;

let rp_cert_stail = define
 `(rp_cert_stail [] (x:real) = &0) /\
  (rp_cert_stail (CONS (cz:complex#complex) t) x =
     --(Re(FST cz * clog(Cx(&1) - Cx x * SND cz))) + rp_cert_stail t x)`;;

let rp_cert_dttail = define
 `(rp_cert_dttail [] (x:real) = &0) /\
  (rp_cert_dttail (CONS (cz:complex#complex) t) x =
     Re(FST cz * SND cz / (Cx(&1) - Cx(&2 * x) * SND cz + SND cz pow 2)) +
     rp_cert_dttail t x)`;;

let rp_cert_dstail = define
 `(rp_cert_dstail [] (x:real) = &0) /\
  (rp_cert_dstail (CONS (cz:complex#complex) t) x =
     Re(FST cz * SND cz / (Cx(&1) - Cx x * SND cz)) + rp_cert_dstail t x)`;;

let rp_cert_ntail1 = define
 `(rp_cert_ntail1 (cz:complex#complex) [] = &0) /\
  (rp_cert_ntail1 cz (CONS (cw:complex#complex) t) =
     --(Re(FST cz * FST cw * clog(Cx(&1) - SND cz * SND cw)) +
        Re(FST cz * cnj(FST cw) * clog(Cx(&1) - SND cz * cnj(SND cw)))) / &2 +
     rp_cert_ntail1 cz t)`;;

let rp_cert_ntail = define
 `(rp_cert_ntail [] (t2:(complex#complex)list) = &0) /\
  (rp_cert_ntail (CONS (cz:complex#complex) t) t2 =
     rp_cert_ntail1 cz t2 + rp_cert_ntail t t2)`;;

(* ------------------------------------------------------------------------- *)
(* Polynomials as coefficient lists, lowest degree first (Horner).           *)
(* ------------------------------------------------------------------------- *)

let rp_cert_peval = define
 `(rp_cert_peval [] (x:real) = &0) /\
  (rp_cert_peval (CONS a p) x = a + x * rp_cert_peval p x)`;;

(* ------------------------------------------------------------------------- *)
(* Utility: sequential tactic application (like interactive e), always on    *)
(* the first open goal; fails if goals remain.                               *)
(* ------------------------------------------------------------------------- *)

let rp_cert_steps (tm:term) (tacs:tactic list) =
  let _ = set_goal([],tm) in
  List.iter (fun t -> ignore(refine(by(VALID t)))) tacs;
  top_thm();;
