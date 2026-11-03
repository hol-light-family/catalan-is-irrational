(* ========================================================================= *)
(* CERT part, final file:                                                    *)
(*   RP_CERT1_THM : |- RP_CERT1_STMT   (kappa = 1, src/catalan_rp_cert_c1.ml) *)
(*   RP_CERT2_THM : |- RP_CERT2_STMT   (kappa = 2, src/catalan_rp_cert_c2.ml) *)
(* ========================================================================= *)

needs "src/catalan_rp_cert_c1.ml";;
needs "src/catalan_rp_cert_c2.ml";;

let RP_CERT1_THM = (RP_CERT1_THM : thm);;
let RP_CERT2_THM = (RP_CERT2_THM : thm);;
if concl RP_CERT1_THM <> `RP_CERT1_STMT` || hyp RP_CERT1_THM <> [] then failwith "RP_CERT1_THM";;
if concl RP_CERT2_THM <> `RP_CERT2_STMT` || hyp RP_CERT2_THM <> [] then failwith "RP_CERT2_THM";;
