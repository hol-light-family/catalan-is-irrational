(* ========================================================================= *)
(* CAT_REAL_PLACE (paper, Proposition 7.1).                                  *)
(* ========================================================================= *)

needs "src/catalan_rp_asm.ml";;
needs "src/catalan_rp_int_final.ml";;
needs "src/catalan_rp_alg_final.ml";;
needs "src/catalan_rp_la_final.ml";;
needs "src/catalan_rp_hol_final.ml";;
needs "src/catalan_rp_ip_final.ml";;
needs "src/catalan_rp_en_final.ml";;
needs "src/catalan_rp_cert_final.ml";;

let CAT_REAL_PLACE_THM = prove
 (`CAT_REAL_PLACE`,
  MATCH_MP_TAC RP_ASSEMBLY THEN
  REWRITE_TAC[RP_INT_THM; RP_ALG_THM; RP_HAD_THM; RP_EN1_THM; RP_EN2_THM;
              RP_CERT1_THM; RP_CERT2_THM] THEN
  MATCH_MP_TAC RP_IP_THM THEN REWRITE_TAC[RP_LA_THM; RP_PICK_THM]);;
