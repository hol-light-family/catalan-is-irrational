(* ========================================================================= *)
(* rp_hol_: RP_PICK_THM : |- RP_PICK_STMT  (Lemma 5.1 + Cauchy formula on    *)
(* the unit circle).                                                          *)
(* ========================================================================= *)

needs "src/catalan_rp_hol_asm.ml";;
needs "src/catalan_rp_hol_bl.ml";;
needs "src/catalan_rp_hol_gla.ml";;
needs "src/catalan_rp_hol_glb.ml";;
needs "src/catalan_rp_hol_ck.ml";;

let RP_PICK_THM = prove
 (`RP_PICK_STMT`,
  MATCH_MP_TAC RP_HOL_PICK_FROM_PARTS THEN
  REWRITE_TAC[RP_HOL_BL_THM; RP_HOL_GLA_THM; RP_HOL_GLB_THM; RP_HOL_CK_THM]);;
