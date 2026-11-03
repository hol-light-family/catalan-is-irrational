(* ========================================================================= *)
(* rp_la_ final: both statements of part LA of CAT_REAL_PLACE.              *)
(*   RP_LA_THM  : |- RP_LA_STMT   (src/catalan_rp_la_det.ml)                 *)
(*   RP_HAD_THM : |- RP_HAD_STMT  (src/catalan_rp_la_had.ml)                 *)
(* ========================================================================= *)

needs "src/catalan_rp_defs.ml";;
needs "src/catalan_rp_la_det.ml";;
needs "src/catalan_rp_la_had.ml";;

let RP_LA_THM = prove(`RP_LA_STMT`, ACCEPT_TAC RP_LA_THM);;
let RP_HAD_THM = prove(`RP_HAD_STMT`, ACCEPT_TAC RP_HAD_THM);;
