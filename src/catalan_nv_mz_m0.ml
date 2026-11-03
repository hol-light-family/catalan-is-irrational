(* NV_MZ_M0 from the digit facts of the nv_dig_ files. *)
needs "src/catalan_nv_mz.ml";;
needs "src/catalan_nv_dig.ml";;

let NV_MZ_M0 = MP NV_MZ_M0_IMP
  (end_itlist CONJ [NV_DIG_C_PINT; NV_DIG_M; NV_DIG_KMINUS; NV_DIG_KPLUS]);;

let NV_MZ_IF_M0 = prove
 (`nv_if_m0`, REWRITE_TAC[nv_if_m0; NV_MZ_M0]);;
