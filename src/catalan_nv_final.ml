(* ========================================================================= *)
(* CAT_NONVANISHING (paper, Proposition 4.1): final theorem.                 *)
(* ========================================================================= *)

needs "src/catalan_defs.ml";;
needs "src/catalan_components.ml";;
needs "src/catalan_nv_assemble.ml";;
needs "src/catalan_nv_pal_final.ml";;
needs "src/catalan_nv_dig.ml";;
needs "src/catalan_nv_mz.ml";;
needs "src/catalan_nv_mz_m0.ml";;
needs "src/catalan_nv_cert.ml";;

let CAT_NONVANISHING_THM = prove
 (`CAT_NONVANISHING`,
  MATCH_MP_TAC NV_G_FINAL THEN
  REWRITE_TAC[NV_G_IFACES; NV_PAL_IF_P; NV_PAL_IF_D; NV_PAL_IF_BINOM;
              NV_DIG_IF_C_PINT; NV_DIG_IF_ECOEF; NV_MZ_IF_M0; NV_MZ_IF_Z0;
              NV_CERT_IF]);;
