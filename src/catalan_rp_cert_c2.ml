(* ========================================================================= *)
(* CERT / case kappa = 2 (paper Section 7, first barrier, lambda = 0).  *)
(* ========================================================================= *)

needs "src/catalan_rp_cert_case.ml";;

let rp_cert_c2_d = (rp_cert_c2_kappa, rp_cert_c2_lam, rp_cert_c2_lp, rp_cert_c2_tp, rp_cert_c2_lv, rp_cert_c2_tv);;
let RP_CERT_C2_OKP = rp_cert_case_ok rp_cert_c2_tp;;
let RP_CERT_C2_OKV = rp_cert_case_ok rp_cert_c2_tv;;
let rp_cert_c2_p = mk_comb(mk_comb(`rp_cert_seq`, rp_cert_c2_lp), rp_cert_c2_tp);;
let rp_cert_c2_v = mk_comb(mk_comb(`rp_cert_seq`, rp_cert_c2_lv), rp_cert_c2_tv);;
let rp_cert_c2_bx = rp_cert_chk_num "-984033/1000000";;
let rp_cert_c2_by = rp_cert_chk_num "-1608946/1000000";;

let RP_CERT_C2_X =
  let x = `x:real` in
  let xth = ISPECL [rp_cert_c2_kappa; rp_cert_c2_lam; rp_cert_c2_lp; rp_cert_c2_tp;
                    rp_cert_c2_lv; rp_cert_c2_tv; x] RP_CERT_GLUE_X_DERIV in
  let a,q,s,ds,gth = rp_cert_chk_deriv_setup x xth in
  let qs = rp_cert_chk_qsign2 q ds in
  let f = list_mk_comb(`rp_X`, [rp_cert_c2_kappa; rp_cert_c2_lam; rp_cert_c2_p; rp_cert_c2_v]) in
  let lofn lo = if lo =/ rp_cert_chk_num "-1" then
     Some(rp_cert_case_xval rp_cert_c2_d RP_CERT_C2_OKP RP_CERT_C2_OKV lo, None) else None in
  let [tn; tp] = rp_cert_case_func f a q s gth (CONJUNCT1 qs) (CONJUNCT2 qs) rp_cert_cert_c2x
     (rp_cert_case_xval rp_cert_c2_d RP_CERT_C2_OKP RP_CERT_C2_OKV) lofn rp_cert_c2_bx in
  MATCH_MP RP_CERT_CASE_XALL (CONJ tn tp);;

let RP_CERT_C2_Y =
  let x = `x:real` in
  let yth = INST [x,`s:real`] (ISPECL [rp_cert_c2_lv; rp_cert_c2_tv; `s:real`] RP_CERT_GLUE_Y_DERIV) in
  let a,q,s,ds,gth = rp_cert_chk_deriv_setup x yth in
  let qs = rp_cert_chk_qsign2 q ds in
  let f = mk_comb(`rp_Y`, rp_cert_c2_v) in
  let [t] = rp_cert_case_func f a q s gth (CONJUNCT1 qs) (CONJUNCT2 qs) rp_cert_cert_c2y
     (rp_cert_case_yval (rp_cert_c2_lv, rp_cert_c2_tv) RP_CERT_C2_OKV) (fun _ -> None) rp_cert_c2_by in
  t;;

let RP_CERT_C2_NP = rp_cert_case_nsq rp_cert_c2_lp rp_cert_c2_tp RP_CERT_C2_OKP;;
let RP_CERT_C2_NV = rp_cert_case_nsq rp_cert_c2_lv rp_cert_c2_tv RP_CERT_C2_OKV;;

let RP_CERT2_THM = rp_cert_case_final `RP_CERT2_STMT` RP_CERT2_STMT `true`
  rp_cert_c2_p rp_cert_c2_v rp_cert_c2_bx rp_cert_c2_by RP_CERT_C2_X RP_CERT_C2_Y
  RP_CERT_C2_NP RP_CERT_C2_NV RP_CERT_C2_OKP RP_CERT_C2_OKV;;
