(* ========================================================================= *)
(* CERT / case kappa = 1 (paper Section 7, second barrier with lambda > 0).  *)
(* ========================================================================= *)

needs "src/catalan_rp_cert_case.ml";;

let rp_cert_c1_d = (rp_cert_c1_kappa, rp_cert_c1_lam, rp_cert_c1_lp, rp_cert_c1_tp, rp_cert_c1_lv, rp_cert_c1_tv);;
let RP_CERT_C1_OKP = rp_cert_case_ok rp_cert_c1_tp;;
let RP_CERT_C1_OKV = rp_cert_case_ok rp_cert_c1_tv;;
let rp_cert_c1_p = mk_comb(mk_comb(`rp_cert_seq`, rp_cert_c1_lp), rp_cert_c1_tp);;
let rp_cert_c1_v = mk_comb(mk_comb(`rp_cert_seq`, rp_cert_c1_lv), rp_cert_c1_tv);;
let rp_cert_c1_bx = rp_cert_chk_num "-1324/1000";;
let rp_cert_c1_by = rp_cert_chk_num "-1428/1000";;

let RP_CERT_C1_X =
  let x = `x:real` in
  let xth = ISPECL [rp_cert_c1_kappa; rp_cert_c1_lam; rp_cert_c1_lp; rp_cert_c1_tp;
                    rp_cert_c1_lv; rp_cert_c1_tv; x] RP_CERT_GLUE_X_DERIV in
  let a,q,s,ds,gth = rp_cert_chk_deriv_setup x xth in
  let qs = rp_cert_chk_qsign2 q ds in
  let f = list_mk_comb(`rp_X`, [rp_cert_c1_kappa; rp_cert_c1_lam; rp_cert_c1_p; rp_cert_c1_v]) in
  let lofn lo = if lo =/ rp_cert_chk_num "-1" then
     let fth = rp_cert_case_xval rp_cert_c1_d RP_CERT_C1_OKP RP_CERT_C1_OKV lo in
     let dm1 = MP (ISPECL [rp_cert_c1_kappa; rp_cert_c1_lam; rp_cert_c1_lp; rp_cert_c1_lv; `--(&1)`]
                    RP_CERT_GLUE_X_DERIV_FIN)
                  (EQT_ELIM(rp_cert_chk_red `--(&1) < &1 /\ ~(--(&1) = &0)`)) in
     let c = MATCH_MP REAL_CONTINUOUS_ATREAL_WITHINREAL
               (MATCH_MP HAS_REAL_DERIVATIVE_IMP_CONTINUOUS_ATREAL dm1) in
     Some(fth, Some c) else None in
  let [tn; tp] = rp_cert_case_func f a q s gth (CONJUNCT1 qs) (CONJUNCT2 qs) rp_cert_cert_c1x
     (rp_cert_case_xval rp_cert_c1_d RP_CERT_C1_OKP RP_CERT_C1_OKV) lofn rp_cert_c1_bx in
  MATCH_MP RP_CERT_CASE_XALL (CONJ tn tp);;

let RP_CERT_C1_Y =
  let x = `x:real` in
  let yth = INST [x,`s:real`] (ISPECL [rp_cert_c1_lv; rp_cert_c1_tv; `s:real`] RP_CERT_GLUE_Y_DERIV) in
  let a,q,s,ds,gth = rp_cert_chk_deriv_setup x yth in
  let qs = rp_cert_chk_qsign2 q ds in
  let f = mk_comb(`rp_Y`, rp_cert_c1_v) in
  let [t] = rp_cert_case_func f a q s gth (CONJUNCT1 qs) (CONJUNCT2 qs) rp_cert_cert_c1y
     (rp_cert_case_yval (rp_cert_c1_lv, rp_cert_c1_tv) RP_CERT_C1_OKV) (fun _ -> None) rp_cert_c1_by in
  t;;

let RP_CERT_C1_NP = rp_cert_case_nsq rp_cert_c1_lp rp_cert_c1_tp RP_CERT_C1_OKP;;
let RP_CERT_C1_NV = rp_cert_case_nsq rp_cert_c1_lv rp_cert_c1_tv RP_CERT_C1_OKV;;

let RP_CERT1_THM = rp_cert_case_final `RP_CERT1_STMT` RP_CERT1_STMT rp_cert_c1_lam
  rp_cert_c1_p rp_cert_c1_v rp_cert_c1_bx rp_cert_c1_by RP_CERT_C1_X RP_CERT_C1_Y
  RP_CERT_C1_NP RP_CERT_C1_NV RP_CERT_C1_OKP RP_CERT_C1_OKV;;
