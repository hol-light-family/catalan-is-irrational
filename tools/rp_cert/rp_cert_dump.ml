needs "src/catalan_rp_cert_check.ml";;
needs "src/catalan_rp_cert_data.ml";;
let time_it name f x = let t0 = Sys.time() in let r = f x in Printf.printf "TIMING %s %f\n%!" name (Sys.time() -. t0); r;;
let x = `x:real`;;
let dump name a q s =
  let oc = open_out ("tools/rp_cert/dump_" ^ name ^ ".txt") in
  let pr l = String.concat " " (map string_of_num (rp_cert_eng_of_hol_list l)) in
  Printf.fprintf oc "%s\n%s\n%s\n" (pr a) (pr q) (string_of_num (rat_of_term s)); close_out oc;;
let xd c (k,l,lp,tp,lv,tv) =
  let xth = ISPECL [k;l;lp;tp;lv;tv;x] RP_CERT_GLUE_X_DERIV in
  let a,q,s,ds,th = time_it ("setupX"^c) (rp_cert_chk_deriv_setup x) xth in
  dump ("c"^c^"x") a q s;;
let yd c (lv,tv) =
  let yth = INST [x,`s:real`] (ISPECL [lv;tv;`s:real`] RP_CERT_GLUE_Y_DERIV) in
  let a,q,s,ds,th = time_it ("setupY"^c) (rp_cert_chk_deriv_setup x) yth in
  dump ("c"^c^"y") a q s;;
xd "1" (rp_cert_c1_kappa, rp_cert_c1_lam, rp_cert_c1_lp, rp_cert_c1_tp, rp_cert_c1_lv, rp_cert_c1_tv);;
yd "1" (rp_cert_c1_lv, rp_cert_c1_tv);;
xd "2" (rp_cert_c2_kappa, rp_cert_c2_lam, rp_cert_c2_lp, rp_cert_c2_tp, rp_cert_c2_lv, rp_cert_c2_tv);;
yd "2" (rp_cert_c2_lv, rp_cert_c2_tv);;
