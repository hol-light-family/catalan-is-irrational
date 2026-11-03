(* ========================================================================= *)
(* CAT_NONVANISHING, part C: congruences modulo 101 for all the rational     *)
(* data at N = 1, computed lazily and memoized.                              *)
(* ========================================================================= *)

needs "src/catalan_nv_cert_lem.ml";;

let rec nv_cert_thash tm =
  match tm with
    Var(n,_) -> Hashtbl.hash n
  | Const(n,_) -> Hashtbl.hash n
  | Comb(s,t) -> (nv_cert_thash s * 65599 + nv_cert_thash t + 1) land 0x3FFFFFFF
  | Abs(v,b) -> (nv_cert_thash v * 31 + nv_cert_thash b + 7) land 0x3FFFFFFF;;

let nv_cert_tsize = 262144;;
let nv_cert_tbl : (term * thm) list array = Array.make nv_cert_tsize [];;
let nv_cert_tcount = ref 0;;

let nv_cert_find tm =
  let h = nv_cert_thash tm land (nv_cert_tsize - 1) in
  snd(List.find (fun (t,_) -> t = tm) nv_cert_tbl.(h));;

let nv_cert_store tm th =
  let h = nv_cert_thash tm land (nv_cert_tsize - 1) in
  nv_cert_tbl.(h) <- (tm,th) :: nv_cert_tbl.(h); incr nv_cert_tcount;;

let nv_cert_arith_consts =
  ["real_add"; "real_sub"; "real_mul"; "real_div"; "real_inv"; "real_neg";
   "real_pow"; "real_of_num"; "NUMERAL"; "BIT0"; "BIT1"; "_0"];;

let rec nv_cert_isnum tm =
  match tm with
    Const(c,_) -> mem c nv_cert_arith_consts
  | Comb(s,t) -> nv_cert_isnum s && nv_cert_isnum t
  | _ -> false;;

let nv_cert_normc =
  NUM_REDUCE_CONV THENC DEPTH_CONV NUM_BINOM_CONV THENC
  REWRITE_CONV[] THENC NUM_REDUCE_CONV;;

let nv_cert_norm th = CONV_RULE nv_cert_normc th;;

let nv_cert_ival tm = nv_cert_numval tm;;

let nv_cert_ne_th m n =
  EQF_ELIM(NUM_EQ_CONV(mk_eq(nv_cert_mk_num m,nv_cert_mk_num n)));;

let nv_cert_real_div_conv = REWR_CONV real_div;;

let nv_cert_step_spec =
  Array.map (fun th -> if th = TRUTH then th else
     SPEC_ALL th) nv_cert_step_tab;;

let nv_cert_le_tbl : (int * int, thm) Hashtbl.t = Hashtbl.create 5000;;

let nv_cert_le_th a k =
  try Hashtbl.find nv_cert_le_tbl (a,k) with Not_found ->
  let th = nv_cert_arith (mk_binop `(<=):num->num->bool` (nv_cert_mk_num a) (nv_cert_mk_num k)) in
  Hashtbl.replace nv_cert_le_tbl (a,k) th; th;;

let rec nv_cert_cong tm =
  try nv_cert_find tm with Not_found ->
  let th = nv_cert_cong_raw tm in
  nv_cert_store tm th; th

and nv_cert_via eth = nv_cert_eq eth (nv_cert_cong (rand(concl eth)))

and nv_cert_cong_raw tm =
  if nv_cert_isnum tm then
    (if is_comb tm && rator tm = `real_of_num` && is_numeral (rand tm) &&
        nv_cert_numval (rand tm) < 101
     then nv_cert_refl (rand tm) else nv_cert_rat tm)
  else
  let hd,args = strip_comb tm in
  match hd,args with
    Const("real_add",_),[x;y] -> nv_cert_add (nv_cert_cong x) (nv_cert_cong y)
  | Const("real_sub",_),[x;y] -> nv_cert_sub (nv_cert_cong x) (nv_cert_cong y)
  | Const("real_mul",_),[x;y] -> nv_cert_mul (nv_cert_cong x) (nv_cert_cong y)
  | Const("real_neg",_),[x] -> nv_cert_neg (nv_cert_cong x)
  | Const("real_div",_),[x;y] -> nv_cert_via (nv_cert_real_div_conv tm)
  | _ ->
  if exists (fun a -> type_of a = `:num` && not (is_numeral a)) args then
    let eth = NUM_REDUCE_CONV tm in
    if rand(concl eth) = tm then failwith ("nv_cert_cong: " ^ string_of_term tm)
    else nv_cert_via eth
  else
  match hd,args with
    Const("cheb_T",_),[d;k] ->
      let dv = nv_cert_ival d and kv = nv_cert_ival k in
      if dv < kv then
        nv_cert_via (MP (SPECL [d;k] NV_CERT_CHEB_T_ZERO)
                        (EQT_ELIM(NUM_LT_CONV(mk_binop `(<):num->num->bool` d k))))
      else if dv = 0 then nv_cert_via (nv_cert_norm (SPEC k (CONJUNCT1 NV_CERT_CHEB_T_01)))
      else if dv = 1 then nv_cert_via (nv_cert_norm (SPEC k (CONJUNCT2 NV_CERT_CHEB_T_01)))
      else nv_cert_via (nv_cert_norm (SPECL [nv_cert_mk_num (dv - 2); k] NV_CERT_CHEB_T_STEP))
  | Const("cheb_U",_),[d;k] ->
      let dv = nv_cert_ival d and kv = nv_cert_ival k in
      if dv < kv then
        nv_cert_via (MP (SPECL [d;k] NV_CERT_CHEB_U_ZERO)
                        (EQT_ELIM(NUM_LT_CONV(mk_binop `(<):num->num->bool` d k))))
      else if dv = 0 then nv_cert_via (nv_cert_norm (SPEC k (CONJUNCT1 NV_CERT_CHEB_U_01)))
      else if dv = 1 then nv_cert_via (nv_cert_norm (SPEC k (CONJUNCT2 NV_CERT_CHEB_U_01)))
      else nv_cert_via (nv_cert_norm (SPECL [nv_cert_mk_num (dv - 2); k] NV_CERT_CHEB_U_STEP))
  | Const("cat_m",_),[i] -> nv_cert_via (nv_cert_norm (SPEC i NV_CERT_M_EVEN))
  | Const("cat_kminus",_),[d] ->
      let dv = nv_cert_ival d in
      if dv = 0 then nv_cert_via (CONJUNCT1 NV_CERT_K01)
      else if dv = 1 then nv_cert_via (CONJUNCT1(CONJUNCT2 NV_CERT_K01))
      else nv_cert_via (nv_cert_norm (SPEC (nv_cert_mk_num (dv - 2)) NV_CERT_KM_STEP))
  | Const("cat_kplus",_),[d] ->
      let dv = nv_cert_ival d in
      if dv = 0 then nv_cert_via (CONJUNCT1(CONJUNCT2(CONJUNCT2 NV_CERT_K01)))
      else if dv = 1 then nv_cert_via (CONJUNCT2(CONJUNCT2(CONJUNCT2 NV_CERT_K01)))
      else nv_cert_via (nv_cert_norm (SPEC (nv_cert_mk_num (dv - 2)) NV_CERT_KP_STEP))
  | Const("cat_M0",_),[i;j] ->
      let iv = nv_cert_ival i and jv = nv_cert_ival j in
      if jv = 0 then nv_cert_via (SPEC i NV_CERT_M0_I0)
      else if iv = 0 then nv_cert_via (SPEC j NV_CERT_M0_0J)
      else nv_cert_via (nv_cert_norm (SPECL [nv_cert_mk_num (iv - 1); nv_cert_mk_num (jv - 1)]
                                        NV_CERT_M0_REC))
  | Const("cat_harm",_),[d;n] ->
      let nv = nv_cert_ival n in
      if nv = 0 then nv_cert_via (SPEC d NV_CERT_HARM_0)
      else nv_cert_via (nv_cert_norm (SPECL [d; nv_cert_mk_num (nv - 1)] NV_CERT_HARM_STEP))
  | Const("cat_Z0",_),[i;j] ->
      let iv = nv_cert_ival i and jv = nv_cert_ival j in
      if iv = jv then nv_cert_via (SPEC i NV_CERT_Z0_EQ)
      else nv_cert_via (MP (SPECL [i;j] NV_CERT_Z0_NE) (nv_cert_ne_th iv jv))
  | Const("nv_cert_mt",_),[k;i] -> nv_cert_via (nv_cert_norm (SPECL [k;i] NV_CERT_MT_EXP))
  | Const("nv_cert_zt",_),[k;i] -> nv_cert_via (nv_cert_norm (SPECL [k;i] NV_CERT_ZT_EXP))
  | Const("cat_pcoef",_),[n;r;i] when n = `1` ->
      nv_cert_via ((REWRITE_CONV[NV_CERT_PCOEF; NV_CERT_MULFAC2; NV_CERT_REVC63; cat_dist]
                    THENC nv_cert_normc) tm)
  | Const("cat_dcoef",_),[n;r;i] when n = `1` ->
      nv_cert_via ((REWRITE_CONV[NV_CERT_DCOEF; NV_CERT_MULFAC2; NV_CERT_REVC63; cat_dist;
                                 cat_sgn] THENC nv_cert_normc) tm)
  | Const("cat_entryq",_),[z;n;r;k] when z = `&0` && n = `1` -> nv_cert_entry r k
  | _ -> failwith ("nv_cert_cong: no rule for " ^ string_of_term tm)

(* cong theorem for sum(a..n) f, f a lambda whose body is a product x * y *)
and nv_cert_fold a n f =
  let atm = nv_cert_mk_num a in
  let fv = mk_var("f",type_of f) in
  let th0 = CONV_RULE (RAND_CONV BETA_CONV) (ISPECL [f; atm] SUM_SING_NUMSEG) in
  let rec go k acc =
    if k > n then acc else
    let th = INST [atm,nv_cert_va; f,fv] nv_cert_step_spec.(k) in
    let th = MP th (nv_cert_le_th a k) in
    let th = CONV_RULE (RAND_CONV (RAND_CONV BETA_CONV)) th in
    let xy = rand(rand(concl th)) in
    let c = nv_cert_muladd acc (nv_cert_cong (lhand xy)) (nv_cert_cong (rand xy)) in
    go (k + 1) (nv_cert_eq th c) in
  go (a + 1) (nv_cert_eq th0 (nv_cert_cong (rand(concl th0))))

and nv_cert_entry r k =
  let rv = nv_cert_ival r in
  let d = if rv < 4 then 4 - rv else rv - 4 in
  let a = 62 - d in
  let atm = nv_cert_mk_num a in
  let skip lem g =
    let th = SPECL [r; atm; g] lem in
    MP th (EQT_ELIM((REWRITE_CONV[cat_dist] THENC NUM_REDUCE_CONV) (lhand(concl th)))) in
  let th = SPECL [r; k] NV_CERT_ENTRY in
  let mtk = mk_comb(`nv_cert_mt`,k) and ztk = mk_comb(`nv_cert_zt`,k) in
  let ps = skip NV_CERT_PSKIP mtk and ds = skip NV_CERT_DSKIP ztk in
  let cp = nv_cert_eq ps (nv_cert_fold a 65 (rand(rand(concl ps))))
  and cd = nv_cert_eq ds (nv_cert_fold a 65 (rand(rand(concl ds)))) in
  nv_cert_eq th (nv_cert_mulsub cp (nv_cert_cong `&3 / &2`) cd);;
