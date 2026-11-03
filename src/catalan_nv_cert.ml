(* ========================================================================= *)
(* CAT_NONVANISHING, part C: the three fixed 48x48 determinants (paper,      *)
(* Section 4.4, Table 1) are nonzero.  Certificate: modulo 101 each matrix   *)
(* is congruent to an integer matrix C, and an explicit integer matrix X     *)
(* (computed below by Gauss-Jordan elimination mod 101, then checked in HOL) *)
(* satisfies X * C == I (mod 101).                                           *)
(* ========================================================================= *)

needs "src/catalan_nv_cert_tab.ml";;
needs "src/catalan_nv_iface.ml";;

let nv_cert_t0 = Sys.time();;

(* Residues of B r k = cat_entryq (&0) 1 r k, r <= 48, k <= 47 (with proofs). *)
let nv_cert_B =
  Array.init 49 (fun r -> Array.init 48 (fun k ->
    nv_cert_res (nv_cert_cong (list_mk_comb(`cat_entryq (&0) 1`,
                  [nv_cert_mk_num r; nv_cert_mk_num k])))));;

Printf.printf "nv_cert: entries done, %f s\n%!" (Sys.time() -. nv_cert_t0);;

(* inverse modulo 101 by Gauss-Jordan elimination *)
let nv_cert_inverse (c:int array array) =
  let n = Array.length c in
  let m = Array.init n (fun i -> Array.init (2 * n) (fun j ->
            if j < n then c.(i).(j) else if j - n = i then 1 else 0)) in
  let inv x = let rec go k = if (x * k) mod 101 = 1 then k else go (k + 1) in go 1 in
  for col = 0 to n - 1 do
    let piv = let rec f i = if i >= n then failwith "nv_cert_inverse: singular"
                            else if m.(i).(col) <> 0 then i else f (i + 1) in f col in
    let t = m.(piv) in m.(piv) <- m.(col); m.(col) <- t;
    let iv = inv m.(col).(col) in
    m.(col) <- Array.map (fun x -> (x * iv) mod 101) m.(col);
    for i = 0 to n - 1 do
      if i <> col && m.(i).(col) <> 0 then
        let f = m.(i).(col) in
        m.(i) <- Array.mapi (fun j x -> nv_cert_mod (x - f * m.(col).(j))) m.(i)
    done
  done;
  Array.init n (fun i -> Array.sub m.(i) n n);;

let nv_cert_cmat sigma =
  Array.init 48 (fun r -> Array.init 48 (fun k ->
    nv_cert_mod (nv_cert_B.(r).(k) + sigma * nv_cert_B.(r + 1).(k))));;

(* binary decision tree term for a table *)
let rec nv_cert_tree v lo hi leaf =
  if hi - lo = 1 then leaf lo else
  let mid = (lo + hi) / 2 in
  mk_cond(mk_binop `(<):num->num->bool` v (nv_cert_mk_num mid),
          nv_cert_tree v lo mid leaf, nv_cert_tree v mid hi leaf);;

let nv_cert_define name (x:int array array) =
  let iv = `i:num` and jv = `j:num` in
  let body = mk_abs(iv, nv_cert_tree iv 0 48 (fun i ->
               mk_abs(jv, nv_cert_tree jv 0 48 (fun j -> nv_cert_mk_num x.(i).(j))))) in
  new_definition (mk_eq(mk_var(name,`:num->num->num`), body));;

let nv_cert_cev =
  let ct = CONJUNCT1(SPEC_ALL COND_CLAUSES) and cf = CONJUNCT2(SPEC_ALL COND_CLAUSES) in
  let rec cev tm =
    if is_cond tm then
      (RATOR_CONV(RATOR_CONV(RAND_CONV NUM_LT_CONV)) THENC
       (REWR_CONV ct ORELSEC REWR_CONV cf) THENC cev) tm
    else REFL tm in
  cev;;

(* store cong theorems for all &(c i j) *)
let nv_cert_lookups defth =
  let c = lhs(concl defth) in
  for i = 0 to 47 do
    let rowth = CONV_RULE (RAND_CONV (BETA_CONV THENC nv_cert_cev))
                  (AP_THM defth (nv_cert_mk_num i)) in
    for j = 0 to 47 do
      let eth = CONV_RULE (RAND_CONV (BETA_CONV THENC nv_cert_cev))
                  (AP_THM rowth (nv_cert_mk_num j)) in
      let eth' = AP_TERM `real_of_num` eth in
      nv_cert_store (lhs(concl eth')) (nv_cert_eq eth' (nv_cert_refl (rand(concl eth))))
    done
  done;
  ignore c;;

let nv_cert_trans_th = nv_cert_spec NV_CERT_TRANS_MOD;;

let nv_cert_det_proof atm sigma name =
  let cm = nv_cert_cmat sigma in
  let x = nv_cert_inverse cm in
  (* sanity check in OCaml *)
  for i = 0 to 47 do for j = 0 to 47 do
    let s = ref 0 in
    for k = 0 to 47 do s := (!s + x.(i).(k) * cm.(k).(j)) mod 101 done;
    if !s <> (if i = j then 1 else 0) then failwith "nv_cert: bad inverse"
  done done;
  let defth = nv_cert_define name x in
  nv_cert_lookups defth;
  let fin = BETA_RULE (ISPECL [atm; lhs(concl defth)] NV_CERT_FINAL) in
  let hyp = lhand(concl fin) in
  let iv,b1 = dest_forall hyp in
  let q = rand b1 in
  let jv,b2 = dest_forall q in
  let r = rand b2 in
  let rows = Array.init 48 (fun i ->
    let itm = nv_cert_mk_num i in
    let ths = Array.init 48 (fun j ->
      let rij = vsubst [itm,iv; nv_cert_mk_num j,jv] r in
      let s = rand(rator rij) in
      let c = nv_cert_fold 0 47 (rand s) in
      let tgt = rand(rand rij) in
      let th = INST [s,nv_cert_vx; rand(rand(concl c)),nv_cert_va; tgt,nv_cert_vb]
                 nv_cert_trans_th in
      let ar = rand(lhand(concl th)) in
      let ath = EQT_ELIM((NUM_REDUCE_CONV THENC REWRITE_CONV[] THENC NUM_REDUCE_CONV) ar) in
      MP th (CONJ c ath)) in
    nv_cert_forall (mk_abs(jv, vsubst [itm,iv] r)) ths) in
  let res = MP fin (nv_cert_forall (mk_abs(iv, q)) rows) in
  Printf.printf "nv_cert: %s done, %f s\n%!" name (Sys.time() -. nv_cert_t0);
  res;;

let NV_CERT_DET0 = nv_cert_det_proof
  `\r k. cat_entryq (&0) 1 r k` 0 "nv_cert_x0";;

let NV_CERT_DETP = nv_cert_det_proof
  `\r k. cat_entryq (&0) 1 r k + cat_entryq (&0) 1 (r + 1) k` 1 "nv_cert_xp";;

let NV_CERT_DETM = nv_cert_det_proof
  `\r k. cat_entryq (&0) 1 r k - cat_entryq (&0) 1 (r + 1) k` (-1) "nv_cert_xm";;

let NV_CERT_DETS = prove
 (`~(ndet (0..47) (\r k. cat_entryq (&0) 1 r k) = &0) /\
   ~(ndet (0..47) (\r k. cat_entryq (&0) 1 r k + cat_entryq (&0) 1 (r + 1) k) = &0) /\
   ~(ndet (0..47) (\r k. cat_entryq (&0) 1 r k - cat_entryq (&0) 1 (r + 1) k) = &0)`,
  REWRITE_TAC[NV_CERT_DET0; NV_CERT_DETP; NV_CERT_DETM]);;

let NV_CERT_IF = prove
 (`nv_if_cert`,
  REWRITE_TAC[nv_if_cert; NV_CERT_DETS]);;

Printf.printf "nv_cert: total %f s\n%!" (Sys.time() -. nv_cert_t0);;
