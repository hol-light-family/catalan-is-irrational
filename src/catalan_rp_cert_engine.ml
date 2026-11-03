(* ========================================================================= *)
(* CERT / ENGINE: OCaml machinery turning the derivative of rp_X / rp_Y into *)
(* the form A(x) / (s Q(x)) and checking root/sign certificates.            *)
(* ========================================================================= *)

needs "src/catalan_rp_cert_glue.ml";;
needs "src/catalan_rp_cert_cplx.ml";;

(* ---- rational polynomials in OCaml (lists of num, low degree first) ---- *)
let rp_cert_eng_zero = num_of_string "0";;
let rp_cert_eng_one = num_of_string "1";;
let rec rp_cert_eng_padd p q = match p, q with
    [], q -> q | p, [] -> p | a::p', b::q' -> (a +/ b) :: rp_cert_eng_padd p' q';;
let rp_cert_eng_pcmul c p = map (fun a -> c */ a) p;;
let rec rp_cert_eng_pmul p q = match p with
    [] -> [] | a::p' -> rp_cert_eng_padd (rp_cert_eng_pcmul a q) (rp_cert_eng_zero :: rp_cert_eng_pmul p' q);;
let rec rp_cert_eng_trim p =
  let r = rev p in
  let rec drop l = match l with a::l' when a =/ rp_cert_eng_zero -> drop l' | _ -> l in
  rev (drop r);;
let rp_cert_eng_peq p q = rp_cert_eng_trim p = rp_cert_eng_trim q ||
  (let a = rp_cert_eng_trim p and b = rp_cert_eng_trim q in
   length a = length b && forall2 (fun x y -> x =/ y) a b);;
let rp_cert_eng_hol_list p =
  mk_list(map term_of_rat p, `:real`);;
let rp_cert_eng_of_hol_list tm = map rat_of_term (dest_list tm);;

(* ---- polynomials over (x, atoms): association list ((deg, atom), coeff) - *)
let rp_cert_eng_mpadd p q =
  let rec ins (k,c) l = match l with
      [] -> [k,c]
    | (k',c')::l' -> if k = k' then (k, c +/ c')::l' else (k',c')::ins (k,c) l' in
  itlist ins p q;;
let rp_cert_eng_mpmul p q =
  itlist (fun ((d1,a1),c1) acc ->
    itlist (fun ((d2,a2),c2) acc ->
      if a1 >= 0 && a2 >= 0 then failwith "rp_cert_eng_mpmul: atom product" else
      rp_cert_eng_mpadd [((d1 + d2, max a1 a2), c1 */ c2)] acc) q acc) p [];;

let rec rp_cert_eng_topoly x atoms tm =
  if not (vfree_in x tm) && not (exists (fun a -> vfree_in a tm) atoms) then
    let v = rat_of_term(rand(concl((NUM_REDUCE_CONV THENC REAL_RAT_REDUCE_CONV) tm))) in
    [((0,-1), v)]
  else if tm = x then [((1,-1), rp_cert_eng_one)]
  else if mem tm atoms then [((0, index tm atoms), rp_cert_eng_one)]
  else match tm with
    Comb(Comb(Const("real_add",_),a),b) ->
      rp_cert_eng_mpadd (rp_cert_eng_topoly x atoms a) (rp_cert_eng_topoly x atoms b)
  | Comb(Comb(Const("real_sub",_),a),b) ->
      rp_cert_eng_mpadd (rp_cert_eng_topoly x atoms a)
        (map (fun (k,c) -> k, minus_num c) (rp_cert_eng_topoly x atoms b))
  | Comb(Const("real_neg",_),a) ->
      map (fun (k,c) -> k, minus_num c) (rp_cert_eng_topoly x atoms a)
  | Comb(Comb(Const("real_mul",_),a),b) ->
      rp_cert_eng_mpmul (rp_cert_eng_topoly x atoms a) (rp_cert_eng_topoly x atoms b)
  | Comb(Comb(Const("real_div",_),a),b) when not (vfree_in x b) && not (exists (fun a -> vfree_in a b) atoms) ->
      let v = rat_of_term(rand(concl((NUM_REDUCE_CONV THENC REAL_RAT_REDUCE_CONV) b))) in
      rp_cert_eng_mpmul (rp_cert_eng_topoly x atoms a) [((0,-1), rp_cert_eng_one // v)]
  | Comb(Comb(Const("real_pow",_),a),n) ->
      let k = dest_small_numeral n in
      let p = rp_cert_eng_topoly x atoms a in
      funpow k (rp_cert_eng_mpmul p) [((0,-1), rp_cert_eng_one)]
  | _ -> failwith ("rp_cert_eng_topoly: " ^ string_of_term tm);;

(* pure polynomial in x as coefficient list *)
let rp_cert_eng_xpoly x tm =
  let mp = rp_cert_eng_topoly x [] tm in
  let d = itlist (fun ((k,_),_) m -> max k m) mp 0 in
  map (fun i -> itlist (fun ((k,_),c) s -> if k = i then s +/ c else s) mp rp_cert_eng_zero)
      (0--d);;

let RP_CERT_ENG_PEVAL_CONV = REWRITE_CONV[rp_cert_peval];;

(* |- tm = rp_cert_peval L x  for a polynomial term tm in x *)
let rp_cert_eng_poly_thm x tm =
  let l = rp_cert_eng_xpoly x tm in
  let lt = rp_cert_eng_hol_list l in
  let rhs = mk_comb(mk_comb(`rp_cert_peval`, lt), x) in
  let th = REAL_RING (mk_eq(tm, rhs) |> fun t -> mk_eq(tm, rand(concl(RP_CERT_ENG_PEVAL_CONV rhs)))) in
  l, TRANS th (SYM(RP_CERT_ENG_PEVAL_CONV rhs));;

let RP_CERT_ENG_INV_FRAC = prove
 (`forall p x. inv(rp_cert_peval p x) = rp_cert_peval [&1] x / rp_cert_peval p x`,
  REWRITE_TAC[rp_cert_peval; real_div] THEN REAL_ARITH_TAC);;

let RP_CERT_ENG_FRAC_SCALE = prove
 (`forall n d c x. ~(c = &0)
     ==> rp_cert_peval n x / rp_cert_peval d x =
         rp_cert_peval (rp_cert_poly_cmul c n) x / rp_cert_peval (rp_cert_poly_cmul c d) x`,
  REWRITE_TAC[RP_CERT_POLY_EVAL_CMUL] THEN CONV_TAC REAL_FIELD);;

let rp_cert_eng_lcm_den0 l =
  itlist (fun a s -> let d = snd(numdom a) in
           let g = gcd_num s d in quo_num (s */ d) g) l rp_cert_eng_one;;

(* atoms: inv p, p / q with x free in the denominator *)
let rp_cert_eng_is_atom x tm =
  match tm with
    Comb(Const("real_inv",_),p) -> vfree_in x p
  | Comb(Comb(Const("real_div",_),_),q) -> vfree_in x q
  | _ -> false;;

(* |- atom = rp_cert_peval N x / rp_cert_peval D x, with (N, D) *)
let rp_cert_eng_atom_thm0 x tm =
  match tm with
    Comb(Const("real_inv",_),p) ->
      let d, dth = rp_cert_eng_poly_thm x p in
      let th = TRANS (AP_TERM `inv:real->real` dth)
                     (ISPECL [rp_cert_eng_hol_list d; x] RP_CERT_ENG_INV_FRAC) in
      [rp_cert_eng_one], d, th
  | Comb(Comb(Const("real_div",_),p),q) ->
      let n, nth = rp_cert_eng_poly_thm x p and d, dth = rp_cert_eng_poly_thm x q in
      n, d, MK_COMB(AP_TERM `(/):real->real->real` nth, dth)
  | _ -> failwith "rp_cert_eng_atom_thm";;

(* scale the denominator to integer coefficients *)
let rp_cert_eng_atom_thm x tm =
  let n, d, th = rp_cert_eng_atom_thm0 x tm in
  let c = rp_cert_eng_lcm_den0 d in
  if c =/ rp_cert_eng_one then n, d, th else
  let ct = term_of_rat c in
  let nz = EQT_ELIM(REAL_RAT_REDUCE_CONV (mk_neg(mk_eq(ct, `&0`)))) in
  let e = MP (ISPECL [rp_cert_eng_hol_list n; rp_cert_eng_hol_list d; ct; x] RP_CERT_ENG_FRAC_SCALE) nz in
  let e = CONV_RULE (RAND_CONV (BINOP_CONV (RATOR_CONV (RAND_CONV rp_cert_poly_list_conv)))) e in
  rp_cert_eng_pcmul c n, rp_cert_eng_pcmul c d, TRANS th e;;


(* ---- preprocessing of derivative expressions ---- *)

let rp_cert_eng_chebu_cache = ref ([] : (int * thm) list);;
let RP_CERT_ENG_CHEBU_REC = prove
 (`forall n x. rp_cert_chebu (n + 2) x = &2 * x * rp_cert_chebu (n + 1) x - rp_cert_chebu n x`,
  REWRITE_TAC[rp_cert_chebu]);;
(* |- rp_cert_chebu n x = (expression in x) for a numeral n and the variable x *)
let rec rp_cert_eng_chebu_thm x n =
  if n = 0 then INST [x,`x:real`] (CONJUNCT1 rp_cert_chebu)
  else if n = 1 then INST [x,`x:real`] (CONJUNCT1(CONJUNCT2 rp_cert_chebu))
  else
    let th = SPECL [mk_small_numeral (n - 2); x] RP_CERT_ENG_CHEBU_REC in
    let th = CONV_RULE (LAND_CONV (RATOR_CONV (RAND_CONV NUM_REDUCE_CONV)) THENC
                        RAND_CONV (ONCE_DEPTH_CONV NUM_REDUCE_CONV)) th in
    let t1 = rp_cert_eng_chebu_thm x (n - 1) and t2 = rp_cert_eng_chebu_thm x (n - 2) in
    CONV_RULE (RAND_CONV (PURE_ONCE_REWRITE_CONV[t1] THENC PURE_ONCE_REWRITE_CONV[t2])) th;;

let rp_cert_eng_chebu_conv x tm =
  match tm with
    Comb(Comb(Const("rp_cert_chebu",_),n),y) when y = x ->
      rp_cert_eng_chebu_thm x (dest_small_numeral n)
  | _ -> failwith "rp_cert_eng_chebu_conv";;

let RP_CERT_ENG_TAIL_CLAUSES = prove
 (`(forall x. rp_cert_dttail [] x = &0) /\
   (forall c z t x. rp_cert_dttail (CONS (c,z) t) x =
      Re(c * z / (Cx(&1) - Cx(&2 * x) * z + z pow 2)) + rp_cert_dttail t x) /\
   (forall x. rp_cert_dstail [] x = &0) /\
   (forall c z t x. rp_cert_dstail (CONS (c,z) t) x =
      Re(c * z / (Cx(&1) - Cx x * z)) + rp_cert_dstail t x)`,
  REWRITE_TAC[rp_cert_dttail; rp_cert_dstail]);;

(* rewrite Re(c * z / W) into rational form with numeral constants *)
let rp_cert_eng_re_conv tm =
  let th =
    (REWR_CONV RP_CERT_GLUE_RE_TDIV_REAL ORELSEC REWR_CONV RP_CERT_GLUE_RE_SDIV_REAL ORELSEC
     REWR_CONV RP_CERT_GLUE_RE_TDIV ORELSEC REWR_CONV RP_CERT_GLUE_RE_SDIV) tm in
  let cv t = match t with
      Comb(Const("Re",_),a) when frees a = [] -> rp_cert_log_cplx_conv t
    | Comb(Const("Im",_),a) when frees a = [] -> rp_cert_log_cplx_conv t
    | _ -> failwith "" in
  CONV_RULE (RAND_CONV (ONCE_DEPTH_CONV cv THENC ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV)) th;;

let rp_cert_eng_prep_conv x =
  let sumc t = (rp_cert_cplx_sum_conv THENC
                ONCE_DEPTH_CONV NUM_REDUCE_CONV) t in
  ONCE_DEPTH_CONV LENGTH_CONV THENC
  ONCE_DEPTH_CONV sumc THENC
  ONCE_DEPTH_CONV EL_CONV THENC
  PURE_REWRITE_CONV[RP_CERT_ENG_TAIL_CLAUSES] THENC
  ONCE_DEPTH_CONV (rp_cert_eng_chebu_conv x) THENC
  ONCE_DEPTH_CONV rp_cert_eng_re_conv;;

(* ---- main: |- ~(rp_cert_peval Q x = &0) ==> E = rp_cert_peval A x / (s * rp_cert_peval Q x) *)

let rec rp_cert_eng_find_atoms x tm acc =
  if rp_cert_eng_is_atom x tm then (if mem tm acc then acc else acc @ [tm]) else
  match tm with
    Comb(f,a) -> rp_cert_eng_find_atoms x a (rp_cert_eng_find_atoms x f acc)
  | Abs(_,b) -> acc
  | _ -> acc;;

let rp_cert_eng_lcm_den l =
  itlist (fun a s -> let d = snd(numdom a) in
           let g = gcd_num s d in quo_num (s */ d) g) l rp_cert_eng_one;;

let rp_cert_eng_rational_form x e =
  let atoms = rp_cert_eng_find_atoms x e [] in
  let infos = map (rp_cert_eng_atom_thm x) atoms in
  let vars = map (fun _ -> genvar `:real`) atoms in
  let ea = subst (zip vars atoms) e in
  let mp = rp_cert_eng_topoly x vars ea in
  if exists (fun ((d,a),c) -> a >= 0 && d > 0 && not (c =/ rp_cert_eng_zero)) mp then
    failwith "rp_cert_eng_rational_form: x * atom" else
  let ks = map (fun i -> itlist (fun ((d,a),c) s -> if a = i then s +/ c else s) mp rp_cert_eng_zero)
               (0--(length atoms - 1)) in
  let pdeg = itlist (fun ((d,a),_) m -> if a < 0 then max d m else m) mp 0 in
  let pl = map (fun i -> itlist (fun ((d,a),c) s -> if a < 0 && d = i then s +/ c else s) mp rp_cert_eng_zero)
               (0--pdeg) in
  let pt = mk_comb(mk_comb(`rp_cert_peval`, rp_cert_eng_hol_list pl), x) in
  let terms = map2 (fun k v -> mk_binop `( * ):real->real->real` (term_of_rat k) v) ks vars in
  let ta = itlist (fun t s -> mk_binop `(+):real->real->real` t s) terms pt in
  let ta_exp = rand(concl(RP_CERT_ENG_PEVAL_CONV ta)) in
  let th1 = TRANS (REAL_RING (mk_eq(ea, ta_exp))) (SYM(RP_CERT_ENG_PEVAL_CONV ta)) in
  let th2 = INST (zip atoms vars) th1 in
  (* now e = sum k_i * atom_i + peval P x ; replace atoms *)
  let th3 = CONV_RULE (RAND_CONV (PURE_REWRITE_CONV (map (fun (_,_,t) -> t) infos))) th2 in
  (* denominators *)
  let ds = itlist (fun (_,d,_) acc -> if exists (rp_cert_eng_peq d) acc then acc else acc @ [d]) infos [] in
  let ds = rev ds in
  let qpoly = itlist rp_cert_eng_pmul ds [rp_cert_eng_one] in
  let qt = rp_cert_eng_hol_list qpoly in
  let qx = mk_comb(mk_comb(`rp_cert_peval`, qt), x) in
  let hyp_q = mk_neg(mk_eq(qx, `&0`)) in
  let cof d = let rec rm l = match l with [] -> [] | a::l' -> if rp_cert_eng_peq a d then l' else a::rm l' in
              itlist rp_cert_eng_pmul (rm ds) [rp_cert_eng_one] in
  let qth d = (* |- rp_cert_poly_mul D R = Q *)
    let r = cof d in
    let tm = mk_binop `rp_cert_poly_mul` (rp_cert_eng_hol_list d) (rp_cert_eng_hol_list r) in
    let th = rp_cert_poly_list_conv tm in
    if rand(concl th) <> qt then failwith "rp_cert_eng: cofactor mismatch" else r, th in
  let qths = map (fun d -> d, qth d) ds in
  (* convert one term k * (peval N x / peval D x) *)
  let conv_term t =
    match t with
      Comb(Comb(Const("real_mul",_),k),f) ->
        let th_a = REWR_CONV RP_CERT_GLUE_FRAC_CMUL t in
        let r = rand(concl th_a) in
        let n' = lhand(lhand r) in
        let d = lhand(rand r) in
        let dl = rp_cert_eng_of_hol_list d in
        let _, (rl, qeq) = find (fun (d',_) -> rp_cert_eng_peq d' dl) qths in
        let th_b = MP (ISPECL [n'; d; rp_cert_eng_hol_list rl; qt; x] RP_CERT_GLUE_FRAC_TERM)
                      (CONJ qeq (ASSUME hyp_q)) in
        let th_c = CONV_RULE (RAND_CONV (LAND_CONV (RATOR_CONV (RAND_CONV
                     (rp_cert_poly_list_conv))))) (TRANS th_a th_b) in
        th_c
    | Comb(Comb(Const("rp_cert_peval",_),p),_) ->
        let th = MP (ISPECL [p; qt; x] RP_CERT_GLUE_FRAC_POLY) (ASSUME hyp_q) in
        CONV_RULE (RAND_CONV (LAND_CONV (RATOR_CONV (RAND_CONV rp_cert_poly_list_conv)))) th
    | _ -> failwith "conv_term" in
  let rec conv_sum t =
    match t with
      Comb(Comb(Const("real_add",_),a),b) ->
        let ta = conv_term a and tb = conv_sum b in
        let th = MK_COMB(AP_TERM `(+):real->real->real` ta, tb) in
        let th2 = CONV_RULE (RAND_CONV (REWR_CONV RP_CERT_GLUE_FRAC_ADD THENC
                    LAND_CONV (RATOR_CONV (RAND_CONV rp_cert_poly_list_conv)))) th in
        th2
    | _ -> conv_term t in
  let th4 = TRANS th3 (conv_sum (rand(concl th3))) in
  let al = rp_cert_eng_of_hol_list (lhand(lhand(rand(concl th4)))) in
  let s0 = rp_cert_eng_lcm_den al in
  let g = itlist (fun a g -> gcd_num g (fst(numdom (a */ s0))) ) al rp_cert_eng_zero in
  let s = if g =/ rp_cert_eng_zero then s0 else s0 // abs_num g in
  let st = term_of_rat s in
  let spos = rp_cert_cplx_lt `&0` st in
  let th5 = MP (ISPECL [lhand(lhand(rand(concl th4))); qt; st; x] RP_CERT_GLUE_FRAC_SCALE) spos in
  let th6 = CONV_RULE (RAND_CONV (LAND_CONV (RATOR_CONV (RAND_CONV rp_cert_poly_list_conv)))) th5 in
  let th7 = TRANS th4 th6 in
  DISCH hyp_q th7, (rp_cert_eng_of_hol_list (lhand(lhand(rand(concl th7))))), qpoly, ds, s;;
