(* ========================================================================= *)
(* CERT / CASE: drivers producing the bounds for X and Y in each case.       *)
(* ========================================================================= *)

needs "src/catalan_rp_cert_check.ml";;
needs "src/catalan_rp_cert_log.ml";;
needs "src/catalan_rp_cert_data.ml";;
needs "src/catalan_rp_cert_certdata.ml";;

let RP_CERT_CASE_NORM = prove
 (`(forall r. abs r < &1 ==> norm(Cx r) < &1) /\
   (forall a b. a pow 2 + b pow 2 < &1 ==> norm(complex(a,b)) < &1)`,
  CONJ_TAC THENL [SIMP_TAC[COMPLEX_NORM_CX]; ALL_TAC] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[complex_norm; RE; IM] THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM SQRT_1] THEN MATCH_MP_TAC SQRT_MONO_LT THEN
  ASM_REWRITE_TAC[] THEN MP_TAC(SPEC `a:real` REAL_LE_POW_2) THEN
  MP_TAC(SPEC `b:real` REAL_LE_POW_2) THEN REAL_ARITH_TAC);;

let rp_cert_case_ok t =
  let th = (REWRITE_CONV[rp_cert_ok; ALL] THENC DEPTH_CONV BETA_CONV THENC REWRITE_CONV[FST; SND]) 
             (mk_comb(`rp_cert_ok`, t)) in
  let cs = conjuncts (rand(concl th)) in
  let pr c =
    let z = rand(lhand c) in
    match z with
      Comb(Const("Cx",_),r) -> MP (SPEC r (CONJUNCT1 RP_CERT_CASE_NORM))
                                 (EQT_ELIM(rp_cert_chk_red (mk_binop `(<):real->real->bool` (mk_comb(`abs:real->real`, r)) `&1`)))
    | _ -> let a, b = dest_pair(rand z) in
           let h = mk_binop `(<):real->real->bool`
                     (mk_binop `(+):real->real->real` (mk_binop `(pow):real->num->real` a `2`)
                                                       (mk_binop `(pow):real->num->real` b `2`)) `&1` in
           MP (SPECL [a; b] (CONJUNCT2 RP_CERT_CASE_NORM)) (EQT_ELIM(rp_cert_chk_red h)) in
  if cs = [`true`] then EQT_ELIM th else
  EQ_MP (SYM th) (end_itlist CONJ (map pr cs));;

(* numeric Chebyshev T values *)
let rp_cert_case_cheb_thm m n =
  let cache = Hashtbl.create 16 in
  let rec go n =
    try Hashtbl.find cache n with Not_found ->
    let th =
      if n = 0 then INST [m,`x:real`] (CONJUNCT1 rp_cheb)
      else if n = 1 then INST [m,`x:real`] (CONJUNCT1(CONJUNCT2 rp_cheb))
      else
        let th = CONJUNCT1 (SPECL [mk_small_numeral (n - 2); m] RP_CERT_SER_CHEB_REC) in
        let th = CONV_RULE (LAND_CONV (RATOR_CONV (RAND_CONV NUM_REDUCE_CONV)) THENC
                            RAND_CONV (ONCE_DEPTH_CONV NUM_REDUCE_CONV)) th in
        let t1 = go (n - 1) and t2 = go (n - 2) in
        CONV_RULE (RAND_CONV (PURE_ONCE_REWRITE_CONV[t1] THENC PURE_ONCE_REWRITE_CONV[t2] THENC
                              REAL_RAT_REDUCE_CONV)) th in
    Hashtbl.add cache n th; th in
  go n;;

let rp_cert_case_cheb_conv tm =
  match tm with
    Comb(Comb(Const("rp_cheb",_),n),m) when frees m = [] ->
      rp_cert_case_cheb_thm m (dest_small_numeral n)
  | _ -> failwith "rp_cert_case_cheb_conv";;

let RP_CERT_CASE_TAIL_CLAUSES = prove
 (`(forall x. rp_cert_ttail [] x = &0) /\
   (forall c z t x. rp_cert_ttail (CONS (c,z) t) x =
      --(Re(c * clog(Cx(&1) - Cx(&2 * x) * z + z pow 2))) / &2 + rp_cert_ttail t x) /\
   (forall x. rp_cert_stail [] x = &0) /\
   (forall c z t x. rp_cert_stail (CONS (c,z) t) x =
      --(Re(c * clog(Cx(&1) - Cx x * z))) + rp_cert_stail t x)`,
  REWRITE_TAC[rp_cert_ttail; rp_cert_stail]);;

(* expand a closed-form value expression to transcendental atoms *)
let rp_cert_case_expand_conv =
  ONCE_DEPTH_CONV LENGTH_CONV THENC
  ONCE_DEPTH_CONV (rp_cert_cplx_sum_conv THENC ONCE_DEPTH_CONV NUM_REDUCE_CONV) THENC
  ONCE_DEPTH_CONV EL_CONV THENC
  PURE_REWRITE_CONV[RP_CERT_CASE_TAIL_CLAUSES] THENC
  ONCE_DEPTH_CONV rp_cert_case_cheb_conv;;

(* |- f m <= V  for f = rp_X kappa lam (seq lp tp) (seq lv tv) *)
let rp_cert_case_xval (kappa, lam, lp, tp, lv, tv) okp okv m =
  let mt = rp_cert_chk_tm m in
  let p = mk_comb(mk_comb(`rp_cert_seq`, lp), tp) and v = mk_comb(mk_comb(`rp_cert_seq`, lv), tv) in
  let tm = list_mk_comb(`rp_X`, [kappa; lam; p; v; mt]) in
  let hyps = EQT_ELIM(rp_cert_chk_red (mk_conj(mk_binop `(<=):real->real->bool` `--(&1)` mt,
                                                mk_binop `(<=):real->real->bool` mt `&1`))) in
  let ct = MP (ISPECL [lp; tp; mt] RP_CERT_ST_CLOSED) (CONJ okp hyps) in
  let cs = MP (ISPECL [lv; tv; mt] RP_CERT_SS_CLOSED) (CONJ okv hyps) in
  let th = (REWRITE_CONV[rp_X] THENC PURE_REWRITE_CONV[ct; cs] THENC rp_cert_case_expand_conv) tm in
  let b = rp_cert_log_ibound (rand(concl th)) in
  TRANS th (REFL (rand(concl th))) |> fun e -> MATCH_MP RP_CERT_LOG_B_EQ (CONJ e b) |> CONJUNCT2;;

let rp_cert_case_yval (lv, tv) okv m =
  let mt = rp_cert_chk_tm m in
  let v = mk_comb(mk_comb(`rp_cert_seq`, lv), tv) in
  let tm = list_mk_comb(`rp_Y`, [v; mt]) in
  let hyps = EQT_ELIM(rp_cert_chk_red (mk_conj(mk_binop `(<=):real->real->bool` `--(&1)` mt,
                                                mk_binop `(<=):real->real->bool` mt `&1`))) in
  let ct = MP (ISPECL [lv; tv; mt] RP_CERT_ST_CLOSED) (CONJ okv hyps) in
  let th = (REWRITE_CONV[rp_Y] THENC PURE_REWRITE_CONV[ct] THENC rp_cert_case_expand_conv) tm in
  let b = rp_cert_log_ibound (rand(concl th)) in
  CONJUNCT2 (MATCH_MP RP_CERT_LOG_B_EQ (CONJ th b));;

(* ---- assembling segments ---- *)
let RP_CERT_CASE_NZ = prove
 (`forall e q:real. &0 < e * q ==> ~(q = &0)`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `q = &0` THEN ASM_REWRITE_TAC[REAL_MUL_RZERO; REAL_LT_REFL]);;

let RP_CERT_CASE_ADDPT = prove
 (`forall P (a:real) b B. (forall x. a < x /\ x <= b ==> P x <= B) /\ P a <= B
                    ==> forall x. a <= x /\ x <= b ==> P x <= B`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `x:real = a` THEN ASM_SIMP_TAC[] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC);;

let rp_cert_case_fold segs =
  let ext acc s =
    let c = concl acc in
    let x, body = dest_forall c in
    let h = lhand body in
    let closed_left = is_binary "real_le" (lhand h) in
    let sh = lhand(snd(dest_forall(concl s))) in
    let open_right = is_binary "real_lt" (rand sh) in
    let lem = match closed_left, open_right with
        false, false -> RP_CERT_SUP_EXTEND | true, false -> RP_CERT_SUP_EXTEND_C
      | false, true -> RP_CERT_SUP_EXTEND_LAST | true, true -> RP_CERT_SUP_EXTEND_LAST_C in
    MATCH_MP lem (CONJ acc s) in
  List.fold_left ext (hd segs) (tl segs);;

(* driver for one function on its domain intervals.
   xsetup : (A, Q, s, gth) where gth : !x. H x /\ ~(Q x = 0) ==> deriv
   hfacts x : proves H x given lo < x < hi for the interval *)
let rp_cert_case_func f a q s gth qpos qneg certs valfn lofn bnd =
  List.map (fun (los, his, pieces, maxes) ->
    let lo = rp_cert_chk_num los and hi = rp_cert_chk_num his in
    let pcs = map (fun (b,c,br) -> (rp_cert_chk_num b, rp_cert_chk_num c,
                    match br with None -> None
                    | Some(m,w) -> Some(rp_cert_chk_num m, rp_cert_chk_num w))) pieces in
    let qthm, eqt = if lo >=/ num_of_string "0" then qpos, `&1` else qneg, `--(&1)` in
    let lot = rp_cert_chk_tm lo and hit = rp_cert_chk_tm hi in
    let x = `x:real` in
    (* dthm *)
    let hyp = mk_conj(mk_binop `(<):real->real->bool` lot x, mk_binop `(<):real->real->bool` x hit) in
    let hth = ASSUME hyp in
    let qnz = MATCH_MP RP_CERT_CASE_NZ (MP (SPEC x qthm) hth) in
    let gx = SPEC x gth in
    let hconj = lhand(lhand(concl gx)) in
    let hprove = prove(mk_imp(hyp, hconj),
       STRIP_TAC THEN REPEAT CONJ_TAC THEN
       FIRST [(fun g -> ACCEPT_TAC (rp_cert_case_ok (rand(snd g))) g);
              ASM_REAL_ARITH_TAC]) in
    let dthm = try GEN x (DISCH hyp (MP gx (CONJ (MP hprove hth) qnz))) with Failure e -> failwith ("dthm: "^e) in
    let vals = try map (fun m -> let mm = rp_cert_chk_num m in (mm, valfn mm)) maxes with Failure e -> failwith ("vals: "^e) in
    let lokind = try lofn lo with Failure e -> failwith ("lofn: "^e) in
    let segs, _ = rp_cert_chk_run f a q s eqt dthm qthm lo hi lokind pcs vals bnd in
    let segs = match lokind with
        Some(fth, None) -> (* INC from regular lo: add the point *)
          let s0 = hd segs in
          let fb = MATCH_MP REAL_LE_TRANS (CONJ fth (rp_cert_chk_le (rand(concl fth)) (rp_cert_chk_tm bnd))) in
          MATCH_MP RP_CERT_CASE_ADDPT (CONJ s0 fb) :: tl segs
      | _ -> segs in
    rp_cert_case_fold segs) certs;;

(* ---- norms ---- *)
let RP_CERT_CASE_NTAIL_CLAUSES = prove
 (`(forall t2. rp_cert_ntail [] t2 = &0) /\
   (forall cz t t2. rp_cert_ntail (CONS cz t) t2 = rp_cert_ntail1 cz t2 + rp_cert_ntail t t2) /\
   (forall cz. rp_cert_ntail1 cz [] = &0) /\
   (forall c z c' z' t. rp_cert_ntail1 (c,z) (CONS (c',z') t) =
      --(Re((c * c') * clog(Cx(&1) - z * z')) +
         Re((c * cnj c') * clog(Cx(&1) - z * cnj z'))) / &2 + rp_cert_ntail1 (c,z) t) /\
   (forall k. rp_cert_tail [] k = &0) /\
   (forall c z t k. rp_cert_tail (CONS (c,z) t) k = Re(c * z pow k) + rp_cert_tail t k)`,
  REWRITE_TAC[rp_cert_ntail; rp_cert_ntail1; rp_cert_tail; COMPLEX_MUL_ASSOC]);;

let rp_cert_case_reval_conv tm =
  match tm with
    Comb(Const("Re",_),a) when frees a = [] && not (can (find_term (fun t -> try fst(dest_const t) = "clog" with Failure _ -> false)) a) ->
      rp_cert_log_cplx_conv tm
  | _ -> failwith "reval";;

(* |- rp_nsq (rp_cert_seq l t) <= V *)
let rp_cert_case_nsq l t ok =
  let th0 = MP (ISPECL [l; t] RP_CERT_SS_NSQ) ok in
  let th = CONV_RULE (RAND_CONV (ONCE_DEPTH_CONV LENGTH_CONV THENC
             ONCE_DEPTH_CONV (rp_cert_cplx_sum_conv THENC ONCE_DEPTH_CONV NUM_REDUCE_CONV) THENC
             ONCE_DEPTH_CONV EL_CONV THENC PURE_REWRITE_CONV[RP_CERT_CASE_NTAIL_CLAUSES] THENC
             ONCE_DEPTH_CONV rp_cert_case_reval_conv)) th0 in
  let b = rp_cert_log_ibound (rand(concl th)) in
  CONJUNCT2 (MATCH_MP RP_CERT_LOG_B_EQ (CONJ th b));;

let RP_CERT_CASE_XALL = prove
 (`forall f B. (forall x. --(&1) <= x /\ x < &0 ==> f x <= B) /\ (forall x. &0 < x /\ x < &1 ==> f x <= B)
         ==> forall x. --(&1) <= x /\ x < &1 /\ ~(x = &0) ==> f x <= B`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `x < &0 \/ &0 < x` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ASM_MESON_TAC[]; ASM_MESON_TAC[]]);;

let rp_cert_case_final stmt stmt_def lam p v bx by xth yth np nv okp okv =
  let sp = MP (ISPECL [rand(rator p); rand p] RP_CERT_SS_SUMMABLE) okp in
  let sv = MP (ISPECL [rand(rator v); rand v] RP_CERT_SS_SUMMABLE) okv in
  prove(stmt,
    REWRITE_TAC[stmt_def] THEN
    MAP_EVERY EXISTS_TAC ((if lam = `true` then [] else [lam]) @ [p; v; rp_cert_chk_tm bx; rp_cert_chk_tm by]) THEN
    REWRITE_TAC[sp; sv] THEN
    REPEAT CONJ_TAC THEN
    TRY(CONV_TAC rp_cert_chk_red THEN NO_TAC) THEN
    TRY(MATCH_ACCEPT_TAC xth THEN NO_TAC) THEN
    TRY(MATCH_ACCEPT_TAC yth THEN NO_TAC) THEN
    REWRITE_TAC[rp_dual] THEN
    MP_TAC np THEN MP_TAC nv THEN MP_TAC RP_CERT_LOG_TWO THEN REAL_ARITH_TAC);;
