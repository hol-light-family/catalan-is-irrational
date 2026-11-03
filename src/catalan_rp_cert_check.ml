(* ========================================================================= *)
(* CERT / CHECK: checking a root/bracket certificate for f' = A/(sQ) on an   *)
(* interval and deriving a global upper bound for f.                         *)
(* ========================================================================= *)

needs "src/catalan_rp_cert_engine.ml";;

let rp_cert_chk_num s =
  let int_of t = if String.length t > 0 && t.[0] = '-' then
      minus_num (num_of_string (String.sub t 1 (String.length t - 1))) else num_of_string t in
  match String.index_opt s '/' with
    None -> int_of s
  | Some i -> int_of (String.sub s 0 i) // int_of (String.sub s (i+1) (String.length s - i - 1));;
let rp_cert_chk_tm q = term_of_rat q;;
let rp_cert_chk_lt a b = rp_cert_cplx_lt a b;;
let rp_cert_chk_le a b = rp_cert_cplx_le a b;;
let rp_cert_chk_red = NUM_REDUCE_CONV THENC REAL_RAT_REDUCE_CONV;;

(* reduce closed rational subterms of the forms b / d and m + w to canonical *)
let rp_cert_chk_canon tms th =
  let eqs = map (fun t -> rp_cert_chk_red t) tms in
  let eqs = filter (fun e -> lhs(concl e) <> rhs(concl e)) eqs in
  if eqs = [] then th else CONV_RULE (PURE_REWRITE_CONV eqs) th;;

(* --- piece certificates --- *)
let rp_cert_chk_scale b c =
  (* integers B C D with b = B/D, c = C/D *)
  let db = snd(numdom b) and dc = snd(numdom c) in
  let d = quo_num (db */ dc) (gcd_num db dc) in
  b */ d, c */ d, d;;

let rp_cert_chk_piece a b c kind =
  (* kind = 0: NOROOT, 1: ONEROOT; returns theorem with canonical b, c *)
  let bb, cc, dd = rp_cert_chk_scale b c in
  let n = length (dest_list a) - 1 in
  let bt = mk_realintconst bb and ct = mk_realintconst cc and dt = mk_realintconst dd in
  let nt = mk_small_numeral n in
  let lem = if kind = 0 then RP_CERT_POLY_NOROOT else RP_CERT_POLY_ONEROOT in
  let th0 = ISPECL [a; bt; ct; dt; nt] lem in
  let mtm = list_mk_comb(`rp_cert_poly_mobr`, [bt; ct; dt; a; nt]) in
  let mth = rp_cert_poly_mobr_conv mtm in
  let l = rand(concl mth) in
  let varth = rp_cert_poly_var_conv (mk_comb(`rp_cert_poly_var`, l)) in
  let azth = rp_cert_poly_allzero_conv (mk_comb(mk_comb(`ALL:(real->bool)->real list->bool`, `\a:real. a = &0`), l)) in
  let ant = lhand(concl th0) in
  let pc c =
    if is_neg c then EQ_MP (SYM(AP_TERM `(~)` (TRANS (PURE_REWRITE_CONV[mth] (rand c)) azth)))
                       (EQT_ELIM(REWRITE_CONV[] (mk_neg(rand(concl azth)))))
    else if can (find_term ((=) `rp_cert_poly_var`)) c then
      EQT_ELIM((PURE_REWRITE_CONV[mth] THENC PURE_REWRITE_CONV[varth] THENC NUM_REDUCE_CONV) c)
    else EQT_ELIM((ONCE_DEPTH_CONV LENGTH_CONV THENC NUM_REDUCE_CONV THENC REAL_RAT_REDUCE_CONV) c) in
  let pth = end_itlist CONJ (map pc (conjuncts ant)) in
  let th1 = MP th0 pth in
  rp_cert_chk_canon [mk_binop `(/):real->real->real` bt dt; mk_binop `(/):real->real->real` ct dt] th1;;

(* sign of A at rational point q:  |- &0 < peval A q  or  |- peval A q < &0 *)
let rp_cert_chk_sign a q =
  let p, d = numdom q in
  let th = rp_cert_poly_sign_at a (mk_realintconst p) (mk_realintconst d) in
  let qt = rp_cert_chk_tm q in
  let e = rp_cert_chk_red (mk_binop `(/):real->real->real` (mk_realintconst p) (mk_realintconst d)) in
  let th = if rand(concl e) = qt then PURE_REWRITE_RULE[e] th else th in
  th;;

let rp_cert_chk_is_pos th = is_comb(concl th) && lhand(concl th) = `&0`;;

let RP_CERT_CHK_NZ = prove
 (`forall x:real. (&0 < x ==> ~(x = &0)) /\ (x < &0 ==> ~(x = &0))`, REAL_ARITH_TAC);;
let RP_CERT_CHK_SGN1 = prove
 (`forall x:real. (&0 < x ==> &0 < &1 * x) /\ (x < &0 ==> &0 < --(&1) * x)`, REAL_ARITH_TAC);;
let RP_CERT_CHK_E = prove
 (`forall x:real. (&0 < (&1 * &1) * x <=> &0 < x) /\ (&0 < (--(&1) * --(&1)) * x <=> &0 < x) /\
            (&0 < (&1 * --(&1)) * x <=> x < &0) /\ (&0 < (--(&1) * &1) * x <=> x < &0)`,
  REAL_ARITH_TAC);;

let rp_cert_chk_nz th =
  if rp_cert_chk_is_pos th then MP (CONJUNCT1 (SPEC (rand(concl th)) RP_CERT_CHK_NZ)) th
  else MP (CONJUNCT2 (SPEC (lhand(concl th)) RP_CERT_CHK_NZ)) th;;

(* dnorm of an explicit list: |- rp_cert_poly_dnorm L = q *)
let rp_cert_chk_dnorm l =
  (REWRITE_CONV[rp_cert_poly_dnorm; rp_cert_poly_asum] THENC REAL_RAT_REDUCE_CONV)
    (mk_comb(`rp_cert_poly_dnorm`, l));;

(* exact value of peval L at rational q *)
let rp_cert_chk_value l q =
  let p, d = numdom q in
  let tm = list_mk_comb(`rp_cert_poly_hz`, [l; mk_realintconst p; mk_realintconst d]) in
  let th = rp_cert_poly_hz_conv tm in
  let hv = rat_of_term(rand(concl th)) in
  let n = length (dest_list l) - 1 in
  hv // power_num d (num_of_string (string_of_int n));;

(* ---- segment lemmas, with G(y) = peval a y / (s * peval q y) ---- *)

let RP_CERT_CHK_CONT = prove
 (`forall f a q s lo hi p.
     (forall x. lo < x /\ x < hi ==>
          (f has_real_derivative (rp_cert_peval a x / (s * rp_cert_peval q x))) (atreal x)) /\
     lo < p /\ p < hi
     ==> forall t. f real_continuous (atreal p within t)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_CONTINUOUS_ATREAL_WITHINREAL THEN
  MATCH_MP_TAC HAS_REAL_DERIVATIVE_IMP_CONTINUOUS_ATREAL THEN
  EXISTS_TAC `rp_cert_peval a p / (s * rp_cert_peval q p)` THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;




let RP_CERT_CHK_GSIGN = rp_cert_steps
 `forall f a q s lo hi u v c ea eq.
     (forall x. lo < x /\ x < hi ==>
          (f has_real_derivative (rp_cert_peval a x / (s * rp_cert_peval q x))) (atreal x)) /\
     (forall y. u < y /\ y < v ==> ~(rp_cert_peval a y = &0)) /\ u <= c /\ c <= v /\
     lo <= u /\ v <= hi /\ (forall y. lo < y /\ y < hi ==> &0 < eq * rp_cert_peval q y) /\
     (eq = &1 \/ eq = --(&1)) /\ &0 < s /\ &0 < ea * rp_cert_peval a c /\ (ea = &1 \/ ea = --(&1))
     ==> forall y. u < y /\ y < v ==>
             (f has_real_derivative (rp_cert_peval a y / (s * rp_cert_peval q y))) (atreal y) /\
             &0 < (ea * eq) * (rp_cert_peval a y / (s * rp_cert_peval q y))`
 [(REPEAT GEN_TAC THEN DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)) THEN X_GEN_TAC `y:real` THEN STRIP_TAC THEN CONJ_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC]);
  (MP_TAC(SPECL [`a:real list`; `q:real list`; `s:real`; `u:real`; `v:real`; `ea:real`; `eq:real`]
    RP_CERT_SUP_GSIGN) THEN ASM_REWRITE_TAC[]);
  (ANTS_TAC THENL [ALL_TAC; DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);
  (CONJ_TAC THENL
   [MP_TAC(SPECL [`a:real list`; `u:real`; `v:real`; `c:real`] RP_CERT_SUP_SIGN_ON_GAP) THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `&0 < ea * rp_cert_peval a c` THEN
    UNDISCH_TAC `ea = &1 \/ ea = --(&1)` THEN
    DISCH_THEN(DISJ_CASES_THEN SUBST1_TAC) THEN
    REWRITE_TAC[REAL_MUL_LID; REAL_MUL_LNEG; REAL_NEG_GT0] THEN
    DISCH_TAC THEN ASM_REWRITE_TAC[] THEN MESON_TAC[];
    X_GEN_TAC `z:real` THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC])];;
let RP_CERT_CHK_INC = prove
 (`forall f g u v.
     (forall y. u < y /\ y < v ==> (f has_real_derivative g y) (atreal y) /\ &0 < (&1) * g y) /\
     (forall t. f real_continuous (atreal u within t)) /\ (forall t. f real_continuous (atreal v within t))
     ==> forall x. u <= x /\ x <= v ==> f x <= f v`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC RP_CERT_SUP_INC2 THEN
  EXISTS_TAC `g:real->real` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `z:real` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `z:real` o check (is_forall o concl)) THEN
  ASM_REWRITE_TAC[] THEN SIMP_TAC[REAL_MUL_LID; REAL_MUL_LNEG; REAL_NEG_GT0]);;

let RP_CERT_CHK_DEC = prove
 (`forall f g u v.
     (forall y. u < y /\ y < v ==> (f has_real_derivative g y) (atreal y) /\ &0 < --(&1) * g y) /\
     (forall t. f real_continuous (atreal u within t)) /\ (forall t. f real_continuous (atreal v within t))
     ==> forall x. u <= x /\ x <= v ==> f x <= f u`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC RP_CERT_SUP_DEC2 THEN
  EXISTS_TAC `g:real->real` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `z:real` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `z:real` o check (is_forall o concl)) THEN
  ASM_REWRITE_TAC[] THEN SIMP_TAC[REAL_MUL_LID; REAL_MUL_LNEG; REAL_NEG_GT0]);;

let RP_CERT_CHK_INC_LO = prove
 (`forall f g u v.
     (forall y. u < y /\ y < v ==> (f has_real_derivative g y) (atreal y) /\ &0 < (&1) * g y) /\
     (forall t. f real_continuous (atreal v within t))
     ==> forall x. u < x /\ x <= v ==> f x <= f v`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC RP_CERT_SUP_INC THEN
  EXISTS_TAC `g:real->real` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `z:real` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `z:real` o check (is_forall o concl)) THEN
  ASM_REWRITE_TAC[] THEN SIMP_TAC[REAL_MUL_LID; REAL_MUL_LNEG; REAL_NEG_GT0]);;

let RP_CERT_CHK_DEC_HI = prove
 (`forall f g u v.
     (forall y. u < y /\ y < v ==> (f has_real_derivative g y) (atreal y) /\ &0 < --(&1) * g y) /\
     (forall t. f real_continuous (atreal u within t))
     ==> forall x. u <= x /\ x < v ==> f x <= f u`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC RP_CERT_SUP_DEC THEN
  EXISTS_TAC `g:real->real` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `z:real` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `z:real` o check (is_forall o concl)) THEN
  ASM_REWRITE_TAC[] THEN SIMP_TAC[REAL_MUL_LID; REAL_MUL_LNEG; REAL_NEG_GT0]);;




let RP_CERT_CHK_BRK = rp_cert_steps
 `forall f a q s lo hi m w ka kq q0.
     (forall x. lo < x /\ x < hi ==>
          (f has_real_derivative (rp_cert_peval a x / (s * rp_cert_peval q x))) (atreal x)) /\
     lo < m /\ m + w < hi /\ &0 < w /\ --(&1) <= m /\ m + w <= &1 /\ &0 < s /\
     rp_cert_peval a m * rp_cert_peval a (m + w) <= &0 /\
     rp_cert_poly_dnorm a <= ka /\ rp_cert_poly_dnorm q <= kq /\
     &0 < q0 /\ q0 <= abs(rp_cert_peval q m) - kq * w
     ==> forall x. m <= x /\ x <= m + w ==> f x <= f m + ((ka * w) / (s * q0)) * w`
 [(REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC RP_CERT_SUP_BRACKET THEN
  EXISTS_TAC `\y. rp_cert_peval a y / (s * rp_cert_peval q y)` THEN
  ASM_REWRITE_TAC[]);
  (X_GEN_TAC `y:real` THEN STRIP_TAC THEN CONJ_TAC);
  (FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC);
  (MATCH_MP_TAC RP_CERT_SUP_BRK_DERIV2 THEN MAP_EVERY EXISTS_TAC [`m:real`; `kq:real`] THEN ASM_REWRITE_TAC[])];;

(* discharge the antecedent of th using facts or closed computation *)
let rp_cert_chk_mp th facts =
  let ant = lhand(concl th) in
  let cs = conjuncts ant in
  let prove_c c =
    try find (fun f -> aconv (concl f) c) facts with Failure _ ->
    try EQT_ELIM(rp_cert_chk_red c) with Failure _ ->
    try EQT_ELIM((rp_cert_chk_red THENC REWRITE_CONV[]) c) with Failure _ ->
      (List.iter (fun f -> print_string ("FACT: " ^ string_of_term (concl f) ^ "\n")) facts;
       failwith ("rp_cert_chk_mp: cannot prove " ^ string_of_term c)) in
  let ths = map prove_c cs in
  let rec build l = match l with [t] -> t | t::l' -> CONJ t (build l') | [] -> TRUTH in
  MP th (build ths);;

(* rational helpers *)
let rp_cert_chk_floor q k =
  let sc = power_num (num_of_string "10") (num_of_string (string_of_int k)) in
  floor_num (q */ sc) // sc;;
let rp_cert_chk_ceil q k =
  let sc = power_num (num_of_string "10") (num_of_string (string_of_int k)) in
  ceiling_num (q */ sc) // sc;;


let RP_CERT_CHK_HZVAL = prove
 (`forall p m d v. ~(d = &0) /\ rp_cert_poly_hz p m d = v
     ==> rp_cert_peval p (m / d) = v / d pow (LENGTH p - 1)`,
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  ASM_SIMP_TAC[RP_CERT_POLY_HZ] THEN
  SUBGOAL_THEN `~((d:real) pow (LENGTH (p:real list) - 1) = &0)` MP_TAC THENL
   [ASM_REWRITE_TAC[REAL_POW_EQ_0]; CONV_TAC REAL_FIELD]);;

(* |- rp_cert_peval L q = v  (q canonical rational term) *)
let rp_cert_chk_eval l q =
  let p, d = numdom q in
  let mt = mk_realintconst p and dt = mk_realintconst d in
  let hth = rp_cert_poly_hz_conv (list_mk_comb(`rp_cert_poly_hz`, [l; mt; dt])) in
  let th = rp_cert_chk_mp (ISPECL [l; mt; dt; rand(concl hth)] RP_CERT_CHK_HZVAL) [hth] in
  let th = CONV_RULE (RAND_CONV (ONCE_DEPTH_CONV LENGTH_CONV THENC rp_cert_chk_red)) th in
  let e = rp_cert_chk_red (mk_binop `(/):real->real->real` mt dt) in
  if lhs(concl e) = rhs(concl e) then th else PURE_REWRITE_RULE[e] th;;

let rp_cert_chk_lam a =
  let y = `y:real` in mk_abs(y, mk_neg(mk_eq(mk_comb(mk_comb(`rp_cert_peval`, a), y), `&0`)));;

let rp_cert_chk_interval f a q s eqt dthm qthm lo hi lokind pieces vals bnd =
  let tq = rp_cert_chk_tm in
  let lot = tq lo and hit = tq hi and bt = tq bnd in
  let y = `y:real` in
  let pa t = mk_comb(mk_comb(`rp_cert_peval`, a), t) in
  let lt a b = mk_binop `(<):real->real->bool` a b and le a b = mk_binop `(<=):real->real->bool` a b in
  let plus a b = mk_binop `(+):real->real->real` a b in
  let pth = map (fun (b,c,br) -> (b, c, br,
                   (try rp_cert_chk_piece a b c (match br with None -> 0 | Some _ -> 1)
                    with Failure e -> failwith ("piece " ^ string_of_num b ^ ": " ^ e)))) pieces in
  let sign_cache = ref [] in
  let sign x = try assoc x !sign_cache with Failure _ ->
    let th = rp_cert_chk_sign a x in sign_cache := (x,th) :: !sign_cache; th in
  let addeq m w = rp_cert_chk_red (plus (tq m) (tq w)) in
  (* bracket data *)
  let brx = flat (map (fun (b,c,br,th) -> match br with None -> [] | Some(m,w) ->
    let mt = tq m and wt = tq w in
    let smth = sign m and swth = PURE_REWRITE_RULE[SYM(addeq m w)] (sign (m +/ w)) in
    if rp_cert_chk_is_pos smth = rp_cert_chk_is_pos swth then failwith "no sign change" else
    let prod = prove(lt (mk_binop `( * ):real->real->real` (pa mt) (pa (plus mt wt))) `&0`,
       MP_TAC smth THEN MP_TAC swth THEN
       SPEC_TAC(pa mt, `u1:real`) THEN SPEC_TAC(pa (plus mt wt), `u2:real`) THEN
       REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
       ASM_MESON_TAC[REAL_LT_MUL; REAL_MUL_LNEG; REAL_MUL_RNEG; REAL_NEG_GT0;
                     REAL_ARITH `forall x:real. x < &0 <=> &0 < --x`; REAL_MUL_SYM; REAL_NEG_NEG]) in
    let ex = rp_cert_chk_mp (ISPECL [a; tq b; tq c; mt; wt] RP_CERT_SUP_BRK_EXCL) [th; prod] in
    [(b,c,m,w,ex,prod)]) pth) in
  let pl = rp_cert_chk_lam a in
  (* root-freeness on (u,v) *)
  let rootfree u v =
    let bs = setify (flat (map (fun (b,c,_,_) -> [b;c]) pth)) in
    let bs = filter (fun c -> u </ c && c </ v) bs in
    let bs = sort (</) bs in
    let pts = u :: bs @ [v] in
    let rec subs l = match l with s0::s1::l' -> (s0,s1) :: subs (s1::l') | _ -> [] in
    let sub_thm (s0, s1) =
      let (b,c,br,th) = find (fun (b,c,_,_) -> b <=/ s0 && s1 <=/ c) pth in
      match br with
        None -> rp_cert_chk_mp (BETA_RULE (ISPECL [pl; tq b; tq c; tq s0; tq s1] RP_CERT_SUP_WEAKEN)) [th]
      | Some(m,w) ->
          let (_,_,_,_,ex,_) = find (fun (b',c',_,_,_,_) -> b' =/ b && c' =/ c) brx in
          let goal = mk_forall(y, mk_imp(mk_conj(lt (tq s0) y, lt y (tq s1)),
                                         mk_neg(mk_eq(pa y, `&0`)))) in
          prove(goal, GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC (SPEC y ex) THEN
                      ASM_REAL_ARITH_TAC) in
    let ths = map sub_thm (subs pts) in
    let rec fold ths bs = match ths, bs with
        [t], [] -> t
      | t1::t2::ts, c::bs' ->
          let nzc = rp_cert_chk_nz (sign c) in
          let comb = rp_cert_chk_mp (BETA_RULE (ISPECL [pl; tq u; tq c; tq (if bs' = [] then v else hd bs')]
                        RP_CERT_SUP_COMB)) [] |> fun _ -> failwith "" in comb
      | _ -> failwith "fold" in
    let _ = fold in
    (* left fold: maintain theorem for (u, cur) *)
    let rec lfold acc cur ths bs = match ths, bs with
        [], [] -> acc
      | t::ts, c::bs' ->
          let nxt = match bs' with [] -> v | c'::_ -> c' in
          let nzc = rp_cert_chk_nz (sign c) in
          let comb = rp_cert_chk_mp (BETA_RULE (ISPECL [pl; tq u; tq c; tq nxt] RP_CERT_SUP_COMB))
                       [acc; nzc; t] in
          lfold comb nxt ts bs'
      | _ -> failwith "lfold" in
    lfold (hd ths) (if bs = [] then v else hd bs) (tl ths) bs in
  (* monotone segment on gap (u,v); returns theorem of the shape given by INC/DEC lemmas *)
  let gseg u v =
    let rf = rootfree u v in
    let c = if u =/ lo then v else u in
    let sc = sign c in
    let ea = if rp_cert_chk_is_pos sc then `&1` else `--(&1)` in
    let sg = if rp_cert_chk_is_pos sc then MP (CONJUNCT1 (SPEC (pa (tq c)) RP_CERT_CHK_SGN1)) sc
             else MP (CONJUNCT2 (SPEC (pa (tq c)) RP_CERT_CHK_SGN1)) sc in
    let gs = rp_cert_chk_mp (ISPECL [f; a; q; s; lot; hit; tq u; tq v; tq c; ea; eqt] RP_CERT_CHK_GSIGN)
               [dthm; rf; qthm; sg] in
    let e = rp_cert_chk_red (mk_binop `( * ):real->real->real` ea eqt) in
    let gs = PURE_REWRITE_RULE[e] gs in
    let inc = rand(concl e) = `&1` in
    let g = mk_abs(y, mk_binop `(/):real->real->real` (pa y)
                        (mk_binop `( * ):real->real->real` s (mk_comb(mk_comb(`rp_cert_peval`, q), y)))) in
    let cont p = rp_cert_chk_mp (ISPECL [f; a; q; s; lot; hit; tq p] RP_CERT_CHK_CONT) [dthm] in
    inc, gs, g, cont in
  (* bracket segment *)
  let bseg (b,c,m,w,ex,prod) =
    let mt = tq m and wt = tq w in
    let ka_th = rp_cert_chk_dnorm a and kq_th = rp_cert_chk_dnorm q in
    let ka = rat_of_term(rand(concl ka_th)) and kq = rat_of_term(rand(concl kq_th)) in
    let qv_th = rp_cert_chk_eval q m in
    let qv = rat_of_term(rand(concl qv_th)) in
    let q0 = rp_cert_chk_floor (abs_num qv -/ kq */ w) 30 in
    if q0 <=/ num_of_string "0" then failwith "bseg: q0 <= 0" else
    let leth eq_th bnd = (* dnorm l = v ==> dnorm l <= bnd *)
      EQ_MP (SYM(AP_THM (AP_TERM `(<=):real->real->bool` eq_th) bnd))
            (rp_cert_chk_le (rand(concl eq_th)) bnd) in
    let kat = rand(concl ka_th) and kqt = rand(concl kq_th) in
    let q0t = tq q0 in
    let qth = (* q0 <= abs(peval q m) - kq * w *)
      let tm = le q0t (mk_binop `(-):real->real->real`
                 (mk_comb(`abs:real->real`, lhs(concl qv_th))) (mk_binop `( * ):real->real->real` kqt wt)) in
      EQT_ELIM((PURE_REWRITE_CONV[qv_th] THENC rp_cert_chk_red) tm) in
    let prodle = MATCH_MP REAL_LT_IMP_LE prod in
    let th = rp_cert_chk_mp (ISPECL [f; a; q; s; lot; hit; mt; wt; kat; kqt; q0t] RP_CERT_CHK_BRK)
               [dthm; prodle; leth ka_th kat; leth kq_th kqt; qth] in
    (* evaluate the slack *)
    let slack = rand(rand(snd(dest_imp(snd(dest_forall(concl th)))))) in
    let sth = rp_cert_chk_red slack in
    PURE_REWRITE_RULE[sth] (CONV_RULE (ONCE_DEPTH_CONV (fun t -> if t = plus mt wt then addeq m w else failwith "")) th) in
  pth, brx, rootfree, gseg, bseg, sign;;

let RP_CERT_CHK_LE_ADD = prove
 (`forall a fm d b. a <= fm + d /\ fm <= b ==> a <= b + d`, REAL_ARITH_TAC);;

(* th : !x. P x ==> f x <= t ;  tb : t <= b  gives  !x. P x ==> f x <= b' with b' evaluated *)
let rp_cert_chk_seg_bound th tb =
  let x, body = dest_forall(concl th) in
  let hyp, cl = dest_imp body in
  let th1 = UNDISCH (SPEC x th) in
  let th2 = MATCH_MP REAL_LE_TRANS (CONJ th1 tb) in
  GEN x (DISCH hyp th2);;

let rp_cert_chk_seg_bound_add th tb =
  (* th : !x. P x ==> f x <= f m + d ; tb : f m <= b *)
  let x, body = dest_forall(concl th) in
  let hyp, cl = dest_imp body in
  let th1 = UNDISCH (SPEC x th) in
  let th2 = MATCH_MP RP_CERT_CHK_LE_ADD (CONJ th1 tb) in
  let th3 = CONV_RULE (RAND_CONV rp_cert_chk_red) th2 in
  GEN x (DISCH hyp th3);;

let rp_cert_chk_weaken_to th bt =
  (* th : !x. P x ==> f x <= c  with c <= bt numerically *)
  let c = rand(snd(dest_imp(snd(dest_forall(concl th))))) in
  rp_cert_chk_seg_bound th (rp_cert_chk_le c bt);;

let rp_cert_chk_run f a q s eqt dthm qthm lo hi lokind pieces vals bnd =
  let pth, brx, rootfree, gseg, bseg, sign =
    rp_cert_chk_interval f a q s eqt dthm qthm lo hi lokind pieces vals bnd in
  let tq = rp_cert_chk_tm in
  let bt = tq bnd in
  let fx t = mk_comb(f, t) in
  let bmap = ref (match lokind with Some(fth,_) -> (lo,fth)::vals | None -> vals) in
  let getb p = try assoc p !bmap with Failure _ ->
    failwith ("rp_cert_chk_run: no bound at " ^ string_of_num p) in
  let ks = map (fun (b,c,m,w,_,_) -> (m,w)) brx in
  let brk_of m = find (fun (_,_,m',_,_,_) -> m' =/ m) brx in
  let n = length ks in
  let gaps = map (fun i ->
      let u = if i = 0 then lo else let (m,w) = el (i-1) ks in m +/ w in
      let v = if i = n then hi else fst(el i ks) in (i, u, v)) (0--n) in
  let segs = ref [] in
  let do_gap0 = ref (fun (_:int*num*num) -> ()) in
  let do_gap (i, u, v) = try !do_gap0 (i,u,v) with Failure e ->
    failwith ("gap " ^ string_of_num u ^ " " ^ string_of_num v ^ ": " ^ e) in
  let _ = do_gap0 := fun (i, u, v) ->
    let inc, gs, g, cont = gseg u v in
    let fu () = getb u and fv () = getb v in
    if i = 0 && lokind = None then
      (if not inc then failwith "decreasing from singular left end" else
       let th = rp_cert_chk_mp (BETA_RULE (ISPECL [f; g; tq u; tq v] RP_CERT_CHK_INC_LO))
                  [gs; cont v] in
       segs := !segs @ [rp_cert_chk_weaken_to (rp_cert_chk_seg_bound th (fv())) bt])
    else if i = n then
      (if inc then failwith "increasing to singular right end" else
       let th = rp_cert_chk_mp (BETA_RULE (ISPECL [f; g; tq u; tq v] RP_CERT_CHK_DEC_HI))
                  [gs; (if i = 0 then (match lokind with Some(_,Some c) -> c | _ -> failwith "cont") else cont u)] in
       segs := !segs @ [rp_cert_chk_weaken_to (rp_cert_chk_seg_bound th (fu())) bt])
    else if inc then
      (let th = if i = 0 then
                  rp_cert_chk_mp (BETA_RULE (ISPECL [f; g; tq u; tq v] RP_CERT_CHK_INC_LO)) [gs; cont v]
                else rp_cert_chk_mp (BETA_RULE (ISPECL [f; g; tq u; tq v] RP_CERT_CHK_INC)) [gs; cont u; cont v] in
       segs := !segs @ [rp_cert_chk_weaken_to (rp_cert_chk_seg_bound th (fv())) bt])
    else
      (let cu = if i = 0 then (match lokind with Some(_,Some c) -> c | _ -> failwith "need continuity at lo")
                else cont u in
       let th = rp_cert_chk_mp (BETA_RULE (ISPECL [f; g; tq u; tq v] RP_CERT_CHK_DEC)) [gs; cu; cont v] in
       let bu = fu () in
       segs := !segs @ [rp_cert_chk_weaken_to (rp_cert_chk_seg_bound th bu) bt];
       (* f v <= f u <= b_u *)
       let fv_le = MP (SPEC (tq v) th) (EQT_ELIM(rp_cert_chk_red
                     (mk_conj(mk_binop `(<=):real->real->bool` (tq u) (tq v),
                              mk_binop `(<=):real->real->bool` (tq v) (tq v))))) in
       bmap := (v, MATCH_MP REAL_LE_TRANS (CONJ fv_le bu)) :: !bmap) in
  let do_brk0 (m, w) =
    let b = brk_of m in
    let th = bseg b in
    let bm = getb m in
    let th2 = rp_cert_chk_seg_bound_add th bm in
    segs := !segs @ [rp_cert_chk_weaken_to th2 bt];
    let mw = m +/ w in
    let fmw = MP (SPEC (tq mw) th2) (EQT_ELIM(rp_cert_chk_red
                 (mk_conj(mk_binop `(<=):real->real->bool` (tq m) (tq mw),
                          mk_binop `(<=):real->real->bool` (tq mw) (tq mw))))) in
    bmap := (mw, fmw) :: !bmap in
  let do_brk (m,w) = try do_brk0 (m,w) with Failure e -> failwith ("brk " ^ string_of_num m ^ ": " ^ e) in
  (* process: gap0, br1, gap1, br2, ..., gapn ; for a DEC gap the bound at its
     left end is needed first, which is available in this order *)
  (* if gap0 is INC we need the bound of the first bracket first: values provide it *)
  List.iter (fun i -> do_gap (el i gaps); if i < n then do_brk (el i ks)) (0--n);
  !segs, getb;;

(* ---- derivative setup ---- *)
let RP_CERT_CHK_DERIV_REWRITE = prove
 (`forall f e e' e'' x. (f has_real_derivative e) (atreal x) /\ e = e' /\ e' = e''
                  ==> (f has_real_derivative e'') (atreal x)`,
  MESON_TAC[]);;

(* xth: theorem with hypotheses-free form  H x ==> (f has_real_derivative E x) (atreal x)
   (x free).  Returns (A, Q, s, ds, |- !x. H x /\ ~(peval Q x = &0) ==> (f has_real_derivative A/(sQ)) (atreal x)) *)
let rp_cert_chk_deriv_setup x xth =
  let h, cl = dest_imp(concl xth) in
  let e = rand(rator cl) in
  let pth = rp_cert_eng_prep_conv x e in
  let rth, al, ql, ds, s = rp_cert_eng_rational_form x (rand(concl pth)) in
  let hq = lhand(concl rth) in
  let d1 = UNDISCH xth and r1 = UNDISCH rth in
  let th = MATCH_MP RP_CERT_CHK_DERIV_REWRITE (CONJ d1 (CONJ pth r1)) in
  let th = DISCH (mk_conj(h, hq)) (PROVE_HYP (CONJUNCT2 (ASSUME (mk_conj(h,hq))))
             (PROVE_HYP (CONJUNCT1 (ASSUME (mk_conj(h,hq)))) th)) in
  rp_cert_eng_hol_list al, rp_cert_eng_hol_list ql, term_of_rat s, ds, GEN x th;;

(* Q = [0;1] * R with R > 0 on (-1,1):  returns (qpos01, qneg) theorems
   qpos: !y. &0 < y /\ y < &1 ==> &0 < &1 * peval Q y
   qneg: !y. --(&1) < y /\ y < &0 ==> &0 < --(&1) * peval Q y *)
let RP_CERT_CHK_QSIGN = prove
 (`forall q r. rp_cert_poly_mul [&0; &1] r = q /\
         (forall y. --(&1) < y /\ y < &1 ==> &0 < rp_cert_peval r y)
         ==> (forall y. &0 < y /\ y < &1 ==> &0 < &1 * rp_cert_peval q y) /\
             (forall y. --(&1) < y /\ y < &0 ==> &0 < --(&1) * rp_cert_peval q y)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[RP_CERT_POLY_EVAL_MUL] THEN
  REWRITE_TAC[CONJUNCT2 rp_cert_peval; CONJUNCT1 rp_cert_peval] THEN
  REWRITE_TAC[REAL_MUL_RZERO; REAL_ADD_RID; REAL_ADD_LID; REAL_MUL_RID; REAL_MUL_LID] THEN
  CONJ_TAC THEN X_GEN_TAC `y:real` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `y:real`) THEN
  (ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC]) THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC;
    ONCE_REWRITE_TAC[REAL_ARITH `--(&1) * ((y:real) * r) = (--y) * r`] THEN
    MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC]);;

let rp_cert_chk_qsign q =
  let ql = rp_cert_eng_of_hol_list q in
  if not (hd ql =/ num_of_string "0") then failwith "qsign: Q(0) <> 0" else
  let r = rp_cert_eng_hol_list (tl ql) in
  let mth = rp_cert_poly_list_conv (mk_binop `rp_cert_poly_mul` `[&0; &1]` r) in
  if rand(concl mth) <> q then failwith "qsign: mismatch" else
  let nr = rp_cert_chk_piece r (rp_cert_chk_num "-1") (num_of_string "1") 0 in
  let s0 = rp_cert_chk_sign r (num_of_string "0") in
  let pos = rp_cert_chk_mp (ISPECL [r; `--(&1)`; `&1`; `&0`] RP_CERT_SUP_POS_FROM_NOROOT) [nr; s0] in
  rp_cert_chk_mp (ISPECL [q; r] RP_CERT_CHK_QSIGN) [mth; pos];;

let RP_CERT_CHK_POS_COMB = prove
 (`forall p (u:real) c v.
     (forall y. u < y /\ y < c ==> &0 < rp_cert_peval p y) /\ &0 < rp_cert_peval p c /\
     (forall y. c < y /\ y < v ==> &0 < rp_cert_peval p y)
     ==> forall y. u < y /\ y < v ==> &0 < rp_cert_peval p y`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `y < c \/ y = c \/ c < y` STRIP_ASSUME_TAC THENL
   [REAL_ARITH_TAC; ASM_MESON_TAC[]; ASM_MESON_TAC[]; ASM_MESON_TAC[]]);;

let RP_CERT_CHK_POS_MUL = prove
 (`forall a b (u:real) v.
     (forall y. u < y /\ y < v ==> &0 < rp_cert_peval a y) /\
     (forall y. u < y /\ y < v ==> &0 < rp_cert_peval b y)
     ==> forall y. u < y /\ y < v ==> &0 < rp_cert_peval (rp_cert_poly_mul a b) y`,
  SIMP_TAC[RP_CERT_POLY_EVAL_MUL; REAL_LT_MUL]);;

let RP_CERT_CHK_POS_ONE = prove
 (`forall (u:real) v. forall y. u < y /\ y < v ==> &0 < rp_cert_peval [&1] y`,
  REWRITE_TAC[rp_cert_peval] THEN REAL_ARITH_TAC);;

(* |- !y. a < y /\ y < b ==> &0 < peval p y  (p explicit, positive there) *)
let rec rp_cert_chk_pos_on p a b =
  let c = (a +/ b) // num_of_string "2" in
  try
    let nr = rp_cert_chk_piece p a b 0 in
    let s0 = rp_cert_chk_sign p c in
    if not (rp_cert_chk_is_pos s0) then failwith "negative" else
    rp_cert_chk_mp (ISPECL [p; rp_cert_chk_tm a; rp_cert_chk_tm b; rp_cert_chk_tm c]
                      RP_CERT_SUP_POS_FROM_NOROOT) [nr; s0]
  with Failure _ ->
    if b -/ a </ rp_cert_chk_num "1/64" then failwith "rp_cert_chk_pos_on" else
    let t1 = rp_cert_chk_pos_on p a c and t2 = rp_cert_chk_pos_on p c b in
    let sc = rp_cert_chk_sign p c in
    rp_cert_chk_mp (ISPECL [p; rp_cert_chk_tm a; rp_cert_chk_tm c; rp_cert_chk_tm b]
                      RP_CERT_CHK_POS_COMB) [t1; sc; t2];;

let rp_cert_chk_qsign2 q ds =
  let ql = rp_cert_eng_of_hol_list q in
  if not (hd ql =/ num_of_string "0") then failwith "qsign: Q(0) <> 0" else
  if not (rp_cert_eng_peq (hd ds) [num_of_string "0"; num_of_string "1"]) then failwith "qsign: x first" else
  let r = rp_cert_eng_hol_list (tl ql) in
  let mth = rp_cert_poly_list_conv (mk_binop `rp_cert_poly_mul` `[&0; &1]` r) in
  if rand(concl mth) <> q then failwith "qsign: mismatch" else
  let m1 = rp_cert_chk_num "-1" and p1 = num_of_string "1" in
  let fs = tl ds in
  (* product term and positivity *)
  let one_th = ISPECL [`--(&1)`; `&1`] RP_CERT_CHK_POS_ONE in
  let pos = itlist (fun d acc ->
      let dt = rp_cert_eng_hol_list d in
      let pd = rp_cert_chk_pos_on dt m1 p1 in
      let th = MATCH_MP RP_CERT_CHK_POS_MUL (CONJ pd acc) in
      CONV_RULE (BINDER_CONV (RAND_CONV (RAND_CONV (RATOR_CONV (RAND_CONV rp_cert_poly_list_conv))))) th)
    fs one_th in
  let rterm = lhand(rand(snd(dest_imp(snd(dest_forall(concl pos)))))) in
  if rterm <> r then failwith "qsign2: product mismatch" else
  rp_cert_chk_mp (ISPECL [q; r] RP_CERT_CHK_QSIGN) [mth; pos];;
