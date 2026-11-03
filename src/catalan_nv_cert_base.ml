(* ========================================================================= *)
(* CAT_NONVANISHING, part C: basic machinery for computing modulo 101.       *)
(* Theorems of the form |- nv_cong 101 x (&n) with 0 <= n < 101 are built    *)
(* compositionally ("cong theorems").                                        *)
(* ========================================================================= *)

needs "Library/pocklington.ml";;
needs "src/catalan_nv_base.ml";;

let NV_CERT_PRIME = prove
 (`prime 101`,
  CONV_TAC PRIME_CONV);;

let NV_CERT_NUM_MOD = prove
 (`forall a b. a MOD 101 = b MOD 101 ==> nv_cong 101 (&a) (&b)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[nv_cong] THEN
  MP_TAC(SPECL [`a:num`; `101`] DIVISION) THEN
  MP_TAC(SPECL [`b:num`; `101`] DIVISION) THEN
  REWRITE_TAC[ARITH_EQ] THEN
  DISCH_THEN(fun th -> ONCE_REWRITE_TAC[CONJUNCT1 th]) THEN
  DISCH_THEN(fun th -> ONCE_REWRITE_TAC[CONJUNCT1 th]) THEN
  ASM_REWRITE_TAC[GSYM REAL_OF_NUM_ADD; GSYM REAL_OF_NUM_MUL] THEN
  SUBGOAL_THEN
   `((&(a DIV 101) * &101 + &(b MOD 101)) - (&(b DIV 101) * &101 + &(b MOD 101))) / &101 =
    &(a DIV 101) - &(b DIV 101)` SUBST1_TAC THENL
   [CONV_TAC REAL_FIELD;
    MATCH_MP_TAC NV_PINT_SUB THEN REWRITE_TAC[NV_CERT_PRIME] THEN
    SIMP_TAC[NV_PINT_NUM; NV_CERT_PRIME]]);;

let NV_CERT_TRANS_MOD = prove
 (`forall x a b. nv_cong 101 x (&a) /\ a MOD 101 = b MOD 101 ==> nv_cong 101 x (&b)`,
  MESON_TAC[NV_CERT_NUM_MOD; NV_CONG_TRANS; NV_CERT_PRIME]);;

let NV_CERT_ADD = prove
 (`forall x y a b c. nv_cong 101 x (&a) ==> nv_cong 101 y (&b) ==>
               (a + b) MOD 101 = c MOD 101 ==> nv_cong 101 (x + y) (&c)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC NV_CERT_TRANS_MOD THEN
  EXISTS_TAC `a + b:num` THEN ASM_REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN
  MATCH_MP_TAC NV_CONG_ADD THEN ASM_REWRITE_TAC[NV_CERT_PRIME]);;

let NV_CERT_SUB = prove
 (`forall x y a b c. nv_cong 101 x (&a) ==> nv_cong 101 y (&b) ==>
               (c + b) MOD 101 = a MOD 101 ==> nv_cong 101 (x - y) (&c)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `nv_cong 101 (&a) (&(c + b))` MP_TAC THENL
   [MATCH_MP_TAC NV_CERT_NUM_MOD THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN DISCH_TAC THEN
  SUBGOAL_THEN `nv_cong 101 (x - y) ((&c + &b) - &b)` MP_TAC THENL
   [MATCH_MP_TAC NV_CONG_SUB THEN REWRITE_TAC[NV_CERT_PRIME] THEN
    ASM_MESON_TAC[NV_CONG_TRANS; NV_CERT_PRIME];
    REWRITE_TAC[REAL_ARITH `(c + b) - b:real = c`]]);;

let NV_CERT_MUL = prove
 (`forall x y a b c. nv_cong 101 x (&a) ==> nv_cong 101 y (&b) ==>
               (a * b) MOD 101 = c MOD 101 ==> nv_cong 101 (x * y) (&c)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC NV_CERT_TRANS_MOD THEN
  EXISTS_TAC `a * b:num` THEN ASM_REWRITE_TAC[GSYM REAL_OF_NUM_MUL] THEN
  MATCH_MP_TAC NV_CONG_MUL THEN ASM_REWRITE_TAC[NV_CERT_PRIME] THEN
  SIMP_TAC[NV_PINT_NUM; NV_CERT_PRIME]);;

let NV_CERT_REFL = prove
 (`forall n. nv_cong 101 (&n) (&n)`,
  SIMP_TAC[NV_CONG_REFL; NV_CERT_PRIME]);;

let NV_CERT_REFL0 = SPEC `0` NV_CERT_REFL;;

let NV_CERT_NEG = prove
 (`forall x a c. nv_cong 101 x (&a) ==> (c + a) MOD 101 = 0 ==> nv_cong 101 (--x) (&c)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`&0`; `x:real`; `0`; `a:num`; `c:num`] NV_CERT_SUB) THEN
  ASM_REWRITE_TAC[REAL_SUB_LZERO; NV_CERT_REFL0] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let NV_CERT_MULADD = prove
 (`forall s x y a b c d. nv_cong 101 s (&a) ==> nv_cong 101 x (&b) ==> nv_cong 101 y (&c) ==>
               (a + b * c) MOD 101 = d MOD 101 ==> nv_cong 101 (s + x * y) (&d)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC NV_CERT_TRANS_MOD THEN
  EXISTS_TAC `a + b * c:num` THEN
  ASM_REWRITE_TAC[GSYM REAL_OF_NUM_ADD; GSYM REAL_OF_NUM_MUL] THEN
  MATCH_MP_TAC NV_CONG_ADD THEN ASM_REWRITE_TAC[NV_CERT_PRIME] THEN
  MATCH_MP_TAC NV_CONG_MUL THEN ASM_REWRITE_TAC[NV_CERT_PRIME] THEN
  SIMP_TAC[NV_PINT_NUM; NV_CERT_PRIME]);;

let NV_CERT_MULSUB = prove
 (`forall s x y a b c d. nv_cong 101 s (&a) ==> nv_cong 101 x (&b) ==> nv_cong 101 y (&c) ==>
               (d + b * c) MOD 101 = a MOD 101 ==> nv_cong 101 (s - x * y) (&d)`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_IMP] NV_CERT_SUB) THEN
  MAP_EVERY EXISTS_TAC [`a:num`; `b * c:num`] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_MUL] THEN
  MATCH_MP_TAC NV_CONG_MUL THEN ASM_REWRITE_TAC[NV_CERT_PRIME] THEN
  SIMP_TAC[NV_PINT_NUM; NV_CERT_PRIME]);;

let NV_CERT_EQ = prove
 (`forall x y a. x = y ==> nv_cong 101 y (&a) ==> nv_cong 101 x (&a)`,
  SIMP_TAC[]);;

let NV_CERT_RAT = prove
 (`forall q c t. (q - &c) / &101 = t ==> nv_pint 101 t ==> nv_cong 101 q (&c)`,
  SIMP_TAC[nv_cong]);;

let NV_CERT_PINT_NUM = prove
 (`forall n. nv_pint 101 (&n)`,
  SIMP_TAC[NV_PINT_NUM; NV_CERT_PRIME]);;

let NV_CERT_PINT_NEGNUM = prove
 (`forall n. nv_pint 101 (--(&n))`,
  SIMP_TAC[NV_PINT_NUM; NV_CERT_PRIME; NV_PINT_NEG]);;

let NV_CERT_PINT_DIV = prove
 (`forall n m. ~(101 divides m) ==> nv_pint 101 (&n / &m)`,
  SIMP_TAC[NV_PINT_DIV_NUM; NV_PINT_NUM; NV_CERT_PRIME]);;

let NV_CERT_PINT_NEGDIV = prove
 (`forall n m. ~(101 divides m) ==> nv_pint 101 (--(&n) / &m)`,
  SIMP_TAC[NV_PINT_DIV_NUM; NV_PINT_NUM; NV_CERT_PRIME; NV_PINT_NEG]);;

(* ------------------------------------------------------------------------- *)
(* OCaml machinery.                                                          *)
(* ------------------------------------------------------------------------- *)

let nv_cert_spec th = let vs,_ = strip_forall(concl th) in SPECL vs th;;

let nv_cert_add_th = nv_cert_spec NV_CERT_ADD
and nv_cert_sub_th = nv_cert_spec NV_CERT_SUB
and nv_cert_mul_th = nv_cert_spec NV_CERT_MUL
and nv_cert_neg_th = nv_cert_spec NV_CERT_NEG
and nv_cert_muladd_th = nv_cert_spec NV_CERT_MULADD
and nv_cert_mulsub_th = nv_cert_spec NV_CERT_MULSUB
and nv_cert_eq_th = nv_cert_spec NV_CERT_EQ
and nv_cert_rat_th = nv_cert_spec NV_CERT_RAT
and nv_cert_refl_th = nv_cert_spec NV_CERT_REFL;;

let nv_cert_vx = `x:real` and nv_cert_vy = `y:real` and nv_cert_vs = `s:real`
and nv_cert_vq = `q:real` and nv_cert_vt = `t:real`
and nv_cert_va = `a:num` and nv_cert_vb = `b:num` and nv_cert_vc = `c:num`
and nv_cert_vd = `d:num` and nv_cert_vn = `n:num` and nv_cert_vm = `m:num`;;

let nv_cert_mk_num n = mk_numeral (Num.num_of_int n);;
let nv_cert_numval tm = Num.int_of_num (dest_numeral tm);;

(* residue of a cong theorem |- nv_cong 101 x (&n) *)
let nv_cert_res th = nv_cert_numval (rand(rand(concl th)));;
let nv_cert_lhs th = rand(rator(concl th));;

let nv_cert_arith tm = EQT_ELIM(NUM_REDUCE_CONV tm);;

let nv_cert_mod n = let r = n mod 101 in if r < 0 then r + 101 else r;;

let nv_cert_add th1 th2 =
  let a = nv_cert_res th1 and b = nv_cert_res th2 in
  let c = nv_cert_mod (a + b) in
  let th = INST [nv_cert_lhs th1,nv_cert_vx; nv_cert_lhs th2,nv_cert_vy;
                 rand(rand(concl th1)),nv_cert_va; rand(rand(concl th2)),nv_cert_vb;
                 nv_cert_mk_num c,nv_cert_vc] nv_cert_add_th in
  let th' = MP (MP th th1) th2 in
  MP th' (nv_cert_arith (lhand(concl th')));;

let nv_cert_sub th1 th2 =
  let a = nv_cert_res th1 and b = nv_cert_res th2 in
  let c = nv_cert_mod (a - b) in
  let th = INST [nv_cert_lhs th1,nv_cert_vx; nv_cert_lhs th2,nv_cert_vy;
                 rand(rand(concl th1)),nv_cert_va; rand(rand(concl th2)),nv_cert_vb;
                 nv_cert_mk_num c,nv_cert_vc] nv_cert_sub_th in
  let th' = MP (MP th th1) th2 in
  MP th' (nv_cert_arith (lhand(concl th')));;

let nv_cert_mul th1 th2 =
  let a = nv_cert_res th1 and b = nv_cert_res th2 in
  let c = nv_cert_mod (a * b) in
  let th = INST [nv_cert_lhs th1,nv_cert_vx; nv_cert_lhs th2,nv_cert_vy;
                 rand(rand(concl th1)),nv_cert_va; rand(rand(concl th2)),nv_cert_vb;
                 nv_cert_mk_num c,nv_cert_vc] nv_cert_mul_th in
  let th' = MP (MP th th1) th2 in
  MP th' (nv_cert_arith (lhand(concl th')));;

let nv_cert_neg th1 =
  let a = nv_cert_res th1 in
  let c = nv_cert_mod (-a) in
  let th = INST [nv_cert_lhs th1,nv_cert_vx; rand(rand(concl th1)),nv_cert_va;
                 nv_cert_mk_num c,nv_cert_vc] nv_cert_neg_th in
  let th' = MP th th1 in
  MP th' (nv_cert_arith (lhand(concl th')));;

(* s + x * y *)
let nv_cert_muladd ths th1 th2 =
  let a = nv_cert_res ths and b = nv_cert_res th1 and c = nv_cert_res th2 in
  let d = nv_cert_mod (a + b * c) in
  let th = INST [nv_cert_lhs ths,nv_cert_vs; nv_cert_lhs th1,nv_cert_vx;
                 nv_cert_lhs th2,nv_cert_vy;
                 rand(rand(concl ths)),nv_cert_va; rand(rand(concl th1)),nv_cert_vb;
                 rand(rand(concl th2)),nv_cert_vc; nv_cert_mk_num d,nv_cert_vd]
                nv_cert_muladd_th in
  let th' = MP (MP (MP th ths) th1) th2 in
  MP th' (nv_cert_arith (lhand(concl th')));;

(* s - x * y *)
let nv_cert_mulsub ths th1 th2 =
  let a = nv_cert_res ths and b = nv_cert_res th1 and c = nv_cert_res th2 in
  let d = nv_cert_mod (a - b * c) in
  let th = INST [nv_cert_lhs ths,nv_cert_vs; nv_cert_lhs th1,nv_cert_vx;
                 nv_cert_lhs th2,nv_cert_vy;
                 rand(rand(concl ths)),nv_cert_va; rand(rand(concl th1)),nv_cert_vb;
                 rand(rand(concl th2)),nv_cert_vc; nv_cert_mk_num d,nv_cert_vd]
                nv_cert_mulsub_th in
  let th' = MP (MP (MP th ths) th1) th2 in
  MP th' (nv_cert_arith (lhand(concl th')));;

(* from |- x = y and cong for y, cong for x *)
let nv_cert_eq eth th =
  let x,y = dest_eq(concl eth) in
  MP (MP (INST [x,nv_cert_vx; y,nv_cert_vy; rand(rand(concl th)),nv_cert_va]
              nv_cert_eq_th) eth) th;;

(* cong theorem for a real literal &n *)
let nv_cert_refl ntm = INST [ntm,nv_cert_vn] nv_cert_refl_th;;

(* residue of a rational (OCaml num) *)
let nv_cert_res_of_rat (q:Num.num) =
  let nn,dd = numdom q in
  let md x = let y = Num.mod_num x (Num.num_of_int 101) in
             Num.int_of_num (if Num.lt_num y (Num.num_of_int 0)
                             then Num.add_num y (Num.num_of_int 101) else y) in
  let a = md nn and b = md dd in
  if b = 0 then failwith "nv_cert_res_of_rat: denominator divisible by 101" else
  let rec inv k = if (b * k) mod 101 = 1 then k else inv (k + 1) in
  (a * inv 1) mod 101;;

let nv_cert_is_div = is_binop `(/):real->real->real`;;
let nv_cert_is_rneg t = is_comb t && rator t = `real_neg`;;

let nv_cert_pint_lit =
  let pnum = SPEC_ALL NV_CERT_PINT_NUM and pnegnum = SPEC_ALL NV_CERT_PINT_NEGNUM
  and pdiv = SPEC_ALL NV_CERT_PINT_DIV and pnegdiv = SPEC_ALL NV_CERT_PINT_NEGDIV in
  let ndiv m = EQF_ELIM(DIVIDES_CONV(mk_comb(mk_comb(`(divides)`,`101`),m))) in
  fun t ->
    if nv_cert_is_div t then
      let u = lhand t and m = rand(rand t) in
      if nv_cert_is_rneg u then
        MP (INST [rand(rand u),nv_cert_vn; m,nv_cert_vm] pnegdiv) (ndiv m)
      else MP (INST [rand u,nv_cert_vn; m,nv_cert_vm] pdiv) (ndiv m)
    else if nv_cert_is_rneg t then INST [rand(rand t),nv_cert_vn] pnegnum
    else INST [rand t,nv_cert_vn] pnum;;

(* cong theorem for a real rational literal *)
let nv_cert_ratlit q =
  let c = nv_cert_res_of_rat (rat_of_term q) in
  let ctm = nv_cert_mk_num c in
  let ttm = mk_comb(mk_comb(`(/):real->real->real`,
                    mk_comb(mk_comb(`(-):real->real->real`,q),mk_comb(`(&):num->real`,ctm))),
                    `&101`) in
  let eth = REAL_RAT_REDUCE_CONV ttm in
  let t = rand(concl eth) in
  let th = INST [q,nv_cert_vq; ctm,nv_cert_vc; t,nv_cert_vt] nv_cert_rat_th in
  MP (MP th eth) (nv_cert_pint_lit t);;

(* cong theorem for a closed real expression that REAL_RAT_REDUCE_CONV evaluates *)
let nv_cert_rat tm =
  let eth = REAL_RAT_REDUCE_CONV tm in
  let q = rand(concl eth) in
  if q = tm then nv_cert_ratlit q else nv_cert_eq eth (nv_cert_ratlit q);;
