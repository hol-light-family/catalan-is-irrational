(* ========================================================================= *)
(* CERT / CPLX: normalization of closed complex rational expressions.       *)
(* ========================================================================= *)

needs "src/catalan_rp_cert_base.ml";;

let rp_cert_cplx_lt a b = EQT_ELIM(REAL_RAT_LT_CONV(mk_binop `(<):real->real->bool` a b));;
let rp_cert_cplx_le a b = EQT_ELIM(REAL_RAT_LE_CONV(mk_binop `(<=):real->real->bool` a b));;

(* ------------------------------------------------------------------------- *)
(* Complex rational arithmetic: normalize to complex(a,b).                   *)
(* ------------------------------------------------------------------------- *)

let RP_CERT_LOG_CPLX = prove
 (`(forall a. Cx a = complex(a,&0)) /\
   ii = complex(&0,&1) /\
   (forall a b c d. complex(a,b) + complex(c,d) = complex(a + c,b + d)) /\
   (forall a b c d. complex(a,b) - complex(c,d) = complex(a - c,b - d)) /\
   (forall a b. --complex(a,b) = complex(--a,--b)) /\
   (forall a b c d. complex(a,b) * complex(c,d) = complex(a * c - b * d,a * d + b * c)) /\
   (forall a b. cnj(complex(a,b)) = complex(a,--b)) /\
   (forall a b. inv(complex(a,b)) = complex(a / (a pow 2 + b pow 2),--b / (a pow 2 + b pow 2))) /\
   (forall w z. w / z = w * inv z) /\
   (forall z. z pow 0 = complex(&1,&0)) /\
   (forall z n. z pow (SUC n) = z * z pow n) /\
   (forall a b. Re(complex(a,b)) = a) /\
   (forall a b. Im(complex(a,b)) = b)`,
  REWRITE_TAC[CX_DEF; ii; COMPLEX_EQ; RE; IM; RE_ADD; IM_ADD; RE_SUB; IM_SUB; RE_NEG; IM_NEG;
              complex_mul; cnj; complex_inv; complex_div; complex_pow; RE_CX; IM_CX]);;

let rp_cert_log_cplx_conv =
  let [cx;ii_th;add;sub;neg;mul;cnj_th;inv_th;div_th;pow0;powS;re_th;im_th] =
    CONJUNCTS RP_CERT_LOG_CPLX in
  let red = NUM_REDUCE_CONV THENC REAL_RAT_REDUCE_CONV in
  let norm = RAND_CONV (COMB2_CONV (RAND_CONV red) red) in
  let rec cv tm =
    match tm with
      Comb(Const("Cx",_),_) -> (REWR_CONV cx THENC norm) tm
    | Const("ii",_) -> REWR_CONV ii_th tm
    | Comb(Const("complex",_),_) -> norm tm
    | Comb(Comb(Const("vector_add",_),_),_) -> (BINOP_CONV cv THENC REWR_CONV add THENC norm) tm
    | Comb(Comb(Const("vector_sub",_),_),_) -> (BINOP_CONV cv THENC REWR_CONV sub THENC norm) tm
    | Comb(Const("vector_neg",_),_) -> (RAND_CONV cv THENC REWR_CONV neg THENC norm) tm
    | Comb(Comb(Const("complex_mul",_),_),_) -> (BINOP_CONV cv THENC REWR_CONV mul THENC norm) tm
    | Comb(Comb(Const("complex_div",_),_),_) -> (REWR_CONV div_th THENC cv) tm
    | Comb(Const("complex_inv",_),_) -> (RAND_CONV cv THENC REWR_CONV inv_th THENC norm) tm
    | Comb(Const("cnj",_),_) -> (RAND_CONV cv THENC REWR_CONV cnj_th THENC norm) tm
    | Comb(Comb(Const("complex_pow",_),_),n) ->
        let k = dest_small_numeral n in
        if k = 0 then REWR_CONV pow0 tm else
        (RAND_CONV num_CONV THENC REWR_CONV powS THENC
         RAND_CONV (RAND_CONV NUM_REDUCE_CONV THENC cv) THENC LAND_CONV cv THENC
         REWR_CONV mul THENC norm) tm
    | Comb(Const("Re",_),_) -> (RAND_CONV cv THENC REWR_CONV re_th) tm
    | Comb(Const("Im",_),_) -> (RAND_CONV cv THENC REWR_CONV im_th) tm
    | _ -> failwith "rp_cert_log_cplx_conv" in
  cv;;


(* expand sum(m..n) f for numerals m <= n *)
let rec rp_cert_cplx_sum_conv tm =
  let s,f = match strip_comb tm with
     (Const("sum",_),[s;f]) -> s,f | _ -> failwith "rp_cert_cplx_sum_conv" in
  let m,n = match strip_comb s with
     (Const("..",_),[m;n]) -> m,n | _ -> failwith "rp_cert_cplx_sum_conv" in
  let mi = dest_small_numeral m and ni = dest_small_numeral n in
  if mi > ni then REWRITE_CONV[SUM_TRIV_NUMSEG; ARITH_RULE `n < m <=> ~(m <= n)`] tm
  else if mi = ni then (REWR_CONV SUM_SING_NUMSEG THENC BETA_CONV) tm
  else
    let th = MP (ISPECL [f; m; n] SUM_CLAUSES_LEFT)
                (EQT_ELIM(NUM_REDUCE_CONV(mk_binop `(<=):num->num->bool` m n))) in
    (REWR_CONV th THENC
     COMB2_CONV (RAND_CONV BETA_CONV)
       (RATOR_CONV(RAND_CONV(LAND_CONV NUM_REDUCE_CONV)) THENC rp_cert_cplx_sum_conv)) tm;;

