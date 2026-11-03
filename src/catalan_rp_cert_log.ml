(* ========================================================================= *)
(* CERT / LOG: rigorous rational bounds for log, atn, pi and Re(c clog w).  *)
(* ========================================================================= *)

needs "src/catalan_rp_cert_base.ml";;
needs "src/catalan_rp_cert_cplx.ml";;

let RP_CERT_LOG_TAYLOR = prove
 (`forall n h. abs h < &1
         ==> abs(log(&1 + h) - sum(1..n) (\k. --(&1) pow (k + 1) * h pow k / &k))
             <= abs h pow (n + 1) / (&1 - abs h)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`n:num`; `Cx h`] TAYLOR_CLOG) THEN
  ASM_REWRITE_TAC[COMPLEX_NORM_CX] THEN
  SUBGOAL_THEN `clog(Cx(&1) + Cx h) = Cx(log(&1 + h))` SUBST1_TAC THENL
   [REWRITE_TAC[GSYM CX_ADD] THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC CX_LOG THEN
    ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[GSYM CX_NEG; GSYM CX_POW; GSYM CX_MUL; GSYM CX_DIV; VSUM_CX_NUMSEG;
              GSYM CX_SUB; COMPLEX_NORM_CX]);;




let RP_CERT_LOG_GEOM = rp_cert_steps
 `forall m t. sum(0..m) (\k. --(&1) pow k * t pow (2 * k)) * (&1 + t pow 2) =
         &1 - --(&1) pow (m + 1) * t pow (2 * (m + 1))`
 [(INDUCT_TAC THEN REWRITE_TAC[SUM_CLAUSES_NUMSEG; LE_0] THEN
  CONV_TAC NUM_REDUCE_CONV);
  (CONV_TAC REAL_RAT_REDUCE_CONV THEN GEN_TAC THEN CONV_TAC REAL_RING);
  (GEN_TAC THEN REWRITE_TAC[REAL_ADD_RDISTRIB] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[ADD1; ARITH_RULE `2 * ((m + 1) + 1) = 2 * (m + 1) + 2`; REAL_POW_ADD]);
  (CONV_TAC REAL_RING)];;




let RP_CERT_LOG_ATN_DERIV = rp_cert_steps
 `forall m t. ((\t. atn t - sum(0..m) (\k. --(&1) pow k * t pow (2 * k + 1) / &(2 * k + 1)))
          has_real_derivative
          (--(&1) pow (m + 1) * t pow (2 * (m + 1)) / (&1 + t pow 2))) (atreal t)`
 [(REPEAT GEN_TAC THEN
  SUBGOAL_THEN `--(&1) pow (m + 1) * t pow (2 * (m + 1)) / (&1 + t pow 2) =
                inv(&1 + t pow 2) -
                sum(0..m) (\k. --(&1) pow k / &(2 * k + 1) *
                               (&(2 * k + 1) * t pow ((2 * k + 1) - 1) * &1))`
    SUBST1_TAC);
  (SUBGOAL_THEN `sum(0..m) (\k. --(&1) pow k / &(2 * k + 1) *
                               (&(2 * k + 1) * t pow ((2 * k + 1) - 1) * &1)) =
                  sum(0..m) (\k. --(&1) pow k * t pow (2 * k))` SUBST1_TAC THENL
     [MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `k:num` THEN STRIP_TAC THEN
      REWRITE_TAC[ADD_SUB] THEN
      SUBGOAL_THEN `~(&(2 * k + 1) = &0)` MP_TAC THENL
       [REWRITE_TAC[REAL_OF_NUM_EQ] THEN ARITH_TAC; CONV_TAC REAL_FIELD];
      ALL_TAC] THEN
    MP_TAC(SPECL [`m:num`; `t:real`] RP_CERT_LOG_GEOM) THEN
    SUBGOAL_THEN `&0 < &1 + t pow 2` MP_TAC THENL
     [MP_TAC(SPEC `t:real` REAL_LE_POW_2) THEN REAL_ARITH_TAC; ALL_TAC] THEN
    CONV_TAC REAL_FIELD);
  (MATCH_MP_TAC HAS_REAL_DERIVATIVE_SUB);
  (REWRITE_TAC[HAS_REAL_DERIVATIVE_ATN] THEN
  MATCH_MP_TAC HAS_REAL_DERIVATIVE_SUM THEN REWRITE_TAC[FINITE_NUMSEG] THEN
  X_GEN_TAC `k:num` THEN DISCH_TAC THEN REWRITE_TAC[]);
  (SUBGOAL_THEN `(\t. --(&1) pow k * t pow (2 * k + 1) / &(2 * k + 1)) =
                (\t. (--(&1) pow k / &(2 * k + 1)) * t pow (2 * k + 1))` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; real_div] THEN REAL_ARITH_TAC; ALL_TAC]);
  (MATCH_MP_TAC HAS_REAL_DERIVATIVE_LMUL_ATREAL);
  (MP_TAC(SPECL [`\t:real. t`; `&1`; `t:real`; `2 * k + 1`] HAS_REAL_DERIVATIVE_POW_ATREAL) THEN
  REWRITE_TAC[HAS_REAL_DERIVATIVE_ID])];;




let RP_CERT_LOG_ATN_TAYLOR = rp_cert_steps
 `forall m t. abs(atn t - sum(0..m) (\k. --(&1) pow k * t pow (2 * k + 1) / &(2 * k + 1)))
         <= abs t pow (2 * (m + 1) + 1)`
 [(REPEAT GEN_TAC THEN
  ABBREV_TAC `f = \t. atn t - sum(0..m) (\k. --(&1) pow k * t pow (2 * k + 1) / &(2 * k + 1))` THEN
  SUBGOAL_THEN `atn t - sum(0..m) (\k. --(&1) pow k * t pow (2 * k + 1) / &(2 * k + 1)) =
                f t - f (&0)` SUBST1_TAC THENL
   [EXPAND_TAC "f" THEN REWRITE_TAC[ATN_0] THEN
    REWRITE_TAC[REAL_POW_ZERO; ADD_EQ_0; ARITH_EQ; REAL_MUL_RZERO; real_div; REAL_MUL_LZERO;
                SUM_0; REAL_SUB_REFL; REAL_SUB_RZERO];
    ALL_TAC]);
  (SUBGOAL_THEN `forall s. (f has_real_derivative
                    (--(&1) pow (m + 1) * s pow (2 * (m + 1)) / (&1 + s pow 2))) (atreal s)`
    ASSUME_TAC THENL
   [EXPAND_TAC "f" THEN REWRITE_TAC[RP_CERT_LOG_ATN_DERIV]; ALL_TAC]);
  (SUBGOAL_THEN `forall s. abs(--(&1) pow (m + 1) * s pow (2 * (m + 1)) / (&1 + s pow 2)) <=
                    abs s pow (2 * (m + 1))` ASSUME_TAC);
  (GEN_TAC THEN REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_DIV; REAL_ABS_POW; REAL_ABS_NEG; REAL_ABS_1;
                             REAL_POW_ONE; REAL_MUL_LID]);
  (SUBGOAL_THEN `&1 <= abs(&1 + s pow 2)` ASSUME_TAC THENL
     [MP_TAC(SPEC `s:real` REAL_LE_POW_2) THEN REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_ARITH `&1 <= x ==> &0 < x`]);
  (GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_POW_LE; REAL_ABS_POS]);
  (SUBGOAL_THEN `exists x. abs x <= abs t /\ f t - f (&0) = (--(&1) pow (m + 1) * x pow (2 * (m + 1)) / (&1 + x pow 2)) * (t - &0)`
    STRIP_ASSUME_TAC);
  (SUBGOAL_THEN `&0 <= t \/ t <= &0` DISJ_CASES_TAC THENL [REAL_ARITH_TAC; ALL_TAC; ALL_TAC]);
  (MP_TAC(SPECL [`f:real->real`; `\s. --(&1) pow (m + 1) * s pow (2 * (m + 1)) / (&1 + s pow 2)`;
                    `&0`; `t:real`] REAL_MVT_VERY_SIMPLE) THEN
      ASM_SIMP_TAC[HAS_REAL_DERIVATIVE_ATREAL_WITHIN]);
  (REWRITE_TAC[IN_REAL_INTERVAL] THEN MATCH_MP_TAC MONO_EXISTS THEN
      GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);
  (MP_TAC(SPECL [`f:real->real`; `\s. --(&1) pow (m + 1) * s pow (2 * (m + 1)) / (&1 + s pow 2)`;
                    `t:real`; `&0`] REAL_MVT_VERY_SIMPLE) THEN
      ASM_SIMP_TAC[HAS_REAL_DERIVATIVE_ATREAL_WITHIN] THEN
  REWRITE_TAC[IN_REAL_INTERVAL] THEN MATCH_MP_TAC MONO_EXISTS THEN
      GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      POP_ASSUM MP_TAC THEN REAL_ARITH_TAC);
  (ASM_REWRITE_TAC[REAL_SUB_RZERO] THEN ONCE_REWRITE_TAC[REAL_ABS_MUL] THEN
  REWRITE_TAC[ARITH_RULE `2 * (m + 1) + 1 = SUC(2 * (m + 1))`; real_pow] THEN
  GEN_REWRITE_TAC LAND_CONV [REAL_MUL_SYM] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
  REWRITE_TAC[REAL_ABS_POS] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `abs x pow (2 * (m + 1))` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REWRITE_TAC[REAL_ABS_POS])];;



let RP_CERT_LOG_IM_CLOG_ATN = rp_cert_steps
 `forall w. &0 < Re w ==> Im(clog w) = atn(Im w / Re w)`
 [(REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `clog w = complex(log(norm w), atn(Im w / Re w))` SUBST1_TAC THENL
   [ALL_TAC; REWRITE_TAC[IM]] THEN
  MATCH_MP_TAC CLOG_UNIQUE THEN REWRITE_TAC[IM] THEN
  MP_TAC(SPEC `Im w / Re w` ATN_BOUNDS) THEN MP_TAC PI_POS THEN
  DISCH_TAC THEN DISCH_TAC THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC]);
  (SUBGOAL_THEN `&0 < norm(w:complex)` ASSUME_TAC THENL
   [MP_TAC(SPEC `w:complex` COMPLEX_NORM_GE_RE_IM) THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[CEXP_COMPLEX; EXP_LOG; COS_ATN; SIN_ATN] THEN
  SUBGOAL_THEN `norm(w:complex) = Re w * sqrt(&1 + (Im w / Re w) pow 2)` SUBST1_TAC THENL
   [REWRITE_TAC[complex_norm] THEN
    SUBGOAL_THEN `Re w pow 2 + Im w pow 2 = Re w pow 2 * (&1 + (Im w / Re w) pow 2)` SUBST1_TAC THENL
     [UNDISCH_TAC `&0 < Re w` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
    ASM_SIMP_TAC[SQRT_MUL; POW_2_SQRT; REAL_LT_IMP_LE]; ALL_TAC]);
  (REWRITE_TAC[COMPLEX_EQ; RE_MUL_CX; IM_MUL_CX; RE; IM] THEN
  SUBGOAL_THEN `&0 < sqrt(&1 + (Im w / Re w) pow 2)` MP_TAC THENL
   [MATCH_MP_TAC SQRT_POS_LT THEN MP_TAC(SPEC `Im w / Re w` REAL_LE_POW_2) THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  UNDISCH_TAC `&0 < Re w` THEN CONV_TAC REAL_FIELD)];;



let RP_CERT_LOG_RE_CLOG = prove
 (`forall w. ~(w = Cx(&0)) ==> Re(clog w) = log(Re w pow 2 + Im w pow 2) / &2`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[RE_CLOG; complex_norm] THEN
  MATCH_MP_TAC LOG_SQRT THEN
  REWRITE_TAC[REAL_LT_LE] THEN CONJ_TAC THENL
   [MP_TAC(SPEC `Re w` REAL_LE_POW_2) THEN MP_TAC(SPEC `Im w` REAL_LE_POW_2) THEN
    REAL_ARITH_TAC;
    ONCE_REWRITE_TAC[EQ_SYM_EQ] THEN
    REWRITE_TAC[GSYM COMPLEX_SQNORM; REAL_POW_EQ_0; COMPLEX_NORM_ZERO; ARITH_EQ; COMPLEX_VEC_0] THEN
    ASM_REWRITE_TAC[]]);;

let RP_CERT_LOG_RECLOG = rp_cert_steps
 `forall c w. (&0 < Re w
          ==> Re(c * clog w) =
              Re c * (log(Re w pow 2 + Im w pow 2) / &2) - Im c * atn(Im w / Re w)) /\
         (Re w < &0 /\ &0 <= Im w
          ==> Re(c * clog w) =
              Re c * (log(Re w pow 2 + Im w pow 2) / &2) - Im c * (atn(Im w / Re w) + pi)) /\
         (Re w < &0 /\ Im w < &0
          ==> Re(c * clog w) =
              Re c * (log(Re w pow 2 + Im w pow 2) / &2) - Im c * (atn(Im w / Re w) - pi))`
 [(REPEAT GEN_TAC THEN REWRITE_TAC[complex_mul; RE] THEN
  SUBGOAL_THEN `forall w. ~(Re w = &0) ==> ~(w = Cx(&0))` ASSUME_TAC THENL
   [GEN_TAC THEN ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN SIMP_TAC[RE_CX]; ALL_TAC] THEN
  REPEAT CONJ_TAC THEN STRIP_TAC THEN
  (SUBGOAL_THEN `~(w = Cx(&0))` ASSUME_TAC THENL
    [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC]) THEN
  ASM_SIMP_TAC[RP_CERT_LOG_RE_CLOG; RP_CERT_LOG_IM_CLOG_ATN]);
  (AP_TERM_TAC THEN AP_TERM_TAC THEN
  MP_TAC(SPEC `--w:complex` CLOG_NEG));
  (REWRITE_TAC[COMPLEX_NEG_NEG; COMPLEX_NEG_EQ_0; RE_NEG; IM_NEG] THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[REAL_ARITH `x < &0 ==> ~(--x < &0)`; REAL_ARITH `&0 <= x ==> --x <= &0`] THEN
  DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[IM_ADD; IM_SUB; IM_MUL_II; RE_CX] THEN
  MP_TAC(SPEC `--w:complex` RP_CERT_LOG_IM_CLOG_ATN) THEN
  ASM_REWRITE_TAC[RE_NEG; IM_NEG] THEN
  (ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC]) THEN
  REWRITE_TAC[real_div; REAL_INV_NEG; REAL_MUL_LNEG; REAL_MUL_RNEG; REAL_NEG_NEG]);
  (AP_TERM_TAC THEN AP_TERM_TAC THEN
  MP_TAC(SPEC `--w:complex` CLOG_NEG) THEN
  REWRITE_TAC[COMPLEX_NEG_NEG; COMPLEX_NEG_EQ_0; RE_NEG; IM_NEG] THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[REAL_ARITH `x < &0 ==> ~(--x < &0)`; REAL_ARITH `x < &0 ==> ~(--x <= &0)`] THEN
  DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[IM_ADD; IM_SUB; IM_MUL_II; RE_CX] THEN
  MP_TAC(SPEC `--w:complex` RP_CERT_LOG_IM_CLOG_ATN) THEN
  ASM_REWRITE_TAC[RE_NEG; IM_NEG] THEN
  (ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC]) THEN
  REWRITE_TAC[real_div; REAL_INV_NEG; REAL_MUL_LNEG; REAL_MUL_RNEG; REAL_NEG_NEG])];;

(* ------------------------------------------------------------------------- *)
(* Generic bound-combination lemmas.                                         *)
(* ------------------------------------------------------------------------- *)

let RP_CERT_LOG_ABS_BOUNDS = prove
 (`forall x p r. abs(x - p) <= r ==> p - r <= x /\ x <= p + r`, REAL_ARITH_TAC);;

let RP_CERT_LOG_B_ADD = prove
 (`forall a b la ha lb hb. la <= a /\ a <= ha /\ lb <= b /\ b <= hb
     ==> la + lb <= a + b /\ a + b <= ha + hb`, REAL_ARITH_TAC);;

let RP_CERT_LOG_B_SUB = prove
 (`forall a b la ha lb hb. la <= a /\ a <= ha /\ lb <= b /\ b <= hb
     ==> la - hb <= a - b /\ a - b <= ha - lb`, REAL_ARITH_TAC);;

let RP_CERT_LOG_B_NEG = prove
 (`forall a la ha. la <= a /\ a <= ha ==> --ha <= --a /\ --a <= --la`, REAL_ARITH_TAC);;

let RP_CERT_LOG_B_CMUL_POS = prove
 (`forall c a la ha. &0 <= c /\ la <= a /\ a <= ha ==> c * la <= c * a /\ c * a <= c * ha`,
  MESON_TAC[REAL_LE_LMUL]);;

let RP_CERT_LOG_B_CMUL_NEG = prove
 (`forall c a la ha. c <= &0 /\ la <= a /\ a <= ha ==> c * ha <= c * a /\ c * a <= c * la`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[REAL_ARITH `x <= y <=> --y <= --x:real`] THEN
  REWRITE_TAC[GSYM REAL_MUL_LNEG] THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC);;

let RP_CERT_LOG_B_WIDEN = prove
 (`forall a la ha la' ha'. la <= a /\ a <= ha /\ la' <= la /\ ha <= ha' ==> la' <= a /\ a <= ha'`,
  REAL_ARITH_TAC);;

let RP_CERT_LOG_B_EQ = prove
 (`forall a b la ha. a = b /\ la <= b /\ b <= ha ==> la <= a /\ a <= ha`, MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* OCaml utilities.                                                          *)
(* ------------------------------------------------------------------------- *)

let rp_cert_log_int n =
  if n < 0 then minus_num (num_of_string (string_of_int (-n)))
  else num_of_string (string_of_int n);;

let rp_cert_log_toint n = int_of_string (string_of_num n);;

let rp_cert_log_rat tm = rat_of_term (rand(concl(REAL_RAT_REDUCE_CONV tm)));;

let rp_cert_log_eval tm = REAL_RAT_REDUCE_CONV tm;;

(* lo <= x /\ x <= hi  -> (lo, hi) as rationals *)
let rp_cert_log_dest_bounds th =
  let l,r = dest_conj(concl th) in
  rat_of_term(lhand l), rat_of_term(rand r);;

let rp_cert_log_le a b = EQT_ELIM(REAL_RAT_LE_CONV(mk_binop `(<=):real->real->bool` a b));;

(* evaluate both bounds to canonical rationals and round outward to multiples
   of 1/10^digits *)
let rp_cert_log_digits = ref 22;;

let rp_cert_log_normalize th =
  let cv = NUM_REDUCE_CONV THENC REAL_RAT_REDUCE_CONV in
  let th1 = CONV_RULE (COMB2_CONV (RAND_CONV (LAND_CONV cv)) (RAND_CONV cv)) th in
  let l,r = dest_conj(concl th1) in
  let lo = rat_of_term(lhand l) and hi = rat_of_term(rand r) in
  let sc = power_num (num_of_string "10") (num_of_string (string_of_int !rp_cert_log_digits)) in
  let lo' = floor_num (lo */ sc) // sc and hi' = ceiling_num (hi */ sc) // sc in
  if lo' =/ lo && hi' =/ hi then th1 else
  let x = rand l in
  let tlo = term_of_rat lo' and thi = term_of_rat hi' in
  MATCH_MP (ISPECL [x; lhand l; rand r; tlo; thi] RP_CERT_LOG_B_WIDEN)
    (CONJ (CONJUNCT1 th1) (CONJ (CONJUNCT2 th1)
       (CONJ (rp_cert_log_le tlo (lhand l)) (rp_cert_log_le (rand r) thi))));;

let rp_cert_log_sum_conv = rp_cert_cplx_sum_conv;;

(* |- lo <= log(&1 + h) /\ log(&1 + h) <= hi, h a rational numeral, |h| < 1 *)
let rp_cert_log_log1p h n =
  let th0 = ISPECL [mk_small_numeral n; h] RP_CERT_LOG_TAYLOR in
  let hyp_th = EQT_ELIM(REAL_RAT_REDUCE_CONV(lhand(concl th0))) in
  let th1 = MATCH_MP RP_CERT_LOG_ABS_BOUNDS (MP th0 hyp_th) in
  let th2 = CONV_RULE (ONCE_DEPTH_CONV rp_cert_log_sum_conv) th1 in
  rp_cert_log_normalize th2;;

(* ------------------------------------------------------------------------- *)
(* log tables.                                                               *)
(* ------------------------------------------------------------------------- *)

let RP_CERT_LOG_ATANH = prove
 (`forall q. abs q < &1 ==> log((&1 + q) / (&1 - q)) = log(&1 + q) - log(&1 + --q)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM real_sub] THEN MATCH_MP_TAC LOG_DIV THEN
  ASM_REAL_ARITH_TAC);;

(* number of Taylor terms n with |q|^(n+1)/(1-|q|) <= 10^-17 *)
let rp_cert_log_nterms q =
  let eps = num_of_string "1" // power_num (num_of_string "10") (num_of_string "17") in
  let rec go n p = if p // (num_of_string "1" -/ q) <=/ eps then n else go (n + 1) (p */ q) in
  go 1 (q */ q);;

(* |- lo <= log c /\ log c <= hi for a rational c in [1, 2] via atanh *)
let rp_cert_log_table_entry c =
  let cr = rp_cert_log_rat c in
  let q = (cr -/ num_of_string "1") // (cr +/ num_of_string "1") in
  let qt = term_of_rat q and mqt = term_of_rat (minus_num q) in
  let nt = rp_cert_log_nterms (abs_num q) in
  let th1 = rp_cert_log_log1p qt nt and th2 = rp_cert_log_log1p mqt nt in
  let ath = MP (ISPEC qt RP_CERT_LOG_ATANH) (EQT_ELIM(REAL_RAT_REDUCE_CONV
              (mk_comb(mk_comb(`(<):real->real->bool`, mk_comb(`abs:real->real`, qt)), `&1`)))) in
  let ath2 = CONV_RULE (LAND_CONV(RAND_CONV REAL_RAT_REDUCE_CONV) THENC
                        RAND_CONV(RAND_CONV(RAND_CONV(RAND_CONV REAL_RAT_REDUCE_CONV)))) ath in
  (* ath2: log c = log(1 + q) - log(1 + -q)   with -q reduced *)
  let th2r = CONV_RULE (BINOP_CONV (ONCE_DEPTH_CONV (fun t ->
      if is_comb t && rator t = `log` then RAND_CONV(RAND_CONV REAL_RAT_REDUCE_CONV) t
      else failwith ""))) th2 in
  let sth = MATCH_MP RP_CERT_LOG_B_SUB (CONJ (CONJUNCT1 th1) (CONJ (CONJUNCT2 th1)
                (CONJ (CONJUNCT1 th2r) (CONJUNCT2 th2r)))) in
  let eth = MATCH_MP RP_CERT_LOG_B_EQ (CONJ ath2 sth) in
  let eth' = CONV_RULE (BINOP_CONV (RAND_CONV (TRY_CONV (RAND_CONV REAL_RAT_REDUCE_CONV)) ORELSEC
                                    LAND_CONV (TRY_CONV (RAND_CONV REAL_RAT_REDUCE_CONV)))) eth in
  rp_cert_log_normalize eth';;

let RP_CERT_LOG_TWO = rp_cert_log_table_entry `&2`;;

let rp_cert_log_tab1 = Array.init 17 (fun j ->
  if j = 0 then TRUTH else rp_cert_log_table_entry (term_of_rat (num_of_string "1" +/ (num_of_string (string_of_int j) // num_of_string "16"))));;

let rp_cert_log_tab2 = Array.init 33 (fun i ->
  let h = rp_cert_log_int (i - 16) // num_of_string "512" in
  if i = 16 then TRUTH else rp_cert_log_log1p (term_of_rat h) (rp_cert_log_nterms (abs_num h)));;

let RP_CERT_LOG_SANDWICH = prove
 (`forall s a b. &0 < a /\ a <= s /\ s <= b ==> log a <= log s /\ log s <= log b`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC LOG_MONO_LE_IMP THEN ASM_REAL_ARITH_TAC);;

let RP_CERT_LOG_MUL4 = prove
 (`forall a b c d. &0 < a /\ &0 < b /\ &0 < c /\ &0 < d
     ==> log(a * b * c * d) = log a + log b + log c + log d`,
  SIMP_TAC[LOG_MUL; REAL_LT_MUL]);;

let RP_CERT_LOG_POW2 = prove
 (`forall n. log(&2 pow n) = &n * log(&2) /\ log(inv(&2 pow n)) = --(&n * log(&2))`,
  SIMP_TAC[LOG_POW; LOG_INV; REAL_POW_LT; REAL_ARITH `&0 < &2`]);;

let RP_CERT_LOG_ZERO = prove
 (`log(&1) = &0 /\ log(&1 + &0) = &0`, REWRITE_TAC[LOG_1; REAL_ADD_RID]);;

(* bounds for log(P) where P = 2^e (e >= 0) or inv(2^e) *)
let rp_cert_log_pow2_bounds e =
  let en = abs e in
  let lo2,hi2 = rp_cert_log_dest_bounds RP_CERT_LOG_TWO in
  let ent = mk_small_numeral en in
  let ef = mk_comb(`real_of_num`, ent) in
  let pos = EQT_ELIM(REAL_RAT_LE_CONV(mk_binop `(<=):real->real->bool` `&0` ef)) in
  let th = MATCH_MP RP_CERT_LOG_B_CMUL_POS (CONJ pos RP_CERT_LOG_TWO) in
  let [p1;p2] = CONJUNCTS (SPEC ent RP_CERT_LOG_POW2) in
  if e >= 0 then
    let pp = mk_binop `(pow):real->num->real` `&2` ent in
    pp, MATCH_MP RP_CERT_LOG_B_EQ (CONJ p1 th)
  else
    let pp = mk_comb(`inv:real->real`, mk_binop `(pow):real->num->real` `&2` ent) in
    pp, MATCH_MP RP_CERT_LOG_B_EQ (CONJ p2 (MATCH_MP RP_CERT_LOG_B_NEG th));;

(* factor bounds: |- lo <= log(f) /\ log(f) <= hi with f syntactically as given *)
let RP_CERT_LOG_C1_ZERO = prove
 (`&0 <= log(&1) /\ log(&1) <= &0`, REWRITE_TAC[LOG_1; REAL_LE_REFL]);;

let RP_CERT_LOG_C2_ZERO = prove
 (`&0 <= log(&1 + &0) /\ log(&1 + &0) <= &0`, REWRITE_TAC[REAL_ADD_RID; LOG_1; REAL_LE_REFL]);;

let rp_cert_log_c1 j =
  if j = 0 then `&1`, RP_CERT_LOG_C1_ZERO
  else let th = rp_cert_log_tab1.(j) in rand(rand(lhand(concl th))), th;;

let rp_cert_log_c2 i =
  if i = 16 then `&1 + &0`, RP_CERT_LOG_C2_ZERO
  else let th = rp_cert_log_tab2.(i) in rand(rand(lhand(concl th))), th;;

let rp_cert_log_lt a b = EQT_ELIM(REAL_RAT_LT_CONV(mk_binop `(<):real->real->bool` a b));;

(* |- lo <= log(f1 * f2 * f3 * f4) /\ ... from factor bound theorems *)
let rp_cert_log_prod4 ths =
  let fs = map (fun th -> rand(rand(lhand(concl th)))) ths in
  let [f1;f2;f3;f4] = fs in
  let poss = map (fun f -> rp_cert_log_lt `&0` (rand(concl(REAL_RAT_REDUCE_CONV f)))
                           |> fun th -> EQ_MP (SYM(AP_TERM `(<) (&0)` (REAL_RAT_REDUCE_CONV f))) th) fs in
  let eq = MP (ISPECL [f1;f2;f3;f4] RP_CERT_LOG_MUL4) (end_itlist CONJ poss) in
  let [t1;t2;t3;t4] = ths in
  let add a b = MATCH_MP RP_CERT_LOG_B_ADD (CONJ (CONJUNCT1 a) (CONJ (CONJUNCT2 a)
                   (CONJ (CONJUNCT1 b) (CONJUNCT2 b)))) in
  let sth = add t1 (add t2 (add t3 t4)) in
  rp_cert_log_normalize (MATCH_MP RP_CERT_LOG_B_EQ (CONJ eq sth));;

(* main entry: |- lo <= log r /\ log r <= hi *)
let rp_cert_log_bounds r =
  let eqr = REAL_RAT_REDUCE_CONV r in
  let rv = rand(concl eqr) in
  let s = rat_of_term rv in
  if s <=/ num_of_string "0" then failwith "rp_cert_log_bounds: nonpositive" else
  let one = num_of_string "1" and two = num_of_string "2" in
  (* exponent e with 1 <= s / 2^e < 2 *)
  let rec findexp e y = if y >=/ two then findexp (e + 1) (y // two)
                        else if y </ one then findexp (e - 1) (y */ two) else e, y in
  let e, y = findexp 0 s in
  let j = rp_cert_log_toint (round_num ((y -/ one) */ num_of_string "16")) in
  let j = if j >= 16 then 16 else j in
  let (c1t, c1th), e = if j = 16 then (`&1`, snd(rp_cert_log_c1 0)), e + 1 else rp_cert_log_c1 j, e in
  let c1 = if j = 16 then one else one +/ (num_of_string (string_of_int j) // num_of_string "16") in
  let y1 = s // (power_num two (rp_cert_log_int e)) // c1 in
  let y1 = if e >= 0 then y1 else s */ power_num two (rp_cert_log_int (-e)) // c1 in
  let i = rp_cert_log_toint (round_num ((y1 -/ one) */ num_of_string "512")) + 16 in
  let i = max 0 (min 32 i) in
  let c2t, c2th = rp_cert_log_c2 i in
  let c2 = one +/ (rp_cert_log_int (i - 16) // num_of_string "512") in
  let y2 = y1 // c2 in
  let sc = power_num (num_of_string "2") (num_of_string "50") in
  let hl = floor_num ((y2 -/ one) */ sc) // sc and hh = ceiling_num ((y2 -/ one) */ sc) // sc in
  let _, pth = rp_cert_log_pow2_bounds e in
  let mk h = let ht = term_of_rat h in
             let th = rp_cert_log_log1p ht (rp_cert_log_nterms (abs_num h)) in
             rp_cert_log_prod4 [c1th; c2th; th; pth] in
  let thl = mk hl and thh = mk hh in
  let a = rand(rand(lhand(concl thl))) in
  let b = rand(rand(lhand(concl thh))) in
  let apos = EQ_MP (SYM(AP_TERM `(<) (&0)` (REAL_RAT_REDUCE_CONV a)))
                   (rp_cert_log_lt `&0` (rand(concl(REAL_RAT_REDUCE_CONV a)))) in
  let le1 = EQT_ELIM((RAND_CONV (K eqr) THENC LAND_CONV REAL_RAT_REDUCE_CONV THENC REAL_RAT_LE_CONV)
                     (mk_binop `(<=):real->real->bool` a r)) in
  let le2 = EQT_ELIM((LAND_CONV (K eqr) THENC RAND_CONV REAL_RAT_REDUCE_CONV THENC REAL_RAT_LE_CONV)
                     (mk_binop `(<=):real->real->bool` r b)) in
  let sw = MP (ISPECL [r; a; b] RP_CERT_LOG_SANDWICH) (CONJ apos (CONJ le1 le2)) in
  let lo = CONJUNCT1 thl and hi = CONJUNCT2 thh in
  CONJ (MATCH_MP REAL_LE_TRANS (CONJ lo (CONJUNCT1 sw)))
       (MATCH_MP REAL_LE_TRANS (CONJ (CONJUNCT2 sw) hi));;

(* ------------------------------------------------------------------------- *)
(* atn bounds.                                                               *)
(* ------------------------------------------------------------------------- *)

let rp_cert_log_atn_taylor t =
  let tr = rat_of_term t in
  let eps = num_of_string "1" // power_num (num_of_string "10") (num_of_string "15") in
  let a = abs_num tr in
  let rec go m p = if p <=/ eps then m else go (m + 1) (p */ a */ a) in
  let m = if a =/ num_of_string "0" then 0 else go 0 (a */ a */ a) in
  let th0 = ISPECL [mk_small_numeral m; t] RP_CERT_LOG_ATN_TAYLOR in
  let th1 = MATCH_MP RP_CERT_LOG_ABS_BOUNDS th0 in
  let th2 = CONV_RULE (ONCE_DEPTH_CONV rp_cert_log_sum_conv) th1 in
  rp_cert_log_normalize th2;;

let RP_CERT_LOG_ATN_ADD = prove
 (`forall x y. abs x <= &1 /\ abs y < &1 ==> atn((x + y) / (&1 - x * y)) = atn x + atn y`,
  REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC ATN_ADD THEN
  MP_TAC(SPEC `x:real` ATN_LE_PI4) THEN MP_TAC(SPEC `y:real` ATN_LT_PI4) THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN REAL_ARITH_TAC);;

(* |- lo <= atn(r) /\ atn(r) <= hi  where r is the given term (a rational
   expression), using t = atn c + atn t' *)
let rp_cert_log_atn_via c cth t =
  (* cth: bounds for atn c ; t : rational numeral *)
  let cr = rat_of_term c and tr = rat_of_term t in
  let one = num_of_string "1" in
  let t1 = (tr -/ cr) // (one +/ tr */ cr) in
  let sc = power_num (num_of_string "2") (num_of_string "52") in
  let tl = floor_num (t1 */ sc) // sc and th = ceiling_num (t1 */ sc) // sc in
  let tlt = term_of_rat tl and tht = term_of_rat th in
  let bl = rp_cert_log_atn_taylor tlt and bh = rp_cert_log_atn_taylor tht in
  (* atn c + atn tl <= atn t <= atn c + atn th *)
  let mk tq bq =
    let e = MP (ISPECL [c; tq] RP_CERT_LOG_ATN_ADD)
               (EQT_ELIM(REAL_RAT_REDUCE_CONV (lhand(concl(ISPECL [c; tq] RP_CERT_LOG_ATN_ADD))))) in
    let s = MATCH_MP RP_CERT_LOG_B_ADD (CONJ (CONJUNCT1 cth) (CONJ (CONJUNCT2 cth)
                    (CONJ (CONJUNCT1 bq) (CONJUNCT2 bq)))) in
    MATCH_MP RP_CERT_LOG_B_EQ (CONJ e s) in
  let ml = mk tlt bl and mh = mk tht bh in
  (* atn((c + tq)/(1 - c tq)) with tq <= ... : monotonicity *)
  let argl = rand(rand(lhand(concl ml))) and argh = rand(rand(lhand(concl mh))) in
  let le1 = EQ_MP (SYM(SPECL [argl; t] ATN_MONO_LE_EQ))
             (EQT_ELIM((LAND_CONV REAL_RAT_REDUCE_CONV THENC REAL_RAT_LE_CONV)
                        (mk_binop `(<=):real->real->bool` argl t))) in
  let le2 = EQ_MP (SYM(SPECL [t; argh] ATN_MONO_LE_EQ))
             (EQT_ELIM((RAND_CONV REAL_RAT_REDUCE_CONV THENC REAL_RAT_LE_CONV)
                        (mk_binop `(<=):real->real->bool` t argh))) in
  rp_cert_log_normalize
   (CONJ (MATCH_MP REAL_LE_TRANS (CONJ (CONJUNCT1 ml) le1))
         (MATCH_MP REAL_LE_TRANS (CONJ le2 (CONJUNCT2 mh))));;

let RP_CERT_LOG_PI_BOUNDS = prove
 (`&13493037704 / &4294967296 <= pi /\ pi <= &13493037706 / &4294967296`,
  MP_TAC PI_APPROX_32 THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN REAL_ARITH_TAC);;

let RP_CERT_LOG_ATN1 = prove
 (`&13493037704 / &17179869184 <= atn(&1) /\ atn(&1) <= &13493037706 / &17179869184`,
  REWRITE_TAC[ATN_1] THEN MP_TAC RP_CERT_LOG_PI_BOUNDS THEN REAL_ARITH_TAC);;

let RP_CERT_LOG_ATN0 = prove
 (`&0 <= atn(&0) /\ atn(&0) <= &0`, REWRITE_TAC[ATN_0; REAL_LE_REFL]);;

(* table of atn(k/64), k = 0..64 *)
let rp_cert_log_atn_tab =
  let a = Array.make 65 RP_CERT_LOG_ATN0 in
  a.(64) <- RP_CERT_LOG_ATN1;
  for k = 1 to 63 do
    let c = term_of_rat (rp_cert_log_int (k - 1) // num_of_string "64")
    and t = term_of_rat (rp_cert_log_int k // num_of_string "64") in
    let c = if k = 1 then `&0` else c in
    a.(k) <- rp_cert_log_atn_via c a.(k - 1) t
  done; a;;

let RP_CERT_LOG_ATN_INV = prove
 (`forall x. &0 < x ==> atn x = pi / &2 - atn(inv x)`,
  SIMP_TAC[ATN_INV] THEN REAL_ARITH_TAC);;

let rp_cert_log_atn_core t =
  (* t rational numeral with |t| <= 1 *)
  let tr = rat_of_term t in
  let k = rp_cert_log_toint (round_num (tr */ num_of_string "64")) in
  let k = max (-64) (min 64 k) in
  if k = 0 then rp_cert_log_atn_taylor t else
  let cth = rp_cert_log_atn_tab.(abs k) in
  let cth = if k > 0 then cth else
    let c = rand(lhand(concl(CONJUNCT2 cth))) in
    let nb = MATCH_MP RP_CERT_LOG_B_NEG cth in
    let nc = mk_comb(`(--):real->real`, c) in
    let th = MATCH_MP RP_CERT_LOG_B_EQ (CONJ (SPEC c ATN_NEG) nb) in
    CONV_RULE (BINOP_CONV (ONCE_DEPTH_CONV (fun tm ->
       if tm = mk_comb(`atn`, nc) then RAND_CONV REAL_RAT_REDUCE_CONV tm else failwith ""))) th in
  let c = rand(rand(lhand(concl cth))) in
  if rat_of_term c =/ tr then cth else
  rp_cert_log_atn_via c cth t;;

let rp_cert_log_atn_bounds r =
  let eqr = REAL_RAT_REDUCE_CONV r in
  let rv = rand(concl eqr) in
  let tr = rat_of_term rv in
  let one = num_of_string "1" in
  let th =
    if abs_num tr <=/ one then rp_cert_log_atn_core rv
    else if tr >/ one then
      let ir = term_of_rat (one // tr) in
      let e = MP (SPEC rv RP_CERT_LOG_ATN_INV) (rp_cert_log_lt `&0` rv) in
      let e = CONV_RULE (RAND_CONV (RAND_CONV (RAND_CONV REAL_RAT_REDUCE_CONV))) e in
      let b = rp_cert_log_atn_core ir in
      let pb = RP_CERT_LOG_PI_BOUNDS in
      let half = REAL_ARITH `&0 <= inv(&2)` in
      let pb2 = MATCH_MP RP_CERT_LOG_B_CMUL_POS (CONJ half pb) in
      let pb2 = CONV_RULE (BINOP_CONV (ONCE_DEPTH_CONV (fun tm ->
                  if tm = `inv(&2) * pi` then REWRITE_CONV[GSYM real_div; REAL_MUL_SYM] tm |> fun _ ->
                     REAL_ARITH `inv(&2) * pi = pi / &2` else failwith ""))) pb2 in
      let s = MATCH_MP RP_CERT_LOG_B_SUB (CONJ (CONJUNCT1 pb2) (CONJ (CONJUNCT2 pb2)
                  (CONJ (CONJUNCT1 b) (CONJUNCT2 b)))) in
      rp_cert_log_normalize (MATCH_MP RP_CERT_LOG_B_EQ (CONJ e s))
    else
      let nr = term_of_rat (minus_num tr) in
      let e = CONV_RULE (LAND_CONV (RAND_CONV REAL_RAT_REDUCE_CONV))
                (SPEC nr ATN_NEG) in
      let b = (if minus_num tr >/ one then
                 let ir = term_of_rat (one // minus_num tr) in
                 let e2 = MP (SPEC nr RP_CERT_LOG_ATN_INV) (rp_cert_log_lt `&0` nr) in
                 let e2 = CONV_RULE (RAND_CONV (RAND_CONV (RAND_CONV REAL_RAT_REDUCE_CONV))) e2 in
                 let b0 = rp_cert_log_atn_core ir in
                 let pb2 = MATCH_MP RP_CERT_LOG_B_CMUL_POS (CONJ (REAL_ARITH `&0 <= inv(&2)`) RP_CERT_LOG_PI_BOUNDS) in
                 let pb2 = CONV_RULE (BINOP_CONV (ONCE_DEPTH_CONV (fun tm ->
                  if tm = `inv(&2) * pi` then REAL_ARITH `inv(&2) * pi = pi / &2` else failwith ""))) pb2 in
                 let s = MATCH_MP RP_CERT_LOG_B_SUB (CONJ (CONJUNCT1 pb2) (CONJ (CONJUNCT2 pb2)
                  (CONJ (CONJUNCT1 b0) (CONJUNCT2 b0)))) in
                 MATCH_MP RP_CERT_LOG_B_EQ (CONJ e2 s)
               else rp_cert_log_atn_core nr) in
      rp_cert_log_normalize (MATCH_MP RP_CERT_LOG_B_EQ (CONJ e (MATCH_MP RP_CERT_LOG_B_NEG b))) in
  (* replace the reduced argument by the original term r *)
  let eqa = AP_TERM `atn` (SYM eqr) in
  CONV_RULE (BINOP_CONV (ONCE_DEPTH_CONV (fun tm -> if tm = mk_comb(`atn`, rv) then eqa else failwith ""))) th;;

(* ------------------------------------------------------------------------- *)
(* General interval bounding of closed real expressions built from rational  *)
(* constants, +, -, --, products/quotients with a constant side, log, atn,   *)
(* pi, and Re(c * clog w).                                                   *)
(* ------------------------------------------------------------------------- *)

let rp_cert_log_const_bounds tm =
  let th = (NUM_REDUCE_CONV THENC REAL_RAT_REDUCE_CONV) tm in
  let v = rand(concl th) in
  if not (is_ratconst v) then failwith "rp_cert_log_const_bounds" else
  let le = REAL_LE_REFL in
  let a = EQ_MP (SYM(AP_TERM (mk_comb(`(<=):real->real->bool`, v)) th)) (SPEC v le) in
  let b = EQ_MP (SYM(AP_THM (AP_TERM `(<=):real->real->bool` th) v)) (SPEC v le) in
  CONJ a b;;

let rp_cert_log_is_const tm =
  frees tm = [] &&
  not (can (find_term (fun t -> match t with
          Const(("log"|"atn"|"pi"|"Re"|"Im"|"clog"|"sqrt"|"exp"),_) -> true | _ -> false)) tm);;

let rec rp_cert_log_ibound tm =
  if rp_cert_log_is_const tm then rp_cert_log_const_bounds tm else
  let comb2 lem a b =
    let ta = rp_cert_log_ibound a and tb = rp_cert_log_ibound b in
    rp_cert_log_normalize (MATCH_MP lem (CONJ (CONJUNCT1 ta) (CONJ (CONJUNCT2 ta)
        (CONJ (CONJUNCT1 tb) (CONJUNCT2 tb))))) in
  let cmul c a =
    let ta = rp_cert_log_ibound a in
    let cv = rand(concl((NUM_REDUCE_CONV THENC REAL_RAT_REDUCE_CONV) c)) in
    let ceq = (NUM_REDUCE_CONV THENC REAL_RAT_REDUCE_CONV) c in
    let th =
      if rat_of_term cv >=/ num_of_string "0" then
        let p = EQ_MP (SYM(AP_TERM `(<=) (&0)` ceq)) (rp_cert_log_le `&0` cv) in
        MATCH_MP RP_CERT_LOG_B_CMUL_POS (CONJ p ta)
      else
        let p = EQ_MP (SYM(AP_THM (AP_TERM `(<=):real->real->bool` ceq) `&0`)) (rp_cert_log_le cv `&0`) in
        MATCH_MP RP_CERT_LOG_B_CMUL_NEG (CONJ p ta) in
    rp_cert_log_normalize th in
  match tm with
    Comb(Comb(Const("real_add",_),a),b) -> comb2 RP_CERT_LOG_B_ADD a b
  | Comb(Comb(Const("real_sub",_),a),b) -> comb2 RP_CERT_LOG_B_SUB a b
  | Comb(Const("real_neg",_),a) ->
      rp_cert_log_normalize (MATCH_MP RP_CERT_LOG_B_NEG (rp_cert_log_ibound a))
  | Comb(Comb(Const("real_mul",_),a),b) ->
      if rp_cert_log_is_const a then cmul a b
      else if rp_cert_log_is_const b then
        let e = SPECL [a; b] REAL_MUL_SYM in
        let th = cmul b a in
        MATCH_MP RP_CERT_LOG_B_EQ (CONJ e th)
      else failwith "rp_cert_log_ibound: nonlinear product"
  | Comb(Comb(Const("real_div",_),a),b) ->
      if rp_cert_log_is_const b then
        let e = SPECL [a; b] real_div in
        let e2 = TRANS e (SPECL [a; mk_comb(`inv:real->real`, b)] REAL_MUL_SYM) in
        let th = cmul (mk_comb(`inv:real->real`, b)) a in
        MATCH_MP RP_CERT_LOG_B_EQ (CONJ e2 th)
      else failwith "rp_cert_log_ibound: division"
  | Comb(Const("log",_),r) -> rp_cert_log_normalize (rp_cert_log_bounds r)
  | Comb(Const("atn",_),r) -> rp_cert_log_atn_bounds r
  | Const("pi",_) -> RP_CERT_LOG_PI_BOUNDS
  | Comb(Const("Re",_),Comb(Comb(Const("complex_mul",_),c),Comb(Const("clog",_),w))) ->
      rp_cert_log_reclog_bounds tm
  | _ -> failwith ("rp_cert_log_ibound: " ^ string_of_term tm)

and rp_cert_log_reclog_bounds tm =
  let c, w = match tm with
      Comb(Const("Re",_),Comb(Comb(Const("complex_mul",_),c),Comb(Const("clog",_),w))) -> c, w
    | _ -> failwith "rp_cert_log_reclog_bounds" in
  let ceq = rp_cert_log_cplx_conv c and weq = rp_cert_log_cplx_conv w in
  let cn = rand(concl ceq) and wn = rand(concl weq) in
  let wr, wi = dest_pair(rand wn) in
  let wrv = rat_of_term wr and wiv = rat_of_term wi in
  let zero = num_of_string "0" in
  let [l1;l2;l3] = CONJUNCTS (ISPECL [cn; wn] RP_CERT_LOG_RECLOG) in
  let red = PURE_REWRITE_CONV[CONJUNCT2(CONJUNCT2(CONJUNCT2(CONJUNCT2(CONJUNCT2(CONJUNCT2(
              CONJUNCT2(CONJUNCT2(CONJUNCT2(CONJUNCT2(CONJUNCT2 RP_CERT_LOG_CPLX))))))))))] in
  let hyp_conv = red THENC REAL_RAT_REDUCE_CONV in
  let disch l = let h = lhand(concl l) in MP l (EQT_ELIM(hyp_conv h)) in
  let eq =
    if wrv >/ zero then disch l1
    else if wrv </ zero && wiv >=/ zero then disch l2
    else if wrv </ zero then disch l3
    else failwith "rp_cert_log_reclog_bounds: Re w = 0" in
  (* eq : Re(cn * clog wn) = expr; simplify Re/Im of complex(...) in expr *)
  let eq2 = CONV_RULE (RAND_CONV red) eq in
  let rhs = rand(concl eq2) in
  let bth = rp_cert_log_ibound rhs in
  let th = MATCH_MP RP_CERT_LOG_B_EQ (CONJ eq2 bth) in
  (* restore original c and w *)
  let back = AP_TERM `Re` (MK_COMB(AP_TERM `complex_mul` ceq, AP_TERM `clog` weq)) in
  MATCH_MP RP_CERT_LOG_B_EQ (CONJ back th);;
