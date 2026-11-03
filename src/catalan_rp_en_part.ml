(* ========================================================================= *)
(* EN part: the pair interactions bounded by trial quantities, (86)-(87)    *)
(* with damping, diagonal corrections and the completed squares.            *)
(* ========================================================================= *)

needs "src/catalan_rp_en_sq.ml";;

(* Linear arithmetic treating finite sums as atoms up to alpha-conversion  *)
(* (same as RP_EN_X_GEN_SUMS_TAC in catalan_rp_en_x.ml)                     *)
let RP_EN_GEN_SUMS_TAC =
  let is_sumlike t =
    match strip_comb t with
      (Const(c,_), [_;_]) -> c = "sum" || c = "rp_en_psum"
    | _ -> false in
  let rec tsize t =
    match t with
      Comb(f,x) -> tsize f + tsize x
    | Abs(_,b) -> 1 + tsize b
    | _ -> 1 in
  W(fun (asl,w) ->
    let fvs = frees w in
    let ts = find_terms (fun t -> is_sumlike t && subset (frees t) fvs) w in
    let ts = sort (fun a b -> tsize a > tsize b) ts in
    let reps = itlist (fun t acc -> if exists (aconv t) acc then acc else t::acc)
                      (rev ts) [] in
    let reps = sort (fun a b -> tsize a > tsize b) reps in
    MAP_EVERY (fun t -> SPEC_TAC(t, genvar(type_of t))) reps THEN
    REPEAT GEN_TAC);;

let RP_EN_SUMARITH_TAC = RP_EN_GEN_SUMS_TAC THEN REAL_ARITH_TAC;;

let RP_EN_P_SYM = prove
 (`forall r u v. rp_en_P r u v = rp_en_P r v u`,
  REWRITE_TAC[rp_en_P] THEN REAL_ARITH_TAC);;

let RP_EN_L_SYM = prove
 (`forall r u v. rp_en_L r u v = rp_en_L r v u`,
  REWRITE_TAC[rp_en_L] THEN MESON_TAC[RP_EN_P_SYM]);;

let RP_EN_SUM_CONST_LT = prove
 (`forall c n. sum {i:num | i < n} (\i. c) = &n * c`,
  SIMP_TAC[SUM_CONST; FINITE_NUMSEG_LT; CARD_NUMSEG_LT]);;

let RP_EN_SUM_LE_LT = prove
 (`forall (f:num->real) g n. (forall i. i < n ==> f i <= g i)
           ==> sum {i | i < n} f <= sum {i | i < n} g`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUM_LE THEN
  ASM_SIMP_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM] THEN
  REWRITE_TAC[FINITE_NUMSEG_LT]);;

let RP_EN_DISTINCT_LT = prove
 (`forall n (x:num->real) i j.
     (forall i j. i < n /\ j < n /\ x i = x j ==> i = j) /\ i < j /\ j < n
     ==> ~(x j = x i)`,
  REPEAT STRIP_TAC THEN SUBGOAL_THEN `j:num = i` MP_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC LT_TRANS THEN EXISTS_TAC `j:num` THEN ASM_REWRITE_TAC[];
    DISCH_THEN SUBST_ALL_TAC THEN ASM_MESON_TAC[LT_REFL]]);;

let RP_EN_SUM_LE_CONST_ADD = prove
 (`forall c (f:num->real) g n. (forall i. i < n ==> c + f i <= g i)
           ==> &n * c + sum {i | i < n} f <= sum {i | i < n} g`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM RP_EN_SUM_CONST_LT] THEN
  SIMP_TAC[GSYM SUM_ADD; FINITE_NUMSEG_LT] THEN
  MATCH_MP_TAC RP_EN_SUM_LE_LT THEN ASM_SIMP_TAC[]);;

let RP_EN_SUM_LE_CONST = prove
 (`forall c (g:num->real) n. (forall i. i < n ==> c <= g i)
           ==> &n * c <= sum {i | i < n} g`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`c:real`; `\i:num. &0`; `g:num->real`; `n:num`] RP_EN_SUM_LE_CONST_ADD) THEN
  ASM_SIMP_TAC[REAL_ADD_RID; SUM_0]);;

let RP_EN_COS_TERM = prove
 (`forall t u v k. (t pow 2) pow k * u * v / &k =
             (t pow k * u) * (t pow k * v) / &k`,
  REWRITE_TAC[REAL_POW_2; REAL_POW_MUL; real_div] THEN REAL_ARITH_TAC);;

(* x cosine kernel: Equation (86) with damping tau^2 and trial p *)
let RP_EN_PART_X = prove
 (`forall n (x:num->real) p e.
     1 <= n /\ &0 < e /\ e < &1 / &8 /\
     (forall i. i < n ==> --(&1) < x i /\ x i < &1) /\
     (forall i j. i < n /\ j < n /\ x i = x j ==> i = j) /\
     rp_summable p
     ==> rp_en_psum n (\i j. log(abs(x j - x i))) <=
         &n pow 2 * (--(log(&2)) / &2 + rp_nsq p) -
         &2 * &n * sum {i | i < n} (\i. rp_en_Te p e (x i)) +
         &n * (log(&2) - &2 * log(&1 - (&1 - e) pow 2)) / &2 +
         &2 * e * &n pow 2`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `r = (&1 - e) pow 2` THEN
  SUBGOAL_THEN `(&1 - e) pow 2 <= r /\ r <= &1 /\ &0 < r /\ r < &1` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "r" THEN REWRITE_TAC[REAL_LE_REFL] THEN
    REWRITE_TAC[REAL_POW_2] THEN CONJ_TAC THENL
     [MATCH_MP_TAC RP_EN_MUL_LE1 THEN ASM_REAL_ARITH_TAC;
      CONJ_TAC THENL [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC(REAL_ARITH `a * a <= a * &1 /\ a < &1 ==> a * a < &1`) THEN
      CONJ_TAC THENL [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
                      ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  SUBGOAL_THEN `--log r <= &4 * e` ASSUME_TAC THENL
   [MATCH_MP_TAC RP_EN_DMP_LOGR THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `forall i. i < n ==> abs((x:num->real) i) <= &1` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    UNDISCH_TAC `forall i. i < n ==> --(&1) < (x:num->real) i /\ x i < &1` THEN
    DISCH_THEN(MP_TAC o SPEC `i:num`) THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* step 1: comparison with the damped kernel *)
  SUBGOAL_THEN
   `rp_en_psum n (\i j. log(abs(x j - x i))) <=
    rp_en_psum n (\i j. rp_en_L r (x i) (x j)) + &n * (&n - &1) / &2 * (&4 * e)`
  ASSUME_TAC THENL
   [REWRITE_TAC[GSYM RP_EN_PSUM_CONST] THEN REWRITE_TAC[GSYM RP_EN_PSUM_ADD] THEN
    MATCH_MP_TAC RP_EN_PSUM_LE THEN REPEAT STRIP_TAC THEN BETA_TAC THEN
    MP_TAC(SPECL [`r:real`; `(x:num->real) j`; `(x:num->real) i`] RP_EN_DMP_COS_CMP) THEN
    SUBGOAL_THEN `~((x:num->real) j = x i)` ASSUME_TAC THENL
     [MATCH_MP_TAC RP_EN_DISTINCT_LT THEN EXISTS_TAC `n:num` THEN
      ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `i:num < n` ASSUME_TAC THENL
     [MATCH_MP_TAC LT_TRANS THEN EXISTS_TAC `j:num` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[ISPECL [`r:real`; `(x:num->real) j`; `(x:num->real) i`] RP_EN_L_SYM] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* step 2: symmetric pair sum *)
  MP_TAC(ISPECL [`\i j. rp_en_L r ((x:num->real) i) (x j)`; `n:num`] RP_EN_PSUM_SYM) THEN
  ANTS_TAC THENL [REWRITE_TAC[] THEN REPEAT GEN_TAC THEN MATCH_ACCEPT_TAC RP_EN_L_SYM;
                  ALL_TAC] THEN
  REWRITE_TAC[] THEN DISCH_TAC THEN
  (* step 3: the full double sum via the series *)
  ABBREV_TAC `Q = sum {i | i < n} (\i. sum {j | j < n}
                    (\j. --(log(rp_en_P r ((x:num->real) i) (x j))) / &4))` THEN
  SUBGOAL_THEN
   `sum {i | i < n} (\i. sum {j | j < n} (\j. rp_en_L r ((x:num->real) i) (x j))) =
    --(&n pow 2 * log(&2)) - &2 * Q`
  ASSUME_TAC THENL
   [EXPAND_TAC "Q" THEN
    REWRITE_TAC[rp_en_L; REAL_ARITH `--a + b / &2 = --a - &2 * (--b / &4)`] THEN
    SIMP_TAC[SUM_SUB; FINITE_NUMSEG_LT; SUM_LMUL; RP_EN_SUM_CONST_LT] THEN
    REWRITE_TAC[REAL_POW_2] THEN RP_EN_SUMARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `((\k. sum {i | i < n} (\i. (&1 - e) pow k * rp_cheb k ((x:num->real) i)) pow 2 / &k)
     real_sums Q) (from 1)`
  ASSUME_TAC THENL
   [EXPAND_TAC "Q" THEN
    MP_TAC(ISPECL [`\i k. (&1 - e) pow k * rp_cheb k ((x:num->real) i)`;
                   `\i j. --(log(rp_en_P r ((x:num->real) i) (x j))) / &4`;
                   `n:num`] RP_EN_GEN_SQ) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN REPEAT STRIP_TAC THEN
    REWRITE_TAC[GSYM RP_EN_COS_TERM] THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC RP_EN_KER_COS_SERIES THEN ASM_SIMP_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* step 4: the trial completion *)
  MP_TAC(ISPECL [`\k. sum {i | i < n} (\i. (&1 - e) pow k * rp_cheb k ((x:num->real) i))`;
                 `p:num->real`; `Q:real`;
                 `sum {i | i < n} (\i. rp_en_Te p e ((x:num->real) i))`; `&n`]
         RP_EN_TRIAL1) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REWRITE_TAC[rp_en_Te] THEN
    MP_TAC(ISPECL [`p:num->real`;
                   `\i k. (&1 - e) pow k * rp_cheb k ((x:num->real) i)`; `n:num`]
           RP_EN_TRIALSUM) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    REPEAT STRIP_TAC THEN REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_POW] THEN
    MATCH_MP_TAC RP_EN_MUL_LE1 THEN REWRITE_TAC[REAL_ABS_POS] THEN
    ASM_SIMP_TAC[RP_EN_KER_CHEB_BOUND; REAL_POW_LE; REAL_ABS_POS] THEN
    MATCH_MP_TAC REAL_POW_1_LE THEN ASM_REAL_ARITH_TAC;
    DISCH_TAC] THEN
  (* step 5: the diagonal *)
  SUBGOAL_THEN
   `&n * (--log(&2) + &2 * log(&1 - r)) <=
    sum {i | i < n} (\i. rp_en_L r ((x:num->real) i) (x i))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC RP_EN_SUM_LE_CONST THEN
    REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN MATCH_MP_TAC RP_EN_DMP_COS_DIAG THEN
    ASM_SIMP_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= e * &n` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o check (fun th -> free_in `rp_en_psum` (concl th) ||
     free_in `Q:real` (concl th) || free_in `log(&1 - r)` (concl th)))) THEN
  UNDISCH_TAC `&0 <= e * &n` THEN
  REWRITE_TAC[REAL_POW_2] THEN RP_EN_SUMARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Power kernel with damping rho, Equation (87) first term.                  *)
(* ------------------------------------------------------------------------- *)

let RP_EN_Y_BOUND = prove
 (`forall e x. &0 < e /\ e < &1 / &8 /\ --(&1) < x /\ x < &1
         ==> abs(rp_en_rho e x * x) < &1`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`e:real`; `x:real`] RP_EN_DMP_RHO_BOUNDS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN REWRITE_TAC[REAL_ABS_MUL] THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `&1 * abs x` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[REAL_ABS_POS] THEN ASM_REAL_ARITH_TAC;
    ASM_REAL_ARITH_TAC]);;

let RP_EN_ABS_MUL_LT1 = prove
 (`forall a b. abs a < &1 /\ abs b < &1 ==> abs(a * b) < &1`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[REAL_ABS_MUL] THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `abs a * &1` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC]);;

let RP_EN_PS_POW = prove
 (`forall n (x:num->real) e.
     1 <= n /\ &0 < e /\ e < &1 / &8 /\
     (forall i. i < n ==> --(&1) < x i /\ x i < &1)
     ==> rp_en_psum n (\i j. log(&1 - x i * x j)) <=
         --(sum {i | i < n} (\i. sum {j | j < n}
              (\j. --(log(&1 - (rp_en_rho e (x i) * x i) *
                               (rp_en_rho e (x j) * x j)))))) / &2 +
         (&n * (log(&2) - log e) - sum {i | i < n} (\i. log(&1 - x i))) / &2 +
         &2 * e * &n pow 2`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `rp_en_psum n (\i j. log(&1 - x i * x j)) <=
    rp_en_psum n (\i j. log(&1 - (rp_en_rho e (x i) * x i) *
                                 (rp_en_rho e (x j) * x j))) +
    &n * (&n - &1) / &2 * (&4 * e)`
  ASSUME_TAC THENL
   [REWRITE_TAC[GSYM RP_EN_PSUM_CONST] THEN REWRITE_TAC[GSYM RP_EN_PSUM_ADD] THEN
    MATCH_MP_TAC RP_EN_PSUM_LE THEN REPEAT STRIP_TAC THEN BETA_TAC THEN
    SUBGOAL_THEN `i:num < n` ASSUME_TAC THENL
     [MATCH_MP_TAC LT_TRANS THEN EXISTS_TAC `j:num` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC RP_EN_DMP_POW_CMP THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\i j. log(&1 - (rp_en_rho e ((x:num->real) i) * x i) *
                                 (rp_en_rho e (x j) * x j))`; `n:num`] RP_EN_PSUM_SYM) THEN
  ANTS_TAC THENL [REWRITE_TAC[] THEN REPEAT GEN_TAC THEN
                  REWRITE_TAC[REAL_MUL_SYM]; ALL_TAC] THEN
  REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `&n * (log e - log(&2)) + sum {i | i < n} (\i. log(&1 - (x:num->real) i)) <=
    sum {i | i < n} (\i. log(&1 - (rp_en_rho e (x i) * x i) *
                                  (rp_en_rho e (x i) * x i)))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC RP_EN_SUM_LE_CONST_ADD THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(SPECL [`e:real`; `(x:num->real) i`] RP_EN_DMP_POW_DIAG) THEN
    ASM_REWRITE_TAC[GSYM REAL_POW_2] THEN DISCH_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `log(e * (&1 - (x:num->real) i) / &2)` THEN CONJ_TAC THENL
     [SUBGOAL_THEN `&0 < &1 - (x:num->real) i` ASSUME_TAC THENL
       [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `&0 < (&1 - (x:num->real) i) / &2` ASSUME_TAC THENL
       [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_SIMP_TAC[LOG_DIV; LOG_MUL; REAL_ARITH `&0 < &2`] THEN
      REAL_ARITH_TAC;
      MATCH_MP_TAC LOG_MONO_LE_IMP THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= e * &n` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SIMP_TAC[SUM_NEG; FINITE_NUMSEG_LT] THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o check (fun th -> free_in `rp_en_psum` (concl th) ||
     free_in `log e` (concl th) || free_in `e * &n` (concl th)))) THEN
  REWRITE_TAC[REAL_POW_2] THEN RP_EN_SUMARITH_TAC);;

let RP_EN_PS_POW_SER = prove
 (`forall n (x:num->real) e.
     &0 < e /\ e < &1 / &8 /\
     (forall i. i < n ==> --(&1) < x i /\ x i < &1)
     ==> ((\k. sum {i | i < n} (\i. (rp_en_rho e (x i) * x i) pow k) pow 2 / &k)
          real_sums
          sum {i | i < n} (\i. sum {j | j < n}
              (\j. --(log(&1 - (rp_en_rho e (x i) * x i) *
                               (rp_en_rho e (x j) * x j)))))) (from 1)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\i k. (rp_en_rho e ((x:num->real) i) * x i) pow k`;
                 `\i j. --(log(&1 - (rp_en_rho e ((x:num->real) i) * x i) *
                                    (rp_en_rho e (x j) * x j)))`;
                 `n:num`] RP_EN_GEN_SQ) THEN
  REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
  MAP_EVERY X_GEN_TAC [`i:num`; `j:num`] THEN STRIP_TAC THEN
  MP_TAC(SPEC `(rp_en_rho e ((x:num->real) i) * x i) * (rp_en_rho e (x j) * x j)`
         RP_EN_KER_POW_SERIES) THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC RP_EN_ABS_MUL_LT1 THEN CONJ_TAC THEN
    MATCH_MP_TAC RP_EN_Y_BOUND THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[REAL_POW_MUL; real_div; REAL_MUL_ASSOC]);;

(* ------------------------------------------------------------------------- *)
(* s cosine kernel with damping sigma(s) sigma(s').                          *)
(* ------------------------------------------------------------------------- *)

let RP_EN_SIG_RANGE = prove
 (`forall e s. &0 < e /\ e < &1 / &8 /\ &0 < s /\ s < &1
         ==> &1 - e <= rp_en_sig e s /\ rp_en_sig e s < &1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC `s:real` RP_EN_DMP_SQRT_ONE_SUB) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN REWRITE_TAC[rp_en_sig] THEN
  SUBGOAL_THEN `&0 < sqrt(&1 - s)` ASSUME_TAC THENL
   [MATCH_MP_TAC SQRT_POS_LT THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `e * q <= e * &1 ==> &1 - e <= &1 - e * q`) THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC(REAL_ARITH `&0 < e * q ==> &1 - e * q < &1`) THEN
    MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC]);;

let RP_EN_SIG2_RANGE = prove
 (`forall e s t. &0 < e /\ e < &1 / &8 /\ &0 < s /\ s < &1 /\ &0 < t /\ t < &1
           ==> (&1 - e) pow 2 <= rp_en_sig e s * rp_en_sig e t /\
               &0 < rp_en_sig e s * rp_en_sig e t /\
               rp_en_sig e s * rp_en_sig e t < &1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`e:real`; `s:real`] RP_EN_SIG_RANGE) THEN
  MP_TAC(SPECL [`e:real`; `t:real`] RP_EN_SIG_RANGE) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THENL
   [REWRITE_TAC[REAL_POW_2] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `&1 * rp_en_sig e t` THEN
    CONJ_TAC THENL [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC;
                    ASM_REAL_ARITH_TAC]]);;

let RP_EN_PS_S = prove
 (`forall n (s:num->real) e.
     1 <= n /\ &0 < e /\ e < &1 / &8 /\
     (forall j. j < n ==> &0 < s j /\ s j < &1) /\
     (forall i j. i < n /\ j < n /\ s i = s j ==> i = j)
     ==> rp_en_psum n (\i j. log(abs(s j - s i))) <=
         --(&n pow 2 * log(&2)) / &2 -
         sum {i | i < n} (\i. sum {j | j < n}
            (\j. --(log(rp_en_P (rp_en_sig e (s i) * rp_en_sig e (s j)) (s i) (s j))) / &4)) +
         (&n * (log(&2) - &2 * log e) - sum {j | j < n} (\j. log(&1 - s j))) / &2 +
         &2 * e * &n pow 2`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `forall i. i < n ==> abs((s:num->real) i) <= &1` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    UNDISCH_TAC `forall j. j < n ==> &0 < (s:num->real) j /\ s j < &1` THEN
    DISCH_THEN(MP_TAC o SPEC `i:num`) THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `rp_en_psum n (\i j. log(abs(s j - s i))) <=
    rp_en_psum n (\i j. rp_en_L (rp_en_sig e (s i) * rp_en_sig e (s j)) (s i) (s j)) +
    &n * (&n - &1) / &2 * (&4 * e)`
  ASSUME_TAC THENL
   [REWRITE_TAC[GSYM RP_EN_PSUM_CONST] THEN REWRITE_TAC[GSYM RP_EN_PSUM_ADD] THEN
    MATCH_MP_TAC RP_EN_PSUM_LE THEN REPEAT STRIP_TAC THEN BETA_TAC THEN
    SUBGOAL_THEN `i:num < n` ASSUME_TAC THENL
     [MATCH_MP_TAC LT_TRANS THEN EXISTS_TAC `j:num` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `~((s:num->real) j = s i)` ASSUME_TAC THENL
     [MATCH_MP_TAC RP_EN_DISTINCT_LT THEN EXISTS_TAC `n:num` THEN
      ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MP_TAC(SPECL [`e:real`; `(s:num->real) j`; `(s:num->real) i`] RP_EN_SIG2_RANGE) THEN
    ASM_SIMP_TAC[] THEN STRIP_TAC THEN
    MP_TAC(SPECL [`rp_en_sig e ((s:num->real) j) * rp_en_sig e (s i)`;
                  `(s:num->real) j`; `(s:num->real) i`] RP_EN_DMP_COS_CMP) THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
    MP_TAC(SPECL [`e:real`; `rp_en_sig e ((s:num->real) j) * rp_en_sig e (s i)`]
           RP_EN_DMP_LOGR) THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
    REWRITE_TAC[ISPECL [`rp_en_sig e ((s:num->real) j)`; `rp_en_sig e ((s:num->real) i)`]
                REAL_MUL_SYM] THEN
    REWRITE_TAC[ISPECL [`rp_en_sig e ((s:num->real) i) * rp_en_sig e (s j)`;
                        `(s:num->real) j`; `(s:num->real) i`] RP_EN_L_SYM] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\i j. rp_en_L (rp_en_sig e ((s:num->real) i) * rp_en_sig e (s j))
                                (s i) (s j)`; `n:num`] RP_EN_PSUM_SYM) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[] THEN REPEAT GEN_TAC THEN
    GEN_REWRITE_TAC LAND_CONV [RP_EN_L_SYM] THEN REWRITE_TAC[REAL_MUL_SYM];
    ALL_TAC] THEN
  REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `sum {i | i < n} (\i. sum {j | j < n}
       (\j. rp_en_L (rp_en_sig e ((s:num->real) i) * rp_en_sig e (s j)) (s i) (s j))) =
    --(&n pow 2 * log(&2)) - &2 *
    sum {i | i < n} (\i. sum {j | j < n}
       (\j. --(log(rp_en_P (rp_en_sig e (s i) * rp_en_sig e (s j)) (s i) (s j))) / &4))`
  ASSUME_TAC THENL
   [REWRITE_TAC[rp_en_L; REAL_ARITH `--a + b / &2 = --a - &2 * (--b / &4)`] THEN
    SIMP_TAC[SUM_SUB; FINITE_NUMSEG_LT; SUM_LMUL; RP_EN_SUM_CONST_LT] THEN
    REWRITE_TAC[REAL_POW_2] THEN RP_EN_SUMARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `&n * (--log(&2) + &2 * log e) + sum {j | j < n} (\j. log(&1 - (s:num->real) j)) <=
    sum {i | i < n} (\i. rp_en_L (rp_en_sig e (s i) * rp_en_sig e (s i)) (s i) (s i))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC RP_EN_SUM_LE_CONST_ADD THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    REWRITE_TAC[] THEN
    SUBGOAL_THEN `&0 < (s:num->real) i /\ s i < &1` STRIP_ASSUME_TAC THENL
     [ASM_SIMP_TAC[]; ALL_TAC] THEN
    MP_TAC(SPECL [`e:real`; `(s:num->real) i`; `(s:num->real) i`] RP_EN_SIG2_RANGE) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(SPECL [`e:real`; `(s:num->real) i`] RP_EN_DMP_SIG_DIAG) THEN
    ASM_REWRITE_TAC[REAL_POW_2] THEN DISCH_TAC THEN
    SUBGOAL_THEN `&0 < sqrt(&1 - (s:num->real) i)` ASSUME_TAC THENL
     [MATCH_MP_TAC SQRT_POS_LT THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&2 * log e + log(&1 - (s:num->real) i) <=
                  &2 * log(&1 - rp_en_sig e (s i) * rp_en_sig e (s i))` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `&2 * log(e * sqrt(&1 - (s:num->real) i))` THEN CONJ_TAC THENL
       [SUBGOAL_THEN `&0 < &1 - (s:num->real) i` ASSUME_TAC THENL
         [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        ASM_SIMP_TAC[LOG_MUL; LOG_SQRT] THEN REAL_ARITH_TAC;
        MATCH_MP_TAC(REAL_ARITH `a <= b ==> &2 * a <= &2 * b`) THEN
        MATCH_MP_TAC LOG_MONO_LE_IMP THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    MP_TAC(SPECL [`rp_en_sig e ((s:num->real) i) * rp_en_sig e (s i)`;
                  `(s:num->real) i`] RP_EN_DMP_COS_DIAG) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
    POP_ASSUM MP_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= e * &n` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o check (fun th -> free_in `rp_en_psum` (concl th) ||
     free_in `log e` (concl th) || free_in `e * &n` (concl th) ||
     free_in `log(&2)` (concl th)))) THEN
  REWRITE_TAC[REAL_POW_2] THEN RP_EN_SUMARITH_TAC);;

let RP_EN_PS_S_SER = prove
 (`forall n (s:num->real) e.
     &0 < e /\ e < &1 / &8 /\ (forall j. j < n ==> &0 < s j /\ s j < &1)
     ==> ((\k. sum {j | j < n} (\j. rp_en_sig e (s j) pow k * rp_cheb k (s j)) pow 2 / &k)
          real_sums
          sum {i | i < n} (\i. sum {j | j < n}
            (\j. --(log(rp_en_P (rp_en_sig e (s i) * rp_en_sig e (s j)) (s i) (s j))) / &4)))
         (from 1)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\j k. rp_en_sig e ((s:num->real) j) pow k * rp_cheb k (s j)`;
                 `\i j. --(log(rp_en_P (rp_en_sig e ((s:num->real) i) * rp_en_sig e (s j))
                                       (s i) (s j))) / &4`;
                 `n:num`] RP_EN_GEN_SQ) THEN
  REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
  MAP_EVERY X_GEN_TAC [`i:num`; `j:num`] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`e:real`; `(s:num->real) i`; `(s:num->real) j`] RP_EN_SIG2_RANGE) THEN
  ASM_SIMP_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`rp_en_sig e ((s:num->real) i) * rp_en_sig e (s j)`;
                `(s:num->real) i`; `(s:num->real) j`] RP_EN_KER_COS_SERIES) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
    UNDISCH_TAC `forall j. j < n ==> &0 < (s:num->real) j /\ s j < &1` THEN
    DISCH_THEN(fun th -> MP_TAC(SPEC `i:num` th) THEN MP_TAC(SPEC `j:num` th)) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[REAL_POW_MUL; real_div] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM] THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Cross kernel with damping rho(x) sigma(s).                                *)
(* ------------------------------------------------------------------------- *)

let RP_EN_PS_CROSS = prove
 (`forall n (x:num->real) s e.
     &0 < e /\ e < &1 / &8 /\
     (forall i. i < n ==> --(&1) < x i /\ x i < &1) /\
     (forall j. j < n ==> &0 < s j /\ s j < &1)
     ==> --(sum {i | i < n} (\i. sum {j | j < n}
              (\j. log(&1 - &2 * x i * s j + x i pow 2)))) <=
         &2 * sum {i | i < n} (\i. sum {j | j < n}
              (\j. --(log(&1 - &2 * (rp_en_rho e (x i) * rp_en_sig e (s j) * x i) * s j +
                           (rp_en_rho e (x i) * rp_en_sig e (s j) * x i) pow 2)) / &2)) +
         &6 * e * &n pow 2`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `sum {i:num | i < n} (\i. sum {j:num | j < n}
      (\j. &2 * (--(log(&1 - &2 * (rp_en_rho e ((x:num->real) i) *
                                   rp_en_sig e ((s:num->real) j) * x i) * s j +
                       (rp_en_rho e (x i) * rp_en_sig e (s j) * x i) pow 2)) / &2) +
           &6 * e))` THEN
  CONJ_TAC THENL
   [SIMP_TAC[GSYM SUM_NEG; FINITE_NUMSEG_LT] THEN
    MATCH_MP_TAC RP_EN_SUM_LE_LT THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    REWRITE_TAC[] THEN
    MATCH_MP_TAC RP_EN_SUM_LE_LT THEN X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    REWRITE_TAC[] THEN
    MP_TAC(SPECL [`e:real`; `(x:num->real) i`; `(s:num->real) j`] RP_EN_DMP_CROSS_CMP) THEN
    ASM_SIMP_TAC[] THEN REAL_ARITH_TAC;
    SIMP_TAC[SUM_ADD; SUM_LMUL; FINITE_NUMSEG_LT; RP_EN_SUM_CONST_LT] THEN
    REWRITE_TAC[REAL_POW_2] THEN RP_EN_SUMARITH_TAC]);;

let RP_EN_PS_CROSS_SER = prove
 (`forall n (x:num->real) s e.
     &0 < e /\ e < &1 / &8 /\
     (forall i. i < n ==> --(&1) < x i /\ x i < &1) /\
     (forall j. j < n ==> &0 < s j /\ s j < &1)
     ==> ((\k. sum {i | i < n} (\i. (rp_en_rho e (x i) * x i) pow k) *
               sum {j | j < n} (\j. rp_en_sig e (s j) pow k * rp_cheb k (s j)) / &k)
          real_sums
          sum {i | i < n} (\i. sum {j | j < n}
              (\j. --(log(&1 - &2 * (rp_en_rho e (x i) * rp_en_sig e (s j) * x i) * s j +
                           (rp_en_rho e (x i) * rp_en_sig e (s j) * x i) pow 2)) / &2)))
         (from 1)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\i k. (rp_en_rho e ((x:num->real) i) * x i) pow k`;
                 `\j k. rp_en_sig e ((s:num->real) j) pow k * rp_cheb k (s j)`;
                 `\i j. --(log(&1 - &2 * (rp_en_rho e ((x:num->real) i) *
                              rp_en_sig e ((s:num->real) j) * x i) * s j +
                           (rp_en_rho e (x i) * rp_en_sig e (s j) * x i) pow 2)) / &2`;
                 `n:num`] RP_EN_GEN_CROSS) THEN
  REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
  MAP_EVERY X_GEN_TAC [`i:num`; `j:num`] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`rp_en_rho e ((x:num->real) i) * rp_en_sig e ((s:num->real) j) * x i`;
                `(s:num->real) j`] RP_EN_KER_CROSS_SERIES) THEN
  ANTS_TAC THENL
   [MP_TAC(SPECL [`e:real`; `(x:num->real) i`] RP_EN_Y_BOUND) THEN
    MP_TAC(SPECL [`e:real`; `(s:num->real) j`] RP_EN_SIG_RANGE) THEN
    ASM_SIMP_TAC[] THEN REPEAT STRIP_TAC THENL
     [ONCE_REWRITE_TAC[REAL_ARITH `a * b * c = b * (a * c:real)`] THEN
      MATCH_MP_TAC RP_EN_ABS_MUL_LT1 THEN ASM_REWRITE_TAC[] THEN
      ASM_REAL_ARITH_TAC;
      UNDISCH_TAC `forall j. j < n ==> &0 < (s:num->real) j /\ s j < &1` THEN
      DISCH_THEN(MP_TAC o SPEC `j:num`) THEN ASM_REWRITE_TAC[] THEN
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM; REAL_POW_MUL; real_div] THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Equation (87): power + s cosine + cross, completed with the trial v.     *)
(* ------------------------------------------------------------------------- *)

let rp_en_qb_tm = `sum {i | i < n} (\i. sum {j | j < n}
   (\j. --(log(&1 - (rp_en_rho e ((x:num->real) i) * x i) *
                    (rp_en_rho e (x j) * x j)))))`;;

let rp_en_qc_tm = `sum {i | i < n} (\i. sum {j | j < n}
   (\j. --(log(rp_en_P (rp_en_sig e ((s:num->real) i) * rp_en_sig e (s j))
                       (s i) (s j))) / &4))`;;

let rp_en_qbc_tm = `sum {i | i < n} (\i. sum {j | j < n}
   (\j. --(log(&1 - &2 * (rp_en_rho e ((x:num->real) i) *
                            rp_en_sig e ((s:num->real) j) * x i) * s j +
               (rp_en_rho e (x i) * rp_en_sig e (s j) * x i) pow 2)) / &2))`;;

let RP_EN_PART_PS = prove
 (`forall n (x:num->real) (s:num->real) v e.
     1 <= n /\ &0 < e /\ e < &1 / &8 /\
     (forall i. i < n ==> --(&1) < x i /\ x i < &1) /\
     (forall j. j < n ==> &0 < s j /\ s j < &1) /\
     (forall i j. i < n /\ j < n /\ s i = s j ==> i = j) /\
     rp_summable v
     ==> rp_en_psum n (\i j. log(&1 - x i * x j)) +
         &2 * rp_en_psum n (\i j. log(abs(s j - s i))) -
         sum {i | i < n} (\i. sum {j | j < n}
              (\j. log(&1 - &2 * x i * s j + x i pow 2)))
         <= &n pow 2 * (--(log(&2)) + rp_nsq v / &2) -
            &n * sum {i | i < n} (\i. rp_en_Se v e (x i)) +
            &2 * &n * sum {j | j < n} (\j. rp_en_Ts v e (s j)) +
            (&n * (log(&2) - log e) - sum {i | i < n} (\i. log(&1 - x i))) / &2 +
            (&n * (log(&2) - &2 * log e) - sum {j | j < n} (\j. log(&1 - s j))) +
            &12 * e * &n pow 2`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`n:num`; `x:num->real`; `e:real`] RP_EN_PS_POW) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`n:num`; `s:num->real`; `e:real`] RP_EN_PS_S) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`n:num`; `x:num->real`; `s:num->real`; `e:real`] RP_EN_PS_CROSS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL
    [`\k. sum {i | i < n} (\i. (rp_en_rho e ((x:num->real) i) * x i) pow k)`;
     `\k. sum {j | j < n} (\j. rp_en_sig e ((s:num->real) j) pow k * rp_cheb k (s j))`;
     `v:num->real`; rp_en_qb_tm; rp_en_qc_tm; rp_en_qbc_tm;
     `sum {i | i < n} (\i. rp_en_Se v e ((x:num->real) i))`;
     `sum {j | j < n} (\j. rp_en_Ts v e ((s:num->real) j))`; `&n`] RP_EN_TRIAL2) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_SIMP_TAC[RP_EN_PS_POW_SER; RP_EN_PS_S_SER; RP_EN_PS_CROSS_SER] THEN
    REWRITE_TAC[rp_en_Se; rp_en_Ts] THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`v:num->real`;
                     `\i k. (rp_en_rho e ((x:num->real) i) * x i) pow k`; `n:num`]
             RP_EN_TRIALSUM) THEN
      REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      MAP_EVERY X_GEN_TAC [`i:num`; `k:num`] THEN STRIP_TAC THEN
      REWRITE_TAC[REAL_ABS_POW] THEN MATCH_MP_TAC REAL_POW_1_LE THEN
      REWRITE_TAC[REAL_ABS_POS] THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN
      MATCH_MP_TAC RP_EN_Y_BOUND THEN ASM_SIMP_TAC[];
      MP_TAC(ISPECL [`v:num->real`;
                     `\j k. rp_en_sig e ((s:num->real) j) pow k * rp_cheb k (s j)`;
                     `n:num`] RP_EN_TRIALSUM) THEN
      REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      MAP_EVERY X_GEN_TAC [`j:num`; `k:num`] THEN STRIP_TAC THEN
      SUBGOAL_THEN `&0 < (s:num->real) j /\ s j < &1` STRIP_ASSUME_TAC THENL
       [ASM_SIMP_TAC[]; ALL_TAC] THEN
      MP_TAC(SPECL [`e:real`; `(s:num->real) j`] RP_EN_SIG_RANGE) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_POW] THEN MATCH_MP_TAC RP_EN_MUL_LE1 THEN
      SIMP_TAC[REAL_ABS_POS; REAL_POW_LE] THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_POW_1_LE THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC RP_EN_KER_CHEB_BOUND THEN ASM_REAL_ARITH_TAC]];
    DISCH_TAC] THEN
  SUBGOAL_THEN `&0 <= e * &n` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o check (fun th -> not(is_forall(concl th))))) THEN
  REWRITE_TAC[REAL_POW_2] THEN RP_EN_SUMARITH_TAC);;
