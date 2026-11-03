needs "src/catalan_rp_en_base.ml";;

(* ========================================================================= *)
(* EN part: the exact identity (80) for log I_1, log I_2 via the            *)
(* substitution (79).                                                        *)
(* ========================================================================= *)


(* ------------------------------------------------------------------------- *)
(* Generic finite product / log helpers.                                     *)
(* ------------------------------------------------------------------------- *)

let RP_EN_X_PROD_POS = prove
 (`forall (f:num->real) n:num. (forall i. i < n ==> &0 < f i) ==> &0 < product {i | i < n} f`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC PRODUCT_POS_LT THEN
  ASM_SIMP_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM]);;

let RP_EN_X_LOG_PROD = prove
 (`forall (f:num->real) n:num. (forall i. i < n ==> &0 < f i)
         ==> log(product {i | i < n} f) = sum {i | i < n} (\i. log(f i))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC LOG_PRODUCT THEN
  ASM_SIMP_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM]);;

let RP_EN_X_PSUM_EQ = prove
 (`forall (f:num->num->real) g n:num. (forall i j. i < j /\ j < n ==> f i j = g i j)
           ==> rp_en_psum n f = rp_en_psum n g`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[rp_en_psum] THEN
  MATCH_MP_TAC SUM_EQ THEN REWRITE_TAC[IN_ELIM_THM] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC SUM_EQ THEN REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[]);;

let RP_EN_X_SUM_EQ = prove
 (`forall (f:num->real) g n:num. (forall i. i < n ==> f i = g i)
           ==> sum {i | i < n} f = sum {i | i < n} g`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUM_EQ THEN
  ASM_SIMP_TAC[IN_ELIM_THM]);;

let RP_EN_X_PSUM_PAIR = prove
 (`forall (f:num->real) n. rp_en_psum n (\i j. f i) + rp_en_psum n (\i j. f j) =
         (&n - &1) * sum {i | i < n} f`,
  GEN_TAC THEN INDUCT_TAC THEN
  REWRITE_TAC[RP_EN_PSUM_0; RP_EN_SUM_LT_0; RP_EN_PSUM_SUC; RP_EN_SUM_LT_SUC] THENL
   [REAL_ARITH_TAC; ALL_TAC] THEN
  SIMP_TAC[SUM_CONST; FINITE_NUMSEG_LT; CARD_NUMSEG_LT; GSYM REAL_OF_NUM_SUC] THEN
  FIRST_X_ASSUM(MP_TAC o check (is_eq o concl)) THEN
  REWRITE_TAC[ETA_AX; GSYM rp_en_lt] THEN CONV_TAC REAL_RING);;

let RP_EN_X_LOG_VDM = prove
 (`forall n:num (y:num->real). (forall i j. i < j /\ j < n ==> ~(y i = y j))
         ==> &0 < abs(rp_vdm n y) /\
             log(abs(rp_vdm n y)) = rp_en_psum n (\i j. log(abs(y j - y i)))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[rp_vdm; rp_en_psum] THEN
  SIMP_TAC[GSYM PRODUCT_ABS; FINITE_NUMSEG_LT] THEN
  SUBGOAL_THEN `forall j i. j < n /\ i < j ==> &0 < abs((y:num->real) j - y i)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM REAL_ABS_NZ; REAL_SUB_0] THEN
    ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `forall j. j < n ==> &0 < product {i | i < j} (\i. abs((y:num->real) j - y i))`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC RP_EN_X_PROD_POS THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[RP_EN_X_PROD_POS; RP_EN_X_LOG_PROD] THEN
  MATCH_MP_TAC RP_EN_X_SUM_EQ THEN REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC RP_EN_X_LOG_PROD THEN ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Pointwise facts for the substitution (79).                                *)
(* ------------------------------------------------------------------------- *)

let RP_EN_X_TWO_POS = REAL_ARITH `&0 < &2`;;

let RP_EN_X_Q_POS = prove
 (`forall x. &0 < &1 + x pow 2`,
  GEN_TAC THEN MP_TAC(SPEC `x:real` REAL_LE_POW_2) THEN REAL_ARITH_TAC);;

let RP_EN_X_XY_POS = prove
 (`forall x y. abs x < &1 /\ abs y < &1 ==> &0 < &1 - x * y`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `abs x * abs y < &1 * &1` MP_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL2 THEN ASM_REWRITE_TAC[REAL_ABS_POS];
    REWRITE_TAC[GSYM REAL_ABS_MUL] THEN REAL_ARITH_TAC]);;

let RP_EN_X_XS_POS = prove
 (`forall x s. &0 < s /\ s < &1 ==> &0 < &1 - &2 * x * s + x pow 2`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `x - s:real` REAL_LE_POW_2) THEN
  SUBGOAL_THEN `&0 < s * (&1 - s)` MP_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  POP_ASSUM MP_TAC THEN REAL_ARITH_TAC);;

let RP_EN_X_T_SUB = prove
 (`forall x y. rp_t y - rp_t x =
         &2 * (y - x) * (&1 - x * y) / ((&1 + x pow 2) * (&1 + y pow 2))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[rp_t] THEN
  MP_TAC(SPEC `x:real` RP_EN_X_Q_POS) THEN MP_TAC(SPEC `y:real` RP_EN_X_Q_POS) THEN
  CONV_TAC REAL_FIELD);;

let RP_EN_X_LOG_TDIFF = prove
 (`forall x y. abs x < &1 /\ abs y < &1 /\ ~(x = y)
         ==> &0 < abs(rp_t y - rp_t x) /\
             log(abs(rp_t y - rp_t x)) =
             ((log(&2) + log(abs(y - x))) + log(&1 - x * y)) -
             (log(&1 + x pow 2) + log(&1 + y pow 2))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC `x:real` RP_EN_X_Q_POS) THEN MP_TAC(SPEC `y:real` RP_EN_X_Q_POS) THEN
  MP_TAC(SPECL [`x:real`; `y:real`] RP_EN_X_XY_POS) THEN ASM_REWRITE_TAC[] THEN
  REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `&0 < abs(y - x)` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_ABS_NZ; REAL_SUB_0] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < abs(y - x) * (&1 - x * y)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_MUL]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &2 * abs(y - x) * (&1 - x * y)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_MUL; RP_EN_X_TWO_POS]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < (&1 + x pow 2) * (&1 + y pow 2)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_MUL]; ALL_TAC] THEN
  SUBGOAL_THEN `abs(rp_t y - rp_t x) =
     (&2 * abs(y - x) * (&1 - x * y)) / ((&1 + x pow 2) * (&1 + y pow 2))`
  SUBST1_TAC THENL
   [REWRITE_TAC[RP_EN_X_T_SUB; real_div; REAL_ABS_MUL; REAL_ABS_INV; REAL_ABS_NUM] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < a ==> abs a = a`] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[LOG_DIV; LOG_MUL; REAL_LT_DIV; RP_EN_X_TWO_POS] THEN
  REAL_ARITH_TAC);;

let RP_EN_X_LOG_TABS = prove
 (`forall x. ~(x = &0)
       ==> &0 < abs(rp_t x) /\
           log(abs(rp_t x)) = (log(&2) + log(abs x)) - log(&1 + x pow 2)`,
  GEN_TAC THEN DISCH_TAC THEN MP_TAC(SPEC `x:real` RP_EN_X_Q_POS) THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 < abs x` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[GSYM REAL_ABS_NZ]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &2 * abs x` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_MUL; RP_EN_X_TWO_POS]; ALL_TAC] THEN
  SUBGOAL_THEN `abs(rp_t x) = (&2 * abs x) / (&1 + x pow 2)` SUBST1_TAC THENL
   [REWRITE_TAC[rp_t; real_div; REAL_ABS_MUL; REAL_ABS_INV; REAL_ABS_NUM] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < a ==> abs a = a`] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[LOG_DIV; LOG_MUL; REAL_LT_DIV; RP_EN_X_TWO_POS]);;

let RP_EN_X_LOG_TONE = prove
 (`forall x. x < &1
       ==> &0 < &1 - rp_t x /\
           log(&1 - rp_t x) = &2 * log(&1 - x) - log(&1 + x pow 2)`,
  GEN_TAC THEN DISCH_TAC THEN MP_TAC(SPEC `x:real` RP_EN_X_Q_POS) THEN DISCH_TAC THEN
  SUBGOAL_THEN `&1 - rp_t x = (&1 - x) pow 2 / (&1 + x pow 2)` SUBST1_TAC THENL
   [REWRITE_TAC[rp_t] THEN POP_ASSUM MP_TAC THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &1 - x` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < (&1 - x) pow 2` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_POW_LT]; ALL_TAC] THEN
  ASM_SIMP_TAC[LOG_DIV; LOG_POW; REAL_LT_DIV]);;

let RP_EN_X_LOG_TS = prove
 (`forall x s. &0 < s /\ s < &1
         ==> &0 < &1 - rp_t x * s /\
             log(&1 - rp_t x * s) =
             log(&1 - &2 * x * s + x pow 2) - log(&1 + x pow 2)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN MP_TAC(SPEC `x:real` RP_EN_X_Q_POS) THEN
  DISCH_TAC THEN
  MP_TAC(SPECL [`x:real`; `s:real`] RP_EN_X_XS_POS) THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `&1 - rp_t x * s = (&1 - &2 * x * s + x pow 2) / (&1 + x pow 2)`
  SUBST1_TAC THENL
   [REWRITE_TAC[rp_t] THEN UNDISCH_TAC `&0 < &1 + x pow 2` THEN
    CONV_TAC REAL_FIELD; ALL_TAC] THEN
  ASM_SIMP_TAC[LOG_DIV; REAL_LT_DIV]);;

let RP_EN_X_INV_SUB = REAL_FIELD
 `forall x y:real. ~(x = &0) /\ ~(y = &0) ==> inv y - inv x = (x - y) / (x * y)`;;

let RP_EN_X_LOG_INVDIFF = prove
 (`forall x y. ~(x = &0) /\ ~(y = &0) /\ ~(x = y)
         ==> &0 < abs(inv y - inv x) /\
             log(abs(inv y - inv x)) =
             log(abs(y - x)) - (log(abs x) + log(abs y))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < abs x /\ &0 < abs y /\ &0 < abs(y - x)` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_ABS_NZ; REAL_SUB_0] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < abs x * abs y` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_MUL]; ALL_TAC] THEN
  SUBGOAL_THEN `abs(inv y - inv x) = abs(y - x) / (abs x * abs y)` SUBST1_TAC THENL
   [ASM_SIMP_TAC[RP_EN_X_INV_SUB] THEN
     (REWRITE_TAC[REAL_ABS_DIV; REAL_ABS_MUL] THEN
      AP_THM_TAC THEN AP_TERM_TAC THEN MATCH_ACCEPT_TAC REAL_ABS_SUB); ALL_TAC] THEN
  ASM_SIMP_TAC[LOG_DIV; LOG_MUL; REAL_LT_DIV]);;

(* ------------------------------------------------------------------------- *)
(* Unpacking configurations.                                                 *)
(* ------------------------------------------------------------------------- *)

let RP_EN_X_CONFIG = prove
 (`forall N x s. rp_config N x s
           ==> (forall i. i < 48 * N ==> abs(x i) < &1 /\ x i < &1 /\ ~(x i = &0)) /\
               (forall i j. i < j /\ j < 48 * N ==> ~(x i = x j)) /\
               (forall j. j < 48 * N ==> &0 < s j /\ s j < &1) /\
               (forall i j. i < j /\ j < 48 * N ==> ~(s i = s j))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[rp_config; rp_nodes] THEN STRIP_TAC THEN
  REPEAT CONJ_TAC THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `--(&1) < (x:num->real) i /\ x i < &1 /\ ~(x i = &0)` MP_TAC THENL
     [ASM_SIMP_TAC[]; REAL_ARITH_TAC];
    MAP_EVERY X_GEN_TAC [`i:num`; `j:num`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `i < 48 * N /\ ~(i:num = j)` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `i:num < j` THEN UNDISCH_TAC `j < 48 * N` THEN ARITH_TAC;
      ASM_MESON_TAC[]];
    ASM_REWRITE_TAC[];
    MAP_EVERY X_GEN_TAC [`i:num`; `j:num`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `i < 48 * N /\ ~(i:num = j)` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `i:num < j` THEN UNDISCH_TAC `j < 48 * N` THEN ARITH_TAC;
      ASM_MESON_TAC[]]]);;

(* ------------------------------------------------------------------------- *)
(* The logarithms of the five factors of J.                                  *)
(* ------------------------------------------------------------------------- *)

(* Linear arithmetic treating finite sums as atoms up to alpha-conversion:  *)
(* all (closed) sum / rp_en_psum subterms are generalized first.            *)
let RP_EN_X_GEN_SUMS_TAC =
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

let RP_EN_X_ARITH_TAC = RP_EN_X_GEN_SUMS_TAC THEN REAL_ARITH_TAC;;

let RP_EN_X_LOGA = prove
 (`forall n (x:num->real).
      (forall i. i < n ==> abs(x i) < &1) /\ (forall i j. i < j /\ j < n ==> ~(x i = x j))
      ==> &0 < abs(rp_vdm n (\i. rp_t(x i))) /\
          log(abs(rp_vdm n (\i. rp_t(x i)))) =
          &n * (&n - &1) / &2 * log(&2) +
          rp_en_psum n (\i j. log(abs(x j - x i))) +
          rp_en_psum n (\i j. log(&1 - x i * x j)) -
          (&n - &1) * sum {i | i < n} (\i. log(&1 + x i pow 2))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`n:num`; `\i. rp_t((x:num->real) i)`] RP_EN_X_LOG_VDM) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(SPECL [`(x:num->real) i`; `(x:num->real) j`] RP_EN_X_LOG_TDIFF) THEN
    ANTS_TAC THENL
     [SUBGOAL_THEN `i:num < n` ASSUME_TAC THENL
       [UNDISCH_TAC `i:num < j` THEN UNDISCH_TAC `j:num < n` THEN ARITH_TAC;
        ASM_SIMP_TAC[]]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `rp_en_psum n (\i j. log(abs(rp_t((x:num->real) j) - rp_t(x i)))) =
    rp_en_psum n (\i j. ((log(&2) + log(abs(x j - x i))) + log(&1 - x i * x j)) -
                        (log(&1 + x i pow 2) + log(&1 + x j pow 2)))`
  SUBST1_TAC THENL
   [MATCH_MP_TAC RP_EN_X_PSUM_EQ THEN REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
    MP_TAC(SPECL [`(x:num->real) i`; `(x:num->real) j`] RP_EN_X_LOG_TDIFF) THEN
    ANTS_TAC THENL
     [SUBGOAL_THEN `i:num < n` ASSUME_TAC THENL
       [UNDISCH_TAC `i:num < j` THEN UNDISCH_TAC `j:num < n` THEN ARITH_TAC;
        ASM_SIMP_TAC[]]; ALL_TAC] THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[RP_EN_PSUM_SUB; RP_EN_PSUM_ADD; RP_EN_PSUM_CONST; RP_EN_X_PSUM_PAIR] THEN
  RP_EN_X_ARITH_TAC);;

let RP_EN_X_LOGC = prove
 (`forall n (x:num->real) (s:num->real).
      (forall j. j < n ==> &0 < s j /\ s j < &1)
      ==> &0 < product {i | i < n}
                 (\i. product {j | j < n} (\j. &1 - rp_t (x i) * s j)) /\
          log(product {i | i < n}
                 (\i. product {j | j < n} (\j. &1 - rp_t (x i) * s j))) =
          sum {i | i < n}
            (\i. sum {j | j < n} (\j. log(&1 - &2 * x i * s j + x i pow 2))) -
          &n * sum {i | i < n} (\i. log(&1 + x i pow 2))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `forall i j. j < (n:num) ==> &0 < &1 - rp_t ((x:num->real) i) * (s:num->real) j /\
                 log(&1 - rp_t (x i) * s j) =
                 log(&1 - &2 * x i * s j + x i pow 2) - log(&1 + x i pow 2)`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC RP_EN_X_LOG_TS THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `forall i. &0 < product {j | j < (n:num)} (\j. &1 - rp_t ((x:num->real) i) * (s:num->real) j)`
  ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC RP_EN_X_PROD_POS THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC RP_EN_X_PROD_POS THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[RP_EN_X_LOG_PROD] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `sum {i | i < n}
     (\i. sum {j | j < (n:num)} (\j. log(&1 - &2 * (x:num->real) i * (s:num->real) j + x i pow 2) -
                               log(&1 + x i pow 2)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC RP_EN_X_SUM_EQ THEN REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC RP_EN_X_SUM_EQ THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SIMP_TAC[SUM_SUB; FINITE_NUMSEG_LT; SUM_CONST; CARD_NUMSEG_LT; SUM_LMUL]);;

let RP_EN_X_LOGD = prove
 (`forall n (s:num->real) a b.
      (forall j. j < n ==> &0 < s j /\ s j < &1)
      ==> &0 < product {j | j < n} (\j. s j pow a * (&1 - s j) pow b) /\
          log(product {j | j < n} (\j. s j pow a * (&1 - s j) pow b)) =
          &a * sum {j | j < n} (\j. log(s j)) +
          &b * sum {j | j < n} (\j. log(&1 - s j))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `forall j. j < (n:num) ==> &0 < (s:num->real) j pow a * (&1 - s j) pow b /\
                  log(s j pow a * (&1 - s j) pow b) =
                  &a * log(s j) + &b * log(&1 - s j)`
  ASSUME_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN
    SUBGOAL_THEN `&0 < (s:num->real) j /\ &0 < &1 - s j` STRIP_ASSUME_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `j:num`) THEN ASM_REWRITE_TAC[] THEN
      REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LT_MUL; REAL_POW_LT; LOG_MUL; LOG_POW];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC RP_EN_X_PROD_POS THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[RP_EN_X_LOG_PROD] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `sum {j | j < (n:num)} (\j. &a * log((s:num->real) j) + &b * log(&1 - s j))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC RP_EN_X_SUM_EQ THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  SIMP_TAC[SUM_ADD; FINITE_NUMSEG_LT; SUM_LMUL]);;

let RP_EN_X_LOGE = prove
 (`forall n (x:num->real) c d.
      (forall i. i < n ==> x i < &1 /\ ~(x i = &0))
      ==> &0 < product {i | i < n}
                 (\i. abs(rp_t (x i)) pow c * (&1 - rp_t (x i)) pow d) /\
          log(product {i | i < n}
                 (\i. abs(rp_t (x i)) pow c * (&1 - rp_t (x i)) pow d)) =
          &c * &n * log(&2) +
          &c * sum {i | i < n} (\i. log(abs(x i))) +
          &2 * &d * sum {i | i < n} (\i. log(&1 - x i)) -
          (&c + &d) * sum {i | i < n} (\i. log(&1 + x i pow 2))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `forall i. i < (n:num) ==>
      &0 < abs(rp_t ((x:num->real) i)) pow c * (&1 - rp_t (x i)) pow d /\
      log(abs(rp_t (x i)) pow c * (&1 - rp_t (x i)) pow d) =
      &c * ((log(&2) + log(abs(x i))) - log(&1 + x i pow 2)) +
      &d * (&2 * log(&1 - x i) - log(&1 + x i pow 2))`
  ASSUME_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(SPEC `(x:num->real) i` RP_EN_X_LOG_TABS) THEN
    MP_TAC(SPEC `(x:num->real) i` RP_EN_X_LOG_TONE) THEN
    ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    ASM_SIMP_TAC[REAL_LT_MUL; REAL_POW_LT; LOG_MUL; LOG_POW];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC RP_EN_X_PROD_POS THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[RP_EN_X_LOG_PROD] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `sum {i | i < (n:num)} (\i.
      &c * ((log(&2) + log(abs((x:num->real) i))) - log(&1 + x i pow 2)) +
      &d * (&2 * log(&1 - x i) - log(&1 + x i pow 2)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC RP_EN_X_SUM_EQ THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  SIMP_TAC[SUM_ADD; SUM_SUB; FINITE_NUMSEG_LT; SUM_LMUL; SUM_CONST; CARD_NUMSEG_LT] THEN
  RP_EN_X_ARITH_TAC);;

let RP_EN_X_LOG5 = prove
 (`forall a b c d e. &0 < a /\ &0 < b /\ &0 < c /\ &0 < d /\ &0 < e
               ==> &0 < a * b pow 2 / c * d * e /\
                   log(a * b pow 2 / c * d * e) =
                   log a + &2 * log b - log c + log d + log e`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < b pow 2` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_POW_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < b pow 2 / c` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_DIV]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < d * e` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_MUL]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < b pow 2 / c * d * e` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_MUL]; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LT_MUL; LOG_MUL; LOG_DIV; LOG_POW] THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* log J.                                                                    *)
(* ------------------------------------------------------------------------- *)

let RP_EN_X_LOG_J = prove
 (`forall N x s. rp_config N x s
     ==> &0 < rp_J N x s /\
         log(rp_J N x s) =
         &(48 * N) * (&(48 * N) - &1) / &2 * log(&2) +
         &(63 * N - 1) * &(48 * N) * log(&2) +
         rp_en_psum (48 * N) (\i j. log(abs(x j - x i))) +
         rp_en_psum (48 * N) (\i j. log(&1 - x i * x j)) +
         &2 * rp_en_psum (48 * N) (\i j. log(abs(s j - s i))) -
         sum {i | i < 48 * N}
           (\i. sum {j | j < 48 * N} (\j. log(&1 - &2 * x i * s j + x i pow 2))) +
         (&1 - &(63 * N - 1) - &(2 * N)) *
           sum {i | i < 48 * N} (\i. log(&1 + x i pow 2)) +
         &(63 * N - 1) * sum {i | i < 48 * N} (\i. log(abs(x i))) +
         &2 * &(2 * N) * sum {i | i < 48 * N} (\i. log(&1 - x i)) +
         &(7 * N) * sum {j | j < 48 * N} (\j. log(s j)) +
         &(4 * N) * sum {j | j < 48 * N} (\j. log(&1 - s j))`,
  REPEAT GEN_TAC THEN DISCH_THEN(STRIP_ASSUME_TAC o MATCH_MP RP_EN_X_CONFIG) THEN
  MP_TAC(ISPECL [`48 * N`; `x:num->real`] RP_EN_X_LOGA) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`48 * N`; `s:num->real`] RP_EN_X_LOG_VDM) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`48 * N`; `x:num->real`; `s:num->real`] RP_EN_X_LOGC) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`48 * N`; `s:num->real`; `7 * N`; `4 * N`] RP_EN_X_LOGD) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`48 * N`; `x:num->real`; `63 * N - 1`; `2 * N`] RP_EN_X_LOGE) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[]; STRIP_TAC] THEN
  REWRITE_TAC[rp_J] THEN
  SUBGOAL_THEN `rp_vdm (48 * N) s pow 2 = abs(rp_vdm (48 * N) s) pow 2`
  SUBST1_TAC THENL [REWRITE_TAC[REAL_POW2_ABS]; ALL_TAC] THEN
  ASM_SIMP_TAC[RP_EN_X_LOG5] THEN RP_EN_X_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The extra factors of I_2 and I_1.                                         *)
(* ------------------------------------------------------------------------- *)

let RP_EN_X_LOGV_INV = prove
 (`forall n (x:num->real).
      (forall i. i < n ==> ~(x i = &0)) /\ (forall i j. i < j /\ j < n ==> ~(x i = x j))
      ==> &0 < abs(rp_vdm n (\i. inv(x i))) /\
          log(abs(rp_vdm n (\i. inv(x i)))) =
          rp_en_psum n (\i j. log(abs(x j - x i))) -
          (&n - &1) * sum {i | i < n} (\i. log(abs(x i)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `forall i j. i < j /\ j < n ==>
     &0 < abs(inv((x:num->real) j) - inv(x i)) /\
     log(abs(inv(x j) - inv(x i))) =
     log(abs(x j - x i)) - (log(abs(x i)) + log(abs(x j)))`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC RP_EN_X_LOG_INVDIFF THEN
    SUBGOAL_THEN `i:num < n` ASSUME_TAC THENL
     [UNDISCH_TAC `i:num < j` THEN UNDISCH_TAC `j:num < n` THEN ARITH_TAC;
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`n:num`; `\i. inv((x:num->real) i)`] RP_EN_X_LOG_VDM) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPECL [`i:num`; `j:num`]) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `rp_en_psum n (\i j. log(abs(inv((x:num->real) j) - inv(x i)))) =
    rp_en_psum n (\i j. log(abs(x j - x i)) - (log(abs(x i)) + log(abs(x j))))`
  SUBST1_TAC THENL
   [MATCH_MP_TAC RP_EN_X_PSUM_EQ THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[RP_EN_PSUM_SUB; RP_EN_PSUM_ADD; RP_EN_X_PSUM_PAIR]);;

let RP_EN_X_LOGP_ABS = prove
 (`forall n (x:num->real) m.
      (forall i. i < n ==> ~(x i = &0))
      ==> &0 < product {i | i < n} (\i. abs(x i) pow m) /\
          log(product {i | i < n} (\i. abs(x i) pow m)) =
          &m * sum {i | i < n} (\i. log(abs(x i)))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `forall i. i < (n:num) ==> &0 < abs((x:num->real) i) pow m /\
                    log(abs(x i) pow m) = &m * log(abs(x i))`
  ASSUME_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN
    SUBGOAL_THEN `&0 < abs((x:num->real) i)` ASSUME_TAC THENL
     [REWRITE_TAC[GSYM REAL_ABS_NZ] THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_POW_LT; LOG_POW];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC RP_EN_X_PROD_POS THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[RP_EN_X_LOG_PROD] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `sum {i | i < (n:num)} (\i. &m * log(abs((x:num->real) i)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC RP_EN_X_SUM_EQ THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[SUM_LMUL]);;

let RP_EN_X_LOGP_I1 = prove
 (`forall n (x:num->real) a b.
      (forall i. i < n ==> ~(x i = &0))
      ==> &0 < product {i | i < n}
                 (\i. sqrt(&1 + x i pow 2) pow a * inv(abs(x i)) pow b) /\
          log(product {i | i < n}
                 (\i. sqrt(&1 + x i pow 2) pow a * inv(abs(x i)) pow b)) =
          &a / &2 * sum {i | i < n} (\i. log(&1 + x i pow 2)) -
          &b * sum {i | i < n} (\i. log(abs(x i)))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `forall i. i < (n:num) ==>
      &0 < sqrt(&1 + (x:num->real) i pow 2) pow a * inv(abs(x i)) pow b /\
      log(sqrt(&1 + x i pow 2) pow a * inv(abs(x i)) pow b) =
      &a / &2 * log(&1 + x i pow 2) - &b * log(abs(x i))`
  ASSUME_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN
    SUBGOAL_THEN `&0 < abs((x:num->real) i)` ASSUME_TAC THENL
     [REWRITE_TAC[GSYM REAL_ABS_NZ] THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
    MP_TAC(SPEC `(x:num->real) i` RP_EN_X_Q_POS) THEN DISCH_TAC THEN
    SUBGOAL_THEN `&0 < sqrt(&1 + (x:num->real) i pow 2)` ASSUME_TAC THENL
     [ASM_SIMP_TAC[SQRT_POS_LT]; ALL_TAC] THEN
    SUBGOAL_THEN `&0 < inv(abs((x:num->real) i))` ASSUME_TAC THENL
     [ASM_SIMP_TAC[REAL_LT_INV]; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_POW_LT; REAL_LT_MUL; LOG_MUL; LOG_POW; LOG_SQRT; LOG_INV] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC RP_EN_X_PROD_POS THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[RP_EN_X_LOG_PROD] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `sum {i | i < (n:num)} (\i. &a / &2 * log(&1 + (x:num->real) i pow 2) -
                                       &b * log(abs(x i)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC RP_EN_X_SUM_EQ THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  SIMP_TAC[SUM_SUB; FINITE_NUMSEG_LT; SUM_LMUL]);;

let RP_EN_X_LOG_I2 = prove
 (`forall N x s. rp_config N x s
     ==> &0 < rp_I2 N x s /\
         log(rp_I2 N x s) =
         log(rp_J N x s) + rp_en_psum (48 * N) (\i j. log(abs(x j - x i))) -
         (&(48 * N) - &1) * sum {i | i < 48 * N} (\i. log(abs(x i))) +
         &(4 * N) * sum {i | i < 48 * N} (\i. log(abs(x i)))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP RP_EN_X_CONFIG) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o CONJUNCT1 o MATCH_MP RP_EN_X_LOG_J) THEN
  MP_TAC(ISPECL [`48 * N`; `x:num->real`] RP_EN_X_LOGV_INV) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`48 * N`; `x:num->real`; `4 * N`] RP_EN_X_LOGP_ABS) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[]; STRIP_TAC] THEN
  REWRITE_TAC[rp_I2] THEN
  SUBGOAL_THEN `&0 < abs(rp_vdm (48 * N) (\i. inv(x i))) *
                product {i | i < 48 * N} (\i. abs(x i) pow (4 * N))`
  ASSUME_TAC THENL [ASM_SIMP_TAC[REAL_LT_MUL]; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LT_MUL; LOG_MUL] THEN RP_EN_X_ARITH_TAC);;

let RP_EN_X_LOG_I1 = prove
 (`forall N x s. rp_config N x s
     ==> &0 < rp_I1 N x s /\
         log(rp_I1 N x s) =
         log(rp_J N x s) -
         &(((48 * N) * (48 * N - 1)) DIV 2) * log(&2) +
         &(48 * N - 1) / &2 * sum {i | i < 48 * N} (\i. log(&1 + x i pow 2)) -
         &(44 * N - 1) * sum {i | i < 48 * N} (\i. log(abs(x i)))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP RP_EN_X_CONFIG) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o CONJUNCT1 o MATCH_MP RP_EN_X_LOG_J) THEN
  MP_TAC(ISPECL [`48 * N`; `x:num->real`; `48 * N - 1`; `44 * N - 1`]
    RP_EN_X_LOGP_I1) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[]; STRIP_TAC] THEN
  REWRITE_TAC[rp_I1] THEN
  SUBGOAL_THEN `&0 < inv(&2) pow (((48 * N) * (48 * N - 1)) DIV 2)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LT THEN MATCH_MP_TAC REAL_LT_INV THEN
    REWRITE_TAC[RP_EN_X_TWO_POS]; ALL_TAC] THEN
  ABBREV_TAC `P = product {i | i < 48 * N}
      (\i. sqrt(&1 + x i pow 2) pow (48 * N - 1) * inv(abs(x i)) pow (44 * N - 1))` THEN
  SUBGOAL_THEN `&0 < inv(&2) pow (((48 * N) * (48 * N - 1)) DIV 2) * P`
  ASSUME_TAC THENL [ASM_SIMP_TAC[REAL_LT_MUL]; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LT_MUL; LOG_MUL; LOG_POW; REAL_LT_INV; RP_EN_X_TWO_POS;
               LOG_INV] THEN
  RP_EN_X_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Main results.                                                             *)
(* ------------------------------------------------------------------------- *)

let RP_EN_X_I2_POS = prove
 (`forall N x s. 1 <= N /\ rp_config N x s ==> &0 < rp_I2 N x s`,
  MESON_TAC[RP_EN_X_LOG_I2]);;

let RP_EN_X_I1_POS = prove
 (`forall N x s. 1 <= N /\ rp_config N x s ==> &0 < rp_I1 N x s`,
  MESON_TAC[RP_EN_X_LOG_I1]);;

let RP_EN_X_CASTS = prove
 (`forall N. 1 <= N
       ==> &(63 * N - 1) = &63 * &N - &1 /\
           &(48 * N - 1) = &48 * &N - &1 /\
           &(44 * N - 1) = &44 * &N - &1 /\
           &(((48 * N) * (48 * N - 1)) DIV 2) = &24 * &N * (&48 * &N - &1)`,
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `1 <= 63 * N /\ 1 <= 48 * N /\ 1 <= 44 * N` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `1 <= N` THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `((48 * N) * (48 * N - 1)) DIV 2 = 24 * N * (48 * N - 1)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC DIV_UNIQ THEN EXISTS_TAC `0` THEN ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[GSYM REAL_OF_NUM_SUB; GSYM REAL_OF_NUM_MUL] THEN
  REWRITE_TAC[REAL_OF_NUM_MUL]);;

let RP_EN_X_FINISH_TAC =
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP RP_EN_X_LOG_J) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP RP_EN_X_CASTS) THEN
  ASM_REWRITE_TAC[rp_en_F; rp_en_W; rp_en_Ws] THEN
  SIMP_TAC[SUM_ADD; SUM_SUB; SUM_LMUL; FINITE_NUMSEG_LT] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_MUL] THEN RP_EN_X_GEN_SUMS_TAC THEN
  SUBGOAL_THEN `&0 < &N` MP_TAC THENL
   [ASM_SIMP_TAC[REAL_OF_NUM_LT; ARITH_RULE `1 <= N ==> 0 < N`]; ALL_TAC] THEN
  CONV_TAC REAL_FIELD;;

let RP_EN_X_I2 = prove
 (`forall N x s. 1 <= N /\ rp_config N x s
         ==> log(rp_I2 N x s) / &(48 * N) pow 2 - log(&2) / &2 =
             rp_en_F (&2) N x s`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP RP_EN_X_LOG_I2) THEN
  RP_EN_X_FINISH_TAC);;

let RP_EN_X_I1 = prove
 (`forall N x s. 1 <= N /\ rp_config N x s
         ==> log(rp_I1 N x s) / &(48 * N) pow 2 - log(&2) / &2 =
             rp_en_F (&1) N x s`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP RP_EN_X_LOG_I1) THEN
  RP_EN_X_FINISH_TAC);;
