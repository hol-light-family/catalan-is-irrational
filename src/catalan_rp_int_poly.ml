(* ========================================================================= *)
(* rp_int_poly_: the row identity RP_INT_POLY_ID expressing the combined    *)
(* row function of the real-place integrand in the x coordinate.            *)
(* ========================================================================= *)

needs "src/catalan_rp_defs.ml";;

(* ------------------------------------------------------------------------- *)
(* Generic sum lemmas.                                                       *)
(* ------------------------------------------------------------------------- *)

let RP_INT_POLY_SHIFT = prove
 (`forall g:num->real n y. 1 <= n ==>
    sum(0..n) (\k. (if k = 0 then &0 else g (k - 1)) * y pow k) =
    y * sum(0..n-1) (\k. g k * y pow k)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `exists m. n = m + 1` (CHOOSE_THEN SUBST1_TAC) THENL
   [EXISTS_TAC `n - 1` THEN ASM_ARITH_TAC; ALL_TAC] THEN
  GEN_REWRITE_TAC LAND_CONV
   [MATCH_MP SUM_CLAUSES_LEFT (SPEC `m + 1` LE_0)] THEN
  REWRITE_TAC[SUM_OFFSET; ADD_EQ_0; ARITH_EQ; ADD_SUB; REAL_MUL_LZERO;
              REAL_ADD_LID; REAL_POW_ADD; REAL_POW_1] THEN
  REWRITE_TAC[GSYM SUM_LMUL] THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN REAL_ARITH_TAC);;

let RP_INT_POLY_DELTA = prove
 (`forall j c y n. j <= n ==>
    sum(0..n) (\k. (if k = j then c else &0) * y pow k) = c * y pow j`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `sum(0..n) (\k. if k = j then c * y pow j else &0)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_EQ_NUMSEG THEN REPEAT STRIP_TAC THEN BETA_TAC THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[REAL_MUL_LZERO];
    REWRITE_TAC[SUM_DELTA; IN_NUMSEG] THEN ASM_REWRITE_TAC[LE_0]]);;

let RP_INT_POLY_REC = prove
 (`forall f:num->num->real d n y.
    (forall k. f (SUC(SUC d)) k =
         (if k = 0 then &0 else &2 * f (SUC d) (k - 1)) - f d k) /\
    1 <= n
    ==> sum(0..n) (\k. f (SUC(SUC d)) k * y pow k) =
        &2 * y * sum(0..n-1) (\k. f (SUC d) k * y pow k) -
        sum(0..n) (\k. f d k * y pow k)`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[REAL_SUB_RDISTRIB; SUM_SUB_NUMSEG] THEN
  ASM_SIMP_TAC[RP_INT_POLY_SHIFT] THEN REWRITE_TAC[GSYM SUM_LMUL] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Chebyshev values at (z + 1/z)/2.                                         *)
(* ------------------------------------------------------------------------- *)

let RP_INT_POLY_T = prove
 (`forall z d n. ~(z = &0) /\ d <= n
    ==> &2 * sum(0..n) (\k. cheb_T d k * ((z + inv z) / &2) pow k) =
        z pow d + inv z pow d`,
  GEN_TAC THEN ASM_CASES_TAC `z = &0` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `forall d. (forall n. d <= n
             ==> &2 * sum(0..n) (\k. cheb_T d k * ((z + inv z) / &2) pow k) =
                 z pow d + inv z pow d) /\
        (forall n. SUC d <= n
             ==> &2 * sum(0..n) (\k. cheb_T (SUC d) k *
                                     ((z + inv z) / &2) pow k) =
                 z pow (SUC d) + inv z pow (SUC d))`
   (fun th -> MESON_TAC[th]) THEN
  INDUCT_TAC THENL
   [REWRITE_TAC[cheb_T] THEN CONJ_TAC THEN REPEAT STRIP_TAC THEN
    ASM_SIMP_TAC[RP_INT_POLY_DELTA; LE_0;
                 ARITH_RULE `SUC 0 <= n ==> 1 <= n`] THEN
    REWRITE_TAC[real_pow; REAL_POW_1] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`cheb_T`; `d:num`; `n:num`; `(z + inv z) / &2`]
     RP_INT_POLY_REC) THEN
  ANTS_TAC THENL [REWRITE_TAC[cheb_T] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `n - 1`) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_TAC] THEN
  REWRITE_TAC[REAL_ARITH
   `&2 * (&2 * (a / &2) * s1 - s0) = a * (&2 * s1) - &2 * s0`] THEN
  ASM_REWRITE_TAC[real_pow] THEN
  MP_TAC(SPEC `z:real` REAL_MUL_RINV) THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC REAL_RING);;

let RP_INT_POLY_U = prove
 (`forall z d n. ~(z = &0) /\ d <= n
    ==> (z - inv z) *
        sum(0..n) (\k. cheb_U d k * ((z + inv z) / &2) pow k) =
        z pow (SUC d) - inv z pow (SUC d)`,
  GEN_TAC THEN ASM_CASES_TAC `z = &0` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `forall d. (forall n. d <= n
             ==> (z - inv z) *
                 sum(0..n) (\k. cheb_U d k * ((z + inv z) / &2) pow k) =
                 z pow (SUC d) - inv z pow (SUC d)) /\
        (forall n. SUC d <= n
             ==> (z - inv z) *
                 sum(0..n) (\k. cheb_U (SUC d) k *
                                ((z + inv z) / &2) pow k) =
                 z pow (SUC(SUC d)) - inv z pow (SUC(SUC d)))`
   (fun th -> MESON_TAC[th]) THEN
  INDUCT_TAC THENL
   [REWRITE_TAC[cheb_U] THEN CONJ_TAC THEN REPEAT STRIP_TAC THEN
    ASM_SIMP_TAC[RP_INT_POLY_DELTA; LE_0;
                 ARITH_RULE `SUC 0 <= n ==> 1 <= n`] THEN
    REWRITE_TAC[real_pow; REAL_POW_1] THEN
    MP_TAC(SPEC `z:real` REAL_MUL_RINV) THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC REAL_RING;
    ALL_TAC] THEN
  FIRST_X_ASSUM(CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`cheb_U`; `d:num`; `n:num`; `(z + inv z) / &2`]
     RP_INT_POLY_REC) THEN
  ANTS_TAC THENL [REWRITE_TAC[cheb_U] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `n - 1`) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_TAC] THEN
  REWRITE_TAC[REAL_ARITH
   `c * (&2 * (a / &2) * s1 - s0) = a * (c * s1) - c * s0`] THEN
  ASM_REWRITE_TAC[real_pow] THEN
  MP_TAC(SPEC `z:real` REAL_MUL_RINV) THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC REAL_RING);;
let RP_INT_POLY_REVC = prove
 (`forall C H c t. ~(t = &0) /\ 1 <= C /\ C - 1 <= H
    ==> sum(0..H) (\m. cat_revc C c m * t pow m) =
        t pow (C - 1) * sum(0..C-1) (\j. c j * inv t pow j)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\m. cat_revc C c m * t pow m`; `0..C-1`; `0..H`]
    SUM_SUPERSET) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[SUBSET_NUMSEG; IN_NUMSEG; cat_revc] THEN
    CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    REPEAT STRIP_TAC THEN COND_CASES_TAC THEN
    REWRITE_TAC[REAL_MUL_LZERO] THEN ASM_ARITH_TAC;
    DISCH_THEN SUBST1_TAC] THEN
  GEN_REWRITE_TAC LAND_CONV [SUM_REFLECT] THEN
  REWRITE_TAC[ARITH_RULE `~(n < 0)`; SUB_0; GSYM SUM_LMUL] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[cat_revc; ARITH_RULE `1 <= C /\ i <= C - 1 ==> C - 1 - i < C`;
    ARITH_RULE `i <= C - 1 ==> C - 1 - (C - 1 - i) = i`; REAL_POW_SUB;
    REAL_POW_INV] THEN
  REWRITE_TAC[real_div] THEN REAL_ARITH_TAC);;

let RP_INT_POLY_SHIFTV = prove
 (`forall v H (f:num->real). v <= H
    ==> sum(0..H) (\i. if v <= i then f i else &0) =
        sum(0..H-v) (\j. f(j + v))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\i. if v <= i then (f:num->real) i else &0`; `v..H`; `0..H`]
    SUM_SUPERSET) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[SUBSET_NUMSEG; IN_NUMSEG] THEN
    CONJ_TAC THENL [ARITH_TAC; ALL_TAC] THEN
    REPEAT STRIP_TAC THEN COND_CASES_TAC THEN ASM_ARITH_TAC;
    DISCH_THEN SUBST1_TAC] THEN
  ASM_SIMP_TAC[SUM_OFFSET_0] THEN
  REWRITE_TAC[ARITH_RULE `v <= i + v:num`]);;

let RP_INT_POLY_TRUNC = prove
 (`forall m n (c:num->real) t. m <= n /\ (forall j. m < j ==> c j = &0)
    ==> sum(0..n) (\j. c j * t pow j) = sum(0..m) (\j. c j * t pow j)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUM_SUPERSET THEN
  REWRITE_TAC[SUBSET_NUMSEG; IN_NUMSEG] THEN
  CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(c:num->real) x = &0` SUBST1_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    REWRITE_TAC[REAL_MUL_LZERO]]);;

let RP_INT_POLY_BINOM = prove
 (`forall h t. (&1 - t) pow h =
         sum(0..h) (\v. (--(&1)) pow v * &(binom(h,v)) * t pow v)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[REAL_ARITH `&1 - t = --(&1) * t + &1`; REAL_BINOMIAL_THEOREM;
              REAL_POW_ONE; REAL_MUL_RID; REAL_POW_MUL] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
  REAL_ARITH_TAC);;

let RP_INT_POLY_MULFAC = prove
 (`forall h H (c:num->real) t. h <= H /\ (forall j. H - h < j ==> c j = &0)
    ==> sum(0..H) (\i. cat_mulfac h c i * t pow i) =
        (&1 - t) pow h * sum(0..H-h) (\j. c j * t pow j)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[cat_mulfac; GSYM SUM_RMUL] THEN
  GEN_REWRITE_TAC LAND_CONV [SUM_SWAP_NUMSEG] THEN
  REWRITE_TAC[RP_INT_POLY_BINOM; GSYM SUM_RMUL] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `v:num` THEN STRIP_TAC THEN
  REWRITE_TAC[COND_RATOR; COND_RAND; REAL_MUL_LZERO] THEN
  SUBGOAL_THEN `v:num <= H` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[RP_INT_POLY_SHIFTV; ADD_SUB] THEN
  MP_TAC(ISPECL [`H - h:num`; `H - v:num`; `c:num->real`; `t:real`]
    RP_INT_POLY_TRUNC) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[GSYM SUM_LMUL; GSYM SUM_RMUL] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[REAL_POW_ADD] THEN REAL_ARITH_TAC);;

let RP_INT_POLY_ROWGEN = prove
 (`forall N c t. 1 <= N /\ ~(t = &0)
    ==> sum(0..65 * N)
          (\i. cat_mulfac (2 * N) (cat_revc (63 * N) c) i * t pow i) =
        (&1 - t) pow (2 * N) * t pow (63 * N - 1) *
        sum(0..63 * N - 1) (\j. c j * inv t pow j)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`2 * N`; `65 * N`; `cat_revc (63 * N) c`; `t:real`]
    RP_INT_POLY_MULFAC) THEN
  REWRITE_TAC[ARITH_RULE `65 * N - 2 * N = 63 * N`] THEN
  ANTS_TAC THENL
   [REWRITE_TAC[cat_revc] THEN CONJ_TAC THENL [ARITH_TAC; ALL_TAC] THEN
    REPEAT STRIP_TAC THEN COND_CASES_TAC THEN ASM_ARITH_TAC;
    DISCH_THEN SUBST1_TAC] THEN
  AP_TERM_TAC THEN MATCH_MP_TAC RP_INT_POLY_REVC THEN
  ASM_ARITH_TAC);;

let RP_INT_POLY_ROWP = prove
 (`forall N r t. 1 <= N /\ ~(t = &0)
    ==> cat_rowP N r t =
        (&1 - t) pow (2 * N) * t pow (63 * N - 1) *
        sum(0..63 * N - 1) (\j. cheb_T (cat_dist N r) j * inv t pow j)`,
  SIMP_TAC[cat_rowP; cat_poly; cat_pcoef; RP_INT_POLY_ROWGEN]);;

let RP_INT_POLY_ROWD = prove
 (`forall N r t. 1 <= N /\ ~(t = &0)
    ==> cat_rowD N r t =
        cat_sgn N r *
        ((&1 - t) pow (2 * N) * t pow (63 * N - 1) *
         sum(0..63 * N - 1) (\j. cheb_U (cat_dist N r - 1) j * inv t pow j))`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[cat_rowD; cat_poly; cat_dcoef; GSYM REAL_MUL_ASSOC; SUM_LMUL] THEN
  ASM_SIMP_TAC[RP_INT_POLY_ROWGEN] THEN REAL_ARITH_TAC);;

let RP_INT_POLY_POWSUB = prove
 (`forall x n d. ~(x = &0) /\ d <= n ==> x pow n * inv x pow d = x pow (n - d)`,
  SIMP_TAC[REAL_POW_SUB; real_div; REAL_POW_INV]);;

(* arithmetic using only the assumptions whose free variables are numbers *)
let rp_int_poly_num_tac : tactic = fun (asl,w as g) ->
  let ok th = forall (fun v -> type_of v = `:num`) (frees (concl th)) in
  (MAP_EVERY (MP_TAC o snd) (filter (ok o snd) asl) THEN ARITH_TAC) g;;

let rp_int_poly_pow_tac =
  FIRST [REWRITE_TAC[GSYM REAL_POW_ADD] THEN AP_TERM_TAC THEN rp_int_poly_num_tac;
         W(fun (_,w) -> let r = rand w in
            MP_TAC(SPECL [`x:real`; rand(lhand r); rand(rand r)] RP_INT_POLY_POWSUB)) THEN
         ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN rp_int_poly_num_tac;
           DISCH_THEN SUBST1_TAC THEN AP_TERM_TAC THEN rp_int_poly_num_tac]];;

let rp_int_poly_fin_tac =
  ASM_CASES_TAC `&0 < x` THEN ASM_REWRITE_TAC[rp_xif; rp_xin] THENL
   [ASM_SIMP_TAC[REAL_ARITH `&0 < x ==> ~(x < &0)`;
                 REAL_ARITH `&0 < x ==> abs x = x`];
    ASM_SIMP_TAC[REAL_ARITH `~(&0 < x) /\ ~(x = &0) ==> x < &0`;
                 REAL_ARITH `~(&0 < x) ==> abs x = --x`]] THEN
  SPEC_TAC(`(&2 / (&1 + x pow 2)) pow (63 * N - 1)`, `q:real`) THEN
  SPEC_TAC(`(&1 - rp_t x) pow (2 * N)`, `k:real`) THEN
  SPEC_TAC(`(&1 + x pow 2) pow 2`, `w:real`) THEN
  SPEC_TAC(`(x:real) pow (63 * N - 1)`, `xx:real`) THEN
  SPEC_TAC(`(x:real) pow d`, `a:real`) THEN
  SPEC_TAC(`inv(x:real) pow d`, `b:real`) THEN
  CONV_TAC REAL_FIELD;;

(* The row identity, with the intended exponents C-1+g-r = 67N-1-r and   *)
(* C-1+r-g = 59N-1+r written out explicitly.                                *)

let RP_INT_POLY_ID = prove
 (`forall N r x. 1 <= N /\ r < 48 * N /\ --(&1) <= x /\ x <= &1
   ==> &4 * abs x / (&1 + x pow 2) pow 2 * cat_rowP N r (rp_t x) -
       (if &0 < x
        then &3 / &2 * (&2 * (&1 - x pow 2) / (&1 + x pow 2) pow 2) *
             cat_rowD N r (rp_t x)
        else &0) =
       &4 * abs x / (&1 + x pow 2) pow 2 *
       ((&1 - x) pow 2 / (&1 + x pow 2)) pow (2 * N) *
       (&2 / (&1 + x pow 2)) pow (63 * N - 1) *
       (rp_xif x * x pow (67 * N - 1 - r) + rp_xin x * x pow (59 * N - 1 + r))`,
  (REPEAT STRIP_TAC) THEN
   (ASM_CASES_TAC `x = &0` THENL
   [ASM_REWRITE_TAC[REAL_ABS_0; REAL_LT_REFL;
                     REAL_MUL_RZERO; real_div;
                    REAL_MUL_LZERO; REAL_SUB_RZERO]; ALL_TAC]) THEN
   (SUBGOAL_THEN `&0 < &1 + (x:real) pow 2` ASSUME_TAC THENL
   [MP_TAC(SPEC `x:real` REAL_LE_POW_2) THEN REAL_ARITH_TAC; ALL_TAC]) THEN
   (SUBGOAL_THEN `~(rp_t x = &0)` ASSUME_TAC THENL
   [REWRITE_TAC[rp_t; real_div; REAL_ENTIRE; REAL_INV_EQ_0] THEN
    ASM_REAL_ARITH_TAC; ALL_TAC]) THEN
   (SUBGOAL_THEN `inv(rp_t x) = (x + inv x) / &2` ASSUME_TAC THENL
   [REWRITE_TAC[rp_t] THEN
    UNDISCH_TAC `&0 < &1 + x pow 2` THEN UNDISCH_TAC `~(x = &0)` THEN
    CONV_TAC REAL_FIELD; ALL_TAC]) THEN
   (SUBGOAL_THEN `(&1 - x) pow 2 / (&1 + x pow 2) = &1 - rp_t x` SUBST1_TAC THENL
   [REWRITE_TAC[rp_t] THEN UNDISCH_TAC `&0 < &1 + x pow 2` THEN
    CONV_TAC REAL_FIELD; ALL_TAC]) THEN
   (ASM_SIMP_TAC[RP_INT_POLY_ROWP; RP_INT_POLY_ROWD]) THEN
   (SUBGOAL_THEN `rp_t x pow (63 * N - 1) =
     (&2 / (&1 + x pow 2)) pow (63 * N - 1) * x pow (63 * N - 1)`
   SUBST1_TAC THENL
   [REWRITE_TAC[GSYM REAL_POW_MUL; rp_t] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[real_div] THEN REAL_ARITH_TAC; ALL_TAC]) THEN
   (ABBREV_TAC `d = cat_dist N r`) THEN
   (SUBGOAL_THEN `d <= 63 * N - 1` ASSUME_TAC THENL
   [EXPAND_TAC "d" THEN REWRITE_TAC[cat_dist] THEN rp_int_poly_num_tac; ALL_TAC]) THEN
   (ASM_REWRITE_TAC[]) THEN
   (ABBREV_TAC `ST = sum(0..63 * N - 1) (\j. cheb_T d j * ((x + inv x) / &2) pow j)`) THEN
   (ABBREV_TAC `SU = sum(0..63 * N - 1)
                (\j. cheb_U (d - 1) j * ((x + inv x) / &2) pow j)`) THEN
   (SUBGOAL_THEN `&2 * ST = (x:real) pow d + inv x pow d` ASSUME_TAC THENL
   [EXPAND_TAC "ST" THEN MATCH_MP_TAC RP_INT_POLY_T THEN ASM_REWRITE_TAC[];
    ALL_TAC]) THEN
   (SUBGOAL_THEN `1 <= d ==> (&1 - (x:real) pow 2) * SU = --x * (x pow d - inv x pow d)`
   ASSUME_TAC THENL
   [DISCH_TAC THEN
    MP_TAC(SPECL [`x:real`; `d - 1`; `63 * N - 1`] RP_INT_POLY_U) THEN
    ASM_SIMP_TAC[ARITH_RULE `1 <= d ==> SUC(d - 1) = d`;
                 ARITH_RULE `d <= n ==> d - 1 <= n`] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    MP_TAC(SPEC `x:real` REAL_MUL_RINV) THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC REAL_RING; ALL_TAC]) THEN
  ASM_CASES_TAC `r < 4 * N` THENL
  [(SUBGOAL_THEN `cat_sgn N r = --(&1)` SUBST1_TAC THENL
   [ASM_REWRITE_TAC[cat_sgn]; ALL_TAC]) THEN
   (SUBGOAL_THEN `r + d = 4 * N` ASSUME_TAC THENL
   [EXPAND_TAC "d" THEN REWRITE_TAC[cat_dist] THEN ASM_REWRITE_TAC[] THEN
    rp_int_poly_num_tac; ALL_TAC]) THEN
   (SUBGOAL_THEN `(x:real) pow (67 * N - 1 - r) = x pow (63 * N - 1) * x pow d`
    SUBST1_TAC THENL [rp_int_poly_pow_tac; ALL_TAC]) THEN
   (SUBGOAL_THEN `(x:real) pow (59 * N - 1 + r) = x pow (63 * N - 1) * inv x pow d`
    SUBST1_TAC THENL [rp_int_poly_pow_tac; ALL_TAC]) THEN
   (SUBGOAL_THEN `1 <= d` ASSUME_TAC THENL [rp_int_poly_num_tac; ALL_TAC]) THEN
   (UNDISCH_TAC `&2 * ST = (x:real) pow d + inv x pow d` THEN
  FIRST_X_ASSUM(fun th -> MP_TAC(MP th (ASSUME `1 <= d`)))) THEN
   (rp_int_poly_fin_tac);
   ALL_TAC] THEN
  ASM_CASES_TAC `r = 4 * N` THENL
  [(SUBGOAL_THEN `cat_sgn N r = &0` SUBST1_TAC THENL
   [ASM_REWRITE_TAC[cat_sgn]; ALL_TAC]) THEN
   (SUBGOAL_THEN `d = 0` SUBST_ALL_TAC THENL
   [EXPAND_TAC "d" THEN REWRITE_TAC[cat_dist] THEN ASM_REWRITE_TAC[] THEN
    rp_int_poly_num_tac; ALL_TAC]) THEN
   (SUBGOAL_THEN `(x:real) pow (67 * N - 1 - r) = x pow (63 * N - 1) /\
                (x:real) pow (59 * N - 1 + r) = x pow (63 * N - 1)`
    (CONJUNCTS_THEN SUBST1_TAC) THENL
   [CONJ_TAC THEN AP_TERM_TAC THEN rp_int_poly_num_tac; ALL_TAC]) THEN
   (UNDISCH_TAC `&2 * ST = (x:real) pow 0 + inv x pow 0` THEN
  REWRITE_TAC[real_pow]) THEN
   (rp_int_poly_fin_tac);
   (SUBGOAL_THEN `cat_sgn N r = &1` SUBST1_TAC THENL
   [ASM_REWRITE_TAC[cat_sgn]; ALL_TAC]) THEN
   (SUBGOAL_THEN `r = 4 * N + d` ASSUME_TAC THENL
   [EXPAND_TAC "d" THEN REWRITE_TAC[cat_dist] THEN ASM_REWRITE_TAC[] THEN
    rp_int_poly_num_tac; ALL_TAC]) THEN
   (SUBGOAL_THEN `(x:real) pow (67 * N - 1 - r) = x pow (63 * N - 1) * inv x pow d`
    SUBST1_TAC THENL [rp_int_poly_pow_tac; ALL_TAC]) THEN
   (SUBGOAL_THEN `(x:real) pow (59 * N - 1 + r) = x pow (63 * N - 1) * x pow d`
    SUBST1_TAC THENL [rp_int_poly_pow_tac; ALL_TAC]) THEN
   (SUBGOAL_THEN `1 <= d` ASSUME_TAC THENL [rp_int_poly_num_tac; ALL_TAC]) THEN
   (UNDISCH_TAC `&2 * ST = (x:real) pow d + inv x pow d` THEN
  FIRST_X_ASSUM(fun th -> MP_TAC(MP th (ASSUME `1 <= d`)))) THEN
   (rp_int_poly_fin_tac)]);;
