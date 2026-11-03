(* ========================================================================= *)
(* rp_alg: the algebraic identity RP_ALG_STMT (paper Equations (63)-(65)).   *)
(*   |rp_integrand| = prod w_i * prod |x_i|^-(44N-1) * |R'(x)| * J_n.        *)
(* ========================================================================= *)

needs "src/catalan_rp_alg_cauchy.ml";;

(* ------------------------------------------------------------------------- *)
(* (b) the psi determinant: det[s_j^(7N+k) (1-s_j)^(4N)] = prod ... V(s).    *)
(* ------------------------------------------------------------------------- *)

let RP_ALG_PSI_DET = prove
 (`forall N n s. ndet {i:num | i < n} (\j k. cat_psi N k (s j)) =
           product {j:num | j < n} (\j. s j pow (7 * N) * (&1 - s j) pow (4 * N)) *
           rp_vdm n s`,
  REPEAT GEN_TAC THEN
  TRANS_TAC EQ_TRANS
   `ndet {i:num | i < n}
      (\j k. (\j. s j pow (7 * N) * (&1 - s j) pow (4 * N)) j * s j pow k)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC RP_ALG_NDET_EQ THEN REWRITE_TAC[cat_psi; REAL_POW_ADD] THEN
    REAL_ARITH_TAC;
    SIMP_TAC[RP_ALG_NDET_ROWS_MUL; FINITE_NUMSEG_LT;
             RP_ALG_NDET_VANDERMONDE]]);;

(* ------------------------------------------------------------------------- *)
(* (c) column factor of the row matrix.                                      *)
(* ------------------------------------------------------------------------- *)

let rp_alg_c = new_definition
 `rp_alg_c N x =
    &4 * abs x / (&1 + x pow 2) pow 2 *
    ((&1 - x) pow 2 / (&1 + x pow 2)) pow (2 * N) *
    (&2 / (&1 + x pow 2)) pow (63 * N - 1) * x pow (19 * N)`;;

let RP_ALG_ROW_FACTOR = prove
 (`forall N r x. 1 <= N /\ r < 48 * N
           ==> rp_row N r x =
               (rp_xif x * x pow (48 * N - 1 - r) +
                rp_xin x * x pow (r + 40 * N - 1)) * rp_alg_c N x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[rp_row; rp_alg_c] THEN
  SUBGOAL_THEN `67 * N - 1 - r = 19 * N + (48 * N - 1 - r)` SUBST1_TAC THENL
   [UNDISCH_TAC `r < 48 * N` THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `59 * N - 1 + r = 19 * N + (r + 40 * N - 1)` SUBST1_TAC THENL
   [UNDISCH_TAC `1 <= N` THEN ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[REAL_POW_ADD] THEN
  MAP_EVERY (fun t -> SPEC_TAC(t,genvar(type_of t)))
   [`&4 * abs x / (&1 + x pow 2) pow 2`;
    `((&1 - x) pow 2 / (&1 + x pow 2)) pow (2 * N)`;
    `(&2 / (&1 + x pow 2)) pow (63 * N - 1)`;
    `x pow (19 * N)`; `x pow (48 * N - 1 - r)`; `x pow (r + 40 * N - 1)`;
    `rp_xif x`; `rp_xin x`] THEN
  CONV_TAC REAL_RING);;

let RP_ALG_ROWDET = prove
 (`forall N x. 1 <= N
         ==> ndet {i:num | i < 48 * N} (\r i. rp_row N r (x i)) =
             rp_R N x * product {i:num | i < 48 * N} (\i. rp_alg_c N (x i))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[rp_R] THEN
  TRANS_TAC EQ_TRANS
   `ndet {i:num | i < 48 * N}
      (\r i. (rp_xif (x i) * x i pow (48 * N - 1 - r) +
              rp_xin (x i) * x i pow (r + 40 * N - 1)) *
             (\i. rp_alg_c N (x i)) i)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC RP_ALG_NDET_EQ THEN REWRITE_TAC[IN_ELIM_THM] THEN
    REPEAT STRIP_TAC THEN ASM_SIMP_TAC[RP_ALG_ROW_FACTOR];
    SIMP_TAC[RP_ALG_NDET_COLUMNS_MUL; FINITE_NUMSEG_LT]]);;

(* ------------------------------------------------------------------------- *)
(* Absolute value of the column factor.                                      *)
(* ------------------------------------------------------------------------- *)

let RP_ALG_C_ABS = prove
 (`forall N x. 1 <= N /\ ~(x = &0)
         ==> abs(rp_alg_c N x) =
             (&4 * abs x / (&1 + x pow 2) pow 2) *
             inv(abs x) pow (44 * N - 1) *
             (abs(rp_t x) pow (63 * N - 1) * (&1 - rp_t x) pow (2 * N))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[rp_alg_c] THEN
  SUBGOAL_THEN `&0 < &1 + x pow 2` ASSUME_TAC THENL
   [MP_TAC(SPEC `x:real` REAL_LE_POW_2) THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(&1 - x) pow 2 / (&1 + x pow 2) = &1 - rp_t x` SUBST1_TAC THENL
   [REWRITE_TAC[rp_t] THEN UNDISCH_TAC `&0 < &1 + x pow 2` THEN
    CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  SUBGOAL_THEN `abs(rp_t x) = &2 / (&1 + x pow 2) * abs x` SUBST1_TAC THENL
   [REWRITE_TAC[rp_t; real_div; REAL_ABS_MUL; REAL_ABS_INV; REAL_ABS_NUM] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < a ==> abs a = a`] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_POW; REAL_POW_MUL] THEN
  SUBGOAL_THEN `abs(abs x / (&1 + x pow 2) pow 2) =
                abs x / (&1 + x pow 2) pow 2` SUBST1_TAC THENL
   [REWRITE_TAC[REAL_ABS_REFL] THEN
    MATCH_MP_TAC REAL_LE_DIV THEN REWRITE_TAC[REAL_ABS_POS; REAL_LE_POW_2];
    ALL_TAC] THEN
  REWRITE_TAC[REAL_ABS_NUM] THEN
  SUBGOAL_THEN `abs(&2 / (&1 + x pow 2)) = &2 / (&1 + x pow 2)` SUBST1_TAC THENL
   [REWRITE_TAC[REAL_ABS_REFL] THEN MATCH_MP_TAC REAL_LE_DIV THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `abs(&1 - rp_t x) pow (2 * N) = (&1 - rp_t x) pow (2 * N)`
  SUBST1_TAC THENL
   [REWRITE_TAC[GSYM REAL_POW_POW; REAL_POW2_ABS]; ALL_TAC] THEN
  SUBGOAL_THEN `abs x pow (63 * N - 1) =
                abs x pow (19 * N) * abs x pow (44 * N - 1)` SUBST1_TAC THENL
   [REWRITE_TAC[GSYM REAL_POW_ADD] THEN AP_TERM_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[REAL_POW_INV] THEN
  SUBGOAL_THEN `~(abs x pow (44 * N - 1) = &0)` MP_TAC THENL
   [ASM_REWRITE_TAC[REAL_POW_EQ_0; REAL_ABS_ZERO]; ALL_TAC] THEN
  MAP_EVERY (fun t -> SPEC_TAC(t,genvar(type_of t)))
   [`(&1 - rp_t x) pow (2 * N)`;
    `(&2 / (&1 + x pow 2)) pow (63 * N - 1)`;
    `abs x pow (19 * N)`; `abs x pow (44 * N - 1)`] THEN
  CONV_TAC REAL_FIELD);;

(* ------------------------------------------------------------------------- *)
(* Positivity of the Cauchy denominators.                                    *)
(* ------------------------------------------------------------------------- *)

let RP_ALG_T_BOUND = prove
 (`forall x. abs(rp_t x) <= &1`,
  GEN_TAC THEN
  SUBGOAL_THEN `&0 < &1 + x pow 2` ASSUME_TAC THENL
   [MP_TAC(SPEC `x:real` REAL_LE_POW_2) THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `abs(rp_t x) = (&2 * abs x) / (&1 + x pow 2)` SUBST1_TAC THENL
   [REWRITE_TAC[rp_t; REAL_ABS_DIV; REAL_ABS_MUL; REAL_ABS_NUM] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < a ==> abs a = a`] THEN
    REWRITE_TAC[real_div; REAL_MUL_ASSOC];
    ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
  ONCE_REWRITE_TAC[GSYM REAL_POW2_ABS] THEN
  MP_TAC(SPEC `abs x - &1` REAL_LE_POW_2) THEN REAL_ARITH_TAC);;

let RP_ALG_DEN_POS = prove
 (`forall x s. &0 < s /\ s < &1 ==> &0 < &1 - rp_t x * s`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(REAL_ARITH `abs(a) < &1 ==> &0 < &1 - a`) THEN
  REWRITE_TAC[REAL_ABS_MUL] THEN MATCH_MP_TAC REAL_LET_TRANS THEN
  EXISTS_TAC `&1 * abs s` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[RP_ALG_T_BOUND; REAL_ABS_POS];
    ASM_REAL_ARITH_TAC]);;

let RP_ALG_ABS_SQ = prove
 (`forall v. abs v * abs v = v pow 2`,
  REWRITE_TAC[GSYM REAL_POW_2; REAL_POW2_ABS]);;

(* ------------------------------------------------------------------------- *)
(* The main identity.                                                        *)
(* ------------------------------------------------------------------------- *)

let RP_ALG_THM = prove
 (`RP_ALG_STMT`,
  REWRITE_TAC[RP_ALG_STMT; rp_config; rp_nodes] THEN
  MAP_EVERY X_GEN_TAC [`N:num`; `x:num->real`; `s:num->real`] THEN
  STRIP_TAC THEN
  (* distinctness is not needed; drop it to keep the simplifier safe *)
  UNDISCH_THEN `forall i j. i < 48 * N /\ j < 48 * N /\ (x:num->real) i = x j ==> i = j`
   (K ALL_TAC) THEN
  UNDISCH_THEN `forall i j. i < 48 * N /\ j < 48 * N /\ (s:num->real) i = s j ==> i = j`
   (K ALL_TAC) THEN
  SUBGOAL_THEN
   `forall i j. i < 48 * (N:num) /\ j < 48 * N ==> &0 < &1 - rp_t (x i) * s j`
  ASSUME_TAC THENL [ASM_MESON_TAC[RP_ALG_DEN_POS]; ALL_TAC] THEN
  REWRITE_TAC[rp_integrand] THEN
  ASM_SIMP_TAC[RP_ALG_ROWDET; RP_ALG_PSI_DET] THEN
  SUBGOAL_THEN
   `ndet {i:num | i < 48 * N} (\i j. inv(&1 - rp_t (x i) * s j)) =
    rp_vdm (48 * N) (\i. rp_t (x i)) * rp_vdm (48 * N) s /
    product {i:num | i < 48 * N}
      (\i. product {j:num | j < 48 * N} (\j. &1 - rp_t (x i) * s j))`
  SUBST1_TAC THENL
   [MP_TAC(ISPECL [`48 * N`; `\i. rp_t ((x:num->real) i)`; `s:num->real`]
                  RP_ALG_CAUCHY) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_MESON_TAC[REAL_LT_IMP_NZ];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `&0 < product {i:num | i < 48 * N}
           (\i. product {j:num | j < 48 * N} (\j. &1 - rp_t (x i) * s j))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC PRODUCT_POS_LT THEN REWRITE_TAC[FINITE_NUMSEG_LT] THEN
    REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC PRODUCT_POS_LT THEN REWRITE_TAC[FINITE_NUMSEG_LT] THEN
    REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `&0 < product {j:num | j < 48 * N}
           (\j. s j pow (7 * N) * (&1 - s j) pow (4 * N))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC PRODUCT_POS_LT THEN REWRITE_TAC[FINITE_NUMSEG_LT] THEN
    REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THEN MATCH_MP_TAC REAL_POW_LT THEN
    ASM_SIMP_TAC[REAL_SUB_LT];
    ALL_TAC] THEN
  REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_DIV] THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 < a ==> abs a = a`] THEN
  SIMP_TAC[GSYM PRODUCT_ABS; FINITE_NUMSEG_LT] THEN
  SUBGOAL_THEN
   `product {i:num | i < 48 * N} (\i. abs(rp_alg_c N (x i))) =
    product {i:num | i < 48 * N} (\i. &4 * abs(x i) / (&1 + x i pow 2) pow 2) *
    product {i:num | i < 48 * N} (\i. inv(abs(x i)) pow (44 * N - 1)) *
    product {i:num | i < 48 * N}
      (\i. abs(rp_t (x i)) pow (63 * N - 1) * (&1 - rp_t (x i)) pow (2 * N))`
  SUBST1_TAC THENL
   [SIMP_TAC[GSYM PRODUCT_MUL; FINITE_NUMSEG_LT] THEN
    MATCH_MP_TAC PRODUCT_EQ THEN REWRITE_TAC[IN_ELIM_THM] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC RP_ALG_C_ABS THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[rp_J] THEN
  MP_TAC(SPEC `rp_vdm (48 * N) s` RP_ALG_ABS_SQ) THEN
  MAP_EVERY (fun t -> SPEC_TAC(t,genvar(type_of t)))
   [`product {i:num | i < 48 * N} (\i. &4 * abs(x i) / (&1 + x i pow 2) pow 2)`;
    `product {i:num | i < 48 * N} (\i. inv(abs(x i)) pow (44 * N - 1))`;
    `product {i:num | i < 48 * N}
      (\i. abs(rp_t (x i)) pow (63 * N - 1) * (&1 - rp_t (x i)) pow (2 * N))`;
    `product {i:num | i < 48 * N}
           (\i. product {j:num | j < 48 * N} (\j. &1 - rp_t (x i) * s j))`;
    `product {j:num | j < 48 * N}
           (\j. s j pow (7 * N) * (&1 - s j) pow (4 * N))`;
    `abs(rp_vdm (48 * N) s)`; `rp_vdm (48 * N) s pow 2`;
    `abs(rp_vdm (48 * N) (\i. rp_t (x i)))`; `abs(rp_R N x)`] THEN
  REWRITE_TAC[real_div] THEN CONV_TAC REAL_RING);;

