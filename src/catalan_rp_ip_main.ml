(* ========================================================================= *)
(* rp_ip: the finite-dimensional interpolation estimate (Proposition 5.2).  *)
(*                                                                           *)
(* Nodes x_0..x_{n-1} distinct in (-1,1); G_ij = 1/(1 - x_i x_j) is the     *)
(* Gram matrix of k_i(z) = 1/(1 - x_i z).  C (columns = coefficients of     *)
(* Q_i(z) = prod_{l<>i} (1 - x_l z)) relates monomials and kernels:          *)
(*   V^T C = Lambda G,  (V^T P C) = Pi  (P = reversal of exponents),         *)
(* with Lambda_j = Q(x_j), Pi_j = prod_{l<>j} (x_j - x_l).  The reversal in *)
(* the kernel basis is R = S G, S = Pi^-1 Lambda; R^2 = I and R is a         *)
(* G-isometry.  Then det[x^(n-1-r) + h x^r] = V(x) det(I + R D) up to sign. *)
(* ========================================================================= *)

needs "src/catalan_rp_ip_qf.ml";;

let rp_ip_ok = new_definition
 `rp_ip_ok n (x:num->real) <=>
    1 <= n /\ (forall i. i < n ==> abs(x i) < &1) /\
    (forall i j. i < n /\ j < n /\ x i = x j ==> i = j)`;;

let rp_ip_G = new_definition
 `rp_ip_G (x:num->real) i j = inv(&1 - x i * x j)`;;

let rp_ip_lam = new_definition
 `rp_ip_lam n (x:num->real) j = product {l | l < n} (\l. &1 - x l * x j)`;;

let rp_ip_pi = new_definition
 `rp_ip_pi n (x:num->real) j = product ({l | l < n} DELETE j) (\l. x j - x l)`;;

let rp_ip_sv = new_definition
 `rp_ip_sv n (x:num->real) j = rp_ip_lam n x j / rp_ip_pi n x j`;;

let rp_ip_R = new_definition
 `rp_ip_R n (x:num->real) k i = rp_ip_sv n x k * rp_ip_G x k i`;;

let rp_ip_C = new_definition
 `rp_ip_C n (x:num->real) i =
    @c. forall y w. product ({l | l < n} DELETE i) (\l. w - x l * y) =
              sum {m | m < n} (\m. c m * y pow m * w pow (n - 1 - m))`;;

let RP_IP_G_ETA = prove
 (`forall x. rp_ip_G x = \i j. inv(&1 - x i * x j)`,
  REWRITE_TAC[FUN_EQ_THM; rp_ip_G]);;

let RP_IP_G_SYM = prove
 (`forall x i j. rp_ip_G x i j = rp_ip_G x j i`,
  REWRITE_TAC[rp_ip_G; REAL_MUL_SYM]);;

(* ------------------------------------------------------------------------- *)
(* Small summation helpers.                                                  *)
(* ------------------------------------------------------------------------- *)

let RP_IP_SUM_DELTA_L = prove
 (`forall s a b f. sum s (\k:num. (if a = k then b else &0) * f k) =
             if a IN s then b * f a else &0`,
  REPEAT GEN_TAC THEN
  TRANS_TAC EQ_TRANS `sum s (\k:num. if k = a then b * f a else &0)` THEN
  CONJ_TAC THENL [ALL_TAC; REWRITE_TAC[SUM_DELTA]] THEN
  MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `k:num` THEN DISCH_TAC THEN
  REWRITE_TAC[] THEN ASM_CASES_TAC `k:num = a` THEN
  ASM_REWRITE_TAC[REAL_MUL_LZERO] THEN
  FIRST_X_ASSUM(ASSUME_TAC o GSYM) THEN ASM_REWRITE_TAC[REAL_MUL_LZERO]);;

let RP_IP_SUM_DELTA_R = prove
 (`forall s a f. sum s (\k:num. f k * (if k = a then &1 else &0)) =
           if a IN s then f a else &0`,
  REPEAT GEN_TAC THEN
  TRANS_TAC EQ_TRANS `sum s (\k:num. if k = a then f a else &0)` THEN
  CONJ_TAC THENL [ALL_TAC; REWRITE_TAC[SUM_DELTA]] THEN
  MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `k:num` THEN DISCH_TAC THEN
  REWRITE_TAC[] THEN ASM_CASES_TAC `k:num = a` THEN
  ASM_REWRITE_TAC[REAL_MUL_RZERO; REAL_MUL_RID]);;

let RP_IP_QF_ALT = prove
 (`forall n G a. rp_ip_qf n G a =
           sum {i | i < n} (\i. a i * sum {k | k < n} (\k. G i k * a k))`,
  REWRITE_TAC[rp_ip_qf; GSYM SUM_LMUL; REAL_MUL_ASSOC]);;

let RP_IP_SUM_SWAP_MUL = prove
 (`forall n (a:num->num->real) b u.
     sum {m | m < n} (\m. sum {k | k < n} (\k. a k m * b k) * u m) =
     sum {k | k < n} (\k. sum {m | m < n} (\m. a k m * u m) * b k)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM SUM_LMUL; GSYM SUM_RMUL] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) SUM_SWAP o lhand o snd) THEN
  REWRITE_TAC[FINITE_NUMSEG_LT] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `k:num` THEN DISCH_TAC THEN
  REWRITE_TAC[] THEN
  MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `m:num` THEN DISCH_TAC THEN
  REWRITE_TAC[] THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Nonvanishing facts.                                                       *)
(* ------------------------------------------------------------------------- *)

let RP_IP_ABS_MUL_LT1 = prove
 (`forall a b. abs a < &1 /\ abs b < &1 ==> abs(a * b) < &1`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`abs a`; `&1`; `abs b`; `&1`] REAL_LT_MUL2) THEN
  ASM_SIMP_TAC[REAL_ABS_POS; REAL_ABS_MUL; REAL_MUL_LID]);;

let RP_IP_DEN_NZ = prove
 (`forall n x i j. rp_ip_ok n x /\ i < n /\ j < n ==> ~(&1 - x i * x j = &0)`,
  REWRITE_TAC[rp_ip_ok] THEN REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`(x:num->real) i`; `(x:num->real) j`] RP_IP_ABS_MUL_LT1) THEN
  ASM_SIMP_TAC[] THEN ASM_REAL_ARITH_TAC);;

let RP_IP_LAM_NZ = prove
 (`forall n x j. rp_ip_ok n x /\ j < n ==> ~(rp_ip_lam n x j = &0)`,
  REPEAT STRIP_TAC THEN POP_ASSUM MP_TAC THEN
  SIMP_TAC[rp_ip_lam; PRODUCT_EQ_0; FINITE_NUMSEG_LT; IN_ELIM_THM] THEN
  ASM_MESON_TAC[RP_IP_DEN_NZ]);;

let RP_IP_PI_NZ = prove
 (`forall n x j. rp_ip_ok n x /\ j < n ==> ~(rp_ip_pi n x j = &0)`,
  REWRITE_TAC[rp_ip_ok] THEN REPEAT STRIP_TAC THEN POP_ASSUM MP_TAC THEN
  SIMP_TAC[rp_ip_pi; PRODUCT_EQ_0; FINITE_NUMSEG_LT; FINITE_DELETE;
           IN_ELIM_THM; IN_DELETE; REAL_SUB_0] THEN
  ASM_MESON_TAC[]);;

let RP_IP_SV_NZ = prove
 (`forall n x j. rp_ip_ok n x /\ j < n ==> ~(rp_ip_sv n x j = &0)`,
  SIMP_TAC[rp_ip_sv; REAL_DIV_EQ_0; RP_IP_LAM_NZ; RP_IP_PI_NZ]);;

(* ------------------------------------------------------------------------- *)
(* The coefficient matrix C.                                                 *)
(* ------------------------------------------------------------------------- *)

let RP_IP_C_EXISTS = prove
 (`forall n x i. 1 <= n /\ i < n
   ==> exists c. forall y w. product ({l | l < n} DELETE i) (\l. w - x l * y) =
                 sum {m | m < n} (\m. c m * y pow m * w pow (n - 1 - m))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`x:num->real`; `{l:num | l < n} DELETE i`] RP_IP_HOMPOLY) THEN
  ASM_SIMP_TAC[FINITE_DELETE; FINITE_NUMSEG_LT; CARD_DELETE; CARD_NUMSEG_LT;
               IN_ELIM_THM] THEN
  SUBGOAL_THEN `0..n-1 = {m | m < n}` (fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[EXTENSION; IN_NUMSEG; IN_ELIM_THM] THEN ASM_ARITH_TAC);;

let RP_IP_C = prove
 (`forall n x i. 1 <= n /\ i < n
   ==> forall y w. product ({l | l < n} DELETE i) (\l. w - x l * y) =
             sum {m | m < n}
               (\m. rp_ip_C n x i m * y pow m * w pow (n - 1 - m))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o SELECT_RULE o SPEC `x:num->real` o
    MATCH_MP RP_IP_C_EXISTS) THEN
  REWRITE_TAC[rp_ip_C]);;

(* V^T C = Lambda G *)
let RP_IP_VTC = prove
 (`forall n x i j. rp_ip_ok n x /\ i < n /\ j < n
     ==> sum {m | m < n} (\m. rp_ip_C n x i m * x j pow m) =
         rp_ip_lam n x j * rp_ip_G x i j`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`n:num`; `x:num->real`; `i:num`] RP_IP_C) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[rp_ip_ok]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPECL [`(x:num->real) j`; `&1`]) THEN
  REWRITE_TAC[REAL_POW_ONE; REAL_MUL_RID] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[rp_ip_lam; rp_ip_G] THEN
  MP_TAC(ISPECL [`\l. &1 - (x:num->real) l * x(j:num)`; `{l:num | l < n}`;
                 `i:num`] PRODUCT_DELETE) THEN
  ASM_REWRITE_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[] THEN
  MP_TAC(SPECL [`n:num`; `x:num->real`; `i:num`; `j:num`] RP_IP_DEN_NZ) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ONCE_REWRITE_TAC[REAL_ARITH `(a * b) * c = b * (a * c):real`] THEN
  ASM_SIMP_TAC[REAL_MUL_RINV; REAL_MUL_RID]);;

(* V^T P C = Pi *)
let RP_IP_VTPC = prove
 (`forall n x i j. rp_ip_ok n x /\ i < n /\ j < n
     ==> sum {m | m < n} (\m. rp_ip_C n x i m * x j pow (n - 1 - m)) =
         if j = i then rp_ip_pi n x j else &0`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`n:num`; `x:num->real`; `i:num`] RP_IP_C) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[rp_ip_ok]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPECL [`&1`; `(x:num->real) j`]) THEN
  REWRITE_TAC[REAL_POW_ONE; REAL_MUL_RID; REAL_MUL_LID] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  COND_CASES_TAC THENL [ASM_REWRITE_TAC[rp_ip_pi]; ALL_TAC] THEN
  SIMP_TAC[PRODUCT_EQ_0; FINITE_DELETE; FINITE_NUMSEG_LT] THEN
  EXISTS_TAC `j:num` THEN ASM_REWRITE_TAC[IN_DELETE; IN_ELIM_THM; REAL_SUB_REFL]);;

let RP_IP_VDM_KERNEL_T = prove
 (`forall n x y. (forall i j. i < n /\ j < n /\ x i = x j ==> i = j) /\
           (forall j. j < n ==> sum {m | m < n} (\m. y m * x j pow m) = &0)
           ==> forall m. m < n ==> y m = &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(ASSUME_TAC o ONCE_REWRITE_RULE[REAL_MUL_SYM]) THEN
  MP_TAC(ISPECL [`{i:num | i < n}`; `\j m. (x:num->real) j pow m`;
                 `y:num->real`] RP_IP_NDET_KERNEL) THEN
  ASM_SIMP_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM; RP_IP_VDM_NDET] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP RP_IP_VDM_NZ th]) THEN
  MESON_TAC[]);;

let RP_IP_VDM_KERNEL_REV = prove
 (`forall n x y. (forall i j. i < n /\ j < n /\ x i = x j ==> i = j) /\
           (forall j. j < n ==> sum {m | m < n} (\m. y m * x j pow (n - 1 - m)) = &0)
           ==> forall m. m < n ==> y m = &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`n:num`; `x:num->real`; `\m. (y:num->real) (n - 1 - m)`]
    RP_IP_VDM_KERNEL_T) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `j:num`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM RP_IP_SUM_REFLECT] THEN
    MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `m:num` THEN
    REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN
    ASM_SIMP_TAC[ARITH_RULE `m < n ==> n - 1 - (n - 1 - m) = m`];
    DISCH_TAC THEN X_GEN_TAC `m:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `n - 1 - m`) THEN
    ASM_SIMP_TAC[ARITH_RULE `m < n ==> n - 1 - (n - 1 - m) = m`] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_ARITH_TAC]);;

(* C R = P C: R is the reversal written in the kernel basis *)
let RP_IP_CR = prove
 (`forall n x i. rp_ip_ok n x /\ i < n
     ==> forall m. m < n
             ==> sum {k | k < n} (\k. rp_ip_C n x k m * rp_ip_R n x k i) =
                 rp_ip_C n x i (n - 1 - m)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ONCE_REWRITE_TAC[GSYM REAL_SUB_0] THEN
  MATCH_MP_TAC RP_IP_VDM_KERNEL_REV THEN EXISTS_TAC `x:num->real` THEN
  CONJ_TAC THENL [ASM_MESON_TAC[rp_ip_ok]; ALL_TAC] THEN
  X_GEN_TAC `j:num` THEN DISCH_TAC THEN
  REWRITE_TAC[REAL_SUB_RDISTRIB] THEN
  SIMP_TAC[SUM_SUB; FINITE_NUMSEG_LT] THEN
  REWRITE_TAC[RP_IP_SUM_SWAP_MUL] THEN
  MP_TAC(ISPECL [`n:num`; `\m. rp_ip_C n x i m * (x:num->real) j pow m`]
    RP_IP_SUM_REFLECT) THEN
  REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  ASM_SIMP_TAC[RP_IP_VTC] THEN
  SUBGOAL_THEN
   `sum {k | k < n}
      (\k. sum {m | m < n} (\m. rp_ip_C n x k m * x j pow (n - 1 - m)) *
           rp_ip_R n x k i) =
    rp_ip_pi n x j * rp_ip_R n x j i`
  SUBST1_TAC THENL
   [TRANS_TAC EQ_TRANS
     `sum {k | k < n}
        (\k. (if j = k then rp_ip_pi n x j else &0) * rp_ip_R n x k i)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `k:num` THEN
      REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN ASM_SIMP_TAC[RP_IP_VTPC];
      ASM_REWRITE_TAC[RP_IP_SUM_DELTA_L; IN_ELIM_THM]];
    ALL_TAC] THEN
  MP_TAC(SPECL [`n:num`; `x:num->real`; `j:num`] RP_IP_PI_NZ) THEN
  ASM_REWRITE_TAC[rp_ip_R; rp_ip_sv] THEN
  REWRITE_TAC[SPECL [`x:num->real`; `j:num`; `i:num`] RP_IP_G_SYM] THEN
  CONV_TAC REAL_FIELD);;

(* C has trivial kernel (via positivity of G) *)
let RP_IP_C_KERNEL = prove
 (`forall n x w. rp_ip_ok n x /\
           (forall m. m < n ==> sum {k | k < n} (\k. rp_ip_C n x k m * w k) = &0)
           ==> forall k. k < n ==> w k = &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `forall j. j < n ==> sum {k | k < n} (\k. rp_ip_G x j k * (w:num->real) k) = &0`
  ASSUME_TAC THENL
   [X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    MP_TAC(SPECL [`n:num`; `x:num->real`; `j:num`] RP_IP_LAM_NZ) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    SUBGOAL_THEN
     `sum {m:num | m < n}
        (\m. sum {k | k < n} (\k. rp_ip_C n x k m * (w:num->real) k) *
             x j pow m) =
      rp_ip_lam n x j * sum {k | k < n} (\k. rp_ip_G x j k * w k)`
    MP_TAC THENL
     [REWRITE_TAC[RP_IP_SUM_SWAP_MUL; GSYM SUM_LMUL] THEN
      MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `k:num` THEN
      REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN REWRITE_TAC[] THEN
      ASM_SIMP_TAC[RP_IP_VTC] THEN
      REWRITE_TAC[SPECL [`x:num->real`; `k:num`; `j:num`] RP_IP_G_SYM] THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN
     `sum {m:num | m < n}
        (\m. sum {k | k < n} (\k. rp_ip_C n x k m * (w:num->real) k) *
             x j pow m) = &0`
    SUBST1_TAC THENL
     [MATCH_MP_TAC SUM_EQ_0 THEN ASM_SIMP_TAC[IN_ELIM_THM; REAL_MUL_LZERO];
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SYM) THEN ASM_REWRITE_TAC[REAL_ENTIRE];
    ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `(~p ==> false) ==> p`) THEN DISCH_TAC THEN
  MP_TAC(SPECL [`n:num`; `x:num->real`; `w:num->real`] RP_IP_GRAM_POS) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[rp_ip_ok]; ALL_TAC] THEN
  REWRITE_TAC[RP_IP_QF_ALT; GSYM rp_ip_G] THEN
  MATCH_MP_TAC(REAL_ARITH `x = &0 ==> ~(&0 < x)`) THEN
  MATCH_MP_TAC SUM_EQ_0 THEN ASM_SIMP_TAC[IN_ELIM_THM; REAL_MUL_RZERO]);;

(* R^2 = I *)
let RP_IP_RR = prove
 (`forall n x l. rp_ip_ok n x /\ l < n
     ==> forall j. j < n
             ==> sum {k | k < n} (\k. rp_ip_R n x j k * rp_ip_R n x k l) =
                 if j = l then &1 else &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ONCE_REWRITE_TAC[GSYM REAL_SUB_0] THEN
  MATCH_MP_TAC RP_IP_C_KERNEL THEN EXISTS_TAC `x:num->real` THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `m:num` THEN DISCH_TAC THEN
  REWRITE_TAC[REAL_SUB_LDISTRIB] THEN SIMP_TAC[SUM_SUB; FINITE_NUMSEG_LT] THEN
  REWRITE_TAC[RP_IP_SUM_DELTA_R; IN_ELIM_THM] THEN
  ASM_REWRITE_TAC[REAL_SUB_0] THEN
  TRANS_TAC EQ_TRANS
   `sum {q:num | q < n}
      (\q. sum {k | k < n} (\k. rp_ip_C n x k m * rp_ip_R n x k q) *
           rp_ip_R n x q l)` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[GSYM SUM_LMUL; GSYM SUM_RMUL] THEN
    W(MP_TAC o PART_MATCH (lhand o rand) SUM_SWAP o lhand o snd) THEN
    REWRITE_TAC[FINITE_NUMSEG_LT] THEN DISCH_THEN SUBST1_TAC THEN
    MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `q:num` THEN DISCH_TAC THEN
    REWRITE_TAC[] THEN
    MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `k:num` THEN DISCH_TAC THEN
    REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  TRANS_TAC EQ_TRANS
   `sum {q:num | q < n} (\q. rp_ip_C n x q (n - 1 - m) * rp_ip_R n x q l)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `q:num` THEN
    REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    MP_TAC(SPECL [`n:num`; `x:num->real`; `q:num`] RP_IP_CR) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPECL [`n:num`; `x:num->real`; `l:num`] RP_IP_CR) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `n - 1 - m`) THEN
  ASM_SIMP_TAC[ARITH_RULE `m < n ==> n - 1 - m < n /\ n - 1 - (n - 1 - m) = m`]);;

(* R is an isometry for the form G *)
let RP_IP_R_ISOM = prove
 (`forall n x u. rp_ip_ok n x
     ==> rp_ip_qf n (rp_ip_G x)
           (\i. sum {k | k < n} (\k. rp_ip_R n x i k * u k)) =
         rp_ip_qf n (rp_ip_G x) u`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `v = \i. sum {k | k < n} (\k. rp_ip_R n x i k * (u:num->real) k)` THEN
  SUBGOAL_THEN
   `forall i. i < n ==> sum {k | k < n} (\k. rp_ip_R n x i k * (v:num->real) k) =
                  (u:num->real) i`
  ASSUME_TAC THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN EXPAND_TAC "v" THEN REWRITE_TAC[] THEN
    TRANS_TAC EQ_TRANS
     `sum {l:num | l < n}
        (\l. sum {k | k < n} (\k. rp_ip_R n x i k * rp_ip_R n x k l) *
             (u:num->real) l)` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[GSYM SUM_LMUL; GSYM SUM_RMUL] THEN
      W(MP_TAC o PART_MATCH (lhand o rand) SUM_SWAP o lhand o snd) THEN
      REWRITE_TAC[FINITE_NUMSEG_LT] THEN DISCH_THEN SUBST1_TAC THEN
      MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `l:num` THEN DISCH_TAC THEN
      REWRITE_TAC[] THEN
      MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `k:num` THEN DISCH_TAC THEN
      REWRITE_TAC[] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    TRANS_TAC EQ_TRANS
     `sum {l:num | l < n} (\l. (if i = l then &1 else &0) * (u:num->real) l)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `l:num` THEN
      REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN REWRITE_TAC[] THEN
      MP_TAC(SPECL [`n:num`; `x:num->real`; `l:num`] RP_IP_RR) THEN
      ASM_SIMP_TAC[];
      ASM_REWRITE_TAC[RP_IP_SUM_DELTA_L; IN_ELIM_THM; REAL_MUL_LID]];
    ALL_TAC] THEN
  REWRITE_TAC[RP_IP_QF_ALT] THEN
  MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `i:num` THEN
  REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `(v:num->real) i =
    rp_ip_sv n x i * sum {k | k < n} (\k. rp_ip_G x i k * (u:num->real) k)`
  SUBST1_TAC THENL
   [EXPAND_TAC "v" THEN REWRITE_TAC[rp_ip_R; GSYM REAL_MUL_ASSOC; SUM_LMUL];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN
  ASM_REWRITE_TAC[rp_ip_R; GSYM REAL_MUL_ASSOC; SUM_LMUL] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  ABBREV_TAC `A = sum {k | k < n} (\k. rp_ip_G x i k * (u:num->real) k)` THEN
  ABBREV_TAC `B = sum {k | k < n} (\k. rp_ip_G x i k * (v:num->real) k)` THEN
  CONV_TAC REAL_RING);;

(* ------------------------------------------------------------------------- *)
(* The determinant identity.                                                 *)
(* ------------------------------------------------------------------------- *)

let RP_IP_NDET_ID = prove
 (`forall s. FINITE s ==> ndet s (\i j. if i = j then &1 else &0) = &1`,
  SIMP_TAC[RP_IP_NDET_DIAGONAL; PRODUCT_ONE]);;

let RP_IP_ALG_FINAL = prove
 (`forall dM dC dB dG P L v.
     dM * dC = P * dB /\ v * dC = L * dG /\
     (L / P * dG) * (L / P * dG) = &1 /\ ~(P = &0)
     ==> abs dM = abs dB * abs v`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `abs L * abs dG = abs(P:real)` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_ABS_MUL; REAL_EQ_SQUARE_ABS] THEN
    UNDISCH_TAC `(L / P * dG) * (L / P * dG) = &1` THEN
    UNDISCH_TAC `~(P:real = &0)` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  SUBGOAL_THEN `(dM:real) * (L * dG) = v * P * dB` MP_TAC THENL
   [UNDISCH_TAC `(dM:real) * dC = P * dB` THEN UNDISCH_TAC `(v:real) * dC = L * dG` THEN
    CONV_TAC REAL_RING;
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o AP_TERM `abs`) THEN
  ASM_REWRITE_TAC[REAL_ABS_MUL] THEN
  SUBGOAL_THEN `&0 < abs(P:real)` MP_TAC THENL
   [ASM_REWRITE_TAC[GSYM REAL_ABS_NZ]; ALL_TAC] THEN
  CONV_TAC REAL_FIELD);;

let RP_IP_SV_ETA = prove
 (`forall n x. rp_ip_sv n x = \j. rp_ip_lam n x j / rp_ip_pi n x j`,
  REWRITE_TAC[FUN_EQ_THM; rp_ip_sv]);;

let RP_IP_DET_IDENT = prove
 (`forall n x h. rp_ip_ok n x
     ==> abs(ndet {i | i < n} (\r i. x i pow (n - 1 - r) + h i * x i pow r)) =
         abs(ndet {i | i < n}
               (\i k. (if i = k then &1 else &0) + rp_ip_R n x i k * h k)) *
         abs(rp_vdm n x)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `forall j. j < n ==> ~(rp_ip_pi n x j = &0) /\ ~(rp_ip_sv n x j = &0)`
  ASSUME_TAC THENL [ASM_MESON_TAC[RP_IP_PI_NZ; RP_IP_SV_NZ]; ALL_TAC] THEN
  (* EQ5: dA = dB *)
  SUBGOAL_THEN
   `ndet {i | i < n}
      (\i k. (if i = k then &1 else &0) + rp_ip_R n x i k * (h:num->real) k) =
    ndet {i | i < n}
      (\j i. (if j = i then &1 else &0) +
             h j * rp_ip_sv n x j * rp_ip_G x i j)`
  SUBST1_TAC THENL
   [MP_TAC(ISPECL [`{i:num | i < n}`; `rp_ip_sv n x`;
       `\i k. ((if k = i then &1 else &0) +
               (h:num->real) k * rp_ip_sv n x k * rp_ip_G x i k) *
              inv(rp_ip_sv n x k)`] RP_IP_NDET_ROWS_MUL) THEN
    MP_TAC(ISPECL [`{i:num | i < n}`; `\k. inv(rp_ip_sv n x k)`;
       `\i k. (if k = i then &1 else &0) +
              (h:num->real) k * rp_ip_sv n x k * rp_ip_G x i k`]
       RP_IP_NDET_COLUMNS_MUL) THEN
    MP_TAC(ISPECL [`{i:num | i < n}`;
       `\j i. (if j = i then &1 else &0) +
              (h:num->real) j * rp_ip_sv n x j * rp_ip_G x i j`]
       RP_IP_NDET_TRANSP) THEN
    REWRITE_TAC[FINITE_NUMSEG_LT] THEN
    DISCH_THEN SUBST1_TAC THEN DISCH_THEN SUBST1_TAC THEN
    SUBGOAL_THEN
     `product {i:num | i < n} (rp_ip_sv n x) *
      product {i | i < n} (\k. inv(rp_ip_sv n x k)) = &1`
    MP_TAC THENL
     [SIMP_TAC[GSYM PRODUCT_MUL; FINITE_NUMSEG_LT] THEN
      MATCH_MP_TAC PRODUCT_EQ_1 THEN REWRITE_TAC[IN_ELIM_THM] THEN
      ASM_SIMP_TAC[REAL_MUL_RINV];
      ALL_TAC] THEN
    DISCH_TAC THEN
    MATCH_MP_TAC(REAL_RING
     `x = y /\ s * t = &1 ==> y = s * (b * t) ==> x = b`) THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC RP_IP_NDET_EQ THEN
    MAP_EVERY X_GEN_TAC [`i:num`; `k:num`] THEN
    REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN REWRITE_TAC[rp_ip_R] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `k:num`) THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN ASM_CASES_TAC `i:num = k` THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC THEN REWRITE_TAC[];
      ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM(ASSUME_TAC o GSYM) THEN
      ASM_REWRITE_TAC[]] THEN
    UNDISCH_TAC `~(rp_ip_sv n x k = &0)` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  MATCH_MP_TAC RP_IP_ALG_FINAL THEN
  MAP_EVERY EXISTS_TAC
   [`ndet {i | i < n} (\r i. rp_ip_C n x i r)`;
    `ndet {i | i < n} (rp_ip_G x)`;
    `product {i:num | i < n} (rp_ip_pi n x)`;
    `product {i:num | i < n} (rp_ip_lam n x)`] THEN
  REPEAT CONJ_TAC THENL
   [(* EQ1 *)
    MP_TAC(ISPECL [`{i:num | i < n}`;
       `\j r. (x:num->real) j pow (n - 1 - r) + (h:num->real) j * x j pow r`;
       `\r i. rp_ip_C n x i r`] RP_IP_NDET_MUL) THEN
    MP_TAC(ISPECL [`{i:num | i < n}`;
       `\r i. (x:num->real) i pow (n - 1 - r) + (h:num->real) i * x i pow r`]
       RP_IP_NDET_TRANSP) THEN
    REWRITE_TAC[FINITE_NUMSEG_LT] THEN DISCH_THEN SUBST1_TAC THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    MP_TAC(ISPECL [`{i:num | i < n}`; `rp_ip_pi n x`;
       `\j i. (if j = i then &1 else &0) +
              (h:num->real) j * rp_ip_sv n x j * rp_ip_G x i j`]
       RP_IP_NDET_ROWS_MUL) THEN
    REWRITE_TAC[FINITE_NUMSEG_LT] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC RP_IP_NDET_EQ THEN
    MAP_EVERY X_GEN_TAC [`j:num`; `i:num`] THEN
    REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
    TRANS_TAC EQ_TRANS
     `sum {k:num | k < n} (\k. rp_ip_C n x i k * (x:num->real) j pow (n - 1 - k)) +
      (h:num->real) j * sum {k | k < n} (\k. rp_ip_C n x i k * x j pow k)` THEN
    CONJ_TAC THENL
     [SIMP_TAC[GSYM SUM_LMUL; GSYM SUM_ADD; FINITE_NUMSEG_LT] THEN
      MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `k:num` THEN DISCH_TAC THEN
      REWRITE_TAC[] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_SIMP_TAC[RP_IP_VTC; RP_IP_VTPC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `j:num`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o CONJUNCT1) THEN REWRITE_TAC[rp_ip_sv] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC REAL_FIELD;
    (* EQ2 *)
    MP_TAC(ISPECL [`{i:num | i < n}`; `\j m. (x:num->real) j pow m`;
       `\r i. rp_ip_C n x i r`] RP_IP_NDET_MUL) THEN
    REWRITE_TAC[FINITE_NUMSEG_LT; RP_IP_VDM_NDET] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    MP_TAC(ISPECL [`{i:num | i < n}`; `rp_ip_lam n x`;
       `\j i. rp_ip_G x i j`] RP_IP_NDET_ROWS_MUL) THEN
    MP_TAC(ISPECL [`{i:num | i < n}`; `rp_ip_G x`] RP_IP_NDET_TRANSP) THEN
    REWRITE_TAC[FINITE_NUMSEG_LT] THEN DISCH_THEN SUBST1_TAC THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC RP_IP_NDET_EQ THEN
    MAP_EVERY X_GEN_TAC [`j:num`; `i:num`] THEN
    REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
    ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN ASM_SIMP_TAC[RP_IP_VTC] THEN
    REAL_ARITH_TAC;
    (* EQ3 *)
    REWRITE_TAC[GSYM RP_IP_SV_ETA] THEN
    SIMP_TAC[GSYM PRODUCT_DIV; FINITE_NUMSEG_LT] THEN
    REWRITE_TAC[GSYM RP_IP_SV_ETA] THEN
    SUBGOAL_THEN
     `ndet {i | i < n} (rp_ip_R n x) =
      product {i:num | i < n} (rp_ip_sv n x) * ndet {i | i < n} (rp_ip_G x)`
    (SUBST1_TAC o SYM) THENL
     [MP_TAC(ISPECL [`{i:num | i < n}`; `rp_ip_sv n x`; `rp_ip_G x`]
        RP_IP_NDET_ROWS_MUL) THEN
      REWRITE_TAC[FINITE_NUMSEG_LT] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM; rp_ip_R];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`{i:num | i < n}`; `rp_ip_R n x`; `rp_ip_R n x`]
      RP_IP_NDET_MUL) THEN
    REWRITE_TAC[FINITE_NUMSEG_LT] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    TRANS_TAC EQ_TRANS `ndet {i:num | i < n} (\i j. if i = j then &1 else &0)` THEN
    CONJ_TAC THENL [ALL_TAC; SIMP_TAC[RP_IP_NDET_ID; FINITE_NUMSEG_LT]] THEN
    MATCH_MP_TAC RP_IP_NDET_EQ THEN
    MAP_EVERY X_GEN_TAC [`j:num`; `l:num`] THEN
    REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
    MP_TAC(SPECL [`n:num`; `x:num->real`; `l:num`] RP_IP_RR) THEN
    ASM_SIMP_TAC[];
    (* P nonzero *)
    SIMP_TAC[PRODUCT_EQ_0; FINITE_NUMSEG_LT; IN_ELIM_THM] THEN
    ASM_MESON_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Main lemma: Pick-form bound for D = diag(h) gives the determinant bound.  *)
(* ------------------------------------------------------------------------- *)

let RP_IP_QF_PSD = prove
 (`forall n x a. rp_ip_ok n x ==> &0 <= rp_ip_qf n (rp_ip_G x) a`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `forall i. i < n ==> (a:num->real) i = &0` THENL
   [MATCH_MP_TAC REAL_EQ_IMP_LE THEN ONCE_REWRITE_TAC[EQ_SYM_EQ] THEN
    REWRITE_TAC[rp_ip_qf] THEN MATCH_MP_TAC SUM_EQ_0 THEN
    ASM_SIMP_TAC[IN_ELIM_THM; REAL_MUL_LZERO; SUM_0];
    MATCH_MP_TAC REAL_LT_IMP_LE THEN REWRITE_TAC[RP_IP_G_ETA] THEN
    MATCH_MP_TAC RP_IP_GRAM_POS THEN ASM_MESON_TAC[rp_ip_ok]]);;

let RP_IP_MAIN = prove
 (`forall n x h c.
     RP_LA_STMT /\ rp_ip_ok n x /\ &0 < c /\
     (forall a. sum {i | i < n}
            (\i. sum {j | j < n}
                   (\j. a i * a j * h i * h j / (&1 - x i * x j))) <=
          c pow 2 *
          sum {i | i < n}
            (\i. sum {j | j < n} (\j. a i * a j / (&1 - x i * x j))))
     ==> abs(ndet {i | i < n} (\r i. x i pow (n - 1 - r) + h i * x i pow r))
         <= (&1 + c) pow n * abs(rp_vdm n x)`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[RP_IP_DET_IDENT] THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[REAL_ABS_POS] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [RP_LA_STMT]) THEN
  DISCH_THEN MATCH_MP_TAC THEN EXISTS_TAC `rp_ip_G x` THEN
  REPEAT CONJ_TAC THENL
   [MESON_TAC[RP_IP_G_SYM];
    X_GEN_TAC `a:num->real` THEN DISCH_TAC THEN
    MP_TAC(SPECL [`n:num`; `x:num->real`; `a:num->real`] RP_IP_GRAM_POS) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[rp_ip_ok]; ALL_TAC] THEN
    REWRITE_TAC[rp_ip_qf; GSYM rp_ip_G] THEN MESON_TAC[];
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  X_GEN_TAC `a:num->real` THEN
  ABBREV_TAC
   `b = \i. sum {k | k < n}
              (\k. rp_ip_R n x i k * ((h:num->real) k * (a:num->real) k))` THEN
  SUBGOAL_THEN
   `forall i. i < n
        ==> sum {k | k < n}
              (\k. ((if i = k then &1 else &0) + rp_ip_R n x i k * h k) *
                   (a:num->real) k) = a i + (b:num->real) i`
  ASSUME_TAC THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN EXPAND_TAC "b" THEN
    REWRITE_TAC[REAL_ADD_RDISTRIB] THEN
    SIMP_TAC[SUM_ADD; FINITE_NUMSEG_LT] THEN
    ASM_REWRITE_TAC[RP_IP_SUM_DELTA_L; IN_ELIM_THM; REAL_MUL_LID] THEN
    REWRITE_TAC[GSYM REAL_MUL_ASSOC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`n:num`; `rp_ip_G x`; `a:num->real`; `b:num->real`;
                 `c:real`] RP_IP_QF_TRIANGLE) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[RP_IP_QF_PSD] THEN CONJ_TAC THENL
     [MESON_TAC[RP_IP_G_SYM]; ALL_TAC] THEN
    EXPAND_TAC "b" THEN ASM_SIMP_TAC[RP_IP_R_ISOM] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `a:num->real`) THEN
    MATCH_MP_TAC(MESON[]
     `(x:real) = x' /\ (y:real) = y' ==> x' <= z * y' ==> x <= z * y`) THEN
    REWRITE_TAC[rp_ip_qf; rp_ip_G] THEN CONJ_TAC THEN
    MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    REWRITE_TAC[] THEN
    MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    REWRITE_TAC[real_div; REAL_MUL_AC];
    ALL_TAC] THEN
  REWRITE_TAC[rp_ip_qf] THEN
  MATCH_MP_TAC(REAL_ARITH `(x:real) = y ==> y <= z ==> x <= z`) THEN
  MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `i:num` THEN
  REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `j:num` THEN
  REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN REWRITE_TAC[] THEN
  ASM_SIMP_TAC[]);;
