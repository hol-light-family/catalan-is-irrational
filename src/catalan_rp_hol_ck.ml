(* ========================================================================= *)
(* rp_hol_ck_: Step 2 of Lemma 5.1 -- Cauchy formula on the unit circle     *)
(* and AM-GM, giving  Qg <= M^2 Qf.   Proves RP_HOL_CK_THM : |- RP_HOL_CK_STMT *)
(* ========================================================================= *)

needs "src/catalan_rp_hol_base.ml";;

let rp_hol_ck_k = new_definition
 `rp_hol_ck_k x z = Cx(&1) / (Cx(&1) - Cx x * z)`;;

let rp_hol_ck_f = new_definition
 `rp_hol_ck_f n (x:num->real) (c:num->real) z =
    vsum {j | j < n} (\j. Cx(c j) * rp_hol_ck_k (x j) z)`;;

let RP_HOL_CK_DERIV = prove
 (`forall t. t IN interval[vec 0,vec 1]
       ==> vector_derivative (circlepath(Cx(&0),&1))
             (at t within interval[vec 0,vec 1]) =
           Cx(&2) * Cx pi * ii * circlepath(Cx(&0),&1) t`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC VECTOR_DERIVATIVE_WITHIN_CLOSED_INTERVAL THEN
  ASM_REWRITE_TAC[DROP_VEC; REAL_LT_01] THEN
  MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_AT_WITHIN THEN
  SUBGOAL_THEN
   `Cx(&2) * Cx pi * ii * circlepath(Cx(&0),&1) t =
    Cx(&2) * Cx(pi) * ii * Cx(&1) * cexp(Cx(&2) * Cx pi * ii * Cx(drop t))`
  SUBST1_TAC THENL
   [REWRITE_TAC[CIRCLEPATH] THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN
    CONV_TAC COMPLEX_RING;
    REWRITE_TAC[HAS_VECTOR_DERIVATIVE_CIRCLEPATH]]);;

let RP_HOL_CK_NORM = prove
 (`forall t. norm(circlepath(Cx(&0),&1) t) = &1`,
  GEN_TAC THEN REWRITE_TAC[CIRCLEPATH] THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  REWRITE_TAC[COMPLEX_ADD_LID; COMPLEX_MUL_LID] THEN
  SUBGOAL_THEN `Cx(&2) * Cx pi * ii * Cx(drop t) = ii * Cx(&2 * pi * drop t)`
  SUBST1_TAC THENL
   [REWRITE_TAC[CX_MUL] THEN CONV_TAC COMPLEX_RING;
    REWRITE_TAC[NORM_CEXP_II]]);;

let RP_HOL_CK_CNJ = prove
 (`forall x z. abs x < &1 /\ norm z = &1
         ==> cnj(rp_hol_ck_k x z) = z / (z - Cx x)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[rp_hol_ck_k; CNJ_DIV; CNJ_SUB; CNJ_MUL; CNJ_CX] THEN
  SUBGOAL_THEN `z * cnj z = Cx(&1)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[COMPLEX_MUL_CNJ] THEN CONV_TAC COMPLEX_RING; ALL_TAC] THEN
  SUBGOAL_THEN `~(z = Cx x)` ASSUME_TAC THENL
   [DISCH_THEN(MP_TAC o AP_TERM `norm:complex->real`) THEN
    ASM_REWRITE_TAC[COMPLEX_NORM_CX] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC(COMPLEX_FIELD
   `forall z w c. z * w = Cx(&1) /\ ~(z = c)
            ==> Cx(&1) / (Cx(&1) - c * w) = z / (z - c)`) THEN
  ASM_REWRITE_TAC[]);;

let RP_HOL_CK_CAUCHY = prove
 (`forall u x. u continuous_on cball(Cx(&0),&1) /\ u holomorphic_on ball(Cx(&0),&1) /\
         abs x < &1
         ==> ((\t. u(circlepath(Cx(&0),&1) t) *
                   cnj(rp_hol_ck_k x (circlepath(Cx(&0),&1) t)))
              has_integral u(Cx x)) (interval[vec 0,vec 1])`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`u:complex->complex`; `Cx(&0)`; `&1`; `Cx x`]
    CAUCHY_INTEGRAL_CIRCLEPATH) THEN
  ASM_REWRITE_TAC[IN_BALL; dist; COMPLEX_SUB_LZERO; NORM_NEG; COMPLEX_NORM_CX] THEN
  REWRITE_TAC[has_path_integral] THEN
  DISCH_THEN(MP_TAC o SPEC `inv(Cx(&2) * Cx pi * ii)` o
    MATCH_MP HAS_INTEGRAL_COMPLEX_LMUL) THEN
  SUBGOAL_THEN `~(Cx pi = Cx(&0))` ASSUME_TAC THENL
   [REWRITE_TAC[CX_INJ; PI_NZ]; ALL_TAC] THEN
  MP_TAC II_NZ THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `inv(Cx(&2) * Cx pi * ii) * Cx(&2) * Cx pi * ii * u(Cx x) = u(Cx x)`
  SUBST1_TAC THENL
   [POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN CONV_TAC COMPLEX_FIELD;
    ALL_TAC] THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  DISCH_TAC THEN MATCH_MP_TAC HAS_INTEGRAL_EQ THEN
  EXISTS_TAC
   `\t. inv(Cx(&2) * Cx pi * ii) *
        u(circlepath(Cx(&0),&1) t) / (circlepath(Cx(&0),&1) t - Cx x) *
        vector_derivative (circlepath(Cx(&0),&1))
             (at t within interval[vec 0,vec 1])` THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `t:real^1` THEN DISCH_TAC THEN
  ASM_SIMP_TAC[RP_HOL_CK_DERIV; RP_HOL_CK_CNJ; RP_HOL_CK_NORM] THEN
  MP_TAC(SPEC `t:real^1` RP_HOL_CK_NORM) THEN
  SPEC_TAC(`circlepath(Cx(&0),&1) t`,`w:complex`) THEN
  X_GEN_TAC `w:complex` THEN DISCH_TAC THEN
  SUBGOAL_THEN `~(w = Cx x)` MP_TAC THENL
   [DISCH_THEN(MP_TAC o AP_TERM `norm:complex->real`) THEN
    ASM_REWRITE_TAC[COMPLEX_NORM_CX] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  UNDISCH_TAC `~(Cx pi = Cx(&0))` THEN UNDISCH_TAC `~(ii = Cx(&0))` THEN
  CONV_TAC COMPLEX_FIELD);;

let RP_HOL_CK_HOLO_K = prove
 (`forall x. abs x < &1 ==> (rp_hol_ck_k x) holomorphic_on cball(Cx(&0),&1)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `rp_hol_ck_k x = \z. Cx(&1) / (Cx(&1) - Cx x * z)` SUBST1_TAC
  THENL [REWRITE_TAC[FUN_EQ_THM; rp_hol_ck_k]; ALL_TAC] THEN
  MATCH_MP_TAC HOLOMORPHIC_ON_DIV THEN
  SIMP_TAC[HOLOMORPHIC_ON_CONST; HOLOMORPHIC_ON_SUB; HOLOMORPHIC_ON_MUL;
           HOLOMORPHIC_ON_ID] THEN
  X_GEN_TAC `z:complex` THEN
  REWRITE_TAC[IN_CBALL; dist; COMPLEX_SUB_LZERO; NORM_NEG] THEN
  DISCH_TAC THEN REWRITE_TAC[COMPLEX_SUB_0] THEN
  DISCH_THEN(MP_TAC o AP_TERM `norm:complex->real`) THEN
  REWRITE_TAC[COMPLEX_NORM_MUL; COMPLEX_NORM_CX; REAL_ABS_NUM] THEN
  MP_TAC(SPECL [`abs x`; `norm(z:complex)`; `&1`] REAL_LE_LMUL) THEN
  ASM_REWRITE_TAC[REAL_ABS_POS] THEN ASM_REAL_ARITH_TAC);;

let RP_HOL_CK_HOLO_F = prove
 (`forall n x c. (forall i. i < n ==> abs(x i) < &1)
           ==> (rp_hol_ck_f n x c) holomorphic_on cball(Cx(&0),&1)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `rp_hol_ck_f n x c =
                \z. vsum {j | j < n} (\j. Cx(c j) * rp_hol_ck_k (x j) z)`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; rp_hol_ck_f]; ALL_TAC] THEN
  MATCH_MP_TAC HOLOMORPHIC_ON_VSUM THEN
  REWRITE_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM] THEN
  X_GEN_TAC `j:num` THEN DISCH_TAC THEN
  MATCH_MP_TAC HOLOMORPHIC_ON_MUL THEN
  REWRITE_TAC[HOLOMORPHIC_ON_CONST; ETA_AX] THEN
  ASM_SIMP_TAC[RP_HOL_CK_HOLO_K]);;

let RP_HOL_CK_INNER = prove
 (`forall u n x c. u continuous_on cball(Cx(&0),&1) /\
             u holomorphic_on ball(Cx(&0),&1) /\
             (forall i. i < n ==> abs(x i) < &1)
             ==> ((\t. u(circlepath(Cx(&0),&1) t) *
                       cnj(rp_hol_ck_f n x c (circlepath(Cx(&0),&1) t)))
                  has_integral vsum {j | j < n} (\j. Cx(c j) * u(Cx(x j))))
                 (interval[vec 0,vec 1])`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[rp_hol_ck_f] THEN
  SIMP_TAC[CNJ_VSUM; FINITE_NUMSEG_LT; GSYM VSUM_COMPLEX_LMUL] THEN
  MATCH_MP_TAC HAS_INTEGRAL_VSUM THEN
  REWRITE_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM] THEN
  X_GEN_TAC `j:num` THEN DISCH_TAC THEN REWRITE_TAC[CNJ_MUL; CNJ_CX] THEN
  MP_TAC(SPECL [`u:complex->complex`; `(x:num->real) j`] RP_HOL_CK_CAUCHY) THEN
  ASM_SIMP_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `Cx(c(j:num))` o MATCH_MP HAS_INTEGRAL_COMPLEX_LMUL) THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN REWRITE_TAC[COMPLEX_MUL_AC]);;

let RP_HOL_CK_FVAL = prove
 (`forall n x c y. rp_hol_ck_f n x c (Cx y) =
             Cx(sum {j | j < n} (\j. c j / (&1 - x j * y)))`,
  REWRITE_TAC[rp_hol_ck_f; rp_hol_ck_k; GSYM CX_MUL; GSYM CX_SUB;
              GSYM CX_DIV; VSUM_CX] THEN
  REWRITE_TAC[real_div; REAL_MUL_LID]);;

let RP_HOL_CK_HYP_F = prove
 (`forall n x c. (forall i. i < n ==> abs(x i) < &1)
           ==> rp_hol_ck_f n x c continuous_on cball(Cx(&0),&1) /\
               rp_hol_ck_f n x c holomorphic_on ball(Cx(&0),&1)`,
  REPEAT STRIP_TAC THENL
   [MATCH_MP_TAC HOLOMORPHIC_ON_IMP_CONTINUOUS_ON THEN
    MATCH_MP_TAC RP_HOL_CK_HOLO_F THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC HOLOMORPHIC_ON_SUBSET THEN
    EXISTS_TAC `cball(Cx(&0),&1)` THEN REWRITE_TAC[BALL_SUBSET_CBALL] THEN
    MATCH_MP_TAC RP_HOL_CK_HOLO_F THEN ASM_REWRITE_TAC[]]);;

let RP_HOL_CK_IFF = prove
 (`forall n x a. (forall i. i < n ==> abs(x i) < &1)
           ==> ((\t. rp_hol_ck_f n x a (circlepath(Cx(&0),&1) t) *
                     cnj(rp_hol_ck_f n x a (circlepath(Cx(&0),&1) t)))
                has_integral
                Cx(sum {i | i < n}
                     (\i. sum {j | j < n} (\j. a i * a j / (&1 - x i * x j)))))
               (interval[vec 0,vec 1])`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`rp_hol_ck_f n x a`; `n:num`; `x:num->real`; `a:num->real`]
    RP_HOL_CK_INNER) THEN
  ASM_SIMP_TAC[RP_HOL_CK_HYP_F] THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[RP_HOL_CK_FVAL] THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  REWRITE_TAC[GSYM CX_MUL; VSUM_CX; CX_INJ] THEN
  MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN BETA_TAC THEN
  REWRITE_TAC[GSYM SUM_LMUL] THEN
  MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `j:num` THEN DISCH_TAC THEN BETA_TAC THEN
  REWRITE_TAC[real_div; REAL_MUL_AC]);;

let RP_HOL_CK_IGG = prove
 (`forall n x hv a. (forall i. i < n ==> abs(x i) < &1)
           ==> ((\t. rp_hol_ck_f n x (\j. a j * hv j) (circlepath(Cx(&0),&1) t) *
                     cnj(rp_hol_ck_f n x (\j. a j * hv j)
                           (circlepath(Cx(&0),&1) t)))
                has_integral
                Cx(sum {i | i < n}
                     (\i. sum {j | j < n}
                       (\j. a i * a j * hv i * hv j / (&1 - x i * x j)))))
               (interval[vec 0,vec 1])`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`rp_hol_ck_f n x (\j. a j * hv j)`; `n:num`; `x:num->real`;
                `\j. (a:num->real) j * hv j`] RP_HOL_CK_INNER) THEN
  ASM_SIMP_TAC[RP_HOL_CK_HYP_F] THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[RP_HOL_CK_FVAL] THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  REWRITE_TAC[GSYM CX_MUL; VSUM_CX; CX_INJ] THEN
  MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN BETA_TAC THEN
  REWRITE_TAC[GSYM SUM_LMUL] THEN
  MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `j:num` THEN DISCH_TAC THEN BETA_TAC THEN
  REWRITE_TAC[real_div; REAL_MUL_AC]);;

let RP_HOL_CK_IHGF = prove
 (`forall n x hv h a.
       (forall i. i < n ==> abs(x i) < &1) /\
       h continuous_on cball(Cx(&0),&1) /\ h holomorphic_on ball(Cx(&0),&1) /\
       (forall i. i < n ==> h(Cx(x i)) = Cx(hv i))
       ==> ((\t. (h(circlepath(Cx(&0),&1) t) *
                  rp_hol_ck_f n x (\j. a j * hv j) (circlepath(Cx(&0),&1) t)) *
                 cnj(rp_hol_ck_f n x a (circlepath(Cx(&0),&1) t)))
            has_integral
            Cx(sum {i | i < n}
                 (\i. sum {j | j < n}
                   (\j. a i * a j * hv i * hv j / (&1 - x i * x j)))))
           (interval[vec 0,vec 1])`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`\z. (h:complex->complex) z * rp_hol_ck_f n x (\j. a j * hv j) z`;
                `n:num`; `x:num->real`; `a:num->real`] RP_HOL_CK_INNER) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_COMPLEX_MUL THEN ASM_SIMP_TAC[ETA_AX; RP_HOL_CK_HYP_F];
      MATCH_MP_TAC HOLOMORPHIC_ON_MUL THEN ASM_SIMP_TAC[ETA_AX; RP_HOL_CK_HYP_F]];
    ALL_TAC] THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `vsum {i | i < n} (\i. Cx(a i) * Cx(hv i) *
                 rp_hol_ck_f n x (\j. a j * hv j) (Cx(x i)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC VSUM_EQ THEN REWRITE_TAC[IN_ELIM_THM] THEN
    REPEAT STRIP_TAC THEN BETA_TAC THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[RP_HOL_CK_FVAL] THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  REWRITE_TAC[GSYM CX_MUL; VSUM_CX; CX_INJ] THEN
  MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN BETA_TAC THEN
  REWRITE_TAC[GSYM SUM_LMUL] THEN
  MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `j:num` THEN DISCH_TAC THEN BETA_TAC THEN
  REWRITE_TAC[real_div; REAL_MUL_AC]);;

let RP_HOL_CK_PTWISE = prove
 (`forall u v w M. norm u <= M
             ==> Re(Cx(&2) * ((u * v) * cnj w)) <=
                 Re(v * cnj v + Cx(M pow 2) * (w * cnj w))`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[COMPLEX_MUL_CNJ; GSYM CX_POW; GSYM CX_MUL; GSYM CX_ADD; RE_CX] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `norm(Cx(&2) * ((u * v) * cnj w))` THEN CONJ_TAC THENL
   [MP_TAC(SPEC `Cx(&2) * ((u * v) * cnj w)` COMPLEX_NORM_GE_RE_IM) THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[COMPLEX_NORM_MUL; COMPLEX_NORM_CNJ; COMPLEX_NORM_CX; REAL_ABS_NUM] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&2 * ((M * norm(v:complex)) * norm(w:complex))` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[NORM_POS_LE] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[NORM_POS_LE];
    MP_TAC(SPEC `norm(v:complex) - M * norm(w:complex)` REAL_LE_POW_2) THEN
    REAL_ARITH_TAC]);;

let rp_hol_ck_qg = "sum {i:num | i < (n:num)} (\\i. sum {j | j < n} (\\j. (a:num->real) i * a j * (hv:num->real) i * hv j / (&1 - (x:num->real) i * x j)))";;
let rp_hol_ck_qf = "sum {i:num | i < (n:num)} (\\i. sum {j | j < n} (\\j. (a:num->real) i * a j / (&1 - (x:num->real) i * x j)))";;

let RP_HOL_CK_THM = prove
 (`RP_HOL_CK_STMT`,
  REWRITE_TAC[RP_HOL_CK_STMT] THEN REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`n:num`; `x:num->real`; `a:num->real`] RP_HOL_CK_IFF) THEN
  MP_TAC(SPECL [`n:num`; `x:num->real`; `hv:num->real`; `a:num->real`]
    RP_HOL_CK_IGG) THEN
  MP_TAC(SPECL [`n:num`; `x:num->real`; `hv:num->real`; `h:complex->complex`;
                `a:num->real`] RP_HOL_CK_IHGF) THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
  MP_TAC(ISPECL
   [`\t. Cx(&2) * ((h(circlepath(Cx(&0),&1) t) *
           rp_hol_ck_f n x (\j. a j * hv j) (circlepath(Cx(&0),&1) t)) *
           cnj(rp_hol_ck_f n x a (circlepath(Cx(&0),&1) t)))`;
    `\t. rp_hol_ck_f n x (\j. a j * hv j) (circlepath(Cx(&0),&1) t) *
           cnj(rp_hol_ck_f n x (\j. a j * hv j) (circlepath(Cx(&0),&1) t)) +
         Cx(M pow 2) *
           (rp_hol_ck_f n x a (circlepath(Cx(&0),&1) t) *
            cnj(rp_hol_ck_f n x a (circlepath(Cx(&0),&1) t)))`;
    `interval[vec 0:real^1,vec 1]`;
    parse_term("Cx(&2) * Cx(" ^ rp_hol_ck_qg ^ ")");
    parse_term("Cx(" ^ rp_hol_ck_qg ^ ") + Cx(M pow 2) * Cx(" ^ rp_hol_ck_qf ^ ")");
    `1`] HAS_INTEGRAL_COMPONENT_LE) THEN
  REWRITE_TAC[DIMINDEX_2; ARITH] THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC HAS_INTEGRAL_COMPLEX_LMUL THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC HAS_INTEGRAL_ADD THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC HAS_INTEGRAL_COMPLEX_LMUL THEN ASM_REWRITE_TAC[];
      X_GEN_TAC `t:real^1` THEN DISCH_TAC THEN
      CONV_TAC(DEPTH_CONV BETA_CONV) THEN REWRITE_TAC[GSYM RE_DEF] THEN
      MATCH_MP_TAC RP_HOL_CK_PTWISE THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        can (find_term ((=) `M:real`)) (concl th) && is_forall (concl th))) THEN
      REWRITE_TAC[RP_HOL_CK_NORM]];
    REWRITE_TAC[GSYM RE_DEF; GSYM CX_MUL; GSYM CX_ADD; RE_CX] THEN
    MATCH_ACCEPT_TAC(REAL_ARITH `forall a b:real. &2 * a <= a + b ==> a <= b`)]);;
