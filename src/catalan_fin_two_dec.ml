(* ========================================================================= *)
(* fin_two_: decomposition of raw and filtered columns into atoms.           *)
(* ========================================================================= *)

needs "src/catalan_fin_two_mk.ml";;
needs "src/catalan_rat_alg.ml";;

let fin_two_Q = new_definition
 `fin_two_Q N u i =
    sum (0..2 * N) (\v. if i + u + 1 = 63 * N + v
                        then (--(&1)) pow v * &(binom(2 * N,v)) else &0)`;;

let FIN_TWO_DELTA_SUM = prove
 (`forall C a (c:num->real) i v. v <= i /\ i - v < C
     ==> sum (0..C - 1) (\u. c u * (if i + u + 1 = C + v then a else &0)) =
         c (C - 1 - (i - v)) * a`,
  REPEAT STRIP_TAC THEN
  TRANS_TAC EQ_TRANS
   `sum (0..C - 1) (\u. if u = C - 1 - (i - v) then c (C - 1 - (i - v)) * a else &0)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `u:num` THEN STRIP_TAC THEN
    REWRITE_TAC[] THEN
    SUBGOAL_THEN `i + u + 1 = C + v <=> u = C - 1 - (i - v)` SUBST1_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[REAL_MUL_RZERO];
    REWRITE_TAC[SUM_DELTA; IN_NUMSEG] THEN
    SUBGOAL_THEN `0 <= C - 1 - (i - v) /\ C - 1 - (i - v) <= C - 1`
     (fun th -> REWRITE_TAC[th]) THEN
    ASM_ARITH_TAC]);;

let FIN_TWO_DELTA_SUM0 = prove
 (`forall C a (c:num->real) i v. 1 <= C /\ ~(v <= i /\ i - v < C)
     ==> sum (0..C - 1) (\u. c u * (if i + u + 1 = C + v then a else &0)) = &0`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUM_EQ_0_NUMSEG THEN
  X_GEN_TAC `u:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  SUBGOAL_THEN `~(i + u + 1 = C + v:num)` (fun th -> REWRITE_TAC[th; REAL_MUL_RZERO]) THEN
  ASM_ARITH_TAC);;

let FIN_TWO_MULFAC_REVC = prove
 (`forall C h (c:num->real) i. 1 <= C ==>
     cat_mulfac h (cat_revc C c) i =
     sum (0..C - 1) (\u. c u * sum (0..h) (\v. if i + u + 1 = C + v
                          then (--(&1)) pow v * &(binom(h,v)) else &0))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[cat_mulfac] THEN
  REWRITE_TAC[GSYM SUM_LMUL] THEN
  GEN_REWRITE_TAC RAND_CONV [SUM_SWAP_NUMSEG] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `v:num` THEN STRIP_TAC THEN
  REWRITE_TAC[cat_revc] THEN
  ASM_CASES_TAC `v:num <= i /\ i - v < C` THENL
   [ASM_SIMP_TAC[FIN_TWO_DELTA_SUM] THEN REAL_ARITH_TAC;
    ASM_SIMP_TAC[FIN_TWO_DELTA_SUM0] THEN
    REPEAT COND_CASES_TAC THEN REWRITE_TAC[REAL_MUL_RZERO] THEN ASM_MESON_TAC[]]);;

let FIN_TWO_PCOEF = prove
 (`forall N r i. 1 <= N ==>
     cat_pcoef N r i =
     sum (0..63 * N - 1) (\u. cheb_T (cat_dist N r) u * fin_two_Q N u i)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[cat_pcoef; fin_two_Q] THEN
  MATCH_MP_TAC FIN_TWO_MULFAC_REVC THEN ASM_ARITH_TAC);;

let FIN_TWO_DCOEF = prove
 (`forall N r i. 1 <= N ==>
     cat_dcoef N r i =
     sum (0..63 * N - 1) (\u. (cat_sgn N r * cheb_U (cat_dist N r - 1) u) *
                              fin_two_Q N u i)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[cat_dcoef; fin_two_Q] THEN
  REWRITE_TAC[GSYM REAL_MUL_ASSOC; SUM_LMUL] THEN AP_TERM_TAC THEN
  MATCH_MP_TAC FIN_TWO_MULFAC_REVC THEN ASM_ARITH_TAC);;

let FIN_TWO_Q_ZP = prove
 (`forall N u i. fin_zp 2 (fin_two_Q N u i)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[fin_two_Q] THEN
  MATCH_MP_TAC FIN_ZP_SUM THEN REWRITE_TAC[FIN_TWO_PRIME; FINITE_NUMSEG] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN COND_CASES_TAC THEN
  SIMP_TAC[FIN_ZP_0; FIN_TWO_PRIME] THEN MATCH_MP_TAC FIN_ZP_MUL THEN
  SIMP_TAC[FIN_TWO_PRIME; FIN_ZP_POW; FIN_ZP_NEG; FIN_ZP_1; FIN_ZP_NUM]);;

let FIN_TWO_Q_SUPP = prove
 (`forall N u i. ~(fin_two_Q N u i = &0) ==> 63 * N <= i + u + 1 /\ i + u + 1 <= 65 * N`,
  REPEAT GEN_TAC THEN REWRITE_TAC[fin_two_Q] THEN
  MATCH_MP_TAC(TAUT `(~b ==> a) ==> ~a ==> b`) THEN DISCH_TAC THEN
  MATCH_MP_TAC SUM_EQ_0_NUMSEG THEN X_GEN_TAC `v:num` THEN STRIP_TAC THEN
  REWRITE_TAC[] THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN ASM_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The 2-adic decomposition of a raw column.                                 *)
(* ------------------------------------------------------------------------- *)

let fin_two_R = new_definition
 `fin_two_R N = 2 EXP ((65 * N + 1) * (65 * N + 1) + (65 * N + 1) + 4)`;;

let fin_two_e1 = new_definition
 `fin_two_e1 z N = &4 * z - fin_two_mk (fin_two_R N) 0 0`;;

let fin_two_e2 = new_definition
 `fin_two_e2 N = --(fin_two_mk (fin_two_R N) 0 1)`;;

let fin_two_SX = new_definition
 `fin_two_SX N r j =
    sum (0..65 * N) (\i. cat_pcoef N r i * fin_two_X (fin_two_R N) i j)`;;

let fin_two_a = new_definition
 `fin_two_a z N u j =
    fin_two_e1 z N * sum (0..65 * N) (\i. fin_two_Q N u i * cat_ckern i j)`;;

let fin_two_b = new_definition
 `fin_two_b N u j =
    sum (0..65 * N) (\i. fin_two_Q N u i *
                         (fin_two_e2 N * (if i = j then &1 else &0) -
                          &3 / &2 * cat_Z0 i j))`;;

let FIN_TWO_SWAP = prove
 (`forall N (c:num->real) (g:num->real).
     sum (0..65 * N) (\i. sum (0..63 * N - 1) (\u. c u * fin_two_Q N u i) * g i) =
     sum (0..63 * N - 1) (\u. c u * sum (0..65 * N) (\i. fin_two_Q N u i * g i))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM SUM_RMUL; GSYM SUM_LMUL] THEN
  GEN_REWRITE_TAC LAND_CONV [SUM_SWAP_NUMSEG] THEN REWRITE_TAC[REAL_MUL_ASSOC]);;

let FIN_TWO_A_SUM = prove
 (`forall z N r j. 1 <= N ==>
     sum (0..63 * N - 1) (\u. cheb_T (cat_dist N r) u * fin_two_a z N u j) =
     sum (0..65 * N) (\i. cat_pcoef N r i * (fin_two_e1 z N * cat_ckern i j))`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[FIN_TWO_PCOEF; FIN_TWO_SWAP] THEN
  REWRITE_TAC[fin_two_a; GSYM SUM_LMUL; REAL_MUL_AC]);;

let FIN_TWO_B_SUM = prove
 (`forall N r j. 1 <= N ==>
     sum (0..63 * N - 1) (\u. (cat_sgn N r * cheb_U (cat_dist N r - 1) u) *
                              fin_two_b N u j) =
     sum (0..65 * N) (\i. cat_dcoef N r i *
                          (fin_two_e2 N * (if i = j then &1 else &0) -
                           &3 / &2 * cat_Z0 i j))`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[FIN_TWO_DCOEF; FIN_TWO_SWAP] THEN
  REWRITE_TAC[fin_two_b]);;

let FIN_TWO_RAW_DEC = prove
 (`forall z N r j. 1 <= N /\ r < 48 * N /\ j < 59 * N ==>
     cat_rawq z N r j =
     fin_two_SX N r j +
     sum (0..63 * N - 1) (\u. cheb_T (cat_dist N r) u * fin_two_a z N u j) +
     sum (0..63 * N - 1) (\u. (cat_sgn N r * cheb_U (cat_dist N r - 1) u) *
                              fin_two_b N u j)`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[FIN_TWO_A_SUM; FIN_TWO_B_SUM] THEN
  REWRITE_TAC[cat_rawq] THEN
  SUBGOAL_THEN
   `forall i. cat_M0 i j + &4 * z * cat_ckern i j =
        fin_two_X (fin_two_R N) i j + fin_two_e1 z N * cat_ckern i j +
        fin_two_e2 N * fin_two_ck2 i j`
   (fun th -> REWRITE_TAC[th])
  THENL [REWRITE_TAC[fin_two_X; fin_two_e1; fin_two_e2] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `sum (0..65 * N) (\i. cat_pcoef N r i * fin_two_e2 N * fin_two_ck2 i j) =
    fin_two_e2 N * cat_dcoef N r j`
  ASSUME_TAC THENL
   [TRANS_TAC EQ_TRANS
     `sum (0..65 * N) (\i. fin_two_e2 N *
         (cat_pcoef N r i * (if i < j then cat_ckern (j - 1) i else &0)))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SUM_EQ_NUMSEG THEN REWRITE_TAC[fin_two_ck2] THEN REAL_ARITH_TAC;
      REWRITE_TAC[SUM_LMUL] THEN AP_TERM_TAC THEN MATCH_MP_TAC RAT_CANCEL THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `sum (0..65 * N) (\i. cat_dcoef N r i * fin_two_e2 N * (if i = j then &1 else &0)) =
    fin_two_e2 N * cat_dcoef N r j`
  ASSUME_TAC THENL
   [TRANS_TAC EQ_TRANS
     `sum (0..65 * N) (\i. if i = j then fin_two_e2 N * cat_dcoef N r j else &0)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
      REWRITE_TAC[] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
      REWRITE_TAC[SUM_DELTA; IN_NUMSEG] THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN
      ASM_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[fin_two_SX; REAL_ADD_LDISTRIB; REAL_SUB_LDISTRIB;
              SUM_ADD_NUMSEG; SUM_SUB_NUMSEG] THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[REAL_ARITH `d * &3 / &2 * z = &3 / &2 * (d * z):real`; SUM_LMUL] THEN
  REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The column filter.                                                        *)
(* ------------------------------------------------------------------------- *)

let fin_two_filt = new_definition
 `fin_two_filt N (FF:num->real) k =
    sum (0..4 * N) (\v. (--(&1)) pow v * &(binom(4 * N,v)) * FF (7 * N + k + v))`;;

let FIN_TWO_FILT_EQ = prove
 (`forall N FF GG k. (forall v. v <= 4 * N ==> FF (7 * N + k + v) = GG (7 * N + k + v))
             ==> fin_two_filt N FF k = fin_two_filt N GG k`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[fin_two_filt] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN ASM_SIMP_TAC[]);;

let FIN_TWO_FILT_ADD = prove
 (`forall N FF GG k. fin_two_filt N (\j. FF j + GG j) k = fin_two_filt N FF k + fin_two_filt N GG k`,
  REWRITE_TAC[fin_two_filt; REAL_ADD_LDISTRIB; SUM_ADD_NUMSEG]);;

let FIN_TWO_FILT_SUM = prove
 (`forall N k (c:num->real) (g:num->num->real) n.
     fin_two_filt N (\j. sum (0..n) (\u. c u * g u j)) k =
     sum (0..n) (\u. c u * fin_two_filt N (\j. g u j) k)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[fin_two_filt; GSYM SUM_LMUL] THEN
  GEN_REWRITE_TAC LAND_CONV [SUM_SWAP_NUMSEG] THEN REWRITE_TAC[REAL_MUL_AC]);;

let FIN_TWO_ENTRY_DEC = prove
 (`forall z N r k. 1 <= N /\ r < 48 * N /\ k < 48 * N ==>
     cat_entryq z N r k =
     fin_two_filt N (fin_two_SX N r) k +
     sum (0..63 * N - 1) (\u. cheb_T (cat_dist N r) u *
                              fin_two_filt N (\j. fin_two_a z N u j) k) +
     sum (0..63 * N - 1) (\u. (cat_sgn N r * cheb_U (cat_dist N r - 1) u) *
                              fin_two_filt N (\j. fin_two_b N u j) k)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `cat_entryq z N r k = fin_two_filt N (\j. cat_rawq z N r j) k`
  SUBST1_TAC THENL [REWRITE_TAC[cat_entryq; fin_two_filt]; ALL_TAC] THEN
  TRANS_TAC EQ_TRANS
   `fin_two_filt N (\j. fin_two_SX N r j +
     (sum (0..63 * N - 1) (\u. cheb_T (cat_dist N r) u * fin_two_a z N u j) +
      sum (0..63 * N - 1) (\u. (cat_sgn N r * cheb_U (cat_dist N r - 1) u) *
                               fin_two_b N u j))) k` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC FIN_TWO_FILT_EQ THEN REPEAT STRIP_TAC THEN BETA_TAC THEN
    MATCH_MP_TAC FIN_TWO_RAW_DEC THEN ASM_ARITH_TAC;
    REWRITE_TAC[FIN_TWO_FILT_ADD] THEN
    REWRITE_TAC[REWRITE_RULE[] (ISPECL [`N:num`; `k:num`; `\u. cheb_T (cat_dist N r) u`]
                  FIN_TWO_FILT_SUM)] THEN
    REWRITE_TAC[REWRITE_RULE[] (ISPECL [`N:num`; `k:num`;
                  `\u. cat_sgn N r * cheb_U (cat_dist N r - 1) u`] FIN_TWO_FILT_SUM)] THEN
    REWRITE_TAC[ETA_AX]]);;

(* ------------------------------------------------------------------------- *)
(* Valuations of the pieces.                                                 *)
(* ------------------------------------------------------------------------- *)

let FIN_TWO_FILT_VAL = prove
 (`forall N FF k w. (forall v. v <= 4 * N ==> fin_vge 2 w (FF (7 * N + k + v)))
             ==> fin_vge 2 w (fin_two_filt N FF k)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[fin_two_filt] THEN
  MATCH_MP_TAC FIN_VGE_SUM THEN REWRITE_TAC[FIN_TWO_PRIME; FINITE_NUMSEG; IN_NUMSEG] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[REAL_MUL_ASSOC] THEN
  MATCH_MP_TAC FIN_VGE_ZP_MUL THEN ASM_SIMP_TAC[FIN_TWO_PRIME] THEN
  MATCH_MP_TAC FIN_ZP_MUL THEN
  SIMP_TAC[FIN_TWO_PRIME; FIN_ZP_POW; FIN_ZP_NEG; FIN_ZP_1; FIN_ZP_NUM]);;

let FIN_TWO_SX_VAL = prove
 (`forall N r j. 1 <= N /\ j < 65 * N + 1
           ==> fin_vge 2 (&(63 * N) - &4 - &2 * &(fin_flog 2 (65 * N + 1)))
                         (fin_two_SX N r j)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[fin_two_SX] THEN
  ASM_SIMP_TAC[FIN_TWO_PCOEF] THEN REWRITE_TAC[GSYM SUM_RMUL] THEN
  MATCH_MP_TAC FIN_VGE_SUM THEN REWRITE_TAC[FIN_TWO_PRIME; FINITE_NUMSEG; IN_NUMSEG] THEN
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  MATCH_MP_TAC FIN_VGE_SUM THEN REWRITE_TAC[FIN_TWO_PRIME; FINITE_NUMSEG; IN_NUMSEG] THEN
  X_GEN_TAC `u:num` THEN STRIP_TAC THEN
  ASM_CASES_TAC `fin_two_Q N u i = &0` THEN
  ASM_SIMP_TAC[REAL_MUL_RZERO; REAL_MUL_LZERO; FIN_VGE_0; FIN_TWO_PRIME] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP FIN_TWO_Q_SUPP) THEN STRIP_TAC THEN
  REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN MATCH_MP_TAC FIN_VGE_MONO THEN
  EXISTS_TAC `(&u - &1) + (&i - &2 * &(fin_flog 2 (65 * N + 1)) - &2)` THEN
  CONJ_TAC THENL
   [UNDISCH_TAC `63 * N <= i + u + 1` THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_LE; GSYM REAL_OF_NUM_ADD; GSYM REAL_OF_NUM_MUL] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC FIN_VGE_MUL THEN REWRITE_TAC[FIN_TWO_PRIME; FIN_TWO_CHEBT_VAL] THEN
  MATCH_MP_TAC FIN_VGE_ZP_MUL THEN REWRITE_TAC[FIN_TWO_PRIME; FIN_TWO_Q_ZP] THEN
  REWRITE_TAC[fin_two_R] THEN MATCH_MP_TAC FIN_TWO_X_VAL THEN ASM_ARITH_TAC);;

let FIN_TWO_E1_VAL = prove
 (`forall z N K. 1 <= N /\ fin_vge 2 (--(&K)) (&4 * z)
           ==> fin_vge 2 (--(&K + &2 * &(fin_flog 2 (65 * N + 1)) + &2)) (fin_two_e1 z N)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[fin_two_e1] THEN
  MATCH_MP_TAC FIN_VGE_SUB THEN REWRITE_TAC[FIN_TWO_PRIME] THEN CONJ_TAC THEN
  MATCH_MP_TAC FIN_VGE_MONO THENL
   [EXISTS_TAC `--(&K)` THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(SPEC `fin_flog 2 (65 * N + 1)` REAL_POS) THEN REAL_ARITH_TAC;
    EXISTS_TAC `&0 - &2 * &(fin_flog 2 (65 * N + 1)) - &2` THEN CONJ_TAC THENL
     [MP_TAC(SPEC `K:num` REAL_POS) THEN REAL_ARITH_TAC;
      MATCH_MP_TAC FIN_TWO_MK_VAL THEN ASM_ARITH_TAC]]);;

let FIN_TWO_E2_VAL = prove
 (`forall N. 1 <= N
       ==> fin_vge 2 (--(&2 * &(fin_flog 2 (65 * N + 1)) + &2)) (fin_two_e2 N)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[fin_two_e2; FIN_VGE_NEG_EQ] THEN
  MATCH_MP_TAC FIN_VGE_MONO THEN
  EXISTS_TAC `&0 - &2 * &(fin_flog 2 (65 * N + 1)) - &2` THEN CONJ_TAC THENL
   [REAL_ARITH_TAC; MATCH_MP_TAC FIN_TWO_MK_VAL THEN ASM_ARITH_TAC]);;

let FIN_TWO_A_VAL = prove
 (`forall z N K u j. 1 <= N /\ fin_vge 2 (--(&K)) (&4 * z)
     ==> fin_vge 2 ((&j + &u + &1 - &(65 * N)) -
                    (&K + &2 * &(fin_flog 2 (65 * N + 1)) + &2))
                   (fin_two_a z N u j)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[fin_two_a] THEN
  MATCH_MP_TAC FIN_VGE_MONO THEN
  EXISTS_TAC `--(&K + &2 * &(fin_flog 2 (65 * N + 1)) + &2) +
              (&j + &u + &1 - &(65 * N))` THEN
  CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC FIN_VGE_MUL THEN ASM_SIMP_TAC[FIN_TWO_PRIME; FIN_TWO_E1_VAL] THEN
  MATCH_MP_TAC FIN_VGE_SUM THEN REWRITE_TAC[FIN_TWO_PRIME; FINITE_NUMSEG] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  ASM_CASES_TAC `fin_two_Q N u i = &0` THEN
  ASM_SIMP_TAC[REAL_MUL_LZERO; FIN_VGE_0; FIN_TWO_PRIME] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP FIN_TWO_Q_SUPP) THEN STRIP_TAC THEN
  MATCH_MP_TAC FIN_VGE_ZP_MUL THEN REWRITE_TAC[FIN_TWO_PRIME; FIN_TWO_Q_ZP] THEN
  MATCH_MP_TAC FIN_VGE_MONO THEN EXISTS_TAC `&j - &i` THEN
  REWRITE_TAC[FIN_TWO_CKERN_VAL] THEN
  UNDISCH_TAC `i + u + 1 <= 65 * N` THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_LE; GSYM REAL_OF_NUM_ADD; GSYM REAL_OF_NUM_MUL] THEN
  REAL_ARITH_TAC);;

let FIN_TWO_THREE_HALVES = prove
 (`fin_vge 2 (--(&1)) (&3 / &2)`,
  SIMP_TAC[FIN_VGE_NEGPOW; FIN_TWO_PRIME] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  SIMP_TAC[FIN_ZP_NUM; FIN_TWO_PRIME]);;

let FIN_TWO_B_VAL = prove
 (`forall N u j. 1 <= N /\ j <= 65 * N
           ==> fin_vge 2 (--(&2 * &(fin_flog 2 (65 * N + 1)) + &3)) (fin_two_b N u j)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[fin_two_b] THEN
  MATCH_MP_TAC FIN_VGE_SUM THEN REWRITE_TAC[FIN_TWO_PRIME; FINITE_NUMSEG; IN_NUMSEG] THEN
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  MATCH_MP_TAC FIN_VGE_ZP_MUL THEN REWRITE_TAC[FIN_TWO_PRIME; FIN_TWO_Q_ZP] THEN
  MATCH_MP_TAC FIN_VGE_SUB THEN REWRITE_TAC[FIN_TWO_PRIME] THEN CONJ_TAC THENL
   [MATCH_MP_TAC FIN_VGE_MUL_ZP THEN REWRITE_TAC[FIN_TWO_PRIME] THEN CONJ_TAC THENL
     [COND_CASES_TAC THEN SIMP_TAC[FIN_ZP_0; FIN_ZP_1; FIN_TWO_PRIME]; ALL_TAC] THEN
    MATCH_MP_TAC FIN_VGE_MONO THEN
    EXISTS_TAC `--(&2 * &(fin_flog 2 (65 * N + 1)) + &2)` THEN
    ASM_SIMP_TAC[FIN_TWO_E2_VAL] THEN REAL_ARITH_TAC;
    MATCH_MP_TAC FIN_VGE_MONO THEN
    EXISTS_TAC `--(&1) + --(&2 * &(fin_flog 2 (65 * N + 1)))` THEN
    CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC FIN_VGE_MUL THEN REWRITE_TAC[FIN_TWO_PRIME; FIN_TWO_THREE_HALVES] THEN
    MATCH_MP_TAC FIN_TWO_Z0_VAL THEN ASM_ARITH_TAC]);;

let FIN_TWO_RAT_VAL = prove
 (`forall z. rational z ==> exists K. fin_vge 2 (--(&K)) (&4 * z)`,
  GEN_TAC THEN REWRITE_TAC[rational] THEN
  DISCH_THEN(X_CHOOSE_THEN `m:real` (X_CHOOSE_THEN `n:real` STRIP_ASSUME_TAC)) THEN
  UNDISCH_TAC `integer n` THEN REWRITE_TAC[integer] THEN
  DISCH_THEN(X_CHOOSE_TAC `q:num`) THEN
  EXISTS_TAC `index 2 q` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `~(q = 0)` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `abs n = &q` THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&4 * m / n = (&4 * m * (if &0 <= n then &1 else -- &1)) * inv(&q)`
  SUBST1_TAC THENL
   [UNDISCH_TAC `abs n = &q` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[real_abs] THEN COND_CASES_TAC THEN
    UNDISCH_TAC `~(n = &0)` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  MATCH_MP_TAC FIN_VGE_ZP_MUL THEN REWRITE_TAC[FIN_TWO_PRIME] THEN CONJ_TAC THENL
   [MATCH_MP_TAC FIN_ZP_INTEGER THEN REWRITE_TAC[FIN_TWO_PRIME] THEN
    REPEAT(MATCH_MP_TAC INTEGER_MUL THEN CONJ_TAC) THEN
    ASM_REWRITE_TAC[INTEGER_CLOSED] THEN COND_CASES_TAC THEN
    SIMP_TAC[INTEGER_CLOSED];
    MATCH_MP_TAC FIN_BDRY_INV_INDEX THEN ASM_REWRITE_TAC[FIN_TWO_PRIME; LE_REFL]]);;
