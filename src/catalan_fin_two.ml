(* ========================================================================= *)
(* fin_two_: Proposition 2.2, the uniform 2-adic estimate                     *)
(*   v_2(Delta_N) >= -(505/4608) n^2 - o(N^2).                               *)
(* ========================================================================= *)

needs "src/catalan_fin_two_dec.ml";;
needs "src/catalan_fin_two_cb.ml";;

let FIN_TWO_SGN_ZP = prove
 (`forall N r. fin_zp 2 (cat_sgn N r)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[cat_sgn] THEN REPEAT COND_CASES_TAC THEN
  SIMP_TAC[FIN_ZP_NEG; FIN_ZP_1; FIN_ZP_0; FIN_TWO_PRIME]);;

let FIN_TWO_SUM_02 = prove
 (`forall f. sum(0..2) f = f 0 + f 1 + f 2`,
  GEN_TAC THEN REWRITE_TAC[TWO; ONE; SUM_CLAUSES_NUMSEG] THEN
  REWRITE_TAC[ARITH_RULE `0 <= SUC n`] THEN REWRITE_TAC[GSYM ONE; GSYM TWO] THEN
  REAL_ARITH_TAC);;

let FIN_TWO_SUM_T = prove
 (`forall n (g:num#num->real).
     sum {(a,u) | a IN 0..2 /\ u IN 0..n} g =
     sum (0..n) (\u. g(0,u)) + sum (0..n) (\u. g(1,u)) + sum (0..n) (\u. g(2,u))`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`0..2`; `\a:num. 0..n`; `\a u. (g:num#num->real)(a,u)`]
         SUM_SUM_PRODUCT) THEN
  REWRITE_TAC[FINITE_NUMSEG; GSYM LAMBDA_PAIR_THM; ETA_AX] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[FIN_TWO_SUM_02]);;

let FIN_TWO_DELTA2 = prove
 (`forall n k (g:num->real). k <= n
     ==> sum (0..n) (\u. (if u = k then &1 else &0) * g u) = g k`,
  REPEAT STRIP_TAC THEN
  TRANS_TAC EQ_TRANS `sum (0..n) (\u. if u = k then (g:num->real) k else &0)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_EQ_NUMSEG THEN REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    REWRITE_TAC[SUM_DELTA; IN_NUMSEG] THEN ASM_REWRITE_TAC[LE_0]]);;

let FIN_TWO_GUARD2 = prove
 (`forall m n (f:num->real) (g:num->real). m <= n
     ==> sum (0..n) (\u. (if u <= m then f u else &0) * g u) =
         sum (0..m) (\u. g u * f u)`,
  REPEAT STRIP_TAC THEN
  TRANS_TAC EQ_TRANS `sum (0..n) (\u. if u <= m then (g:num->real) u * f u else &0)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_EQ_NUMSEG THEN REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
    COND_CASES_TAC THEN REAL_ARITH_TAC;
    MATCH_MP_TAC RAT_A_SUM_GUARD THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Atoms for FIN_VGE_NDET_ATOMS: (0,k) smoothed columns, (1,u) Chebyshev T   *)
(* vectors, (2,u) Chebyshev U vectors.                                       *)
(* ------------------------------------------------------------------------- *)

let fin_two_tt = new_definition
 `fin_two_tt N = {(a,u) | a IN 0..2 /\ u IN 0..65 * N}`;;

let fin_two_cc = new_definition
 `fin_two_cc z N (x:num#num) (k:num) =
      if FST x = 0 then (if SND x = k then &1 else &0)
      else if FST x = 1
      then (if SND x <= 63 * N - 1
            then fin_two_filt N (\j. fin_two_a z N (SND x) j) k else &0)
      else (if SND x <= 63 * N - 1
            then fin_two_filt N (\j. fin_two_b N (SND x) j) k else &0)`;;

let fin_two_vv = new_definition
 `fin_two_vv N (x:num#num) (r:num) =
      if FST x = 0 then fin_two_filt N (fin_two_SX N r) (SND x)
      else if FST x = 1 then cheb_T (cat_dist N r) (SND x)
      else cat_sgn N r * cheb_U (cat_dist N r - 1) (SND x)`;;

let fin_two_ww = new_definition
 `fin_two_ww N lam (x:num#num) (k:num) =
      if FST x = 0 then &(63 * N) - lam
      else if FST x = 1 then &2 * &(SND x) + &k - &(58 * N) - lam
      else &(SND x) - lam`;;

let FIN_TWO_ATOM_DEC = prove
 (`forall z N r k. 1 <= N /\ r IN 0..48 * N - 1 /\ k IN 0..48 * N - 1
     ==> cat_entryq z N r k =
         sum (fin_two_tt N) (\x. fin_two_cc z N x k * fin_two_vv N x r)`,
  REWRITE_TAC[fin_two_tt; FIN_TWO_SUM_T] THEN REWRITE_TAC[IN_NUMSEG] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[fin_two_cc; fin_two_vv; ARITH_EQ; FST; SND] THEN
  SUBGOAL_THEN `r < 48 * N /\ k < 48 * N` STRIP_ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[FIN_TWO_ENTRY_DEC] THEN
  SUBGOAL_THEN `k <= 65 * N /\ 63 * N - 1 <= 65 * N` STRIP_ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[FIN_TWO_DELTA2; FIN_TWO_GUARD2]);;

let FIN_TWO_ATOM_VAL0 = prove
 (`forall z N K u r k. 1 <= N /\ fin_vge 2 (--(&K)) (&4 * z) /\
     u <= 65 * N /\ r <= 48 * N - 1 /\ k <= 48 * N - 1
     ==> fin_vge 2
           (fin_two_ww N (&K + &2 * &(fin_flog 2 (65 * N + 1)) + &4) (0,u) k)
           (fin_two_cc z N (0,u) k * fin_two_vv N (0,u) r)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[fin_two_cc; fin_two_vv; fin_two_ww; FST; SND; ARITH_EQ] THEN
  COND_CASES_TAC THEN SIMP_TAC[REAL_MUL_LZERO; FIN_VGE_0; FIN_TWO_PRIME] THEN
  REWRITE_TAC[REAL_MUL_LID] THEN MATCH_MP_TAC FIN_VGE_MONO THEN
  EXISTS_TAC `&(63 * N) - &4 - &2 * &(fin_flog 2 (65 * N + 1))` THEN
  CONJ_TAC THENL
   [MP_TAC(SPEC `K:num` REAL_POS) THEN REAL_ARITH_TAC;
    MATCH_MP_TAC FIN_TWO_FILT_VAL THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC FIN_TWO_SX_VAL THEN ASM_ARITH_TAC]);;

let FIN_TWO_ATOM_VAL1 = prove
 (`forall z N K u r k. 1 <= N /\ fin_vge 2 (--(&K)) (&4 * z) /\
     u <= 65 * N /\ r <= 48 * N - 1 /\ k <= 48 * N - 1
     ==> fin_vge 2
           (fin_two_ww N (&K + &2 * &(fin_flog 2 (65 * N + 1)) + &4) (1,u) k)
           (fin_two_cc z N (1,u) k * fin_two_vv N (1,u) r)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[fin_two_cc; fin_two_vv; fin_two_ww; FST; SND; ARITH_EQ] THEN
  COND_CASES_TAC THEN SIMP_TAC[REAL_MUL_LZERO; FIN_VGE_0; FIN_TWO_PRIME] THEN
  MATCH_MP_TAC FIN_VGE_MONO THEN
  EXISTS_TAC `((&(7 * N) + &k + &u + &1 - &(65 * N)) -
               (&K + &2 * &(fin_flog 2 (65 * N + 1)) + &2)) + (&u - &1)` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[GSYM REAL_OF_NUM_MUL] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC FIN_VGE_MUL THEN REWRITE_TAC[FIN_TWO_PRIME; FIN_TWO_CHEBT_VAL] THEN
  MATCH_MP_TAC FIN_TWO_FILT_VAL THEN X_GEN_TAC `v:num` THEN DISCH_TAC THEN BETA_TAC THEN
  MATCH_MP_TAC FIN_VGE_MONO THEN
  EXISTS_TAC `(&(7 * N + k + v) + &u + &1 - &(65 * N)) -
              (&K + &2 * &(fin_flog 2 (65 * N + 1)) + &2)` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN MP_TAC(SPEC `v:num` REAL_POS) THEN
    REAL_ARITH_TAC;
    MATCH_MP_TAC FIN_TWO_A_VAL THEN ASM_REWRITE_TAC[]]);;

let FIN_TWO_ATOM_VAL2 = prove
 (`forall z N K u r k. 1 <= N /\ fin_vge 2 (--(&K)) (&4 * z) /\
     u <= 65 * N /\ r <= 48 * N - 1 /\ k <= 48 * N - 1
     ==> fin_vge 2
           (fin_two_ww N (&K + &2 * &(fin_flog 2 (65 * N + 1)) + &4) (2,u) k)
           (fin_two_cc z N (2,u) k * fin_two_vv N (2,u) r)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[fin_two_cc; fin_two_vv; fin_two_ww; FST; SND; ARITH_EQ] THEN
  COND_CASES_TAC THEN SIMP_TAC[REAL_MUL_LZERO; FIN_VGE_0; FIN_TWO_PRIME] THEN
  MATCH_MP_TAC FIN_VGE_MONO THEN
  EXISTS_TAC `--(&2 * &(fin_flog 2 (65 * N + 1)) + &3) + &u` THEN
  CONJ_TAC THENL
   [MP_TAC(SPEC `K:num` REAL_POS) THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC FIN_VGE_MUL THEN REWRITE_TAC[FIN_TWO_PRIME] THEN CONJ_TAC THENL
   [MATCH_MP_TAC FIN_TWO_FILT_VAL THEN X_GEN_TAC `v:num` THEN DISCH_TAC THEN BETA_TAC THEN
    MATCH_MP_TAC FIN_TWO_B_VAL THEN ASM_ARITH_TAC;
    MATCH_MP_TAC FIN_VGE_ZP_MUL THEN
    REWRITE_TAC[FIN_TWO_PRIME; FIN_TWO_SGN_ZP; FIN_TWO_CHEBU_VAL]]);;

let FIN_TWO_ATOM_VAL = prove
 (`forall z N K x r k.
     1 <= N /\ fin_vge 2 (--(&K)) (&4 * z) /\
     x IN fin_two_tt N /\ r IN 0..48 * N - 1 /\ k IN 0..48 * N - 1
     ==> fin_vge 2
           (fin_two_ww N (&K + &2 * &(fin_flog 2 (65 * N + 1)) + &4) x k)
           (fin_two_cc z N x k * fin_two_vv N x r)`,
  REWRITE_TAC[FORALL_PAIR_THM; fin_two_tt; IN_ELIM_PAIR_THM; IN_NUMSEG] THEN
  MAP_EVERY X_GEN_TAC [`z:real`; `N:num`; `K:num`; `a:num`; `u:num`; `r:num`; `k:num`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `a = 0 \/ a = 1 \/ a = 2` (REPEAT_TCL DISJ_CASES_THEN SUBST_ALL_TAC)
  THENL [ASM_ARITH_TAC; ALL_TAC; ALL_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[FIN_TWO_ATOM_VAL0; FIN_TWO_ATOM_VAL1; FIN_TWO_ATOM_VAL2]);;

let FIN_TWO_ATOM_COMB = prove
 (`forall N lam (f:num->num#num).
     1 <= N /\ &0 <= lam /\
     (forall k. k IN 0..48 * N - 1 ==> f k IN fin_two_tt N) /\
     (forall k1 k2. k1 IN 0..48 * N - 1 /\ k2 IN 0..48 * N - 1 /\ f k1 = f k2 ==> k1 = k2)
     ==> --(&505 / &4608 * &(48 * N) pow 2) - &48 * &N * (lam + &2) <=
         sum (0..48 * N - 1) (\k. fin_two_ww N lam (f k) k)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "in") (LABEL_TAC "inj")))) THEN
  REWRITE_TAC[fin_two_ww] THEN MATCH_MP_TAC FIN_TWO_CB_MAIN THEN
  REPEAT CONJ_TAC THENL
   [FIRST_ASSUM ACCEPT_TAC; FIRST_ASSUM ACCEPT_TAC; X_GEN_TAC `k:num` THEN DISCH_TAC THEN
    REMOVE_THEN "in" (MP_TAC o SPEC `k:num`) THEN
    ANTS_TAC THENL [REWRITE_TAC[IN_NUMSEG] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    SPEC_TAC(`(f:num->num#num) k`,`p:num#num`) THEN
    REWRITE_TAC[FORALL_PAIR_THM; fin_two_tt; IN_ELIM_PAIR_THM; IN_NUMSEG] THEN
    ARITH_TAC;
    MAP_EVERY X_GEN_TAC [`k1:num`; `k2:num`] THEN STRIP_TAC THEN
    REMOVE_THEN "inj" MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[IN_NUMSEG] THEN ASM_ARITH_TAC]);;

let FIN_TWO_ADIC = prove
 (`forall z. rational z
   ==> exists f. (forall e. &0 < e ==> exists N0. forall N. N0 <= N ==> f N <= e * &N pow 2) /\
           forall N. 1 <= N ==> fin_vge 2 (--(&505 / &4608 * &(48 * N) pow 2 + f N))
                                    (cat_detq z N)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(X_CHOOSE_TAC `K:num` o MATCH_MP FIN_TWO_RAT_VAL) THEN
  EXISTS_TAC `\N. &96 * &N * ((&K + &6) / &2 + &(fin_flog 2 (65 * N + 1)))` THEN
  CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC FIN_TWO_CB_LITTLE_O THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(SPEC `K:num` REAL_POS) THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  X_GEN_TAC `N:num` THEN DISCH_TAC THEN REWRITE_TAC[cat_detq] THEN
  MATCH_MP_TAC FIN_VGE_MONO THEN
  EXISTS_TAC `--(&505 / &4608 * &(48 * N) pow 2) -
              &48 * &N * ((&K + &2 * &(fin_flog 2 (65 * N + 1)) + &4) + &2)` THEN
  CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC(INST_TYPE [`:num#num`,`:B`] FIN_VGE_NDET_ATOMS) THEN
  MAP_EVERY EXISTS_TAC
   [`fin_two_tt N`; `fin_two_cc z N`; `fin_two_vv N`;
    `fin_two_ww N (&K + &2 * &(fin_flog 2 (65 * N + 1)) + &4)`] THEN
  REWRITE_TAC[FIN_TWO_PRIME; FINITE_NUMSEG] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[fin_two_tt] THEN SIMP_TAC[FINITE_PRODUCT; FINITE_NUMSEG];
    ASM_SIMP_TAC[FIN_TWO_ATOM_DEC];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC FIN_TWO_ATOM_VAL THEN
    REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    REPEAT STRIP_TAC THEN MATCH_MP_TAC FIN_TWO_ATOM_COMB THEN
    REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
    MP_TAC(SPEC `K:num` REAL_POS) THEN
    MP_TAC(SPEC `fin_flog 2 (65 * N + 1)` REAL_POS) THEN REAL_ARITH_TAC]);;
