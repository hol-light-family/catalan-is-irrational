(* ========================================================================= *)
(* CAT_FINITE_PLACE, columns at odd primes (prefix fin_col_): the vector     *)
(* congruences (36)-(37), the pair sums and the central layer (Lemma 3.2),   *)
(* derived termwise from the scalar digit reductions (fin_dig_), which are   *)
(* collected as the hypothesis fin_col_dighyps.                              *)
(* ========================================================================= *)

needs "src/catalan_fin_col_base.ml";;

(* ------------------------------------------------------------------------- *)
(* Digit arithmetic.                                                         *)
(* ------------------------------------------------------------------------- *)

let FIN_COL_MOD_DECOMP = prove
 (`forall p m l. 0 < p /\ m MOD p = l ==> m = ((m - l) DIV p) * p + l`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`m:num`; `p:num`] DIVISION) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ASM_REWRITE_TAC[]] THEN
  DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
  SUBGOAL_THEN `(m - l) DIV p = m DIV p` SUBST1_TAC THENL
   [MATCH_MP_TAC DIV_UNIQ THEN EXISTS_TAC `0` THEN ASM_ARITH_TAC; ASM_ARITH_TAC]);;

let FIN_COL_DIGIT_MOD = prove
 (`forall p i l. 0 < p /\ l < p
           ==> (i + 1 + (l + (p * (i + 1) - (i + 1))) MOD p) MOD p = l`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `i + 1 <= p * (i + 1)` ASSUME_TAC THENL
   [MATCH_MP_TAC(ARITH_RULE `1 * n <= p * n ==> n <= p * n`) THEN
    REWRITE_TAC[LE_MULT_RCANCEL] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `forall a b. (a + b MOD p) MOD p = (a + b) MOD p` (fun th -> REWRITE_TAC[th; ADD_ASSOC])
  THENL [ONCE_REWRITE_TAC[GSYM MOD_ADD_MOD] THEN REWRITE_TAC[MOD_MOD_REFL]; ALL_TAC] THEN
  SUBGOAL_THEN `((i + 1) + l) + (p * (i + 1) - (i + 1)) = l + p * (i + 1)` SUBST1_TAC THENL
   [ASM_ARITH_TAC; ASM_SIMP_TAC[MOD_MULT_ADD; MOD_LT]]);;

let FIN_COL_DIGIT = prove
 (`forall p i l. 0 < p /\ l < p
           ==> (l + (p * (i + 1) - (i + 1))) MOD p < p /\
               i + 1 + (l + (p * (i + 1) - (i + 1))) MOD p =
               (((i + 1 + (l + (p * (i + 1) - (i + 1))) MOD p) - l) DIV p) * p + l`,
  REPEAT STRIP_TAC THENL
   [ASM_SIMP_TAC[MOD_LT_EQ; ARITH_RULE `0 < p ==> ~(p = 0)`];
    MATCH_MP_TAC FIN_COL_MOD_DECOMP THEN ASM_SIMP_TAC[FIN_COL_DIGIT_MOD]]);;

let FIN_COL_MULT_CASES = prove
 (`forall p Q. Q = 0 /\ Q * p = 0 \/ Q = 1 /\ Q * p = p \/ Q = 2 /\ Q * p = 2 * p \/
         3 * p <= Q * p`,
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `Q = 0` THEN ASM_REWRITE_TAC[MULT_CLAUSES] THEN
  ASM_CASES_TAC `Q = 1` THEN ASM_REWRITE_TAC[MULT_CLAUSES] THEN
  ASM_CASES_TAC `Q = 2` THEN ASM_REWRITE_TAC[MULT_CLAUSES] THEN
  REWRITE_TAC[LE_MULT_RCANCEL] THEN ASM_ARITH_TAC);;

let FIN_COL_DIGIT_CLASS = prove
 (`forall p i l. 0 < p /\ l < p /\ i < 2 * p + l
           ==> (i < l /\
                (((i + 1 + (l + (p * (i + 1) - (i + 1))) MOD p) - l) DIV p) = 0) \/
               (l <= i /\ i < p + l /\
                (((i + 1 + (l + (p * (i + 1) - (i + 1))) MOD p) - l) DIV p) = 1) \/
               (p + l <= i /\
                (((i + 1 + (l + (p * (i + 1) - (i + 1))) MOD p) - l) DIV p) = 2 /\
                (l + (p * (i + 1) - (i + 1))) MOD p = ((2 * p + l) - 1) - i)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`p:num`; `i:num`; `l:num`] FIN_COL_DIGIT) THEN ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `d = (l + (p * (i + 1) - (i + 1))) MOD p` THEN
  ABBREV_TAC `Q = ((i + 1 + d) - l) DIV p` THEN STRIP_TAC THEN
  MP_TAC(SPECL [`p:num`; `Q:num`] FIN_COL_MULT_CASES) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

let FIN_COL_RES_CLASS = prove
 (`forall p i l. 0 < p /\ l < p /\ i < 2 * p + l
           ==> (i MOD p = l <=> i = l \/ i = p + l) /\
               (i = l ==> i DIV p = 0) /\ (i = p + l ==> i DIV p = 1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(l DIV p = 0 /\ l MOD p = l) /\ ((p + l) DIV p = 1 /\ (p + l) MOD p = l)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC DIVMOD_UNIQ THEN ASM_ARITH_TAC; ALL_TAC] THEN
  REPEAT CONJ_TAC THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  EQ_TAC THENL [ALL_TAC; STRIP_TAC THEN ASM_REWRITE_TAC[]] THEN
  DISCH_TAC THEN
  MP_TAC(SPECL [`i:num`; `p:num`] DIVISION) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ASM_REWRITE_TAC[]] THEN
  MP_TAC(SPECL [`p:num`; `i DIV p`] FIN_COL_MULT_CASES) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

let FIN_COL_ADD_MOD_P = prove
 (`forall p y. (p + y) MOD p = y MOD p`,
  REPEAT GEN_TAC THEN
  MP_TAC(SPECL [`1`; `p:num`; `y:num`] (CONJUNCT1 MOD_MULT_ADD)) THEN
  REWRITE_TAC[MULT_CLAUSES]);;

(* ------------------------------------------------------------------------- *)
(* The scalar digit reductions (statements of the fin_dig_ agent).           *)
(* ------------------------------------------------------------------------- *)

let fin_col_dighyps = new_definition
 `fin_col_dighyps <=>
   (forall p H i j. prime p /\ ~(p = 2) /\ 4 * H < p * p /\ p <= H /\ i < H /\ j < H
     ==> fin_zp p (&p pow 2 * cat_M0 i j) /\
         fin_vge p (&1) (&p pow 2 * cat_M0 i j - fin_E p ((j + (p * (i + 1) - (i + 1))) MOD p) *
           fin_M0x (((i + 1 + ((j + (p * (i + 1) - (i + 1))) MOD p)) - j MOD p) DIV p) (j DIV p))) /\
   (forall p H i j. prime p /\ ~(p = 2) /\ 4 * H < p * p /\ p <= H /\ i < H /\ j < H
     ==> fin_zp p (&p pow 2 * cat_Z0 i j) /\
         fin_vge p (&1) (&p pow 2 * cat_Z0 i j -
           (if i MOD p = j MOD p then cat_Z0 (i DIV p) (j DIV p) else &0))) /\
   (forall p H i j. prime p /\ ~(p = 2) /\ H < 2 * p /\ p <= H /\ H <= j + p /\ j < p /\ i < H
     ==> fin_zp p (&p * cat_M0 i j) /\
         fin_vge p (&1) (&p * cat_M0 i j + sum {l | l < H - p} (\l. if p + l <= i /\ i < 2 * p + l
                  then &2 * fin_E p (((2 * p + l) - 1) - i) / (&j - &l) else &0))) /\
   (forall p H i j. prime p /\ ~(p = 2) /\ H < 2 * p /\ p <= H /\ H <= j + p /\ j < p /\ i < H
     ==> fin_zp p (&p * cat_Z0 i j) /\
         fin_vge p (&1) (&p * cat_Z0 i j - (if p <= i /\ i < H then &1 / (&(i - p) - &j) else &0)))`;;

let FIN_COL_DIG_M = prove
 (`forall p H i j. fin_col_dighyps /\
     prime p /\ ~(p = 2) /\ 4 * H < p * p /\ p <= H /\ i < H /\ j < H
     ==> fin_zp p (&p pow 2 * cat_M0 i j) /\
         fin_vge p (&1) (&p pow 2 * cat_M0 i j - fin_E p ((j + (p * (i + 1) - (i + 1))) MOD p) *
           fin_M0x (((i + 1 + ((j + (p * (i + 1) - (i + 1))) MOD p)) - j MOD p) DIV p) (j DIV p))`,
  REWRITE_TAC[fin_col_dighyps] THEN MESON_TAC[]);;

let FIN_COL_DIG_Z = prove
 (`forall p H i j. fin_col_dighyps /\
     prime p /\ ~(p = 2) /\ 4 * H < p * p /\ p <= H /\ i < H /\ j < H
     ==> fin_zp p (&p pow 2 * cat_Z0 i j) /\
         fin_vge p (&1) (&p pow 2 * cat_Z0 i j -
           (if i MOD p = j MOD p then cat_Z0 (i DIV p) (j DIV p) else &0))`,
  REWRITE_TAC[fin_col_dighyps] THEN MESON_TAC[]);;

let FIN_COL_DIG_CM = prove
 (`forall p H i j. fin_col_dighyps /\
     prime p /\ ~(p = 2) /\ H < 2 * p /\ p <= H /\ H <= j + p /\ j < p /\ i < H
     ==> fin_zp p (&p * cat_M0 i j) /\
         fin_vge p (&1) (&p * cat_M0 i j + sum {l | l < H - p} (\l. if p + l <= i /\ i < 2 * p + l
                  then &2 * fin_E p (((2 * p + l) - 1) - i) / (&j - &l) else &0))`,
  REWRITE_TAC[fin_col_dighyps] THEN MESON_TAC[]);;

let FIN_COL_DIG_CZ = prove
 (`forall p H i j. fin_col_dighyps /\
     prime p /\ ~(p = 2) /\ H < 2 * p /\ p <= H /\ H <= j + p /\ j < p /\ i < H
     ==> fin_zp p (&p * cat_Z0 i j) /\
         fin_vge p (&1) (&p * cat_Z0 i j - (if p <= i /\ i < H then &1 / (&(i - p) - &j) else &0))`,
  REWRITE_TAC[fin_col_dighyps] THEN MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Termwise expansion of a scaled raw entry.                                 *)
(* ------------------------------------------------------------------------- *)

let FIN_COL_RAW_SCALE = prove
 (`forall z N r j x.
     x * cat_rawq z N r j =
     sum (0..65 * N) (\i. cat_pcoef N r i * (x * cat_M0 i j) -
                          &3 / &2 * (cat_dcoef N r i * (x * cat_Z0 i j))) +
     &4 * z * sum (0..65 * N) (\i. cat_pcoef N r i * (x * cat_ckern i j))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[cat_rawq; REAL_SUB_LDISTRIB; GSYM SUM_LMUL; GSYM SUM_SUB_NUMSEG;
              GSYM SUM_ADD_NUMSEG] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
  REAL_ARITH_TAC);;

let FIN_COL_ODD_ZP_3_2 = prove
 (`forall p. prime p /\ ~(p = 2) ==> fin_zp p (&3 / &2)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC FIN_ZP_DIV_NUM THEN
  ASM_SIMP_TAC[FIN_ZP_NUM; DIVIDES_PRIME_PRIME; PRIME_2]);;

let FIN_COL_ZTERM = prove
 (`forall p z N r j k. prime p /\ ~(p = 2) /\ fin_zp p z
     ==> fin_vge p (&k) (&4 * z * sum (0..65 * N)
                          (\i. cat_pcoef N r i * (&p pow k * cat_ckern i j)))`,
  REPEAT STRIP_TAC THEN
  REPEAT(MATCH_MP_TAC FIN_VGE_ZP_MUL THEN ASM_SIMP_TAC[FIN_ZP_NUM]) THEN
  MATCH_MP_TAC FIN_VGE_SUM THEN ASM_REWRITE_TAC[FINITE_NUMSEG] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC FIN_VGE_ZP_MUL THEN ASM_SIMP_TAC[FIN_COL_PCOEF_ZP] THEN
  MATCH_MP_TAC FIN_VGE_MUL_ZP THEN ASM_SIMP_TAC[FIN_COL_CKERN_ZP; FIN_VGE_PPOW]);;

let FIN_COL_SUM_TERMS = prove
 (`forall p k N r A B. prime p /\ ~(p = 2) /\
     (forall i. i < 65 * N ==> fin_vge p k (cat_pcoef N r i * A i) /\
                         fin_vge p k (cat_dcoef N r i * B i))
     ==> fin_vge p k (sum (0..65 * N) (\i. cat_pcoef N r i * A i -
                                          &3 / &2 * (cat_dcoef N r i * B i)))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC FIN_VGE_SUM THEN
  ASM_REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  REWRITE_TAC[] THEN ASM_CASES_TAC `i < 65 * N` THENL
   [MATCH_MP_TAC FIN_VGE_SUB THEN ASM_SIMP_TAC[] THEN
    MATCH_MP_TAC FIN_VGE_ZP_MUL THEN ASM_SIMP_TAC[FIN_COL_ODD_ZP_3_2];
    SUBGOAL_THEN `65 * N <= i` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[FIN_COL_PCOEF_HIGH; FIN_COL_DCOEF_HIGH] THEN
    ASM_SIMP_TAC[REAL_MUL_LZERO; REAL_MUL_RZERO; REAL_SUB_REFL; FIN_VGE_0]]);;

let FIN_COL_VGE_SCALE = prove
 (`forall p k n x. prime p ==> (fin_vge p (k - &n) x <=> fin_vge p k (&p pow n * x))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`p:num`; `k - &n`; `n:num`; `x:real`] FIN_VGE_PPOW_MUL) THEN
  ASM_REWRITE_TAC[REAL_SUB_ADD] THEN MESON_TAC[]);;

(* Every raw column F_j, j < H, lies in p^(-2) Z_(p)^n. *)

let FIN_COL_RAW_W2 = prove
 (`forall p z N r j. prime p /\ ~(p = 2) /\ 4 * (65 * N) < p * p /\ p <= 65 * N /\
               fin_zp p z /\ fin_col_dighyps /\ j < 65 * N
               ==> fin_vge p (--(&2)) (cat_rawq z N r j)`,
  REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[REAL_ARITH `--(&2) = &0 - &2`] THEN
  ASM_SIMP_TAC[FIN_COL_VGE_SCALE; FIN_COL_RAW_SCALE] THEN
  MATCH_MP_TAC FIN_VGE_ADD THEN ASM_SIMP_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC FIN_COL_SUM_TERMS THEN ASM_REWRITE_TAC[] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC FIN_VGE_ZP_MUL THEN
    ASM_SIMP_TAC[FIN_COL_PCOEF_ZP; FIN_COL_DCOEF_ZP; FIN_VGE_ZP] THEN
    ASM_MESON_TAC[FIN_COL_DIG_M; FIN_COL_DIG_Z];
    MATCH_MP_TAC FIN_VGE_MONO THEN EXISTS_TAC `&2` THEN
    ASM_SIMP_TAC[FIN_COL_ZTERM] THEN REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Elementary combination lemmas.                                            *)
(* ------------------------------------------------------------------------- *)

let FIN_COL_COMB2 = prove
 (`forall p k c A B a b u. prime p /\ fin_zp p c /\
     fin_vge p k (A - u * a) /\ fin_vge p k (B - u * b) /\ a + b = &0
     ==> fin_vge p k (c * (A + B))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(A:real) + B = ((A - u * a) + (B - u * b)) + u * (a + b)` SUBST1_TAC THENL
   [CONV_TAC REAL_RING; ASM_REWRITE_TAC[REAL_MUL_RZERO; REAL_ADD_RID]] THEN
  MATCH_MP_TAC FIN_VGE_ZP_MUL THEN ASM_SIMP_TAC[FIN_VGE_ADD]);;

let FIN_COL_COMB2_NOE = prove
 (`forall p k c A B a b. prime p /\ fin_zp p c /\
     fin_vge p k (A - a) /\ fin_vge p k (B - b) /\ a + b = &0
     ==> fin_vge p k (c * (A + B))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC FIN_COL_COMB2 THEN
  MAP_EVERY EXISTS_TAC [`a:real`; `b:real`; `&1`] THEN
  ASM_REWRITE_TAC[REAL_MUL_LID]);;

let FIN_COL_DCOEF_PICK = prove
 (`forall N r m. sum (0..65 * N) (\i. cat_dcoef N r i * (if i = m then &1 else &0)) =
           cat_dcoef N r m`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `sum (0..65 * N) (\i. cat_dcoef N r i * (if i = m then &1 else &0)) =
                sum (0..65 * N) (\i. if i = m then cat_dcoef N r m else &0)` SUBST1_TAC THENL
   [MATCH_MP_TAC SUM_EQ_NUMSEG THEN REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[REAL_MUL_RID; REAL_MUL_RZERO];
    REWRITE_TAC[SUM_DELTA; IN_NUMSEG; LE_0] THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC FIN_COL_DCOEF_HIGH THEN ASM_ARITH_TAC]);;

let FIN_COL_RAW_SCALE2 = prove
 (`forall z N r j1 j2 x.
     x * cat_rawq z N r j1 + x * cat_rawq z N r j2 =
     sum (0..65 * N) (\i. cat_pcoef N r i * (x * cat_M0 i j1 + x * cat_M0 i j2) -
                          &3 / &2 * (cat_dcoef N r i * (x * cat_Z0 i j1 + x * cat_Z0 i j2))) +
     (&4 * z * sum (0..65 * N) (\i. cat_pcoef N r i * (x * cat_ckern i j1)) +
      &4 * z * sum (0..65 * N) (\i. cat_pcoef N r i * (x * cat_ckern i j2)))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[cat_rawq; REAL_SUB_LDISTRIB; GSYM SUM_LMUL; GSYM SUM_SUB_NUMSEG;
              GSYM SUM_ADD_NUMSEG] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
  REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Index facts for the residue l and the column p + l.                      *)
(* ------------------------------------------------------------------------- *)

let FIN_COL_PL_INDEX = prove
 (`forall p l i. 0 < p /\ l < p
           ==> l MOD p = l /\ l DIV p = 0 /\ (p + l) MOD p = l /\ (p + l) DIV p = 1 /\
               ((p + l) + (p * (i + 1) - (i + 1))) MOD p =
               (l + (p * (i + 1) - (i + 1))) MOD p`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[GSYM ADD_ASSOC; FIN_COL_ADD_MOD_P] THEN
  ASM_SIMP_TAC[MOD_LT; DIV_LT] THEN
  MATCH_MP_TAC DIV_UNIQ THEN EXISTS_TAC `l:num` THEN ASM_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Pair sums: p^2 (F_l + F_(p+l)) == U_l = 0 (mod p) for l < A.             *)
(* ------------------------------------------------------------------------- *)

let FIN_COL_PAIR_M = prove
 (`forall p N r i l. fin_col_dighyps /\ prime p /\ ~(p = 2) /\
     4 * (65 * N) < p * p /\ p <= 65 * N /\ r < 48 * N /\
     65 * N <= 2 * p + l /\ l < p /\ l < 19 * N /\ p + l < 65 * N /\ i < 65 * N
     ==> fin_vge p (&1) (cat_pcoef N r i *
                         (&p pow 2 * cat_M0 i l + &p pow 2 * cat_M0 i (p + l)))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `0 < p` ASSUME_TAC THENL
   [ASM_MESON_TAC[PRIME_IMP_NZ; ARITH_RULE `0 < p <=> ~(p = 0)`]; ALL_TAC] THEN
  MP_TAC(SPECL [`p:num`; `l:num`; `i:num`] FIN_COL_PL_INDEX) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`p:num`; `65 * N`; `i:num`; `p + l:num`] FIN_COL_DIG_M) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; DISCH_THEN(MP_TAC o CONJUNCT2)] THEN
  MP_TAC(SPECL [`p:num`; `65 * N`; `i:num`; `l:num`] FIN_COL_DIG_M) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; DISCH_THEN(MP_TAC o CONJUNCT2)] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`p:num`; `i:num`; `l:num`] FIN_COL_DIGIT_CLASS) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[FIN_COL_M0X_SMALL] THENL
   [SUBGOAL_THEN `i < 19 * N` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[FIN_COL_PCOEF_LOW; REAL_MUL_LZERO; FIN_VGE_0];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC FIN_COL_COMB2 THEN
    MAP_EVERY EXISTS_TAC [`&0`; `&0`; `fin_E p ((l + (p * (i + 1) - (i + 1))) MOD p)`] THEN
    ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[FIN_COL_PCOEF_ZP] THEN REAL_ARITH_TAC;
    REPEAT STRIP_TAC THEN MATCH_MP_TAC FIN_COL_COMB2 THEN
    MAP_EVERY EXISTS_TAC [`&2`; `-- &2`; `fin_E p (((2 * p + l) - 1) - i)`] THEN
    ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[FIN_COL_PCOEF_ZP] THEN REAL_ARITH_TAC]);;



let FIN_COL_PAIR_Z = prove
 (`forall p N r i l. fin_col_dighyps /\ prime p /\ ~(p = 2) /\
     4 * (65 * N) < p * p /\ p <= 65 * N /\ r < 48 * N /\
     65 * N <= 2 * p + l /\ l < p /\ l < 19 * N /\ p + l < 65 * N /\ i < 65 * N
     ==> fin_vge p (&1) (cat_dcoef N r i *
                         (&p pow 2 * cat_Z0 i l + &p pow 2 * cat_Z0 i (p + l)))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `0 < p` ASSUME_TAC THENL
   [ASM_MESON_TAC[PRIME_IMP_NZ; ARITH_RULE `0 < p <=> ~(p = 0)`]; ALL_TAC] THEN
  SUBGOAL_THEN `~(l = p + l) /\ i < 2 * p + l` STRIP_ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`p:num`; `65 * N`; `i:num`; `p + l:num`] FIN_COL_DIG_Z) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; DISCH_THEN(MP_TAC o CONJUNCT2)] THEN
  MP_TAC(SPECL [`p:num`; `65 * N`; `i:num`; `l:num`] FIN_COL_DIG_Z) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; DISCH_THEN(MP_TAC o CONJUNCT2)] THEN
  ASM_CASES_TAC `i:num = l` THENL
   [SUBGOAL_THEN `i <= 19 * N` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[FIN_COL_DCOEF_LOW; REAL_MUL_LZERO; FIN_VGE_0];
    ALL_TAC] THEN
  MP_TAC(SPECL [`p:num`; `l:num`; `i:num`] FIN_COL_PL_INDEX) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`p:num`; `i:num`; `l:num`] FIN_COL_RES_CLASS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_CASES_TAC `i:num = p + l` THENL
   [ASM_REWRITE_TAC[FIN_COL_Z0_SMALL] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC FIN_COL_COMB2_NOE THEN
    MAP_EVERY EXISTS_TAC [`&1`; `-- &1`] THEN
    ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[FIN_COL_DCOEF_ZP] THEN REAL_ARITH_TAC;
    ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC FIN_COL_COMB2_NOE THEN
    MAP_EVERY EXISTS_TAC [`&0`; `&0`] THEN
    ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[FIN_COL_DCOEF_ZP] THEN REAL_ARITH_TAC]);;

(* Equation (37), the pair sum: F_l + F_(p+l) lies in p^(-1) Z_(p)^n.       *)

let FIN_COL_PAIR = prove
 (`forall p z N r l. fin_col_dighyps /\ prime p /\ ~(p = 2) /\
     4 * (65 * N) < p * p /\ p <= 65 * N /\ fin_zp p z /\ r < 48 * N /\
     65 * N <= 2 * p + l /\ l < p /\ l < 19 * N /\ p + l < 65 * N
     ==> fin_vge p (--(&1)) (cat_rawq z N r l + cat_rawq z N r (p + l))`,
  REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[REAL_ARITH `--(&1) = &1 - &2`] THEN
  ASM_SIMP_TAC[FIN_COL_VGE_SCALE] THEN
  ONCE_REWRITE_TAC[REAL_ADD_LDISTRIB] THEN REWRITE_TAC[FIN_COL_RAW_SCALE2] THEN
  MATCH_MP_TAC FIN_VGE_ADD THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC FIN_COL_SUM_TERMS THEN ASM_REWRITE_TAC[] THEN
    REPEAT STRIP_TAC THEN REWRITE_TAC[] THENL
     [MATCH_MP_TAC FIN_COL_PAIR_M; MATCH_MP_TAC FIN_COL_PAIR_Z] THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC FIN_VGE_ADD THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THEN
    MATCH_MP_TAC FIN_VGE_MONO THEN EXISTS_TAC `&2` THEN
    ASM_SIMP_TAC[FIN_COL_ZTERM] THEN REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The leading residue of a low column: p^2 F_l == V_l (mod p), l >= H - 2p.  *)
(* ------------------------------------------------------------------------- *)

let fin_col_V = new_definition
 `fin_col_V N p l r =
    &2 * sum (0..65 * N) (\i. cat_pcoef N r i *
           (if p + l <= i /\ i < 2 * p + l then fin_E p (((2 * p + l) - 1) - i) else &0)) -
    &3 / &2 * cat_dcoef N r (p + l)`;;

let FIN_COL_V_ZP = prove
 (`forall p N l r. prime p /\ ~(p = 2) ==> fin_zp p (fin_col_V N p l r)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[fin_col_V] THEN
  MATCH_MP_TAC FIN_ZP_SUB THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THEN
  MATCH_MP_TAC FIN_ZP_MUL THEN
  ASM_SIMP_TAC[FIN_ZP_NUM; FIN_COL_ODD_ZP_3_2; FIN_COL_DCOEF_ZP] THEN
  MATCH_MP_TAC FIN_ZP_SUM THEN ASM_REWRITE_TAC[FINITE_NUMSEG] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN MATCH_MP_TAC FIN_ZP_MUL THEN
  ASM_SIMP_TAC[FIN_COL_PCOEF_ZP] THEN COND_CASES_TAC THEN
  ASM_SIMP_TAC[FIN_COL_E_ZP; FIN_ZP_0]);;

let FIN_COL_XLOW_M = prove
 (`forall p N r i l. fin_col_dighyps /\ prime p /\ ~(p = 2) /\
     4 * (65 * N) < p * p /\ p <= 65 * N /\
     65 * N <= 2 * p + l /\ l < p /\ i < 65 * N
     ==> fin_vge p (&1) (cat_pcoef N r i *
           (&p pow 2 * cat_M0 i l -
            &2 * (if p + l <= i /\ i < 2 * p + l
                  then fin_E p (((2 * p + l) - 1) - i) else &0)))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `0 < p` ASSUME_TAC THENL
   [ASM_MESON_TAC[PRIME_IMP_NZ; ARITH_RULE `0 < p <=> ~(p = 0)`]; ALL_TAC] THEN
  SUBGOAL_THEN `i < 2 * p + l` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`p:num`; `l:num`; `i:num`] FIN_COL_PL_INDEX) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`p:num`; `65 * N`; `i:num`; `l:num`] FIN_COL_DIG_M) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; DISCH_THEN(MP_TAC o CONJUNCT2)] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`p:num`; `i:num`; `l:num`] FIN_COL_DIGIT_CLASS) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[FIN_COL_M0X_SMALL] THEN
  ASM_SIMP_TAC[ARITH_RULE `i:num < l ==> ~(p + l <= i)`;
               ARITH_RULE `i:num < p + l ==> ~(p + l <= i)`] THEN
  DISCH_TAC THEN MATCH_MP_TAC FIN_VGE_ZP_MUL THEN ASM_SIMP_TAC[FIN_COL_PCOEF_ZP] THEN
  POP_ASSUM MP_TAC THEN MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN REAL_ARITH_TAC);;

let FIN_COL_XLOW_Z = prove
 (`forall p N r i l. fin_col_dighyps /\ prime p /\ ~(p = 2) /\
     4 * (65 * N) < p * p /\ p <= 65 * N /\
     65 * N <= 2 * p + l /\ l < p /\ i < 65 * N
     ==> fin_vge p (&1) (cat_dcoef N r i *
           (&p pow 2 * cat_Z0 i l - (if i = p + l then &1 else &0)))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `0 < p` ASSUME_TAC THENL
   [ASM_MESON_TAC[PRIME_IMP_NZ; ARITH_RULE `0 < p <=> ~(p = 0)`]; ALL_TAC] THEN
  SUBGOAL_THEN `~(l = p + l) /\ i < 2 * p + l` STRIP_ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`p:num`; `65 * N`; `i:num`; `l:num`] FIN_COL_DIG_Z) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; DISCH_THEN(MP_TAC o CONJUNCT2)] THEN
  MP_TAC(SPECL [`p:num`; `l:num`; `i:num`] FIN_COL_PL_INDEX) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`p:num`; `i:num`; `l:num`] FIN_COL_RES_CLASS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_CASES_TAC `i:num = l` THEN ASM_REWRITE_TAC[] THEN
  TRY(ASM_CASES_TAC `i:num = p + l`) THEN ASM_REWRITE_TAC[FIN_COL_Z0_SMALL] THEN
  DISCH_TAC THEN MATCH_MP_TAC FIN_VGE_ZP_MUL THEN ASM_SIMP_TAC[FIN_COL_DCOEF_ZP]);;

let FIN_COL_XLOW = prove
 (`forall p z N r l. fin_col_dighyps /\ prime p /\ ~(p = 2) /\
     4 * (65 * N) < p * p /\ p <= 65 * N /\ fin_zp p z /\
     65 * N <= 2 * p + l /\ l < p
     ==> fin_vge p (&1) (&p pow 2 * cat_rawq z N r l - fin_col_V N p l r)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `&p pow 2 * cat_rawq z N r l - fin_col_V N p l r =
    sum (0..65 * N) (\i. cat_pcoef N r i *
           (&p pow 2 * cat_M0 i l -
            &2 * (if p + l <= i /\ i < 2 * p + l
                  then fin_E p (((2 * p + l) - 1) - i) else &0)) -
         &3 / &2 * (cat_dcoef N r i *
           (&p pow 2 * cat_Z0 i l - (if i = p + l then &1 else &0)))) +
    &4 * z * sum (0..65 * N) (\i. cat_pcoef N r i * (&p pow 2 * cat_ckern i l))`
  SUBST1_TAC THENL
   [REWRITE_TAC[fin_col_V; FIN_COL_RAW_SCALE] THEN
    SUBST1_TAC(SYM(SPECL [`N:num`; `r:num`; `p + l:num`] FIN_COL_DCOEF_PICK)) THEN
    REWRITE_TAC[GSYM SUM_LMUL; GSYM SUM_SUB_NUMSEG; GSYM SUM_ADD_NUMSEG] THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC FIN_VGE_ADD THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC FIN_COL_SUM_TERMS THEN ASM_REWRITE_TAC[] THEN
    REPEAT STRIP_TAC THEN REWRITE_TAC[] THENL
     [MATCH_MP_TAC FIN_COL_XLOW_M; MATCH_MP_TAC FIN_COL_XLOW_Z] THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC FIN_VGE_MONO THEN EXISTS_TAC `&2` THEN
    ASM_SIMP_TAC[FIN_COL_ZTERM] THEN REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The central layer, Lemma 3.2: p F_j == - sum_(l<J) V_l / (j - l) (mod p).  *)
(* ------------------------------------------------------------------------- *)

let FIN_COL_SUM_ALG = prove
 (`forall n (a:num->real) b c d e f.
     sum (0..n) (\i. a i * (b i + c i) - &3 / &2 * (d i * (e i - f i))) =
     sum (0..n) (\i. a i * b i - &3 / &2 * (d i * e i)) +
     sum (0..n) (\i. a i * c i) + &3 / &2 * sum (0..n) (\i. d i * f i)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM SUM_LMUL; GSYM SUM_ADD_NUMSEG] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
  REAL_ARITH_TAC);;

let FIN_COL_REINDEX = prove
 (`forall N r p j. p <= 65 * N
     ==> sum (0..65 * N) (\i. cat_dcoef N r i *
                (if p <= i /\ i < 65 * N then &1 / (&(i - p) - &j) else &0)) =
         sum {l | l < 65 * N - p} (\l. cat_dcoef N r (p + l) * (&1 / (&l - &j)))`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[COND_RAND; REAL_MUL_RZERO] THEN
  REWRITE_TAC[GSYM SUM_RESTRICT_SET] THEN
  SUBGOAL_THEN `{i | i IN 0..65 * N /\ p <= i /\ i < 65 * N} =
                IMAGE (\l. p + l) {l | l < 65 * N - p}` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_IMAGE; IN_NUMSEG] THEN
    X_GEN_TAC `i:num` THEN EQ_TAC THENL
     [STRIP_TAC THEN EXISTS_TAC `i - p:num` THEN ASM_ARITH_TAC;
      STRIP_TAC THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) SUM_IMAGE o lhand o snd) THEN
  ANTS_TAC THENL [ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[o_DEF; ADD_SUB2]);;

let FIN_COL_VSUM = prove
 (`forall N p r j. p <= 65 * N
     ==> sum {l | l < 65 * N - p} (\l. fin_col_V N p l r / (&j - &l)) =
         sum (0..65 * N) (\i. cat_pcoef N r i *
              sum {l | l < 65 * N - p} (\l. if p + l <= i /\ i < 2 * p + l
                  then &2 * fin_E p (((2 * p + l) - 1) - i) / (&j - &l) else &0)) +
         &3 / &2 * sum (0..65 * N) (\i. cat_dcoef N r i *
                (if p <= i /\ i < 65 * N then &1 / (&(i - p) - &j) else &0))`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[FIN_COL_REINDEX] THEN
  REWRITE_TAC[fin_col_V; REAL_ARITH `((a:real) - b) / c = a / c - b / c`] THEN
  SIMP_TAC[SUM_SUB; FINITE_NUMSEG_LT] THEN
  MATCH_MP_TAC(REAL_ARITH `(a:real) = c /\ b = --(&3 / &2 * d) ==> a - b = c + &3 / &2 * d`) THEN
  CONJ_TAC THENL
   [REWRITE_TAC[real_div; GSYM SUM_LMUL; GSYM SUM_RMUL] THEN
    W(MP_TAC o PART_MATCH (lhand o rand) SUM_SWAP o lhand o snd) THEN
    REWRITE_TAC[FINITE_NUMSEG; FINITE_NUMSEG_LT] THEN DISCH_THEN SUBST1_TAC THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC SUM_EQ THEN REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
    COND_CASES_TAC THEN REAL_ARITH_TAC;
    REWRITE_TAC[GSYM SUM_LMUL; GSYM SUM_NEG] THEN
    MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `l:num` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    SUBGOAL_THEN `(&1 / (&l - &j):real) = --(&1 / (&j - &l))` SUBST1_TAC THENL
     [REWRITE_TAC[real_div; REAL_MUL_LID; GSYM REAL_INV_NEG; REAL_NEG_SUB];
      REAL_ARITH_TAC]]);;

let FIN_COL_CENTRAL = prove
 (`forall p z N r j. fin_col_dighyps /\ prime p /\ ~(p = 2) /\
     p <= 65 * N /\ fin_zp p z /\ 65 * N < 2 * p /\ 65 * N <= j + p /\ j < p
     ==> fin_vge p (&1) (&p * cat_rawq z N r j +
                         sum {l | l < 65 * N - p} (\l. fin_col_V N p l r / (&j - &l)))`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[FIN_COL_VSUM; FIN_COL_RAW_SCALE] THEN
  MATCH_MP_TAC(MESON[] `forall y:real. x = y /\ fin_vge p (&1) y ==> fin_vge p (&1) x`) THEN
  EXISTS_TAC
   `sum (0..65 * N) (\i. cat_pcoef N r i *
        (&p * cat_M0 i j +
         sum {l | l < 65 * N - p} (\l. if p + l <= i /\ i < 2 * p + l
                  then &2 * fin_E p (((2 * p + l) - 1) - i) / (&j - &l) else &0)) -
        &3 / &2 * (cat_dcoef N r i *
          (&p * cat_Z0 i j - (if p <= i /\ i < 65 * N then &1 / (&(i - p) - &j) else &0)))) +
    &4 * z * sum (0..65 * N) (\i. cat_pcoef N r i * (&p * cat_ckern i j))` THEN
  CONJ_TAC THENL [REWRITE_TAC[FIN_COL_SUM_ALG; REAL_ADD_AC]; ALL_TAC] THEN
  MATCH_MP_TAC FIN_VGE_ADD THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC FIN_COL_SUM_TERMS THEN ASM_REWRITE_TAC[] THEN
    REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC FIN_VGE_ZP_MUL THEN
    ASM_SIMP_TAC[FIN_COL_PCOEF_ZP; FIN_COL_DCOEF_ZP] THENL
     [MP_TAC(SPECL [`p:num`; `65 * N`; `i:num`; `j:num`] FIN_COL_DIG_CM);
      MP_TAC(SPECL [`p:num`; `65 * N`; `i:num`; `j:num`] FIN_COL_DIG_CZ)] THEN
    ASM_SIMP_TAC[];
    MP_TAC(SPECL [`p:num`; `z:real`; `N:num`; `r:num`; `j:num`; `1`] FIN_COL_ZTERM) THEN
    ASM_REWRITE_TAC[REAL_POW_1]]);;
