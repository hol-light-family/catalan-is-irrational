(* ========================================================================= *)
(* CAT_FINITE_PLACE, columns at odd primes (prefix fin_col_): the odd-prime  *)
(* bound FIN_COL_ODD_BOUND, Equation (38) and Lemma 3.3.                     *)
(*                                                                           *)
(* Atoms are indexed by num # num:                                          *)
(*   (0,j)  the raw column F_j                     (weight 2)                *)
(*   (1,l)  the pair sum F_l + F_(p+l)             (weight 1)                *)
(*   (2,l)  the exceptional vector V_l / p         (weight 1)                *)
(*   (3,j)  the integral remainder w_j of a central column (weight 0)       *)
(* ========================================================================= *)

needs "src/catalan_fin_col_vec.ml";;

(* ------------------------------------------------------------------------- *)
(* Intervals of natural numbers.                                             *)
(* ------------------------------------------------------------------------- *)

let FIN_COL_IV_IMAGE = prove
 (`forall a c. {j:num | a <= j /\ j < c} = IMAGE (\i. a + i) {i | i < c - a}`,
  REPEAT GEN_TAC THEN REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_IMAGE] THEN
  X_GEN_TAC `j:num` THEN EQ_TAC THENL
   [STRIP_TAC THEN EXISTS_TAC `j - a:num` THEN ASM_ARITH_TAC; STRIP_TAC THEN ASM_ARITH_TAC]);;

let FIN_COL_IV_FINITE = prove
 (`forall a c. FINITE {j:num | a <= j /\ j < c}`,
  SIMP_TAC[FIN_COL_IV_IMAGE; FINITE_IMAGE; FINITE_NUMSEG_LT]);;

let FIN_COL_IV_CARD = prove
 (`forall a c. CARD {j:num | a <= j /\ j < c} = c - a`,
  REPEAT GEN_TAC THEN REWRITE_TAC[FIN_COL_IV_IMAGE] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) CARD_IMAGE_INJ o lhand o snd) THEN
  REWRITE_TAC[FINITE_NUMSEG_LT; CARD_NUMSEG_LT] THEN
  ANTS_TAC THENL [ARITH_TAC; SIMP_TAC[]]);;

let FIN_COL_TAG_IN = prove
 (`(forall a j s. (a:num,j:num) IN IMAGE (\x. (a,x)) s <=> j IN s) /\
   (forall a b j s. ~(a = b) ==> ~((a:num,j:num) IN IMAGE (\x. (b,x)) s))`,
  REWRITE_TAC[IN_IMAGE; PAIR_EQ] THEN MESON_TAC[]);;

let FIN_COL_TAG_CARD = prove
 (`forall a s. FINITE s ==> CARD (IMAGE (\x:num. (a:num,x)) s) = CARD s`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CARD_IMAGE_INJ THEN
  ASM_SIMP_TAC[PAIR_EQ]);;

(* ------------------------------------------------------------------------- *)
(* The atoms.                                                                *)
(* ------------------------------------------------------------------------- *)

(* exceptional residues E = [max(0,K), min(b,J)) and the represented ones   *)
let fin_col_E = new_definition
 `fin_col_E N p = {l | 59 * N - p <= l /\ l < MIN (7 * N) (65 * N - p)}`;;

let fin_col_L1 = new_definition
 `fin_col_L1 N p = {l | l < 65 * N - p /\ ~(l IN fin_col_E N p)}`;;

(* the retained column representing V_l: p^2 Y_l == V_l (mod p) *)
let fin_col_Y = new_definition
 `fin_col_Y z N p l r =
    if 7 * N <= l then cat_rawq z N r l else --(cat_rawq z N r (p + l))`;;

(* w_j = C_j + p^(-1) sum_(l in E) V_l / (j - l) *)
let fin_col_W = new_definition
 `fin_col_W z N p j r =
    cat_rawq z N r j +
    &p * sum (fin_col_L1 N p) (\l. fin_col_Y z N p l r / (&j - &l)) +
    sum (fin_col_E N p) (\l. fin_col_V N p l r / (&j - &l)) / &p`;;

let fin_col_atom = new_definition
 `fin_col_atom z N p (x:num#num) r =
    if FST x = 0 then cat_rawq z N r (SND x)
    else if FST x = 1 then cat_rawq z N r (SND x) + cat_rawq z N r (p + SND x)
    else if FST x = 2 then fin_col_V N p (SND x) r / &p
    else fin_col_W z N p (SND x) r`;;

let FIN_COL_ATOM = prove
 (`fin_col_atom z N p (0,j) = (\r. cat_rawq z N r j) /\
   fin_col_atom z N p (1,l) = (\r. cat_rawq z N r l + cat_rawq z N r (p + l)) /\
   fin_col_atom z N p (2,l) = (\r. fin_col_V N p l r / &p) /\
   fin_col_atom z N p (3,j) = fin_col_W z N p j`,
  REWRITE_TAC[FUN_EQ_THM; fin_col_atom] THEN CONV_TAC NUM_REDUCE_CONV);;

let FIN_COL_ATOM_APP = prove
 (`fin_col_atom z N p (0,j) r = cat_rawq z N r j /\
   fin_col_atom z N p (1,l) r = cat_rawq z N r l + cat_rawq z N r (p + l) /\
   fin_col_atom z N p (2,l) r = fin_col_V N p l r / &p /\
   fin_col_atom z N p (3,j) r = fin_col_W z N p j r`,
  REWRITE_TAC[FIN_COL_ATOM]);;

(* ------------------------------------------------------------------------- *)
(* Local integrality of the remainders w_j of central columns.               *)
(* ------------------------------------------------------------------------- *)

let FIN_COL_E_SUBSET = prove
 (`forall N p. fin_col_E N p SUBSET {l | l < 65 * N - p}`,
  REWRITE_TAC[fin_col_E; SUBSET; IN_ELIM_THM] THEN ARITH_TAC);;

let FIN_COL_E_FINITE = prove
 (`forall N p. FINITE(fin_col_E N p)`,
  MESON_TAC[FIN_COL_E_SUBSET; FINITE_SUBSET; FINITE_NUMSEG_LT]);;

let FIN_COL_L1_FINITE = prove
 (`forall N p. FINITE(fin_col_L1 N p)`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC `{l | l < 65 * N - p}` THEN REWRITE_TAC[FINITE_NUMSEG_LT] THEN
  REWRITE_TAC[fin_col_L1; SUBSET; IN_ELIM_THM] THEN MESON_TAC[]);;

let FIN_COL_SPLIT = prove
 (`forall N p (f:num->real). sum {l | l < 65 * N - p} f =
                       sum (fin_col_L1 N p) f + sum (fin_col_E N p) f`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `{l | l < 65 * N - p} = fin_col_L1 N p UNION fin_col_E N p` SUBST1_TAC THENL
   [MP_TAC(SPECL [`N:num`; `p:num`] FIN_COL_E_SUBSET) THEN
    REWRITE_TAC[fin_col_L1] THEN SET_TAC[];
    MATCH_MP_TAC SUM_UNION THEN REWRITE_TAC[FIN_COL_L1_FINITE; FIN_COL_E_FINITE] THEN
    REWRITE_TAC[fin_col_L1] THEN SET_TAC[]]);;

let FIN_COL_INV_DIFF_ZP = prove
 (`forall p j l. prime p /\ l < j /\ j < p ==> fin_zp p (&1 / (&j - &l))`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[REAL_OF_NUM_SUB; LT_IMP_LE] THEN
  MATCH_MP_TAC FIN_ZP_DIV_NUM THEN ASM_SIMP_TAC[FIN_ZP_1] THEN
  DISCH_THEN(MP_TAC o MATCH_MP DIVIDES_LE) THEN ASM_ARITH_TAC);;

let FIN_COL_W_ZP = prove
 (`forall p z N r j. fin_col_dighyps /\ prime p /\ ~(p = 2) /\
     4 * (65 * N) < p * p /\ p <= 65 * N /\ fin_zp p z /\ 65 * N < 2 * p /\
     r < 48 * N /\ 65 * N <= j + p /\ j < p
     ==> fin_zp p (fin_col_W z N p j r)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(&p = &0)` ASSUME_TAC THENL
   [ASM_MESON_TAC[REAL_OF_NUM_EQ; PRIME_IMP_NZ]; ALL_TAC] THEN
  ASM_SIMP_TAC[GSYM FIN_VGE_ZP] THEN
  SUBGOAL_THEN `fin_vge p (&0 + &1) (&p * fin_col_W z N p j r)` MP_TAC THENL
   [ALL_TAC; ASM_SIMP_TAC[FIN_VGE_PMUL]] THEN
  REWRITE_TAC[REAL_ADD_LID] THEN
  SUBGOAL_THEN
   `&p * fin_col_W z N p j r =
    (&p * cat_rawq z N r j +
     sum {l | l < 65 * N - p} (\l. fin_col_V N p l r / (&j - &l))) +
    sum (fin_col_L1 N p)
      (\l. (&p pow 2 * fin_col_Y z N p l r - fin_col_V N p l r) / (&j - &l))`
  SUBST1_TAC THENL
   [REWRITE_TAC[fin_col_W; FIN_COL_SPLIT] THEN
    REWRITE_TAC[real_div; REAL_SUB_RDISTRIB] THEN
    SIMP_TAC[SUM_SUB; FIN_COL_L1_FINITE; GSYM REAL_MUL_ASSOC; SUM_LMUL] THEN
    REWRITE_TAC[REAL_ADD_LDISTRIB] THEN
    SUBGOAL_THEN `forall x. &p * x * inv(&p) = x` (fun th -> REWRITE_TAC[th]) THENL
     [GEN_TAC THEN MATCH_MP_TAC(REAL_FIELD `~(y = &0) ==> y * x * inv y = x`) THEN
      ASM_REWRITE_TAC[];
      REWRITE_TAC[REAL_POW_2; GSYM REAL_MUL_ASSOC] THEN
      ABBREV_TAC `SY = sum (fin_col_L1 N p) (\l. fin_col_Y z N p l r * inv (&j - &l))` THEN
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC FIN_VGE_ADD THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC FIN_COL_CENTRAL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC FIN_VGE_SUM THEN ASM_REWRITE_TAC[FIN_COL_L1_FINITE] THEN
  X_GEN_TAC `l:num` THEN REWRITE_TAC[fin_col_L1; fin_col_E; IN_ELIM_THM] THEN
  STRIP_TAC THEN REWRITE_TAC[real_div] THEN MATCH_MP_TAC FIN_VGE_MUL_ZP THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ONCE_REWRITE_TAC[REAL_ARITH `inv x = &1 / x`] THEN
    MATCH_MP_TAC FIN_COL_INV_DIFF_ZP THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[fin_col_Y] THEN COND_CASES_TAC THENL
   [MATCH_MP_TAC FIN_COL_XLOW THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `l < 59 * N - p` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o check (is_neg o concl)) THEN
    REWRITE_TAC[DE_MORGAN_THM; NOT_LE; NOT_LT] THEN
    POP_ASSUM MP_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC(MESON[] `forall y:real. x = y /\ fin_vge p (&1) y ==> fin_vge p (&1) x`) THEN
  EXISTS_TAC `(&p pow 2 * cat_rawq z N r l - fin_col_V N p l r) -
              &p pow 2 * (cat_rawq z N r l + cat_rawq z N r (p + l))` THEN
  CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC FIN_VGE_SUB THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC FIN_COL_XLOW THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    ASM_SIMP_TAC[GSYM FIN_COL_VGE_SCALE] THEN
    REWRITE_TAC[REAL_ARITH `&1 - &2 = --(&1)`] THEN
    MATCH_MP_TAC FIN_COL_PAIR THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Span helpers.                                                             *)
(* ------------------------------------------------------------------------- *)

let FIN_COL_SPAN_TAG = prove
 (`forall p s t z N P x. prime p /\ FINITE t /\ x IN t
     ==> fin_col_span p s t (fin_col_atom z N P) (fin_col_atom z N P x)`,
  MESON_TAC[FIN_COL_SPAN_ATOM]);;

let FIN_COL_SPAN_COL = prove
 (`forall p s t z N P j. prime p /\ FINITE t /\ (0,j) IN t
     ==> fin_col_span p s t (fin_col_atom z N P) (\r. cat_rawq z N r j)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`p:num`; `s:num->bool`; `t:num#num->bool`; `z:real`; `N:num`; `P:num`;
                 `(0,j):num#num`] FIN_COL_SPAN_TAG) THEN
  ASM_REWRITE_TAC[FIN_COL_ATOM]);;

let FIN_COL_SPAN_PAIRCOL = prove
 (`forall p s t z N P l. prime p /\ FINITE t /\ (0,l) IN t /\ (1,l) IN t
     ==> fin_col_span p s t (fin_col_atom z N P) (\r. cat_rawq z N r (P + l))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC FIN_COL_SPAN_EQ THEN
  EXISTS_TAC `\r. (cat_rawq z N r l + cat_rawq z N r (P + l)) - cat_rawq z N r l` THEN
  CONJ_TAC THENL [ALL_TAC; REWRITE_TAC[] THEN REAL_ARITH_TAC] THEN
  MATCH_MP_TAC FIN_COL_SPAN_SUB THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`p:num`; `s:num->bool`; `t:num#num->bool`; `z:real`; `N:num`; `P:num`;
                   `(1,l):num#num`] FIN_COL_SPAN_TAG) THEN
    ASM_REWRITE_TAC[FIN_COL_ATOM];
    REWRITE_TAC[ETA_AX] THEN
    MP_TAC(ISPECL [`p:num`; `s:num->bool`; `t:num#num->bool`; `z:real`; `N:num`; `P:num`;
                   `l:num`] FIN_COL_SPAN_COL) THEN
    ASM_REWRITE_TAC[ETA_AX]]);;

(* ------------------------------------------------------------------------- *)
(* Case 2p > H: the atom pool of Lemma 3.3.                                  *)
(* ------------------------------------------------------------------------- *)

let fin_col_PB = new_definition
 `fin_col_PB N p = {l | 7 * N <= l /\ l < MIN (19 * N) (59 * N - p)}`;;

let fin_col_T2B = new_definition
 `fin_col_T2B N p =
    ({j | 7 * N <= j /\ j < 65 * N - p} UNION
     {j | p <= j /\ j < p + MIN (7 * N) (59 * N - p)}) UNION
    {j | p + MAX (7 * N) (MIN (19 * N) (59 * N - p)) <= j /\ j < 59 * N}`;;

let fin_col_CB = new_definition
 `fin_col_CB N p = {j | 7 * N <= j /\ j < p /\ j < 59 * N /\ 65 * N - p <= j}`;;

let fin_col_tB1 = new_definition
 `fin_col_tB1 N p = IMAGE (\l. (1,l)) (fin_col_PB N p) UNION
                    IMAGE (\l. (2,l)) (fin_col_E N p)`;;

let fin_col_tB2 = new_definition
 `fin_col_tB2 N p = IMAGE (\j. (0,j)) (fin_col_T2B N p)`;;

let fin_col_tB = new_definition
 `fin_col_tB N p = (fin_col_tB1 N p UNION fin_col_tB2 N p) UNION
                   IMAGE (\j. (3,j)) (fin_col_CB N p)`;;

let FIN_COL_TB_IN = prove
 (`forall N p a b. (a,b) IN fin_col_tB N p <=>
             a = 0 /\ b IN fin_col_T2B N p \/ a = 1 /\ b IN fin_col_PB N p \/
             a = 2 /\ b IN fin_col_E N p \/ a = 3 /\ b IN fin_col_CB N p`,
  REWRITE_TAC[fin_col_tB; fin_col_tB1; fin_col_tB2; IN_UNION; IN_IMAGE; PAIR_EQ] THEN
  MESON_TAC[]);;

let FIN_COL_TB_FINITE = prove
 (`forall N p. FINITE(fin_col_PB N p) /\ FINITE(fin_col_T2B N p) /\ FINITE(fin_col_CB N p) /\
         FINITE(fin_col_tB1 N p) /\ FINITE(fin_col_tB2 N p) /\ FINITE(fin_col_tB N p)`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `FINITE(fin_col_PB N p) /\ FINITE(fin_col_T2B N p) /\ FINITE(fin_col_CB N p)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[fin_col_PB; fin_col_T2B; FINITE_UNION; FIN_COL_IV_FINITE] THEN
    MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `{j:num | j < p}` THEN
    REWRITE_TAC[FINITE_NUMSEG_LT; fin_col_CB; SUBSET; IN_ELIM_THM] THEN ARITH_TAC;
    ASM_SIMP_TAC[fin_col_tB; fin_col_tB1; fin_col_tB2; FINITE_UNION; FINITE_IMAGE;
                 FIN_COL_E_FINITE]]);;

let FIN_COL_SPAN_Y = prove
 (`forall z N p l s. prime p /\ 65 * N < 2 * p /\ p <= 65 * N /\ l IN fin_col_L1 N p
     ==> fin_col_span p s (fin_col_tB N p) (fin_col_atom z N p) (fin_col_Y z N p l)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[fin_col_L1; fin_col_E; IN_ELIM_THM] THEN STRIP_TAC THEN
  MATCH_MP_TAC FIN_COL_SPAN_EQ THEN ASM_CASES_TAC `7 * N <= l` THENL
   [EXISTS_TAC `\r. cat_rawq z N r l` THEN
    CONJ_TAC THENL [ALL_TAC; ASM_REWRITE_TAC[fin_col_Y]] THEN
    MATCH_MP_TAC FIN_COL_SPAN_COL THEN
    ASM_REWRITE_TAC[FIN_COL_TB_IN; FIN_COL_TB_FINITE; fin_col_T2B; IN_UNION; IN_ELIM_THM] THEN
    ASM_ARITH_TAC;
    EXISTS_TAC `\r. --(&1) * cat_rawq z N r (p + l)` THEN
    CONJ_TAC THENL [ALL_TAC; ASM_REWRITE_TAC[fin_col_Y] THEN REAL_ARITH_TAC] THEN
    MATCH_MP_TAC FIN_COL_SPAN_CMUL THEN
    ASM_SIMP_TAC[FIN_COL_TB_FINITE; FIN_ZP_NEG; FIN_ZP_1] THEN
    MATCH_MP_TAC FIN_COL_SPAN_COL THEN
    ASM_REWRITE_TAC[FIN_COL_TB_IN; FIN_COL_TB_FINITE; fin_col_T2B; IN_UNION; IN_ELIM_THM] THEN
    ASM_ARITH_TAC]);;

let FIN_COL_SPAN_B = prove
 (`forall z N p j. prime p /\ 65 * N < 2 * p /\ p <= 65 * N /\ 7 * N <= j /\ j < 59 * N
     ==> fin_col_span p {r | r < 48 * N} (fin_col_tB N p) (fin_col_atom z N p)
                      (\r. cat_rawq z N r j)`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `j < 65 * N - p` THENL
   [MATCH_MP_TAC FIN_COL_SPAN_COL THEN
    ASM_REWRITE_TAC[FIN_COL_TB_IN; FIN_COL_TB_FINITE; fin_col_T2B; IN_UNION; IN_ELIM_THM];
    ALL_TAC] THEN
  ASM_CASES_TAC `p:num <= j` THENL
   [ASM_CASES_TAC `7 * N <= j - p /\ j - p < MIN (19 * N) (59 * N - p)` THENL
     [SUBGOAL_THEN `j:num = p + (j - p)` SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC FIN_COL_SPAN_PAIRCOL THEN
      ASM_REWRITE_TAC[FIN_COL_TB_IN; FIN_COL_TB_FINITE; fin_col_T2B; fin_col_PB;
                      IN_UNION; IN_ELIM_THM] THEN
      ASM_ARITH_TAC;
      MATCH_MP_TAC FIN_COL_SPAN_COL THEN
      ASM_REWRITE_TAC[FIN_COL_TB_IN; FIN_COL_TB_FINITE; fin_col_T2B; IN_UNION; IN_ELIM_THM] THEN
      ASM_ARITH_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC FIN_COL_SPAN_EQ THEN
  EXISTS_TAC
   `\r. (fin_col_atom z N p (3,j) r +
         sum (fin_col_L1 N p) (\l. --(&p * &1 / (&j - &l)) * fin_col_Y z N p l r)) +
        sum (fin_col_E N p) (\l. --(&1 / (&j - &l)) * fin_col_atom z N p (2,l) r)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC FIN_COL_SPAN_ADD THEN ASM_REWRITE_TAC[FIN_COL_TB_FINITE] THEN CONJ_TAC THENL
     [MATCH_MP_TAC FIN_COL_SPAN_ADD THEN ASM_REWRITE_TAC[FIN_COL_TB_FINITE] THEN CONJ_TAC THENL
       [REWRITE_TAC[ETA_AX] THEN MATCH_MP_TAC FIN_COL_SPAN_TAG THEN
        ASM_REWRITE_TAC[FIN_COL_TB_IN; FIN_COL_TB_FINITE; fin_col_CB; IN_ELIM_THM] THEN
        ASM_ARITH_TAC;
        MATCH_MP_TAC FIN_COL_SPAN_SUM THEN
        ASM_REWRITE_TAC[FIN_COL_TB_FINITE; FIN_COL_L1_FINITE] THEN
        X_GEN_TAC `l:num` THEN DISCH_TAC THEN CONJ_TAC THENL
         [MATCH_MP_TAC FIN_ZP_NEG THEN REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN
          MATCH_MP_TAC FIN_ZP_MUL THEN ASM_SIMP_TAC[FIN_ZP_NUM] THEN
          MATCH_MP_TAC FIN_COL_INV_DIFF_ZP THEN ASM_REWRITE_TAC[] THEN
          UNDISCH_TAC `l IN fin_col_L1 N p` THEN
          REWRITE_TAC[fin_col_L1; IN_ELIM_THM] THEN ASM_ARITH_TAC;
          REWRITE_TAC[ETA_AX] THEN MATCH_MP_TAC FIN_COL_SPAN_Y THEN ASM_REWRITE_TAC[]]];
      MATCH_MP_TAC FIN_COL_SPAN_SUM THEN
      ASM_REWRITE_TAC[FIN_COL_TB_FINITE; FIN_COL_E_FINITE] THEN
      X_GEN_TAC `l:num` THEN DISCH_TAC THEN CONJ_TAC THENL
       [MATCH_MP_TAC FIN_ZP_NEG THEN
        MATCH_MP_TAC FIN_COL_INV_DIFF_ZP THEN ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `l IN fin_col_E N p` THEN
        REWRITE_TAC[fin_col_E; IN_ELIM_THM] THEN ASM_ARITH_TAC;
        REWRITE_TAC[ETA_AX] THEN MATCH_MP_TAC FIN_COL_SPAN_TAG THEN
        ASM_REWRITE_TAC[FIN_COL_TB_IN; FIN_COL_TB_FINITE]]];
    ALL_TAC] THEN
  X_GEN_TAC `r:num` THEN DISCH_TAC THEN REWRITE_TAC[FIN_COL_ATOM_APP; fin_col_W] THEN
  MATCH_MP_TAC(REAL_ARITH `(a:real) = --b /\ c = --d ==> x = ((x + b + d) + a) + c`) THEN
  CONJ_TAC THEN REWRITE_TAC[real_div; GSYM SUM_LMUL; GSYM SUM_RMUL; GSYM SUM_NEG] THEN
  MATCH_MP_TAC SUM_EQ THEN REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN REAL_ARITH_TAC);;

let FIN_COL_TB_SETS = prove
 (`forall N p. fin_col_tB1 N p SUBSET fin_col_tB N p /\ fin_col_tB2 N p SUBSET fin_col_tB N p /\
         DISJOINT (fin_col_tB1 N p) (fin_col_tB2 N p)`,
  REPEAT GEN_TAC THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[fin_col_tB] THEN SET_TAC[];
    REWRITE_TAC[fin_col_tB] THEN SET_TAC[];
    REWRITE_TAC[fin_col_tB1; fin_col_tB2; DISJOINT; EXTENSION; IN_INTER; IN_UNION;
                IN_IMAGE; NOT_IN_EMPTY] THEN
    MESON_TAC[PAIR_EQ; ARITH_RULE `~(1 = 0) /\ ~(2 = 0)`]]);;

let FIN_COL_CARD_B = prove
 (`forall N p. CARD (fin_col_tB1 N p) <=
         (MIN (19 * N) (59 * N - p) - 7 * N) + (MIN (7 * N) (65 * N - p) - (59 * N - p)) /\
         (65 * N < 2 * p /\ p <= 65 * N
          ==> CARD (fin_col_tB2 N p) <=
              (59 * N - p) + ((59 * N - p) - 19 * N) +
              ((65 * N - p) - MAX (7 * N) (59 * N - p)))`,
  REPEAT GEN_TAC THEN CONJ_TAC THENL
   [REWRITE_TAC[fin_col_tB1] THEN MATCH_MP_TAC LE_TRANS THEN
    EXISTS_TAC `CARD (IMAGE (\l. (1,l)) (fin_col_PB N p)) +
                CARD (IMAGE (\l. (2,l)) (fin_col_E N p))` THEN
    SIMP_TAC[CARD_UNION_LE; FINITE_IMAGE; FIN_COL_TB_FINITE; FIN_COL_E_FINITE] THEN
    SIMP_TAC[FIN_COL_TAG_CARD; FIN_COL_TB_FINITE; FIN_COL_E_FINITE] THEN
    REWRITE_TAC[fin_col_PB; fin_col_E; FIN_COL_IV_CARD; LE_REFL];
    STRIP_TAC THEN
    SIMP_TAC[fin_col_tB2; FIN_COL_TAG_CARD; FIN_COL_TB_FINITE] THEN
    REWRITE_TAC[fin_col_T2B] THEN MATCH_MP_TAC LE_TRANS THEN
    EXISTS_TAC
     `(CARD {j | 7 * N <= j /\ j < 65 * N - p} +
       CARD {j | p <= j /\ j < p + MIN (7 * N) (59 * N - p)}) +
      CARD {j | p + MAX (7 * N) (MIN (19 * N) (59 * N - p)) <= j /\ j < 59 * N}` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC LE_TRANS THEN
      EXISTS_TAC
       `CARD ({j | 7 * N <= j /\ j < 65 * N - p} UNION
              {j | p <= j /\ j < p + MIN (7 * N) (59 * N - p)}) +
        CARD {j | p + MAX (7 * N) (MIN (19 * N) (59 * N - p)) <= j /\ j < 59 * N}` THEN
      SIMP_TAC[CARD_UNION_LE; FINITE_UNION; FIN_COL_IV_FINITE; LE_ADD_RCANCEL];
      REWRITE_TAC[FIN_COL_IV_CARD] THEN REWRITE_TAC[MIN; MAX] THEN
      REPEAT COND_CASES_TAC THEN ASM_ARITH_TAC]]);;

let FIN_COL_TB_W = prove
 (`forall p z N. fin_col_dighyps /\ prime p /\ ~(p = 2) /\
     4 * (65 * N) < p * p /\ p <= 65 * N /\ fin_zp p z /\ 65 * N < 2 * p
     ==> (forall x r. x IN fin_col_tB2 N p /\ r < 48 * N
                ==> fin_vge p (--(&2)) (fin_col_atom z N p x r)) /\
         (forall x r. x IN fin_col_tB1 N p /\ r < 48 * N
                ==> fin_vge p (--(&1)) (fin_col_atom z N p x r)) /\
         (forall x r. x IN fin_col_tB N p /\ ~(x IN fin_col_tB1 N p) /\
                ~(x IN fin_col_tB2 N p) /\ r < 48 * N
                ==> fin_zp p (fin_col_atom z N p x r))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[fin_col_tB2; IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_IMAGE] THEN
    REWRITE_TAC[FIN_COL_ATOM_APP; fin_col_T2B; IN_UNION; IN_ELIM_THM] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC FIN_COL_RAW_W2 THEN
    ASM_REWRITE_TAC[] THEN RULE_ASSUM_TAC(REWRITE_RULE[MIN; MAX]) THEN ASM_ARITH_TAC;
    REWRITE_TAC[fin_col_tB1; IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_UNION;
                FORALL_IN_IMAGE] THEN
    REWRITE_TAC[FIN_COL_ATOM_APP; fin_col_PB; fin_col_E; IN_ELIM_THM] THEN
    CONJ_TAC THEN REPEAT STRIP_TAC THENL
     [MATCH_MP_TAC FIN_COL_PAIR THEN ASM_REWRITE_TAC[] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[MIN; MAX]) THEN ASM_ARITH_TAC;
      REWRITE_TAC[MESON[REAL_POW_1] `forall y p. (y:real) / &p = y / &p pow 1`] THEN
      ASM_SIMP_TAC[FIN_VGE_PPOW_DIV] THEN
      REWRITE_TAC[REAL_ARITH `--(&1) + &1 = &0`] THEN
      ASM_SIMP_TAC[FIN_VGE_ZP; FIN_COL_V_ZP]];
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    SUBGOAL_THEN `x IN IMAGE (\j. (3,j)) (fin_col_CB N p)` MP_TAC THENL
     [UNDISCH_TAC `x IN fin_col_tB N p` THEN REWRITE_TAC[fin_col_tB] THEN ASM SET_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[IN_IMAGE; fin_col_CB; IN_ELIM_THM] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[FIN_COL_ATOM_APP] THEN
    MATCH_MP_TAC FIN_COL_W_ZP THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC]);;

let FIN_COL_CASE_B = prove
 (`forall z N p. fin_col_dighyps /\ 1 <= N /\ prime p /\ ~(p = 2) /\
     4 * (65 * N) < p * p /\ p <= 65 * N /\ 65 * N < 2 * p /\ fin_zp p z
     ==> fin_vge p (--(&(fin_loss N p))) (cat_detq z N)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[fin_loss] THEN
  COND_CASES_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  MATCH_MP_TAC(INST_TYPE [`:num#num`,`:A`] FIN_COL_DET_ATOMS) THEN
  MAP_EVERY EXISTS_TAC [`fin_col_tB N p`; `fin_col_tB1 N p`; `fin_col_tB2 N p`;
                        `fin_col_atom z N p`] THEN
  MP_TAC(SPECL [`p:num`; `z:real`; `N:num`] FIN_COL_TB_W) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[FIN_COL_TB_FINITE; FIN_COL_TB_SETS; FIN_COL_CARD_B; FIN_COL_SPAN_B]);;

(* ------------------------------------------------------------------------- *)
(* Case 2p <= H: Equation (38).                                              *)
(* ------------------------------------------------------------------------- *)

let fin_col_PA = new_definition
 `fin_col_PA N p =
    {l | MAX (7 * N) (65 * N - 2 * p) <= l /\ l < MIN p (MIN (59 * N - p) (19 * N))}`;;

let fin_col_T2A = new_definition
 `fin_col_T2A N p = {j | 7 * N <= j /\ j < 59 * N} DIFF IMAGE (\l. p + l) (fin_col_PA N p)`;;

let fin_col_tA1 = new_definition
 `fin_col_tA1 N p = IMAGE (\l. (1,l)) (fin_col_PA N p)`;;

let fin_col_tA2 = new_definition
 `fin_col_tA2 N p = IMAGE (\j. (0,j)) (fin_col_T2A N p)`;;

let fin_col_tA = new_definition
 `fin_col_tA N p = fin_col_tA1 N p UNION fin_col_tA2 N p`;;

let FIN_COL_TA_IN = prove
 (`forall N p a b. (a,b) IN fin_col_tA N p <=>
             a = 0 /\ b IN fin_col_T2A N p \/ a = 1 /\ b IN fin_col_PA N p`,
  REWRITE_TAC[fin_col_tA; fin_col_tA1; fin_col_tA2; IN_UNION; IN_IMAGE; PAIR_EQ] THEN
  MESON_TAC[]);;

let FIN_COL_TA_FINITE = prove
 (`forall N p. FINITE(fin_col_PA N p) /\ FINITE(fin_col_T2A N p) /\
         FINITE(fin_col_tA1 N p) /\ FINITE(fin_col_tA2 N p) /\ FINITE(fin_col_tA N p)`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `FINITE(fin_col_PA N p) /\ FINITE(fin_col_T2A N p)` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[fin_col_PA; fin_col_T2A] THEN SIMP_TAC[FINITE_DIFF; FIN_COL_IV_FINITE];
    ASM_SIMP_TAC[fin_col_tA; fin_col_tA1; fin_col_tA2; FINITE_UNION; FINITE_IMAGE]]);;

let FIN_COL_CARD_A = prove
 (`forall N p. CARD (fin_col_tA1 N p) =
         MIN p (MIN (59 * N - p) (19 * N)) - MAX (7 * N) (65 * N - 2 * p) /\
         CARD (fin_col_tA2 N p) =
         52 * N - (MIN p (MIN (59 * N - p) (19 * N)) - MAX (7 * N) (65 * N - 2 * p))`,
  REPEAT GEN_TAC THEN
  SIMP_TAC[fin_col_tA1; fin_col_tA2; FIN_COL_TAG_CARD; FIN_COL_TA_FINITE] THEN
  CONJ_TAC THENL [REWRITE_TAC[fin_col_PA; FIN_COL_IV_CARD]; ALL_TAC] THEN
  REWRITE_TAC[fin_col_T2A] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) CARD_DIFF o lhand o snd) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[FIN_COL_IV_FINITE; SUBSET; FORALL_IN_IMAGE; fin_col_PA; IN_ELIM_THM] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[MIN; MAX]) THEN REWRITE_TAC[MIN; MAX] THEN
    REPEAT STRIP_TAC THEN REPEAT(POP_ASSUM MP_TAC) THEN
    REPEAT COND_CASES_TAC THEN ASM_ARITH_TAC;
    DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[FIN_COL_IV_CARD] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) CARD_IMAGE_INJ o rand o lhand o snd) THEN
  ANTS_TAC THENL [SIMP_TAC[FIN_COL_TA_FINITE; EQ_ADD_LCANCEL]; DISCH_THEN SUBST1_TAC] THEN REWRITE_TAC[fin_col_PA; FIN_COL_IV_CARD] THEN ARITH_TAC);;

let FIN_COL_SPAN_A = prove
 (`forall z N p j. prime p /\ 7 * N <= j /\ j < 59 * N
     ==> fin_col_span p {r | r < 48 * N} (fin_col_tA N p) (fin_col_atom z N p)
                      (\r. cat_rawq z N r j)`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `j IN fin_col_T2A N p` THENL
   [MATCH_MP_TAC FIN_COL_SPAN_COL THEN ASM_REWRITE_TAC[FIN_COL_TA_IN; FIN_COL_TA_FINITE];
    ALL_TAC] THEN
  UNDISCH_TAC `~(j IN fin_col_T2A N p)` THEN
  ASM_REWRITE_TAC[fin_col_T2A; IN_DIFF; IN_ELIM_THM; IN_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `l:num` STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC FIN_COL_SPAN_PAIRCOL THEN
  ASM_REWRITE_TAC[FIN_COL_TA_IN; FIN_COL_TA_FINITE; fin_col_T2A; IN_DIFF; IN_ELIM_THM;
                  IN_IMAGE] THEN
  UNDISCH_TAC `l IN fin_col_PA N p` THEN REWRITE_TAC[fin_col_PA; IN_ELIM_THM] THEN
  REWRITE_TAC[MIN; MAX] THEN REPEAT COND_CASES_TAC THEN
  REPEAT STRIP_TAC THEN TRY(FIRST_X_ASSUM(MP_TAC o check (is_exists o concl))) THEN
  TRY(REWRITE_TAC[NOT_EXISTS_THM] THEN GEN_TAC) THEN ASM_ARITH_TAC);;

let FIN_COL_CASE_A = prove
 (`forall z N p. fin_col_dighyps /\ 1 <= N /\ prime p /\ ~(p = 2) /\
     4 * (65 * N) < p * p /\ 2 * p <= 65 * N /\ fin_zp p z
     ==> fin_vge p (--(&(fin_loss N p))) (cat_detq z N)`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `d = MIN p (MIN (59 * N - p) (19 * N)) - MAX (7 * N) (65 * N - 2 * p)` THEN
  SUBGOAL_THEN `d <= 12 * N` ASSUME_TAC THENL
   [EXPAND_TAC "d" THEN REWRITE_TAC[MIN; MAX] THEN REPEAT COND_CASES_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `fin_loss N p = MIN (2 * (48 * N)) (MIN (48 * N + (52 * N - d)) (2 * (52 * N - d) + d))`
  SUBST1_TAC THENL
   [ASM_REWRITE_TAC[fin_loss] THEN REWRITE_TAC[MIN] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC(INST_TYPE [`:num#num`,`:A`] FIN_COL_DET_ATOMS) THEN
  MAP_EVERY EXISTS_TAC [`fin_col_tA N p`; `fin_col_tA1 N p`; `fin_col_tA2 N p`;
                        `fin_col_atom z N p`] THEN
  ASM_REWRITE_TAC[FIN_COL_TA_FINITE; FIN_COL_CARD_A; LE_REFL] THEN
  ASM_SIMP_TAC[FIN_COL_SPAN_A] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[fin_col_tA] THEN SET_TAC[];
    REWRITE_TAC[fin_col_tA] THEN SET_TAC[];
    REWRITE_TAC[fin_col_tA1; fin_col_tA2; DISJOINT; EXTENSION; IN_INTER;
                IN_IMAGE; NOT_IN_EMPTY] THEN
    MESON_TAC[PAIR_EQ; ARITH_RULE `~(1 = 0)`];
    REWRITE_TAC[fin_col_tA2; IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_IMAGE] THEN
    REWRITE_TAC[FIN_COL_ATOM_APP; fin_col_T2A; IN_DIFF; IN_ELIM_THM] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC FIN_COL_RAW_W2 THEN
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    REWRITE_TAC[fin_col_tA1; IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_IMAGE] THEN
    REWRITE_TAC[FIN_COL_ATOM_APP; fin_col_PA; IN_ELIM_THM] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC FIN_COL_PAIR THEN ASM_REWRITE_TAC[] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[MIN; MAX]) THEN ASM_ARITH_TAC;
    REWRITE_TAC[fin_col_tA] THEN SET_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The odd-prime bound, conditional on the scalar digit reductions.          *)
(* ------------------------------------------------------------------------- *)

let FIN_COL_ODD_BOUND_COND = prove
 (`fin_col_dighyps
   ==> forall z N p. rational z /\ 1 <= N /\ prime p /\ ~(p = 2) /\
               4 * (65 * N) < p * p /\ p <= 65 * N /\ fin_zp p z
               ==> fin_vge p (--(&(fin_loss N p))) (cat_detq z N)`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `2 * p <= 65 * N` THENL
   [MATCH_MP_TAC FIN_COL_CASE_A; MATCH_MP_TAC FIN_COL_CASE_B] THEN
  ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;
