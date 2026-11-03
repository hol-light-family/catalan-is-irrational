(* ========================================================================= *)
(* CAT_FINITE_PLACE, columns at odd primes (prefix fin_col_): basic facts.   *)
(*   integrality and support of the row coefficients, small reduced values, *)
(*   "local span" of atom vectors and the generic atom bound for cat_detq.   *)
(* ========================================================================= *)

needs "src/catalan_fin_base.ml";;

(* ------------------------------------------------------------------------- *)
(* Integrality and support of the Chebyshev coefficients.                    *)
(* ------------------------------------------------------------------------- *)

let FIN_COL_CHEB_T_INTEGER = prove
 (`forall d k. integer(cheb_T d k)`,
  SUBGOAL_THEN `forall d. (forall k. integer(cheb_T d k)) /\ (forall k. integer(cheb_T (SUC d) k))`
   (fun th -> MESON_TAC[th]) THEN
  INDUCT_TAC THEN ASM_REWRITE_TAC[cheb_T] THEN
  REPEAT STRIP_TAC THEN TRY COND_CASES_TAC THEN
  ASM_SIMP_TAC[INTEGER_CLOSED] THEN
  REWRITE_TAC[ARITH_RULE `SUC 0 = 1`] THEN TRY COND_CASES_TAC THEN
  REWRITE_TAC[INTEGER_CLOSED]);;

let FIN_COL_CHEB_U_INTEGER = prove
 (`forall d k. integer(cheb_U d k)`,
  SUBGOAL_THEN `forall d. (forall k. integer(cheb_U d k)) /\ (forall k. integer(cheb_U (SUC d) k))`
   (fun th -> MESON_TAC[th]) THEN
  INDUCT_TAC THEN ASM_REWRITE_TAC[cheb_U] THEN
  REPEAT STRIP_TAC THEN TRY COND_CASES_TAC THEN
  ASM_SIMP_TAC[INTEGER_CLOSED] THEN
  REWRITE_TAC[ARITH_RULE `SUC 0 = 1`] THEN TRY COND_CASES_TAC THEN
  REWRITE_TAC[INTEGER_CLOSED]);;

let FIN_COL_CHEB_T_ZERO = prove
 (`forall d k. d < k ==> cheb_T d k = &0`,
  SUBGOAL_THEN `forall d. (forall k. d < k ==> cheb_T d k = &0) /\
                    (forall k. SUC d < k ==> cheb_T (SUC d) k = &0)`
   (fun th -> MESON_TAC[th]) THEN
  INDUCT_TAC THEN ASM_REWRITE_TAC[cheb_T] THEN REPEAT STRIP_TAC THENL
   [ASM_SIMP_TAC[ARITH_RULE `0 < k ==> ~(k = 0)`];
    ASM_SIMP_TAC[ARITH_RULE `SUC 0 < k ==> ~(k = 1)`];
    ALL_TAC] THEN
  ASM_SIMP_TAC[ARITH_RULE `SUC(SUC d) < k ==> ~(k = 0) /\ SUC d < k - 1 /\ d < k`] THEN
  REAL_ARITH_TAC);;

let FIN_COL_CHEB_U_ZERO = prove
 (`forall d k. d < k ==> cheb_U d k = &0`,
  SUBGOAL_THEN `forall d. (forall k. d < k ==> cheb_U d k = &0) /\
                    (forall k. SUC d < k ==> cheb_U (SUC d) k = &0)`
   (fun th -> MESON_TAC[th]) THEN
  INDUCT_TAC THEN ASM_REWRITE_TAC[cheb_U] THEN REPEAT STRIP_TAC THENL
   [ASM_SIMP_TAC[ARITH_RULE `0 < k ==> ~(k = 0)`];
    ASM_SIMP_TAC[ARITH_RULE `SUC 0 < k ==> ~(k = 1)`];
    ALL_TAC] THEN
  ASM_SIMP_TAC[ARITH_RULE `SUC(SUC d) < k ==> ~(k = 0) /\ SUC d < k - 1 /\ d < k`] THEN
  REAL_ARITH_TAC);;

let FIN_COL_MULFAC_INTEGER = prove
 (`forall h c i. (forall m. integer(c m)) ==> integer(cat_mulfac h c i)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[cat_mulfac] THEN
  MATCH_MP_TAC INTEGER_SUM THEN REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
  COND_CASES_TAC THEN ASM_SIMP_TAC[INTEGER_CLOSED]);;

let FIN_COL_MULFAC_ZERO = prove
 (`forall h c i. (forall m. m <= i ==> c m = &0) ==> cat_mulfac h c i = &0`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[cat_mulfac] THEN
  MATCH_MP_TAC SUM_EQ_0 THEN REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
  COND_CASES_TAC THEN REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `i - x:num`) THEN
  ANTS_TAC THENL [ARITH_TAC; SIMP_TAC[REAL_MUL_RZERO]]);;

let FIN_COL_MULFAC_ZERO_HIGH = prove
 (`forall h C c i. (forall m. C <= m ==> c m = &0) /\ C + h <= i ==> cat_mulfac h c i = &0`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[cat_mulfac] THEN
  MATCH_MP_TAC SUM_EQ_0 THEN REWRITE_TAC[IN_NUMSEG] THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[] THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `i - x:num`) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; SIMP_TAC[REAL_MUL_RZERO]]);;

let FIN_COL_PCOEF_INTEGER = prove
 (`forall N r i. integer(cat_pcoef N r i)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[cat_pcoef] THEN
  MATCH_MP_TAC FIN_COL_MULFAC_INTEGER THEN
  GEN_TAC THEN REWRITE_TAC[cat_revc] THEN COND_CASES_TAC THEN
  REWRITE_TAC[FIN_COL_CHEB_T_INTEGER; INTEGER_CLOSED]);;

let FIN_COL_DCOEF_INTEGER = prove
 (`forall N r i. integer(cat_dcoef N r i)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[cat_dcoef] THEN
  MATCH_MP_TAC(CONJUNCT1(CONJUNCT2(CONJUNCT2(CONJUNCT2 INTEGER_CLOSED)))) THEN
  CONJ_TAC THENL
   [REWRITE_TAC[cat_sgn] THEN REPEAT COND_CASES_TAC THEN REWRITE_TAC[INTEGER_CLOSED] THEN
    MATCH_MP_TAC(CONJUNCT1(CONJUNCT2(CONJUNCT2(CONJUNCT2(CONJUNCT2(CONJUNCT2 INTEGER_CLOSED)))))) THEN
    REWRITE_TAC[INTEGER_CLOSED];
    MATCH_MP_TAC FIN_COL_MULFAC_INTEGER THEN
    GEN_TAC THEN REWRITE_TAC[cat_revc] THEN COND_CASES_TAC THEN
    REWRITE_TAC[FIN_COL_CHEB_U_INTEGER; INTEGER_CLOSED]]);;

let FIN_COL_DIST_BOUND = prove
 (`forall N r. r < 48 * N ==> cat_dist N r < 44 * N`,
  REWRITE_TAC[cat_dist] THEN ARITH_TAC);;

let FIN_COL_PCOEF_LOW = prove
 (`forall N r i. r < 48 * N /\ i < 19 * N ==> cat_pcoef N r i = &0`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[cat_pcoef] THEN
  MATCH_MP_TAC FIN_COL_MULFAC_ZERO THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[cat_revc] THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC FIN_COL_CHEB_T_ZERO THEN
  MP_TAC(SPECL [`N:num`; `r:num`] FIN_COL_DIST_BOUND) THEN ASM_ARITH_TAC);;

let FIN_COL_DCOEF_LOW = prove
 (`forall N r i. r < 48 * N /\ i <= 19 * N ==> cat_dcoef N r i = &0`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[cat_dcoef] THEN
  MATCH_MP_TAC(REAL_RING `x = &0 ==> s * x = &0`) THEN
  MATCH_MP_TAC FIN_COL_MULFAC_ZERO THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[cat_revc] THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC FIN_COL_CHEB_U_ZERO THEN
  SUBGOAL_THEN `1 <= N` ASSUME_TAC THENL
   [REWRITE_TAC[ARITH_RULE `1 <= N <=> ~(N = 0)`] THEN DISCH_TAC THEN
    UNDISCH_TAC `r < 48 * N` THEN ASM_REWRITE_TAC[] THEN ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`N:num`; `r:num`] FIN_COL_DIST_BOUND) THEN ASM_ARITH_TAC);;

let FIN_COL_PCOEF_HIGH = prove
 (`forall N r i. 65 * N <= i ==> cat_pcoef N r i = &0`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[cat_pcoef] THEN
  MATCH_MP_TAC FIN_COL_MULFAC_ZERO_HIGH THEN EXISTS_TAC `63 * N` THEN
  CONJ_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[cat_revc] THEN
    ASM_REWRITE_TAC[GSYM NOT_LE]; ASM_ARITH_TAC]);;

let FIN_COL_DCOEF_HIGH = prove
 (`forall N r i. 65 * N <= i ==> cat_dcoef N r i = &0`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[cat_dcoef] THEN
  MATCH_MP_TAC(REAL_RING `x = &0 ==> s * x = &0`) THEN
  MATCH_MP_TAC FIN_COL_MULFAC_ZERO_HIGH THEN EXISTS_TAC `63 * N` THEN
  CONJ_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[cat_revc] THEN
    ASM_REWRITE_TAC[GSYM NOT_LE]; ASM_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Small values of the reduced arrays (table before Equation (37)).          *)
(* ------------------------------------------------------------------------- *)

let FIN_COL_KPLUS_SMALL = prove
 (`cat_kplus 1 = &0 /\ cat_kplus 2 = &2`,
  let th = SPEC `0` (CONJUNCT2(CONJUNCT2 cat_kplus)) in
  let th' = CONV_RULE(LAND_CONV(RAND_CONV NUM_REDUCE_CONV)) th in
  REWRITE_TAC[th'; REWRITE_RULE[ARITH_RULE `SUC 0 = 1`] cat_kplus] THEN
  CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC REAL_RAT_REDUCE_CONV);;

let FIN_COL_KMINUS_SMALL = prove
 (`cat_kminus 0 = &0 /\ cat_kminus 1 = &2`,
  REWRITE_TAC[REWRITE_RULE[ARITH_RULE `SUC 0 = 1`] cat_kminus]);;

let FIN_COL_SMALL_TAC =
  REWRITE_TAC[cat_M0; cat_Z0; cat_harm; fin_M0x] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[SUM_SING_NUMSEG; SUM_CLAUSES_NUMSEG; FIN_COL_KPLUS_SMALL;
              FIN_COL_KMINUS_SMALL] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[cat_m; cat_c] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[binom] THEN CONV_TAC REAL_RAT_REDUCE_CONV;;

let FIN_COL_M0X_SMALL = prove
 (`fin_M0x 0 0 = &0 /\ fin_M0x 0 1 = &2 /\
   fin_M0x 1 0 = &0 /\ fin_M0x 1 1 = &0 /\
   fin_M0x 2 0 = &2 /\ fin_M0x 2 1 = -- &2`,
  FIN_COL_SMALL_TAC);;

let FIN_COL_Z0_SMALL = prove
 (`cat_Z0 0 0 = &0 /\ cat_Z0 0 1 = &1 /\ cat_Z0 1 0 = &1 /\ cat_Z0 1 1 = -- &1`,
  FIN_COL_SMALL_TAC);;

(* ------------------------------------------------------------------------- *)
(* Local integrality of the simple ingredients at odd primes.                *)
(* ------------------------------------------------------------------------- *)

let FIN_COL_E_ZP = prove
 (`forall p d. prime p ==> fin_zp p (fin_E p d)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC FIN_ZP_INTEGER THEN ASM_REWRITE_TAC[fin_E] THEN
  COND_CASES_TAC THEN SIMP_TAC[INTEGER_CLOSED]);;

let FIN_COL_PCOEF_ZP = prove
 (`forall p N r i. prime p ==> fin_zp p (cat_pcoef N r i)`,
  SIMP_TAC[FIN_ZP_INTEGER; FIN_COL_PCOEF_INTEGER]);;

let FIN_COL_DCOEF_ZP = prove
 (`forall p N r i. prime p ==> fin_zp p (cat_dcoef N r i)`,
  SIMP_TAC[FIN_ZP_INTEGER; FIN_COL_DCOEF_INTEGER]);;

let FIN_COL_NDIV_4EXP = prove
 (`forall p l. prime p /\ ~(p = 2) ==> ~(p divides 4 EXP l)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `p divides 2` MP_TAC THENL
   [MATCH_MP_TAC PRIME_DIVEXP THEN EXISTS_TAC `2 * l` THEN
    ASM_REWRITE_TAC[EXP_MULT] THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[];
    ASM_SIMP_TAC[DIVIDES_PRIME_PRIME; PRIME_2]]);;

let FIN_COL_C_ZP = prove
 (`forall p l. prime p /\ ~(p = 2) ==> fin_zp p (cat_c l)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[cat_c; REAL_OF_NUM_POW] THEN
  MATCH_MP_TAC FIN_ZP_DIV_NUM THEN ASM_SIMP_TAC[FIN_ZP_NUM; FIN_COL_NDIV_4EXP]);;

let FIN_COL_CKERN_ZP = prove
 (`forall p i j. prime p /\ ~(p = 2) ==> fin_zp p (cat_ckern i j)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[cat_ckern] THEN
  COND_CASES_TAC THEN ASM_SIMP_TAC[FIN_COL_C_ZP; FIN_ZP_0]);;

(* ------------------------------------------------------------------------- *)
(* Local span of a finite family of atom vectors.                            *)
(* ------------------------------------------------------------------------- *)

let fin_col_span = new_definition
 `fin_col_span p (s:num->bool) (t:A->bool) (v:A->num->real) (f:num->real) <=>
    exists d. (forall x. x IN t ==> fin_zp p (d x)) /\
        (forall r. r IN s ==> f r = sum t (\x. d x * v x r))`;;

let FIN_COL_SPAN_ATOM = prove
 (`forall p s t v (x:A). prime p /\ FINITE t /\ x IN t ==> fin_col_span p s t v (v x)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[fin_col_span] THEN
  EXISTS_TAC `\y:A. if y = x then &1 else &0` THEN
  REWRITE_TAC[] THEN CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN COND_CASES_TAC THEN ASM_SIMP_TAC[FIN_ZP_0; FIN_ZP_1];
    ALL_TAC] THEN
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[COND_RAND; COND_RATOR; REAL_MUL_LZERO; REAL_MUL_LID] THEN
  SUBGOAL_THEN `sum t (\y:A. if y = x then v y (r:num) else &0) =
                sum t (\y. if y = x then v x r else &0)` SUBST1_TAC THENL
   [MATCH_MP_TAC SUM_EQ THEN REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[SUM_DELTA]]);;

let FIN_COL_SPAN_EQ = prove
 (`forall p s t (v:A->num->real) f g.
        fin_col_span p s t v f /\ (forall r. r IN s ==> g r = f r)
        ==> fin_col_span p s t v g`,
  REWRITE_TAC[fin_col_span] THEN MESON_TAC[]);;

let FIN_COL_SPAN_0 = prove
 (`forall p s t (v:A->num->real). prime p ==> fin_col_span p s t v (\r. &0)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[fin_col_span] THEN
  EXISTS_TAC `\x:A. &0` THEN ASM_SIMP_TAC[FIN_ZP_0; REAL_MUL_LZERO; SUM_0]);;

let FIN_COL_SPAN_LIN = prove
 (`forall p s t (v:A->num->real) f g a b.
        prime p /\ FINITE t /\ fin_zp p a /\ fin_zp p b /\
        fin_col_span p s t v f /\ fin_col_span p s t v g
        ==> fin_col_span p s t v (\r. a * f r + b * g r)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[fin_col_span] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2
    (X_CHOOSE_THEN `d1:A->real` STRIP_ASSUME_TAC)
    (X_CHOOSE_THEN `d2:A->real` STRIP_ASSUME_TAC)))))) THEN
  EXISTS_TAC `\x:A. (a:real) * d1 x + (b:real) * d2 x` THEN
  ASM_SIMP_TAC[FIN_ZP_ADD; FIN_ZP_MUL] THEN
  ASM_SIMP_TAC[REAL_ADD_RDISTRIB; SUM_ADD; GSYM REAL_MUL_ASSOC; SUM_LMUL]);;

let FIN_COL_SPAN_ADD = prove
 (`forall p s t (v:A->num->real) f g.
        prime p /\ FINITE t /\ fin_col_span p s t v f /\ fin_col_span p s t v g
        ==> fin_col_span p s t v (\r. f r + g r)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`p:num`; `s:num->bool`; `t:A->bool`; `v:A->num->real`;
                 `f:num->real`; `g:num->real`; `&1`; `&1`] FIN_COL_SPAN_LIN) THEN
  ASM_SIMP_TAC[FIN_ZP_1; REAL_MUL_LID; ETA_AX]);;

let FIN_COL_SPAN_SUB = prove
 (`forall p s t (v:A->num->real) f g.
        prime p /\ FINITE t /\ fin_col_span p s t v f /\ fin_col_span p s t v g
        ==> fin_col_span p s t v (\r. f r - g r)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`p:num`; `s:num->bool`; `t:A->bool`; `v:A->num->real`;
                 `f:num->real`; `g:num->real`; `&1`; `-- &1`] FIN_COL_SPAN_LIN) THEN
  ASM_SIMP_TAC[FIN_ZP_1; FIN_ZP_NEG; REAL_MUL_LID; ETA_AX] THEN
  REWRITE_TAC[REAL_ARITH `x + -- &1 * y = x - y`]);;

let FIN_COL_SPAN_CMUL = prove
 (`forall p s t (v:A->num->real) f a.
        prime p /\ FINITE t /\ fin_zp p a /\ fin_col_span p s t v f
        ==> fin_col_span p s t v (\r. a * f r)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`p:num`; `s:num->bool`; `t:A->bool`; `v:A->num->real`;
                 `f:num->real`; `\r:num. &0`; `a:real`; `&0`] FIN_COL_SPAN_LIN) THEN
  ASM_SIMP_TAC[FIN_ZP_0; FIN_COL_SPAN_0; REAL_MUL_LZERO; REAL_ADD_RID]);;

let FIN_COL_SPAN_SUM = prove
 (`forall p s t (v:A->num->real) (k:B->bool) c f.
        prime p /\ FINITE t /\ FINITE k /\
        (forall l. l IN k ==> fin_zp p (c l) /\ fin_col_span p s t v (f l))
        ==> fin_col_span p s t v (\r. sum k (\l. c l * f l r))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[fin_col_span] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC
    (MP_TAC o REWRITE_RULE[RIGHT_AND_EXISTS_THM; RIGHT_IMP_EXISTS_THM; SKOLEM_THM])))) THEN
  DISCH_THEN(X_CHOOSE_TAC `d:B->A->real`) THEN
  EXISTS_TAC `\x:A. sum k (\l:B. c l * d l x)` THEN
  REWRITE_TAC[] THEN CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC FIN_ZP_SUM THEN ASM_SIMP_TAC[FIN_ZP_MUL];
    ALL_TAC] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM SUM_RMUL] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) SUM_SWAP o rand o snd) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC SUM_EQ THEN REPEAT STRIP_TAC THEN ASM_SIMP_TAC[] THEN
  REWRITE_TAC[GSYM SUM_LMUL; GSYM REAL_MUL_ASSOC]);;

(* ------------------------------------------------------------------------- *)
(* Generic atom bound for the filtered determinant: if every raw column       *)
(* F_j (7N <= j < 59N) is a local-integral combination of atoms, the atom     *)
(* counting bound FIN_VGE_NDET_ATOMS_012 applies to cat_detq.                 *)
(* ------------------------------------------------------------------------- *)

let FIN_COL_DET_ATOMS = prove
 (`forall p z N (t:A->bool) t1 t2 v R S.
        1 <= N /\ prime p /\ FINITE t /\ t1 SUBSET t /\ t2 SUBSET t /\ DISJOINT t1 t2 /\
        CARD t1 <= S /\ CARD t2 <= R /\
        (forall x r. x IN t2 /\ r < 48 * N ==> fin_vge p (--(&2)) (v x r)) /\
        (forall x r. x IN t1 /\ r < 48 * N ==> fin_vge p (--(&1)) (v x r)) /\
        (forall x r. x IN t /\ ~(x IN t1) /\ ~(x IN t2) /\ r < 48 * N ==> fin_zp p (v x r)) /\
        (forall j. 7 * N <= j /\ j < 59 * N
             ==> fin_col_span p {r | r < 48 * N} t v (\r. cat_rawq z N r j))
        ==> fin_vge p (--(&(MIN (2 * (48 * N)) (MIN (48 * N + R) (2 * R + S)))))
                    (cat_detq z N)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `forall k. k < 48 * N
                    ==> fin_col_span p {r | r < 48 * N} t (v:A->num->real)
                                     (\r. cat_entryq z N r k)`
  MP_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[cat_entryq; REAL_MUL_ASSOC] THEN
    MATCH_MP_TAC FIN_COL_SPAN_SUM THEN
    ASM_SIMP_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
    X_GEN_TAC `w:num` THEN STRIP_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC FIN_ZP_INTEGER THEN ASM_SIMP_TAC[INTEGER_CLOSED];
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[fin_col_span; IN_ELIM_THM; RIGHT_IMP_EXISTS_THM; SKOLEM_THM] THEN
  DISCH_THEN(X_CHOOSE_TAC `d:num->A->real`) THEN
  MP_TAC(ISPECL [`p:num`; `0..48*N-1`; `t:A->bool`; `cat_entryq z N`;
                 `\(x:A) (k:num). (d:num->A->real) k x`; `v:A->num->real`;
                 `t1:A->bool`; `t2:A->bool`; `R:num`; `S:num`]
         FIN_VGE_NDET_ATOMS_012) THEN
  REWRITE_TAC[CARD_NUMSEG; FINITE_NUMSEG; IN_NUMSEG; cat_detq] THEN
  ASM_SIMP_TAC[ARITH_RULE `1 <= N ==> (48 * N - 1 + 1) - 0 = 48 * N`;
               ARITH_RULE `1 <= N ==> (0 <= i /\ i <= 48 * N - 1 <=> i < 48 * N)`] THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC[]);;
