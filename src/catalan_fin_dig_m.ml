(* ========================================================================= *)
(* fin_dig: Lemma 3.1 (M' part) and the scalar part of Lemma 3.2 (M' part),  *)
(* and small-index integrality of the reduced arrays.                       *)
(* ========================================================================= *)

needs "src/catalan_fin_dig_h.ml";;
needs "src/catalan_fin_dig_z.ml";;

prioritize_real();;

let fin_dig_dbg = ref false;;
(* Arithmetic: num assumptions only; DIV/MOD by non-numerals become atoms. *)
let FIN_DIG_NUM_ARITH_TAC : tactic = fun (asl,w) ->
  let has_real tm = can (find_term (fun t -> type_of t = `:real`)) tm in
  let ths = filter (fun (_,th) -> not (has_real (concl th))) asl in
  let is_dm t =
    match t with
      Comb(Comb(Const(("DIV"|"MOD"),_),_),d) -> not (is_numeral d)
    | _ -> false in
  (MAP_EVERY (MP_TAC o snd) ths THEN
   (fun (asl',w') ->
      let dms = find_terms is_dm w' in
      let rec tsize t = match t with Comb(a,b) -> tsize a + tsize b | Abs(_,b) -> 1 + tsize b | _ -> 1 in
      let dms = sort (fun a b -> tsize a > tsize b) dms in
      (MAP_EVERY (fun t -> SPEC_TAC(t, genvar `:num`)) dms THEN
       (fun g -> try ARITH_TAC g with e -> (if !fin_dig_dbg then print_goal g else (); raise e))) (asl',w')))
  (asl,w);;

let FIN_DIG_ARITH_TAC =
  REPEAT CONJ_TAC THEN (FIRST_ASSUM ACCEPT_TAC ORELSE FIN_DIG_NUM_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Helpers.                                                                  *)
(* ------------------------------------------------------------------------- *)

let FIN_DIG_QBOUND = prove
 (`forall p H z. prime p /\ 4 * H < p * p /\ z < H ==> 4 * (z DIV p) < p /\ z DIV p + 2 <= p`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(p:num = 0) /\ 2 <= p` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[PRIME_IMP_NZ; PRIME_GE_2]; ALL_TAC] THEN
  SUBGOAL_THEN `4 * (z DIV p) < p` ASSUME_TAC THENL
   [SUBGOAL_THEN `(4 * (z DIV p)) * p < p * p` MP_TAC THENL
     [MP_TAC(SPECL [`z:num`; `p:num`] DIVISION) THEN ASM_REWRITE_TAC[] THEN
      FIN_DIG_NUM_ARITH_TAC;
      REWRITE_TAC[LT_MULT_RCANCEL] THEN SIMP_TAC[]];
    ASM_REWRITE_TAC[] THEN FIN_DIG_NUM_ARITH_TAC]);;

let FIN_DIG_M_ZP = prove
 (`forall p i. prime p /\ ~(p = 2) /\ i + 1 < p ==> fin_zp p (cat_m i)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[cat_m] THEN COND_CASES_TAC THEN
  ASM_SIMP_TAC[FIN_ZP_0] THEN MATCH_MP_TAC FIN_DIG_ZP_DIV_UNIT THEN
  ASM_SIMP_TAC[FIN_ZP_NUM] THEN MATCH_MP_TAC FIN_DIG_UNIT_MUL THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC FIN_DIG_UNIT_NUM_LT; MATCH_MP_TAC FIN_DIG_C_UNIT] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`i:num`; `2`] DIVISION) THEN FIN_DIG_NUM_ARITH_TAC);;

let FIN_DIG_KMINUS_ZP = prove
 (`forall p u. prime p /\ ~(p = 2) /\ u < p ==> fin_zp p (cat_kminus u)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `fin_dig_unit p (fin_hstar u)` ASSUME_TAC THENL
   [MATCH_MP_TAC FIN_DIG_HSTAR_SMALL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISJ_CASES_TAC(SPEC `u:num` EVEN_OR_ODD) THENL
   [ASM_SIMP_TAC[FIN_BDRY_KMINUS_EVEN; GSYM FIN_DIG_KMT_ETA] THEN
    MATCH_MP_TAC FIN_ZP_MUL THEN ASM_SIMP_TAC[FIN_DIG_KMT_SUM_ZP; FIN_DIG_UNIT_ZP1];
    ASM_SIMP_TAC[FIN_BDRY_KMINUS_ODD] THEN
    MATCH_MP_TAC FIN_ZP_MUL THEN ASM_SIMP_TAC[FIN_DIG_UNIT_ZP1] THEN
    MATCH_MP_TAC FIN_ZP_SUM THEN ASM_REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
    X_GEN_TAC `z:num` THEN STRIP_TAC THEN COND_CASES_TAC THEN
    ASM_SIMP_TAC[FIN_ZP_0] THEN MATCH_MP_TAC FIN_ZP_DIV_NUM THEN
    ASM_SIMP_TAC[FIN_ZP_NUM] THEN
    DISCH_THEN(MP_TAC o MATCH_MP DIVIDES_LE) THEN FIN_DIG_NUM_ARITH_TAC]);;

let FIN_DIG_KPLUS_ZP = prove
 (`forall p v. prime p /\ ~(p = 2) /\ v <= p ==> fin_zp p (cat_kplus v)`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `v:num = 0` THENL
   [ASM_REWRITE_TAC[cat_kplus; FIN_ZP_0] THEN ASM_SIMP_TAC[FIN_ZP_0]; ALL_TAC] THEN
  SUBGOAL_THEN `v = (v - 1) + (1:num)` SUBST1_TAC THENL [FIN_DIG_NUM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[FIN_BDRY_KPLUS] THEN MATCH_MP_TAC FIN_ZP_MUL THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC FIN_DIG_UNIT_ZP1 THEN
    MATCH_MP_TAC FIN_DIG_HSTAR_SMALL THEN FIN_DIG_ARITH_TAC;
    MP_TAC(SPECL [`p:num`; `v - 1`; `\z. EVEN z <=> EVEN (v - 1)`] FIN_DIG_KP_SUM_ZP) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN FIN_DIG_ARITH_TAC]);;

let FIN_DIG_SMALL_INTEGRAL = prove
 (`forall p a j. prime p /\ ~(p = 2) /\ a <= p /\ j + 1 < p
           ==> fin_zp p (fin_M0x a j) /\ (a < p ==> fin_zp p (cat_Z0 a j))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
   [ALL_TAC; DISCH_TAC THEN MATCH_MP_TAC FIN_DIG_Z0_ZP THEN FIN_DIG_ARITH_TAC] THEN
  REWRITE_TAC[fin_M0x] THEN COND_CASES_TAC THENL
   [MATCH_MP_TAC FIN_DIG_KPLUS_ZP THEN FIN_DIG_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[cat_M0] THEN COND_CASES_TAC THEN
  MATCH_MP_TAC FIN_ZP_SUB THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC FIN_DIG_KMINUS_ZP THEN FIN_DIG_ARITH_TAC;
    MATCH_MP_TAC FIN_ZP_SUM THEN ASM_REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
    X_GEN_TAC `k:num` THEN STRIP_TAC THEN MATCH_MP_TAC FIN_ZP_DIV_NUM THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC FIN_DIG_M_ZP THEN FIN_DIG_ARITH_TAC;
      DISCH_THEN(MP_TAC o MATCH_MP DIVIDES_LE) THEN FIN_DIG_NUM_ARITH_TAC];
    MATCH_MP_TAC FIN_DIG_KPLUS_ZP THEN FIN_DIG_ARITH_TAC;
    MATCH_MP_TAC FIN_ZP_SUM THEN ASM_REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
    X_GEN_TAC `k:num` THEN STRIP_TAC THEN MATCH_MP_TAC FIN_ZP_DIV_NUM THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC FIN_DIG_M_ZP THEN FIN_DIG_ARITH_TAC;
      DISCH_THEN(MP_TAC o MATCH_MP DIVIDES_LE) THEN FIN_DIG_NUM_ARITH_TAC]]);;

(* Equation (34) for an arbitrary index z >= 1. *)
let FIN_DIG_M34_GEN = prove
 (`forall p z. prime p /\ ~(p = 2) /\ 1 <= z /\ z DIV p + 2 <= p
         ==> fin_dig_cg p (&p * cat_m (z - 1))
               (fin_E p ((p - 1) - z MOD p) *
                (if z DIV p = 0 then &0 else cat_m (z DIV p - 1)))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(p:num = 0)` ASSUME_TAC THENL [ASM_MESON_TAC[PRIME_IMP_NZ]; ALL_TAC] THEN
  MP_TAC(SPECL [`p:num`; `z DIV p`; `z MOD p`] FIN_DIG_M34) THEN
  ASM_SIMP_TAC[FIN_DIG_DIGITS_EQ; DIVISION]);;

(* ------------------------------------------------------------------------- *)
(* Lemma 3.1 for M', diagonal reduction, case j <= i.                        *)
(* ------------------------------------------------------------------------- *)

let FIN_DIG_L31M_GE = prove
 (`forall p H i j. prime p /\ ~(p = 2) /\ 4 * H < p * p /\ i < H /\ j <= i
   ==> fin_dig_cg p (&p pow 2 * cat_M0 i j)
         (fin_E p ((p - 1) - (i - j) MOD p) *
          cat_M0 ((i - j) DIV p + j DIV p) (j DIV p))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(p:num = 0)` ASSUME_TAC THENL [ASM_MESON_TAC[PRIME_IMP_NZ]; ALL_TAC] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP FIN_DIG_PNZ) THEN
  MP_TAC(SPECL [`i - j:num`; `p:num`] DIVISION) THEN ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `P = (i - j) DIV p` THEN ABBREV_TAC `r = (i - j) MOD p` THEN
  STRIP_TAC THEN
  MP_TAC(SPECL [`p:num`; `H:num`; `i - j:num`] FIN_DIG_QBOUND) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [FIN_DIG_ARITH_TAC; STRIP_TAC] THEN
  MP_TAC(SPECL [`p:num`; `H:num`; `j:num`] FIN_DIG_QBOUND) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [FIN_DIG_ARITH_TAC; STRIP_TAC] THEN
  REWRITE_TAC[cat_M0] THEN ASM_REWRITE_TAC[ARITH_RULE `y <= x + y:num`; ADD_SUB] THEN
  REWRITE_TAC[REAL_SUB_LDISTRIB; GSYM SUM_LMUL] THEN
  MATCH_MP_TAC FIN_DIG_CG_SUB THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC FIN_DIG_KMINUS35 THEN FIN_DIG_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC FIN_DIG_SUM_MULT1 THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `k:num` THEN STRIP_TAC THEN
    MP_TAC(SPECL [`p:num`; `(P * p + r) + k:num`] FIN_DIG_M34_GEN) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [FIN_DIG_ARITH_TAC; ALL_TAC] THEN
      MP_TAC(SPECL [`p:num`; `H:num`; `(P * p + r) + k:num`] FIN_DIG_QBOUND) THEN
      ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [FIN_DIG_ARITH_TAC; SIMP_TAC[]];
      DISCH_THEN(ASSUME_TAC o MATCH_MP FIN_DIG_CG_ZP1)] THEN
    SUBGOAL_THEN `(P * p + r) + (k - 1) = ((P * p + r) + k) - 1:num` SUBST1_TAC THENL
     [FIN_DIG_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN
     `&p pow 2 * cat_m (((P * p + r) + k) - 1) / &k =
      &p * ((&p * cat_m (((P * p + r) + k) - 1)) / &k)` SUBST1_TAC THENL
     [REWRITE_TAC[real_div; REAL_POW_2] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC FIN_DIG_CG_PMUL THEN ASM_SIMP_TAC[FIN_ZP_DIV_NUM];
    ALL_TAC] THEN
  X_GEN_TAC `m:num` THEN STRIP_TAC THEN
  SUBGOAL_THEN `1 <= m * (p:num)` ASSUME_TAC THENL
   [REWRITE_TAC[ARITH_RULE `1 <= n <=> ~(n = 0)`; MULT_EQ_0] THEN FIN_DIG_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(P * p + r) + (m * p - 1) = ((P + m) * p + r) - 1:num` SUBST1_TAC THENL
   [REWRITE_TAC[RIGHT_ADD_DISTRIB] THEN FIN_DIG_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `P + (m - 1) = (P + m) - 1:num` SUBST1_TAC THENL
   [FIN_DIG_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(P + m) * p + r < H:num` ASSUME_TAC THENL
   [SUBGOAL_THEN `m * p <= j:num` MP_TAC THENL
     [UNDISCH_TAC `m <= j DIV p` THEN ASM_SIMP_TAC[LE_RDIV_EQ] THEN
      REWRITE_TAC[MULT_SYM]; ALL_TAC] THEN
    REWRITE_TAC[RIGHT_ADD_DISTRIB] THEN FIN_DIG_NUM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`p:num`; `H:num`; `(P + m) * p + r:num`] FIN_DIG_QBOUND) THEN
  ASM_SIMP_TAC[FIN_DIG_DIV_DIGITS] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`p:num`; `P + m:num`; `r:num`] FIN_DIG_M34) THEN
  ANTS_TAC THENL [FIN_DIG_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[ADD_EQ_0; ARITH_RULE `1 <= m ==> ~(m = 0)`] THEN
  COND_CASES_TAC THENL [FIN_DIG_NUM_ARITH_TAC; ALL_TAC] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `&p pow 2 * cat_m (((P + m) * p + r) - 1) / &(m * p) =
    (&p * cat_m (((P + m) * p + r) - 1)) / &m` SUBST1_TAC THENL
   [REWRITE_TAC[GSYM REAL_OF_NUM_MUL; real_div; REAL_INV_MUL; REAL_POW_2] THEN
    UNDISCH_TAC `~(&p = &0)` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  REWRITE_TAC[real_div; REAL_MUL_ASSOC] THEN REWRITE_TAC[GSYM real_div] THEN
  MATCH_MP_TAC FIN_DIG_CG_DIV_NUM THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o MATCH_MP DIVIDES_LE) THEN FIN_DIG_NUM_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Lemma 3.1 for M', diagonal reduction, case i < j.                         *)
(* ------------------------------------------------------------------------- *)

let FIN_DIG_SUMSET_LT = prove
 (`forall p P r j e. ~(p = 0) /\ r < p /\ P * p + r < j
     ==> sum {m | (P * p + r) + 2 <= m * p /\ m * p <= j}
             (\m. e * (if m - P - 1 = 0 then &0 else cat_m ((m - P - 1) - 1)) / &m) =
         e * sum (1..(j DIV p - P) - 1) (\k. cat_m (k - 1) / &((P + 1) + k))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `P <= j DIV p` ASSUME_TAC THENL
   [ASM_SIMP_TAC[LE_RDIV_EQ] THEN ONCE_REWRITE_TAC[MULT_SYM] THEN
    FIN_DIG_NUM_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `sum (P + 1..j DIV p)
             (\m. e * (if m - P - 1 = 0 then &0 else cat_m ((m - P - 1) - 1)) / &m)` THEN
  CONJ_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC SUM_SUPERSET THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_NUMSEG] THEN CONJ_TAC THENL
     [X_GEN_TAC `m:num` THEN STRIP_TAC THEN CONJ_TAC THENL
       [ASM_CASES_TAC `m <= P:num` THENL
         [SUBGOAL_THEN `m * p <= P * (p:num)` MP_TAC THENL
           [ASM_REWRITE_TAC[LE_MULT_RCANCEL]; FIN_DIG_NUM_ARITH_TAC];
          FIN_DIG_NUM_ARITH_TAC];
        ASM_SIMP_TAC[LE_RDIV_EQ] THEN ONCE_REWRITE_TAC[MULT_SYM] THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    X_GEN_TAC `x:num` THEN STRIP_TAC THEN
    SUBGOAL_THEN `x = P + (1:num)` SUBST1_TAC THENL
     [ASM_CASES_TAC `P + 2 <= x:num` THENL [ALL_TAC; FIN_DIG_NUM_ARITH_TAC] THEN
      SUBGOAL_THEN `(P + 2) * p <= x * p /\ x * p <= (j:num)` MP_TAC THENL
       [ASM_REWRITE_TAC[LE_MULT_RCANCEL] THEN
        UNDISCH_TAC `x <= j DIV p` THEN ASM_SIMP_TAC[LE_RDIV_EQ] THEN
        REWRITE_TAC[MULT_SYM];
        ALL_TAC] THEN
      UNDISCH_TAC `~((P * p + r) + 2 <= x * p /\ x * p <= j)` THEN
      REWRITE_TAC[RIGHT_ADD_DISTRIB] THEN FIN_DIG_NUM_ARITH_TAC;
      REWRITE_TAC[ARITH_RULE `((P + 1) - P) - 1 = 0`] THEN
      REWRITE_TAC[REAL_MUL_RZERO; real_div; REAL_MUL_LZERO]];
    ALL_TAC] THEN
  ASM_CASES_TAC `j DIV p = P` THENL
   [ASM_REWRITE_TAC[SUB_REFL; ARITH_RULE `0 - 1 = 0`] THEN
    SIMP_TAC[SUM_TRIV_NUMSEG; ARITH_RULE `P < P + 1 /\ 0 < 1`; REAL_MUL_RZERO];
    ALL_TAC] THEN
  SIMP_TAC[SUM_CLAUSES_LEFT; ASSUME `P <= j DIV p`;
           ARITH_RULE `P <= J /\ ~(J = P) ==> P + 1 <= J`; ASSUME `~(j DIV p = P)`] THEN
  REWRITE_TAC[ARITH_RULE `((P + 1) - P) - 1 = 0`] THEN
  REWRITE_TAC[REAL_MUL_RZERO; real_div; REAL_MUL_LZERO; REAL_ADD_LID] THEN
  SUBGOAL_THEN `(P + 1) + 1 = 1 + (P + 1) /\ j DIV p = ((j DIV p - P) - 1) + (P + 1)`
    (fun th -> GEN_REWRITE_TAC (LAND_CONV o RATOR_CONV o RAND_CONV o BINOP_CONV) [th])
  THENL [FIN_DIG_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[SUM_OFFSET; GSYM SUM_LMUL] THEN MATCH_MP_TAC SUM_EQ THEN
  X_GEN_TAC `k:num` THEN REWRITE_TAC[IN_NUMSEG] THEN STRIP_TAC THEN
  REWRITE_TAC[ARITH_RULE `((k + P + 1) - P) - 1 = k`] THEN
  ASM_SIMP_TAC[ARITH_RULE `1 <= k ==> ~(k = 0)`] THEN
  REWRITE_TAC[ARITH_RULE `k + P + 1 = (P + 1) + k`] THEN REAL_ARITH_TAC);;

let FIN_DIG_L31M_LT = prove
 (`forall p H i j. prime p /\ ~(p = 2) /\ 4 * H < p * p /\ j < H /\ i < j
   ==> fin_dig_cg p (&p pow 2 * cat_M0 i j)
         (fin_E p ((j - i - 1) MOD p) *
          (cat_kplus ((j - i - 1) DIV p + 1) -
           sum (1..(j DIV p - (j - i - 1) DIV p) - 1)
               (\k. cat_m (k - 1) / &(((j - i - 1) DIV p + 1) + k))))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(p:num = 0)` ASSUME_TAC THENL [ASM_MESON_TAC[PRIME_IMP_NZ]; ALL_TAC] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP FIN_DIG_PNZ) THEN
  MP_TAC(SPECL [`j - i - 1:num`; `p:num`] DIVISION) THEN ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `P = (j - i - 1) DIV p` THEN ABBREV_TAC `r = (j - i - 1) MOD p` THEN
  STRIP_TAC THEN
  MP_TAC(SPECL [`p:num`; `H:num`; `j - i - 1:num`] FIN_DIG_QBOUND) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [FIN_DIG_ARITH_TAC; STRIP_TAC] THEN
  MP_TAC(SPECL [`p:num`; `H:num`; `j:num`] FIN_DIG_QBOUND) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `j - i = (P * p + r) + 1:num` ASSUME_TAC THENL
   [FIN_DIG_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[cat_M0] THEN ASM_REWRITE_TAC[GSYM NOT_LT] THEN
  REWRITE_TAC[REAL_SUB_LDISTRIB] THEN
  MATCH_MP_TAC FIN_DIG_CG_SUB THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC FIN_DIG_KPLUS35 THEN FIN_DIG_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `&p pow 2 * sum (1..i) (\k. cat_m (k - 1) / &(((P * p + r) + 1) + k)) =
    sum ((P * p + r) + 2..j)
        (\k. &p pow 2 * cat_m ((k - ((P * p + r) + 1)) - 1) / &k)` SUBST1_TAC THENL
   [REWRITE_TAC[GSYM SUM_LMUL] THEN
    SUBGOAL_THEN `(P * p + r) + 2 = 1 + ((P * p + r) + 1) /\ j = i + ((P * p + r) + 1)`
      (fun th -> GEN_REWRITE_TAC (RAND_CONV o RATOR_CONV o RAND_CONV o BINOP_CONV) [th])
    THENL [FIN_DIG_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[SUM_OFFSET; ADD_SUB] THEN MATCH_MP_TAC SUM_EQ THEN
    X_GEN_TAC `k:num` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    REWRITE_TAC[ARITH_RULE `k + (x:num) = x + k`];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `fin_E p r * sum (1..(j DIV p - P) - 1) (\k. cat_m (k - 1) / &((P + 1) + k)) =
    sum {m | (P * p + r) + 2 <= m * p /\ m * p <= j}
        (\m. fin_E p r * (if m - P - 1 = 0 then &0 else cat_m ((m - P - 1) - 1)) / &m)`
  SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC FIN_DIG_SUMSET_LT THEN FIN_DIG_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC FIN_DIG_SUM_MULTIPLES THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `k:num` THEN STRIP_TAC THEN
    MP_TAC(SPECL [`p:num`; `k - ((P * p + r) + 1):num`] FIN_DIG_M34_GEN) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [FIN_DIG_ARITH_TAC; ALL_TAC] THEN
      MP_TAC(SPECL [`p:num`; `H:num`; `k - ((P * p + r) + 1):num`] FIN_DIG_QBOUND) THEN
      ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [FIN_DIG_ARITH_TAC; SIMP_TAC[]];
      DISCH_THEN(ASSUME_TAC o MATCH_MP FIN_DIG_CG_ZP1)] THEN
    SUBGOAL_THEN
     `&p pow 2 * cat_m ((k - ((P * p + r) + 1)) - 1) / &k =
      &p * ((&p * cat_m ((k - ((P * p + r) + 1)) - 1)) / &k)` SUBST1_TAC THENL
     [REWRITE_TAC[real_div; REAL_POW_2] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC FIN_DIG_CG_PMUL THEN ASM_SIMP_TAC[FIN_ZP_DIV_NUM];
    ALL_TAC] THEN
  X_GEN_TAC `m:num` THEN STRIP_TAC THEN
  SUBGOAL_THEN `P + 1 <= m:num` ASSUME_TAC THENL
   [ASM_CASES_TAC `m <= P:num` THENL [ALL_TAC; FIN_DIG_NUM_ARITH_TAC] THEN
    SUBGOAL_THEN `m * p <= P * (p:num)` MP_TAC THENL
     [ASM_REWRITE_TAC[LE_MULT_RCANCEL]; FIN_DIG_NUM_ARITH_TAC];
    ALL_TAC] THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `e:num` SUBST_ALL_TAC o REWRITE_RULE[LE_EXISTS]) THEN
  SUBGOAL_THEN `((P + 1) + e) * p - ((P * p + r) + 1) = e * p + ((p - 1) - r):num`
  SUBST1_TAC THENL
   [REWRITE_TAC[RIGHT_ADD_DISTRIB] THEN FIN_DIG_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `e * p + ((p - 1) - r) < H:num` ASSUME_TAC THENL
   [UNDISCH_TAC `((P + 1) + e) * p <= j` THEN REWRITE_TAC[RIGHT_ADD_DISTRIB] THEN
    FIN_DIG_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`p:num`; `H:num`; `e * p + ((p - 1) - r):num`] FIN_DIG_QBOUND) THEN
  ASM_SIMP_TAC[FIN_DIG_DIV_DIGITS; ARITH_RULE `~(p = 0) ==> (p - 1) - r < p`] THEN
  STRIP_TAC THEN
  MP_TAC(SPECL [`p:num`; `e:num`; `(p - 1) - r:num`] FIN_DIG_M34) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `(P * p + r) + 2 <= ((P + 1) + e) * p` THEN
    REWRITE_TAC[RIGHT_ADD_DISTRIB] THEN FIN_DIG_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(p - 1) - ((p - 1) - r) = r /\ ((P + 1) + e) - P - 1 = e` (fun th -> REWRITE_TAC[th])
  THENL [FIN_DIG_ARITH_TAC; ALL_TAC] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `&p pow 2 * cat_m ((e * p + ((p - 1) - r)) - 1) / &(((P + 1) + e) * p) =
    (&p * cat_m ((e * p + ((p - 1) - r)) - 1)) / &((P + 1) + e)` SUBST1_TAC THENL
   [REWRITE_TAC[GSYM REAL_OF_NUM_MUL; real_div; REAL_INV_MUL; REAL_POW_2] THEN
    UNDISCH_TAC `~(&p = &0)` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  REWRITE_TAC[real_div; REAL_MUL_ASSOC] THEN REWRITE_TAC[GSYM real_div] THEN
  MATCH_MP_TAC FIN_DIG_CG_DIV_NUM THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o MATCH_MP DIVIDES_LE) THEN
  UNDISCH_TAC `((P + 1) + e) * p <= j` THEN
  SUBGOAL_THEN `((P + 1) + e) * p <= j <=> (P + 1) + e <= j DIV p` SUBST1_TAC THENL
   [ASM_SIMP_TAC[LE_RDIV_EQ] THEN REWRITE_TAC[MULT_SYM]; ALL_TAC] THEN
  FIN_DIG_NUM_ARITH_TAC);;

let FIN_DIG_M0X_LT = prove
 (`forall P J. P <= J
         ==> fin_M0x (J - P) J =
             cat_kplus (P + 1) - sum (1..(J - P) - 1) (\k. cat_m (k - 1) / &((P + 1) + k))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[fin_M0x] THEN COND_CASES_TAC THENL
   [SUBGOAL_THEN `J:num = P` SUBST_ALL_TAC THENL [FIN_DIG_NUM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[SUB_REFL; ARITH_RULE `0 - 1 = 0`; SUM_CLAUSES_NUMSEG; ARITH_EQ] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[cat_M0] THEN
  SUBGOAL_THEN `~(J <= (J - P) - 1) /\ J - ((J - P) - 1) = P + 1` STRIP_ASSUME_TAC THENL
   [FIN_DIG_NUM_ARITH_TAC; ASM_REWRITE_TAC[]]);;

let FIN_DIG_LEMMA31_M_CG = prove
 (`forall p H i j. prime p /\ ~(p = 2) /\ 4 * H < p * p /\ i < H /\ j < H
   ==> fin_dig_cg p (&p pow 2 * cat_M0 i j)
        (fin_E p ((j + (p * (i + 1) - (i + 1))) MOD p) *
         fin_M0x (((i + 1 + ((j + (p * (i + 1) - (i + 1))) MOD p)) - j MOD p) DIV p) (j DIV p))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(p:num = 0)` ASSUME_TAC THENL [ASM_MESON_TAC[PRIME_IMP_NZ]; ALL_TAC] THEN
  SUBGOAL_THEN `1 <= p` ASSUME_TAC THENL [FIN_DIG_NUM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(MP (SPECL [`j:num`; `p:num`] DIVISION) (ASSUME `~(p:num = 0)`)) THEN
  ABBREV_TAC `J = j DIV p` THEN ABBREV_TAC `l = j MOD p` THEN
  DISCH_THEN(CONJUNCTS_THEN2 (ASSUME_TAC o SYM) ASSUME_TAC) THEN
  SUBGOAL_THEN `i <= i * (p:num)` ASSUME_TAC THENL
   [GEN_REWRITE_TAC LAND_CONV [ARITH_RULE `i = i * (1:num)`] THEN
    ASM_REWRITE_TAC[LE_MULT_LCANCEL]; ALL_TAC] THEN
  ASM_CASES_TAC `j <= i:num` THENL
   [MP_TAC(SPECL [`p:num`; `H:num`; `i:num`; `j:num`] FIN_DIG_L31M_GE) THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(MP (SPECL [`i - j:num`; `p:num`] DIVISION) (ASSUME `~(p:num = 0)`)) THEN
    ABBREV_TAC `P = (i - j) DIV p` THEN ABBREV_TAC `r = (i - j) MOD p` THEN
    DISCH_THEN(CONJUNCTS_THEN2 (ASSUME_TAC o SYM) ASSUME_TAC) THEN
    SUBGOAL_THEN `P * p <= i * (p:num)` ASSUME_TAC THENL
     [REWRITE_TAC[LE_MULT_RCANCEL] THEN DISJ1_TAC THEN
      TRANS_TAC LE_TRANS `P * (p:num)` THEN CONJ_TAC THENL
       [GEN_REWRITE_TAC LAND_CONV [ARITH_RULE `P = P * (1:num)`] THEN
        ASM_REWRITE_TAC[LE_MULT_LCANCEL];
        FIN_DIG_NUM_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `j + (p * (i + 1) - (i + 1)) = (i - P) * p + ((p - 1) - r:num)` SUBST1_TAC THENL
     [REWRITE_TAC[RIGHT_SUB_DISTRIB; LEFT_ADD_DISTRIB; MULT_CLAUSES] THEN
      FIN_DIG_NUM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[FIN_DIG_DIV_DIGITS; ARITH_RULE `~(p = 0) ==> (p - 1) - r < p`] THEN
    SUBGOAL_THEN `(i + 1 + (p - 1) - r) - l = (P + J + 1) * p + (0:num)` SUBST1_TAC THENL
     [REWRITE_TAC[RIGHT_ADD_DISTRIB] THEN FIN_DIG_NUM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[FIN_DIG_DIV_DIGITS; ARITH_RULE `~(p = 0) ==> 0 < p`] THEN
    REWRITE_TAC[fin_M0x; ADD_EQ_0; ARITH_EQ; ARITH_RULE `(P + J + 1) - 1 = P + J`];
    ALL_TAC] THEN
  MP_TAC(SPECL [`p:num`; `H:num`; `i:num`; `j:num`] FIN_DIG_L31M_LT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN FIN_DIG_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(MP (SPECL [`j - i - 1:num`; `p:num`] DIVISION) (ASSUME `~(p:num = 0)`)) THEN
  ABBREV_TAC `P = (j - i - 1) DIV p` THEN ABBREV_TAC `r = (j - i - 1) MOD p` THEN
  DISCH_THEN(CONJUNCTS_THEN2 (ASSUME_TAC o SYM) ASSUME_TAC) THEN
  SUBGOAL_THEN `P <= J:num` ASSUME_TAC THENL
   [ASM_CASES_TAC `P <= J:num` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(J + 1) * p <= P * (p:num)` MP_TAC THENL
     [REWRITE_TAC[LE_MULT_RCANCEL] THEN FIN_DIG_NUM_ARITH_TAC;
      REWRITE_TAC[RIGHT_ADD_DISTRIB] THEN FIN_DIG_NUM_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `P * p <= J * (p:num)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[LE_MULT_RCANCEL]; ALL_TAC] THEN
  SUBGOAL_THEN `j + (p * (i + 1) - (i + 1)) = (i + 1) * p + (j - i - 1:num)` SUBST1_TAC THENL
   [REWRITE_TAC[RIGHT_ADD_DISTRIB; LEFT_ADD_DISTRIB; MULT_CLAUSES] THEN
    FIN_DIG_NUM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[MOD_MULT_ADD] THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(i + 1 + r) - l = (J - P) * p + (0:num)` SUBST1_TAC THENL
   [REWRITE_TAC[RIGHT_SUB_DISTRIB] THEN FIN_DIG_NUM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[FIN_DIG_DIV_DIGITS; ARITH_RULE `~(p = 0) ==> 0 < p`] THEN
  ASM_SIMP_TAC[FIN_DIG_M0X_LT]);;

let FIN_DIG_LEMMA31_M = prove
 (`forall p H i j. prime p /\ ~(p = 2) /\ 4 * H < p * p /\ p <= H /\ i < H /\ j < H
   ==> fin_zp p (&p pow 2 * cat_M0 i j) /\
       fin_vge p (&1)
        (&p pow 2 * cat_M0 i j -
         fin_E p ((j + (p * (i + 1) - (i + 1))) MOD p) *
         fin_M0x (((i + 1 + ((j + (p * (i + 1) - (i + 1))) MOD p)) - j MOD p) DIV p) (j DIV p))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`p:num`; `H:num`; `i:num`; `j:num`] FIN_DIG_LEMMA31_M_CG) THEN
  ASM_SIMP_TAC[fin_dig_cg]);;

(* ------------------------------------------------------------------------- *)
(* Lemma 3.2, scalar part for M'.                                            *)
(* ------------------------------------------------------------------------- *)

let FIN_DIG_CENTRAL_M_CG = prove
 (`forall p H i j. prime p /\ ~(p = 2) /\ H < 2 * p /\ p <= H /\ H <= j + p /\ j < p /\ i < H
   ==> fin_dig_cg p (&p * cat_M0 i j)
         (--(sum {l | l < H - p} (\l. if p + l <= i /\ i < 2 * p + l
                                  then &2 * fin_E p (((2 * p + l) - 1) - i) / (&j - &l)
                                  else &0)))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(p:num = 0) /\ 3 <= p` STRIP_ASSUME_TAC THENL
   [MP_TAC(SPEC `p:num` PRIME_GE_2) THEN ASM_REWRITE_TAC[] THEN FIN_DIG_NUM_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP FIN_DIG_PNZ) THEN
  REWRITE_TAC[cat_M0] THEN ASM_CASES_TAC `j <= i:num` THEN ASM_REWRITE_TAC[] THENL
   [ALL_TAC;
    SUBGOAL_THEN `sum {l | l < H - p} (\l. if p + l <= i /\ i < 2 * p + l
                                  then &2 * fin_E p (((2 * p + l) - 1) - i) / (&j - &l)
                                  else &0) = &0` SUBST1_TAC THENL
     [MATCH_MP_TAC SUM_EQ_0 THEN X_GEN_TAC `l:num` THEN DISCH_TAC THEN
      REWRITE_TAC[] THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN
      FIN_DIG_NUM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[REAL_NEG_0; REAL_SUB_LDISTRIB] THEN
    GEN_REWRITE_TAC RAND_CONV [REAL_ARITH `&0 = &0 - &0`] THEN
    MATCH_MP_TAC FIN_DIG_CG_SUB THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THEN
    MATCH_MP_TAC FIN_DIG_CG_PMUL THEN ASM_REWRITE_TAC[] THENL
     [MATCH_MP_TAC FIN_DIG_KPLUS_ZP THEN FIN_DIG_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC FIN_ZP_SUM THEN ASM_REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
    X_GEN_TAC `k:num` THEN STRIP_TAC THEN MATCH_MP_TAC FIN_ZP_DIV_NUM THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC FIN_DIG_M_ZP THEN FIN_DIG_ARITH_TAC;
      DISCH_THEN(MP_TAC o MATCH_MP DIVIDES_LE) THEN FIN_DIG_NUM_ARITH_TAC]] THEN
  REWRITE_TAC[REAL_SUB_LDISTRIB; GSYM SUM_LMUL] THEN
  GEN_REWRITE_TAC RAND_CONV [REAL_ARITH `--x = &0 - x`] THEN
  MATCH_MP_TAC FIN_DIG_CG_SUB THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC FIN_DIG_CG_PMUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC FIN_DIG_KMINUS_ZP THEN FIN_DIG_ARITH_TAC;
    ALL_TAC] THEN
  ONCE_REWRITE_TAC[SUM_REFLECT] THEN
  ASM_CASES_TAC `j:num = 0` THENL
   [ASM_REWRITE_TAC[ARITH_RULE `0 < 1`] THEN
    SUBGOAL_THEN `{l:num | l < H - p} = {}` SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY] THEN FIN_DIG_NUM_ARITH_TAC;
      REWRITE_TAC[SUM_CLAUSES] THEN MATCH_MP_TAC FIN_DIG_CG_REFL THEN
      ASM_SIMP_TAC[FIN_ZP_0]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[ARITH_RULE `j < 1 <=> j = 0`] THEN
  SUBGOAL_THEN
   `sum {l | l < H - p} (\l. if p + l <= i /\ i < 2 * p + l
                             then &2 * fin_E p (((2 * p + l) - 1) - i) / (&j - &l)
                             else &0) =
    sum (0..j - 1) (\l. if p + l <= i /\ i < 2 * p + l
                        then &2 * fin_E p (((2 * p + l) - 1) - i) / (&j - &l)
                        else &0)` SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC SUM_SUPERSET THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_NUMSEG] THEN CONJ_TAC THENL
     [FIN_DIG_NUM_ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `l:num` THEN STRIP_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN
    FIN_DIG_NUM_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC FIN_DIG_CG_SUM THEN ASM_REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
  X_GEN_TAC `l:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  SUBGOAL_THEN `(i - j) + ((j - l) - 1) = (i - l) - 1` SUBST1_TAC THENL
   [FIN_DIG_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `fin_dig_unit p (&(j - l))` ASSUME_TAC THENL
   [MATCH_MP_TAC FIN_DIG_UNIT_NUM_LT THEN FIN_DIG_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&j - &l = &(j - l)` SUBST1_TAC THENL
   [MATCH_MP_TAC REAL_OF_NUM_SUB THEN FIN_DIG_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`p:num`; `i - l:num`] FIN_DIG_M34_GEN) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [FIN_DIG_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `(i - l) DIV p <= 1` MP_TAC THENL
     [ASM_SIMP_TAC[GSYM LT_SUC_LE; RDIV_LT_EQ] THEN FIN_DIG_ARITH_TAC;
      FIN_DIG_NUM_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[real_div] THEN ONCE_REWRITE_TAC[REAL_MUL_ASSOC] THEN
  REWRITE_TAC[GSYM real_div] THEN DISCH_TAC THEN
  ASM_CASES_TAC `p + l <= i:num` THEN ASM_REWRITE_TAC[] THENL
   [ALL_TAC;
    SUBGOAL_THEN `(i - l) DIV p = 0` (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
     [ASM_SIMP_TAC[DIV_EQ_0] THEN FIN_DIG_ARITH_TAC; ALL_TAC] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[REAL_MUL_RZERO]) THEN
    REWRITE_TAC[real_div; REAL_MUL_LZERO] THEN
    MP_TAC(SPECL [`p:num`; `&p * cat_m ((i - l) - 1)`; `&0`; `j - l:num`] FIN_DIG_CG_DIV_NUM) THEN
    ASM_REWRITE_TAC[real_div; REAL_MUL_LZERO] THEN DISCH_THEN MATCH_MP_TAC THEN
    DISCH_THEN(MP_TAC o MATCH_MP DIVIDES_LE) THEN FIN_DIG_NUM_ARITH_TAC] THEN
  SUBGOAL_THEN `i < 2 * p + l` (fun th -> REWRITE_TAC[th]) THENL
   [FIN_DIG_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(i - l) DIV p = 1 /\ (i - l) MOD p = (i - l) - p` (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]))
  THENL
   [MP_TAC(SPECL [`p:num`; `1`; `(i - l) - p:num`] FIN_DIG_DIV_DIGITS) THEN
    ANTS_TAC THENL [FIN_DIG_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `1 * p + ((i - l) - p) = i - l:num` SUBST1_TAC THENL
     [FIN_DIG_ARITH_TAC; SIMP_TAC[]];
    ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ARITH_EQ; SUB_REFL]) THEN
  SUBGOAL_THEN `(p - 1) - ((i - l) - p) = ((2 * p + l) - 1) - i:num`
    (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
   [FIN_DIG_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `cat_m 0 = &2` (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
   [REWRITE_TAC[cat_m; EVEN; ARITH_RULE `0 DIV 2 = 0`; FIN_BDRY_C_0; ADD_CLAUSES] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV;
    ALL_TAC] THEN
  REWRITE_TAC[real_div; REAL_MUL_ASSOC] THEN REWRITE_TAC[GSYM real_div] THEN
  ONCE_REWRITE_TAC[REAL_ARITH `&2 * e = e * &2`] THEN
  MATCH_MP_TAC FIN_DIG_CG_DIV_NUM THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o MATCH_MP DIVIDES_LE) THEN FIN_DIG_NUM_ARITH_TAC);;

let FIN_DIG_CENTRAL_M = prove
 (`forall p H i j. prime p /\ ~(p = 2) /\ H < 2 * p /\ p <= H /\ H <= j + p /\ j < p /\ i < H
   ==> fin_zp p (&p * cat_M0 i j) /\
       fin_vge p (&1) (&p * cat_M0 i j +
          sum {l | l < H - p} (\l. if p + l <= i /\ i < 2 * p + l
                                   then &2 * fin_E p (((2 * p + l) - 1) - i) / (&j - &l) else &0))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`p:num`; `H:num`; `i:num`; `j:num`] FIN_DIG_CENTRAL_M_CG) THEN
  ASM_REWRITE_TAC[fin_dig_cg; REAL_SUB_RNEG] THEN SIMP_TAC[]);;
