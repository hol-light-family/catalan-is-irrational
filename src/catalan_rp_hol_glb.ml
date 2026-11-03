(* ========================================================================= *)
(* rp_hol_glb_: bound of the local formulas G_s on the unit circle.          *)
(* Proves RP_HOL_GLB_THM : |- RP_HOL_GLB_STMT.                               *)
(* ========================================================================= *)

needs "src/catalan_rp_hol_base.ml";;

let RP_HOL_GLB_CVX = prove
 (`forall u a b. &0 <= u /\ u <= &1
     ==> (a <= b ==> a <= (&1 - u) * a + u * b /\ (&1 - u) * a + u * b <= b) /\
         (b <= a ==> b <= (&1 - u) * a + u * b /\ (&1 - u) * a + u * b <= a) /\
         (&1 - u) * a + u * a = a`,
  REPEAT STRIP_TAC THENL
  [MP_TAC(SPECL [`u:real`; `b - a:real`] REAL_LE_MUL) THEN
   MP_TAC(SPECL [`&1 - u:real`; `b - a:real`] REAL_LE_MUL) THEN
   ASM_REAL_ARITH_TAC;
   MP_TAC(SPECL [`u:real`; `b - a:real`] REAL_LE_MUL) THEN
   MP_TAC(SPECL [`&1 - u:real`; `b - a:real`] REAL_LE_MUL) THEN
   ASM_REAL_ARITH_TAC;
   MP_TAC(SPECL [`u:real`; `a - b:real`] REAL_LE_MUL) THEN
   MP_TAC(SPECL [`&1 - u:real`; `a - b:real`] REAL_LE_MUL) THEN
   ASM_REAL_ARITH_TAC;
   MP_TAC(SPECL [`u:real`; `a - b:real`] REAL_LE_MUL) THEN
   MP_TAC(SPECL [`&1 - u:real`; `a - b:real`] REAL_LE_MUL) THEN
   ASM_REAL_ARITH_TAC;
   REAL_ARITH_TAC]);;

let RP_HOL_GLB_SEGPT = prove
 (`forall s p q w. s pow 2 = &1 /\ w IN segment[p,q]
     ==> exists u. &0 <= u /\ u <= &1 /\
             --s * Re w = (&1 - u) * (--s * Re p) + u * (--s * Re q) /\
             Im w = (&1 - u) * Im p + u * Im q`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IN_SEGMENT] THEN STRIP_TAC THEN
  EXISTS_TAC `u:real` THEN ASM_REWRITE_TAC[RE_ADD; IM_ADD; RE_CMUL; IM_CMUL] THEN
  REAL_ARITH_TAC);;

let RP_HOL_GLB_DIST_REAL = prove
 (`forall s a b x y e. (s = &1 \/ s = --(&1)) /\ x pow 2 + y pow 2 = &1 /\
     &0 <= s * x /\ &0 <= a /\ &0 < e /\
     (abs b = &1 + &2 * e \/ a = e \/ abs b <= &1 - e)
     ==> e pow 2 <= (--s * a - x) pow 2 + (b - y) pow 2`,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN `s pow 2 = &1` ASSUME_TAC THENL
  [FIRST_X_ASSUM(DISJ_CASES_THEN SUBST1_TAC o check (fun th -> concl th = `s = &1 \/ s = --(&1)`)) THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `abs(y) <= &1` ASSUME_TAC THENL
  [REWRITE_TAC[GSYM ABS_SQUARE_LE_1] THEN
   MP_TAC(SPEC `x:real` REAL_LE_POW_2) THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `b * y <= abs b` ASSUME_TAC THENL
  [MATCH_MP_TAC(REAL_ARITH `abs(b * y) <= c ==> b * y <= c`) THEN
   REWRITE_TAC[REAL_ABS_MUL] THEN
   GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
   MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_ABS_POS]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= a * (s * x)` ASSUME_TAC THENL
  [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(--s * a - x) pow 2 + (b - y) pow 2 =
                a pow 2 + &2 * (a * (s * x)) + &1 + abs b pow 2 - &2 * (b * y)`
  SUBST1_TAC THENL
  [REWRITE_TAC[REAL_POW2_ABS] THEN
   UNDISCH_TAC `s pow 2 = &1` THEN UNDISCH_TAC `x pow 2 + y pow 2 = &1` THEN
   CONV_TAC REAL_RING;
   ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `a pow 2 + (&1 - abs b) pow 2` THEN CONJ_TAC THENL
  [ALL_TAC; REWRITE_TAC[REAL_POW_2] THEN ASM_REAL_ARITH_TAC] THEN
  UNDISCH_TAC `abs b = &1 + &2 * e \/ a = e \/ abs b <= &1 - e` THEN
  STRIP_TAC THENL
  [ASM_REWRITE_TAC[REAL_POW_2] THEN
   MP_TAC(SPEC `a:real` REAL_LE_SQUARE) THEN
   MP_TAC(SPECL [`e:real`; `e:real`] REAL_LE_MUL) THEN ASM_REAL_ARITH_TAC;
   ASM_REWRITE_TAC[] THEN MP_TAC(SPEC `&1 - abs b` REAL_LE_POW_2) THEN
   REAL_ARITH_TAC;
   MP_TAC(SPEC `a:real` REAL_LE_POW_2) THEN
   SUBGOAL_THEN `e pow 2 <= (&1 - abs b) pow 2` MP_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC]]);;

let RP_HOL_GLB_NEARI = prove
 (`forall w e. &0 <= e /\ abs(Re w) <= e /\ abs(abs(Im w) - &1) <= &2 * e
         ==> norm(w - ii) <= &3 * e \/ norm(w + ii) <= &3 * e`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `forall c. abs(Im w - c) <= &2 * e ==> norm(w - c % ii) <= &3 * e`
  ASSUME_TAC THENL
  [REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[GSYM REAL_ABS_NORM] THEN
   SUBGOAL_THEN `abs(&3 * e) = &3 * e` (fun th -> ONCE_REWRITE_TAC[GSYM th]) THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   REWRITE_TAC[REAL_LE_SQUARE_ABS; COMPLEX_SQNORM; RE_SUB; IM_SUB; RE_CMUL;
               IM_CMUL; RE_II; IM_II] THEN
   SUBGOAL_THEN `Re w pow 2 <= e pow 2 /\ (Im w - c) pow 2 <= (&2 * e) pow 2`
   MP_TAC THENL
   [REWRITE_TAC[GSYM REAL_LE_SQUARE_ABS] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   MP_TAC(SPEC `e:real` REAL_LE_SQUARE) THEN
   REWRITE_TAC[REAL_POW_2; REAL_MUL_RZERO; REAL_MUL_RID; REAL_SUB_RZERO] THEN
   REAL_ARITH_TAC;
   ALL_TAC] THEN
  ASM_CASES_TAC `&0 <= Im w` THENL
  [DISJ1_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `&1`) THEN
   REWRITE_TAC[VECTOR_MUL_LID] THEN DISCH_THEN MATCH_MP_TAC THEN
   ASM_REAL_ARITH_TAC;
   DISJ2_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `--(&1)`) THEN
   REWRITE_TAC[VECTOR_MUL_LNEG; VECTOR_MUL_LID; VECTOR_ARITH `w - --x:real^2 = w + x`] THEN
   DISCH_THEN MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC]);;
let RP_HOL_GLB_SCASES_TAC =
  FIRST_X_ASSUM(DISJ_CASES_THEN SUBST_ALL_TAC o
    check (fun th -> concl th = `s = &1 \/ s = --(&1)`));;

let RP_HOL_GLB_PT = prove
 (`forall n d s (x:num->real) (f:complex->complex) z w.
     48 <= n /\ &0 < d /\ &2 * d <= inv(&n) /\
     (forall i. i < n ==> &2 * d < abs(x i)) /\ (s = &1 \/ s = --(&1)) /\
     (forall w. norm(w - ii) <= &3 / &n \/ norm(w + ii) <= &3 / &n
          ==> norm(f w) <= exp(&12)) /\
     (forall w. abs(Re w) <= d /\ abs(Im w) <= &1 - inv(&n) ==> norm(f w) <= exp(&12)) /\
     norm z = &1 /\ &0 <= s * Re z /\
     &0 <= --s * Re w /\ --s * Re w <= inv(&n) /\
     (abs(Im w) = &1 + &2 * inv(&n) \/
      (--s * Re w = inv(&n) /\ &1 - inv(&n) <= abs(Im w) /\
       abs(Im w) <= &1 + &2 * inv(&n)) \/
      (abs(Im w) = &1 - inv(&n) /\ d <= --s * Re w) \/
      (--s * Re w = d /\ abs(Im w) <= &1 - inv(&n)))
     ==> (forall i. i < n ==> ~(w = Cx(x i))) /\ norm(f w) <= exp(&12) /\
         inv(&n) <= norm(w - z)`,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN `&0 < inv(&n) /\ inv(&n) <= inv(&48)` STRIP_ASSUME_TAC THENL
  [REWRITE_TAC[REAL_LT_INV_EQ] THEN CONJ_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC;
    MATCH_MP_TAC REAL_LE_INV2 THEN REWRITE_TAC[REAL_OF_NUM_LE; REAL_OF_NUM_LT] THEN
    ASM_ARITH_TAC]; ALL_TAC] THEN
  SUBGOAL_THEN `abs(Re w) = --s * Re w` ASSUME_TAC THENL
  [UNDISCH_TAC `&0 <= --s * Re w` THEN RP_HOL_GLB_SCASES_TAC THEN REAL_ARITH_TAC;
   ALL_TAC] THEN
  UNDISCH_TAC `inv(&n) <= inv(&48)` THEN CONV_TAC(LAND_CONV(RAND_CONV REAL_RAT_REDUCE_CONV)) THEN
  DISCH_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[real_div]) THEN
  ABBREV_TAC `e = inv(&n)` THEN
  REPEAT CONJ_TAC THENL
  [X_GEN_TAC `i:num` THEN DISCH_TAC THEN DISCH_THEN SUBST_ALL_TAC THEN
   FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN ASM_REWRITE_TAC[] THEN
   RULE_ASSUM_TAC(REWRITE_RULE[RE_CX; IM_CX]) THEN ASM_REAL_ARITH_TAC;
   UNDISCH_TAC `abs(Im w) = &1 + &2 * e \/
      (--s * Re w = e /\ &1 - e <= abs(Im w) /\ abs(Im w) <= &1 + &2 * e) \/
      (abs(Im w) = &1 - e /\ d <= --s * Re w) \/
      (--s * Re w = d /\ abs(Im w) <= &1 - e)` THEN
   ASM_CASES_TAC `--s * Re w = d /\ abs(Im w) <= &1 - e` THENL
   [DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    DISCH_TAC THEN FIRST_X_ASSUM(MATCH_MP_TAC o check (is_disj o lhand o snd o dest_forall o concl)) THEN
    MATCH_MP_TAC RP_HOL_GLB_NEARI THEN ASM_REAL_ARITH_TAC];
   ONCE_REWRITE_TAC[GSYM REAL_ABS_NORM] THEN
   SUBGOAL_THEN `abs e = e` (fun th -> ONCE_REWRITE_TAC[GSYM th]) THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   REWRITE_TAC[REAL_LE_SQUARE_ABS; COMPLEX_SQNORM; RE_SUB; IM_SUB] THEN
   MP_TAC(SPECL [`s:real`; `--s * Re w`; `Im w`; `Re z`; `Im z`; `e:real`]
     RP_HOL_GLB_DIST_REAL) THEN
   ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `norm(z:complex) = &1` THEN
    DISCH_THEN(MP_TAC o AP_TERM `\t:real. t pow 2`) THEN
    REWRITE_TAC[COMPLEX_SQNORM] THEN DISCH_THEN SUBST1_TAC THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC(REAL_ARITH `a = b ==> e <= a ==> e <= b`) THEN
    RP_HOL_GLB_SCASES_TAC THEN REAL_ARITH_TAC]]);;
let RP_HOL_GLB_CVX_TAC =
  let pat = `(&1 - u) * A + u * B:real` in
  ASSUM_LIST (fun ths ->
    EVERY (mapfilter (fun th ->
      let r = rand(concl th) in
      let i = term_match [] pat r in
      MP_TAC(SPECL [instantiate i `u:real`; instantiate i `A:real`;
                    instantiate i `B:real`] RP_HOL_GLB_CVX)) ths));;

let RP_HOL_GLB_SEGGEOM = prove
 (`forall n d s k w.
     48 <= n /\ &0 < d /\ &2 * d <= inv(&n) /\ (s = &1 \/ s = --(&1)) /\
     k <= 6 /\ w IN segment[rp_hol_v n d s k, rp_hol_v n d s (k + 1)]
     ==> &0 <= --s * Re w /\ --s * Re w <= inv(&n) /\
         (abs(Im w) = &1 + &2 * inv(&n) \/
          (--s * Re w = inv(&n) /\ &1 - inv(&n) <= abs(Im w) /\
           abs(Im w) <= &1 + &2 * inv(&n)) \/
          (abs(Im w) = &1 - inv(&n) /\ d <= --s * Re w) \/
          (--s * Re w = d /\ abs(Im w) <= &1 - inv(&n)))`,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN `s pow 2 = &1` ASSUME_TAC THENL
  [RP_HOL_GLB_SCASES_TAC THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < inv(&n) /\ inv(&n) <= inv(&48)` STRIP_ASSUME_TAC THENL
  [REWRITE_TAC[REAL_LT_INV_EQ] THEN CONJ_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT] THEN UNDISCH_TAC `48 <= n` THEN ARITH_TAC;
    MATCH_MP_TAC REAL_LE_INV2 THEN REWRITE_TAC[REAL_OF_NUM_LE; REAL_OF_NUM_LT] THEN
    UNDISCH_TAC `48 <= n` THEN ARITH_TAC]; ALL_TAC] THEN
  UNDISCH_TAC `inv(&n) <= inv(&48)` THEN CONV_TAC(LAND_CONV(RAND_CONV REAL_RAT_REDUCE_CONV)) THEN
  MP_TAC(SPECL [`s:real`; `rp_hol_v n d s k`; `rp_hol_v n d s (k + 1)`; `w:complex`]
    RP_HOL_GLB_SEGPT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `u:real` STRIP_ASSUME_TAC) THEN
  UNDISCH_TAC `k <= 6` THEN
  REWRITE_TAC[ARITH_RULE `k <= 6 <=> k = 0 \/ k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/
                                       k = 5 \/ k = 6`] THEN
  STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[rp_hol_v; ARITH; RE; IM; real_div]) THEN
  RP_HOL_GLB_SCASES_TAC THEN
  ABBREV_TAC `e = inv(&n)` THEN
  RP_HOL_GLB_CVX_TAC THEN ASM_REAL_ARITH_TAC);;
let RP_HOL_GLB_SEGBOUND = prove
 (`forall (f:complex->complex) z p q M e.
     &0 < e /\ &0 <= M /\
     (forall w. w IN segment[p,q]
          ==> f complex_differentiable at w /\ norm(f w) <= M /\
              e <= norm(w - z))
     ==> norm(rp_hol_cint f z p q) <= M / e * norm(q - p)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[rp_hol_cint] THEN
  MATCH_MP_TAC(ISPEC `\w. (f:complex->complex) w / (w - z)`
    HAS_PATH_INTEGRAL_BOUND_LINEPATH) THEN
  REPEAT CONJ_TAC THENL
  [MATCH_MP_TAC HAS_PATH_INTEGRAL_INTEGRAL THEN
   MATCH_MP_TAC PATH_INTEGRABLE_CONTINUOUS_LINEPATH THEN
   MATCH_MP_TAC CONTINUOUS_AT_IMP_CONTINUOUS_ON THEN
   X_GEN_TAC `w:complex` THEN DISCH_TAC THEN
   FIRST_X_ASSUM(MP_TAC o SPEC `w:complex`) THEN ASM_REWRITE_TAC[] THEN
   STRIP_TAC THEN
   MATCH_MP_TAC COMPLEX_DIFFERENTIABLE_IMP_CONTINUOUS_AT THEN
   MATCH_MP_TAC COMPLEX_DIFFERENTIABLE_DIV_AT THEN
   ASM_SIMP_TAC[COMPLEX_DIFFERENTIABLE_SUB; COMPLEX_DIFFERENTIABLE_ID;
                COMPLEX_DIFFERENTIABLE_CONST] THEN
   DISCH_TAC THEN UNDISCH_TAC `e <= norm(w - z:complex)` THEN
   ASM_REWRITE_TAC[COMPLEX_NORM_0] THEN ASM_REAL_ARITH_TAC;
   MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC;
   X_GEN_TAC `w:complex` THEN DISCH_TAC THEN
   FIRST_X_ASSUM(MP_TAC o SPEC `w:complex`) THEN ASM_REWRITE_TAC[] THEN
   STRIP_TAC THEN REWRITE_TAC[COMPLEX_NORM_DIV; real_div] THEN
   MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[NORM_POS_LE; REAL_LE_INV_EQ] THEN
   MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REWRITE_TAC[]]);;

let RP_HOL_GLB_K = prove
 (`forall n d s (x:num->real) (f:complex->complex) z k.
     48 <= n /\ &0 < d /\ &2 * d <= inv(&n) /\
     (forall i. i < n ==> &2 * d < abs(x i)) /\ (s = &1 \/ s = --(&1)) /\
     (forall w. (forall i. i < n ==> ~(w = Cx(x i))) ==> f complex_differentiable at w) /\
     (forall w. norm(w - ii) <= &3 / &n \/ norm(w + ii) <= &3 / &n
          ==> norm(f w) <= exp(&12)) /\
     (forall w. abs(Re w) <= d /\ abs(Im w) <= &1 - inv(&n) ==> norm(f w) <= exp(&12)) /\
     norm z = &1 /\ &0 <= s * Re z /\ k <= 6
     ==> norm(rp_hol_cint f z (rp_hol_v n d s k) (rp_hol_v n d s (k + 1))) <=
         exp(&12) * &n * norm(rp_hol_v n d s (k + 1) - rp_hol_v n d s k)`,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REWRITE_TAC[REAL_MUL_ASSOC] THEN
  SUBGOAL_THEN `exp(&12) * &n = exp(&12) / inv(&n)` SUBST1_TAC THENL
  [REWRITE_TAC[real_div; REAL_INV_INV]; ALL_TAC] THEN
  MATCH_MP_TAC RP_HOL_GLB_SEGBOUND THEN
  REWRITE_TAC[REAL_EXP_POS_LE; REAL_LT_INV_EQ; REAL_OF_NUM_LT] THEN
  CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `w:complex` THEN DISCH_TAC THEN
  MP_TAC(SPECL [`n:num`; `d:real`; `s:real`; `k:num`; `w:complex`]
    RP_HOL_GLB_SEGGEOM) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`n:num`; `d:real`; `s:real`; `x:num->real`; `f:complex->complex`;
                `z:complex`; `w:complex`] RP_HOL_GLB_PT) THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;
let RP_HOL_GLB_NORMRI = prove
 (`forall z L. abs(Re z) + abs(Im z) <= L ==> norm z <= L`,
  MESON_TAC[COMPLEX_NORM_LE_RE_IM; REAL_LE_TRANS]);;

let RP_HOL_GLB_LEN = prove
 (`forall n d s. 48 <= n /\ &0 < d /\ &2 * d <= inv(&n) /\ (s = &1 \/ s = --(&1))
     ==> sum(0..6) (\k. norm(rp_hol_v n d s (k + 1) - rp_hol_v n d s k))
         <= &2 + &8 * inv(&n)`,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN `&0 < inv(&n) /\ inv(&n) <= inv(&48)` STRIP_ASSUME_TAC THENL
  [REWRITE_TAC[REAL_LT_INV_EQ] THEN CONJ_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT] THEN UNDISCH_TAC `48 <= n` THEN ARITH_TAC;
    MATCH_MP_TAC REAL_LE_INV2 THEN REWRITE_TAC[REAL_OF_NUM_LE; REAL_OF_NUM_LT] THEN
    UNDISCH_TAC `48 <= n` THEN ARITH_TAC]; ALL_TAC] THEN
  UNDISCH_TAC `inv(&n) <= inv(&48)` THEN
  CONV_TAC(LAND_CONV(RAND_CONV REAL_RAT_REDUCE_CONV)) THEN DISCH_TAC THEN
  CONV_TAC(LAND_CONV EXPAND_SUM_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
  ABBREV_TAC `e = inv(&n)` THEN
  SUBGOAL_THEN
   `norm(rp_hol_v n d s 1 - rp_hol_v n d s 0) <= e /\
    norm(rp_hol_v n d s 2 - rp_hol_v n d s 1) <= &3 * e /\
    norm(rp_hol_v n d s 3 - rp_hol_v n d s 2) <= e - d /\
    norm(rp_hol_v n d s 4 - rp_hol_v n d s 3) <= &2 - &2 * e /\
    norm(rp_hol_v n d s 5 - rp_hol_v n d s 4) <= e - d /\
    norm(rp_hol_v n d s 6 - rp_hol_v n d s 5) <= &3 * e /\
    norm(rp_hol_v n d s 7 - rp_hol_v n d s 6) <= e`
  MP_TAC THENL
  [REPEAT CONJ_TAC THEN MATCH_MP_TAC RP_HOL_GLB_NORMRI THEN
   REWRITE_TAC[rp_hol_v; ARITH; RE_SUB; IM_SUB; RE; IM; real_div] THEN
   ASM_REWRITE_TAC[] THEN RP_HOL_GLB_SCASES_TAC THEN ASM_REAL_ARITH_TAC;
   ASM_REAL_ARITH_TAC]);;
let RP_HOL_GLB_CBOUND = prove
 (`forall n d s (x:num->real) (f:complex->complex) z.
     48 <= n /\ &0 < d /\ &2 * d <= inv(&n) /\
     (forall i. i < n ==> &2 * d < abs(x i)) /\ (s = &1 \/ s = --(&1)) /\
     (forall w. (forall i. i < n ==> ~(w = Cx(x i))) ==> f complex_differentiable at w) /\
     (forall w. norm(w - ii) <= &3 / &n \/ norm(w + ii) <= &3 / &n
          ==> norm(f w) <= exp(&12)) /\
     (forall w. abs(Re w) <= d /\ abs(Im w) <= &1 - inv(&n) ==> norm(f w) <= exp(&12)) /\
     norm z = &1 /\ &0 <= s * Re z
     ==> norm(rp_hol_C n d s f z) <= exp(&12) * (&2 * &n + &8)`,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REWRITE_TAC[rp_hol_C] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum(0..6) (\k. exp(&12) * &n *
                 norm(rp_hol_v n d s (k + 1) - rp_hol_v n d s k))` THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC VSUM_NORM_LE THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
   X_GEN_TAC `k:num` THEN STRIP_TAC THEN
   MATCH_MP_TAC RP_HOL_GLB_K THEN EXISTS_TAC `x:num->real` THEN
   ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  REWRITE_TAC[SUM_LMUL] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
  REWRITE_TAC[REAL_EXP_POS_LE] THEN
  MP_TAC(SPECL [`n:num`; `d:real`; `s:real`] RP_HOL_GLB_LEN) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&n * (&2 + &8 * inv(&n))` THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_POS];
   SUBGOAL_THEN `&n * inv(&n) = &1` MP_TAC THENL
   [MATCH_MP_TAC REAL_MUL_RINV THEN REWRITE_TAC[REAL_OF_NUM_EQ] THEN
    UNDISCH_TAC `48 <= n` THEN ARITH_TAC;
    REAL_ARITH_TAC]]);;

let RP_HOL_GLB_THM = prove
 (`RP_HOL_GLB_STMT`,
  REWRITE_TAC[RP_HOL_GLB_STMT] THEN REPEAT GEN_TAC THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  MP_TAC(SPECL [`n:num`; `d:real`; `s:real`; `x:num->real`;
                `f:complex->complex`; `z:complex`] RP_HOL_GLB_CBOUND) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ABBREV_TAC `C = rp_hol_C n d s f z` THEN
  REWRITE_TAC[rp_hol_G] THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&3 <= pi` ASSUME_TAC THENL
  [MP_TAC PI_APPROX_32 THEN CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
   REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `norm(Cx(&6) / (Cx(&2) * Cx pi * ii)) <= &1` ASSUME_TAC THENL
  [REWRITE_TAC[COMPLEX_NORM_DIV; COMPLEX_NORM_MUL; COMPLEX_NORM_CX;
               COMPLEX_NORM_II; REAL_ABS_NUM; REAL_MUL_RID] THEN
   SUBGOAL_THEN `abs pi = pi` SUBST1_TAC THENL
   [MP_TAC PI_POS THEN REAL_ARITH_TAC; ALL_TAC] THEN
   SIMP_TAC[REAL_LE_LDIV_EQ; REAL_ARITH `&3 <= pi ==> &0 < &2 * pi`;
            ASSUME `&3 <= pi`] THEN
   ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&1 <= exp(&12)` ASSUME_TAC THENL
  [REWRITE_TAC[GSYM REAL_EXP_0; REAL_EXP_MONO_LE] THEN REAL_ARITH_TAC;
   ALL_TAC] THEN
  SUBGOAL_THEN `exp(&12) * &48 <= exp(&12) * &n` ASSUME_TAC THENL
  [MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_EXP_POS_LE; REAL_OF_NUM_LE] THEN
   ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&5 + exp(&12) * (&2 * &n + &8)` THEN CONJ_TAC THENL
  [MATCH_MP_TAC(NORM_ARITH `norm(a:complex) <= x /\ norm(b:complex) <= y
                            ==> norm(a - b) <= x + y`) THEN
   CONJ_TAC THENL
   [REWRITE_TAC[COMPLEX_NORM_MUL; COMPLEX_NORM_CX; COMPLEX_NORM_POW] THEN
    ASM_REWRITE_TAC[REAL_POW_ONE; REAL_MUL_RID] THEN
    COND_CASES_TAC THEN REAL_ARITH_TAC;
    REWRITE_TAC[COMPLEX_NORM_MUL] THEN
    GEN_REWRITE_TAC RAND_CONV [REAL_ARITH `x = &1 * &1 * x`] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[NORM_POS_LE] THEN
    ASM_SIMP_TAC[NORM_POS_LE; REAL_LE_MUL] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[NORM_POS_LE]];
   REWRITE_TAC[rp_K0] THEN ASM_REAL_ARITH_TAC]);;
