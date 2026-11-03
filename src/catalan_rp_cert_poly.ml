(* ========================================================================= *)
(* CERT / POLY: polynomials as coefficient lists (lowest degree first).      *)
(* Ring operations, Moebius transform with integer scaling, sign            *)
(* variations, "at most one positive root" for <= 1 sign variation,          *)
(* continuity, IVT, Lipschitz bound; fast proof-producing conversions.       *)
(* ========================================================================= *)

needs "src/catalan_rp_cert_base.ml";;

let rp_cert_poly_add = define
 `(rp_cert_poly_add [] (q:real list) = q) /\
  (rp_cert_poly_add (CONS (a:real) p) [] = CONS a p) /\
  (rp_cert_poly_add (CONS a p) (CONS b q) = CONS (a + b) (rp_cert_poly_add p q))`;;

let rp_cert_poly_cmul = define
 `(rp_cert_poly_cmul (c:real) [] = []) /\
  (rp_cert_poly_cmul c (CONS a p) = CONS (c * a) (rp_cert_poly_cmul c p))`;;

let rp_cert_poly_mul = define
 `(rp_cert_poly_mul [] (q:real list) = []) /\
  (rp_cert_poly_mul (CONS a p) q =
     rp_cert_poly_add (rp_cert_poly_cmul a q) (CONS (&0) (rp_cert_poly_mul p q)))`;;

let RP_CERT_POLY_EVAL_ADD = prove
 (`forall p q x. rp_cert_peval (rp_cert_poly_add p q) x =
           rp_cert_peval p x + rp_cert_peval q x`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[rp_cert_poly_add; rp_cert_peval] THEN
  TRY REAL_ARITH_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[rp_cert_poly_add; rp_cert_peval] THEN REAL_ARITH_TAC);;

let RP_CERT_POLY_EVAL_CMUL = prove
 (`forall c p x. rp_cert_peval (rp_cert_poly_cmul c p) x = c * rp_cert_peval p x`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[rp_cert_poly_cmul; rp_cert_peval] THEN REAL_ARITH_TAC);;

let RP_CERT_POLY_EVAL_MUL = prove
 (`forall p q x. rp_cert_peval (rp_cert_poly_mul p q) x =
           rp_cert_peval p x * rp_cert_peval q x`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[rp_cert_poly_mul; rp_cert_peval; RP_CERT_POLY_EVAL_ADD;
                  RP_CERT_POLY_EVAL_CMUL] THEN REAL_ARITH_TAC);;

(* (D + D t)^n *)
let rp_cert_poly_pw = define
 `(rp_cert_poly_pw d 0 = [&1]) /\
  (rp_cert_poly_pw d (SUC n) = rp_cert_poly_mul [d; d] (rp_cert_poly_pw d n))`;;

let RP_CERT_POLY_EVAL_PW = prove
 (`forall d n t. rp_cert_peval (rp_cert_poly_pw d n) t = (d + d * t) pow n`,
  GEN_TAC THEN INDUCT_TAC THEN
  ASM_REWRITE_TAC[rp_cert_poly_pw; RP_CERT_POLY_EVAL_MUL; rp_cert_peval; real_pow] THEN
  REAL_ARITH_TAC);;

(* integer-scaled Moebius recursion:  sum_j p_j (B + C t)^j (D + D t)^(n-j) *)
let rp_cert_poly_mobr = define
 `(rp_cert_poly_mobr b c d [] n = []) /\
  (rp_cert_poly_mobr b c d (CONS a p) n =
     rp_cert_poly_add (rp_cert_poly_cmul a (rp_cert_poly_pw d n))
                      (rp_cert_poly_mul [b; c] (rp_cert_poly_mobr b c d p (n - 1))))`;;

let RP_CERT_POLY_EVAL_MOBR = prove
 (`forall p n b c d t. LENGTH p <= n + 1 /\ ~(d + d * t = &0)
     ==> rp_cert_peval (rp_cert_poly_mobr b c d p n) t =
         (d + d * t) pow n * rp_cert_peval p ((b + c * t) / (d + d * t))`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[rp_cert_poly_mobr; rp_cert_peval; REAL_MUL_RZERO] THEN
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[RP_CERT_POLY_EVAL_ADD; RP_CERT_POLY_EVAL_CMUL; RP_CERT_POLY_EVAL_MUL;
              RP_CERT_POLY_EVAL_PW; rp_cert_peval] THEN
  ASM_CASES_TAC `t:(real)list = []` THENL
   [ASM_REWRITE_TAC[rp_cert_poly_mobr; rp_cert_peval] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`n - 1`; `b:real`; `c:real`; `d:real`; `t':real`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `LENGTH (CONS (h:real) t) <= n + 1` THEN
    REWRITE_TAC[LENGTH] THEN UNDISCH_TAC `~(t:(real)list = [])` THEN
    REWRITE_TAC[GSYM LENGTH_EQ_NIL] THEN ARITH_TAC;
    DISCH_THEN SUBST1_TAC] THEN
  SUBGOAL_THEN `exists m. n = SUC m` STRIP_ASSUME_TAC THENL
   [EXISTS_TAC `n - 1` THEN
    UNDISCH_TAC `LENGTH (CONS (h:real) t) <= n + 1` THEN
    REWRITE_TAC[LENGTH] THEN UNDISCH_TAC `~(t:(real)list = [])` THEN
    REWRITE_TAC[GSYM LENGTH_EQ_NIL] THEN ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[SUC_SUB1; real_pow] THEN UNDISCH_TAC `~(d + d * t' = &0)` THEN
  CONV_TAC REAL_FIELD);;

let rp_cert_poly_mob = new_definition
 `rp_cert_poly_mob b c p =
    rp_cert_poly_mobr b c (&1) p (LENGTH p - 1)`;;

let RP_CERT_POLY_EVAL_MOB = prove
 (`forall b c p t. ~(&1 + t = &0)
     ==> rp_cert_peval (rp_cert_poly_mob b c p) t =
         (&1 + t) pow (LENGTH p - 1) * rp_cert_peval p ((b + c * t) / (&1 + t))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[rp_cert_poly_mob] THEN
  MP_TAC(SPECL [`p:(real)list`; `LENGTH(p:(real)list) - 1`; `b:real`; `c:real`; `&1`; `t:real`]
    RP_CERT_POLY_EVAL_MOBR) THEN
  ASM_REWRITE_TAC[REAL_MUL_LID] THEN ANTS_TAC THENL [ARITH_TAC; SIMP_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Sign variations.                                                          *)
(* ------------------------------------------------------------------------- *)

let rp_cert_poly_fnz = define
 `(rp_cert_poly_fnz [] = &0) /\
  (rp_cert_poly_fnz (CONS a p) = if a = &0 then rp_cert_poly_fnz p else a)`;;

let rp_cert_poly_var = define
 `(rp_cert_poly_var [] = 0) /\
  (rp_cert_poly_var (CONS a p) =
     (if (a < &0 /\ &0 < rp_cert_poly_fnz p) \/ (&0 < a /\ rp_cert_poly_fnz p < &0)
      then 1 else 0) + rp_cert_poly_var p)`;;

let RP_CERT_POLY_ALLZERO_EVAL = prove
 (`forall p x. ALL (\a. a = &0) p ==> rp_cert_peval p x = &0`,
  LIST_INDUCT_TAC THEN ASM_SIMP_TAC[ALL; rp_cert_peval] THEN REAL_ARITH_TAC);;

let RP_CERT_POLY_FNZ_NZ = prove
 (`forall p. ~(ALL (\a. a = &0) p) ==> ~(rp_cert_poly_fnz p = &0)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[ALL; rp_cert_poly_fnz] THEN
  COND_CASES_TAC THEN ASM_SIMP_TAC[]);;

let RP_CERT_POLY_SWAP3 = prove
 (`forall s x p:real. s * x * p = x * (s * p)`, REPEAT GEN_TAC THEN CONV_TAC REAL_RING);;

let RP_CERT_POLY_SGN_TAC =
  REWRITE_TAC[real_sgn] THEN REPEAT COND_CASES_TAC THEN ASM_REAL_ARITH_TAC;;

(* var 0: constant strict sign, nondecreasing on t >= 0 after multiplying
   by the sign of the first nonzero coefficient *)
let RP_CERT_POLY_VAR0_LEMMA = prove
 (`forall p. ~(ALL (\a. a = &0) p) /\ rp_cert_poly_var p = 0
       ==> (forall x. &0 < x ==> &0 < real_sgn(rp_cert_poly_fnz p) * rp_cert_peval p x) /\
           (forall x. &0 <= x ==> &0 <= real_sgn(rp_cert_poly_fnz p) * rp_cert_peval p x) /\
           (forall s x. &0 <= s /\ s <= x
                  ==> real_sgn(rp_cert_poly_fnz p) * rp_cert_peval p s <=
                      real_sgn(rp_cert_poly_fnz p) * rp_cert_peval p x)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[ALL] THEN
  REWRITE_TAC[rp_cert_poly_var; rp_cert_poly_fnz; rp_cert_peval; ADD_EQ_0] THEN
  ASM_CASES_TAC `ALL (\a. a = &0) (t:(real)list)` THENL
   [ASM_SIMP_TAC[RP_CERT_POLY_ALLZERO_EVAL] THEN
    REWRITE_TAC[REAL_MUL_RZERO; REAL_ADD_RID] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[REAL_LE_REFL] THEN RP_CERT_POLY_SGN_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `~(rp_cert_poly_fnz t = &0)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[RP_CERT_POLY_FNZ_NZ]; ALL_TAC] THEN
  SUBGOAL_THEN `real_sgn(if h = &0 then rp_cert_poly_fnz t else h) =
                real_sgn(rp_cert_poly_fnz t) /\
                &0 <= real_sgn(rp_cert_poly_fnz t) * h` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(if (h < &0 /\ &0 < rp_cert_poly_fnz t) \/ (&0 < h /\ rp_cert_poly_fnz t < &0)
                  then 1 else 0) = 0` THEN
    COND_CASES_TAC THEN REWRITE_TAC[ARITH_EQ] THEN POP_ASSUM MP_TAC THEN
    UNDISCH_TAC `~(rp_cert_poly_fnz t = &0)` THEN
    COND_CASES_TAC THEN RP_CERT_POLY_SGN_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[REAL_ADD_LDISTRIB] THEN
  ONCE_REWRITE_TAC[RP_CERT_POLY_SWAP3] THEN REPEAT CONJ_TAC THENL
   [X_GEN_TAC `x:real` THEN DISCH_TAC THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= a /\ &0 < b ==> &0 < a + b`) THEN
    ASM_SIMP_TAC[REAL_LT_MUL];
    X_GEN_TAC `x:real` THEN DISCH_TAC THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= a /\ &0 <= b ==> &0 <= a + b`) THEN
    ASM_SIMP_TAC[REAL_LE_MUL];
    MAP_EVERY X_GEN_TAC [`s:real`; `x:real`] THEN STRIP_TAC THEN
    MATCH_MP_TAC(REAL_ARITH `a <= b ==> h + a <= h + b`) THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_SIMP_TAC[]]);;

let RP_CERT_POLY_NOROOT_POS = prove
 (`forall p x. ~(ALL (\a. a = &0) p) /\ rp_cert_poly_var p = 0 /\ &0 < x
         ==> ~(rp_cert_peval p x = &0)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `p:(real)list` RP_CERT_POLY_VAR0_LEMMA) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `x:real` o CONJUNCT1) THEN
  ASM_REWRITE_TAC[REAL_MUL_RZERO; REAL_LT_REFL]);;



let RP_CERT_POLY_VAR1_LEMMA = rp_cert_steps
 `forall p. ~(ALL (\a. a = &0) p) /\ rp_cert_poly_var p <= 1
       ==> forall s x. &0 < s /\ s < x /\
                 real_sgn(rp_cert_poly_fnz p) * rp_cert_peval p s <= &0
                 ==> real_sgn(rp_cert_poly_fnz p) * rp_cert_peval p x < &0 /\
                     real_sgn(rp_cert_poly_fnz p) * rp_cert_peval p x <=
                     real_sgn(rp_cert_poly_fnz p) * rp_cert_peval p s`
 [(LIST_INDUCT_TAC THEN REWRITE_TAC[ALL] THEN
  REWRITE_TAC[rp_cert_poly_var; rp_cert_poly_fnz; rp_cert_peval] THEN
  ASM_CASES_TAC `ALL (\a. a = &0) (t:(real)list)`);
  (ASM_SIMP_TAC[RP_CERT_POLY_ALLZERO_EVAL] THEN
    REWRITE_TAC[REAL_MUL_RZERO; REAL_ADD_RID] THEN
    REPEAT STRIP_TAC THEN REWRITE_TAC[REAL_LE_REFL] THEN POP_ASSUM MP_TAC THEN UNDISCH_TAC `~(h = &0)` THEN RP_CERT_POLY_SGN_TAC);
  (ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(rp_cert_poly_fnz t = &0)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[RP_CERT_POLY_FNZ_NZ]; ALL_TAC] THEN
  REWRITE_TAC[REAL_ADD_LDISTRIB] THEN ONCE_REWRITE_TAC[RP_CERT_POLY_SWAP3] THEN
  ASM_CASES_TAC `(h < &0 /\ &0 < rp_cert_poly_fnz t) \/ (&0 < h /\ rp_cert_poly_fnz t < &0)`);
  (SUBGOAL_THEN `rp_cert_poly_var t = 0` ASSUME_TAC THENL
     [UNDISCH_TAC `(if (h < &0 /\ &0 < rp_cert_poly_fnz t) \/ (&0 < h /\ rp_cert_poly_fnz t < &0)
                    then 1 else 0) + rp_cert_poly_var t <= 1` THEN
      ASM_REWRITE_TAC[] THEN ARITH_TAC; ALL_TAC] THEN
    MP_TAC(SPEC `t:(real)list` RP_CERT_POLY_VAR0_LEMMA) THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `~(h = &0) /\ real_sgn h = --real_sgn(rp_cert_poly_fnz t)`
      STRIP_ASSUME_TAC THENL
     [FIRST_X_ASSUM(DISJ_CASES_TAC o check (is_disj o concl)) THEN
      CONJ_TAC THEN TRY(ASM_REAL_ARITH_TAC) THEN RP_CERT_POLY_SGN_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    MAP_EVERY X_GEN_TAC [`s:real`; `x:real`] THEN STRIP_TAC);
  (SUBGOAL_THEN `s * (real_sgn(rp_cert_poly_fnz t) * rp_cert_peval t s) <
                  x * (real_sgn(rp_cert_poly_fnz t) * rp_cert_peval t x)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LTE_TRANS THEN
      EXISTS_TAC `x * (real_sgn(rp_cert_poly_fnz t) * rp_cert_peval t s)` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LT_RMUL THEN ASM_SIMP_TAC[];
        MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
         [ASM_REAL_ARITH_TAC; FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC]];
      ALL_TAC] THEN
    UNDISCH_TAC `--real_sgn (rp_cert_poly_fnz t) * h +
       s * --real_sgn (rp_cert_poly_fnz t) * rp_cert_peval t s <= &0` THEN
    REWRITE_TAC[REAL_MUL_LNEG; REAL_MUL_RNEG] THEN REAL_ARITH_TAC);
  (SUBGOAL_THEN `real_sgn(if h = &0 then rp_cert_poly_fnz t else h) =
                real_sgn(rp_cert_poly_fnz t) /\
                &0 <= real_sgn(rp_cert_poly_fnz t) * h /\ rp_cert_poly_var t <= 1`
    STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(if (h < &0 /\ &0 < rp_cert_poly_fnz t) \/ (&0 < h /\ rp_cert_poly_fnz t < &0)
                  then 1 else 0) + rp_cert_poly_var t <= 1` THEN
    ASM_REWRITE_TAC[ADD_CLAUSES] THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `~((h < &0 /\ &0 < rp_cert_poly_fnz t) \/ (&0 < h /\ rp_cert_poly_fnz t < &0))` THEN
    UNDISCH_TAC `~(rp_cert_poly_fnz t = &0)` THEN
    COND_CASES_TAC THEN RP_CERT_POLY_SGN_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN MAP_EVERY X_GEN_TAC [`s:real`; `x:real`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `real_sgn(rp_cert_poly_fnz t) * rp_cert_peval t s <= &0` ASSUME_TAC THENL
   [MATCH_MP_TAC(MESON[REAL_LE_LMUL_EQ; REAL_MUL_RZERO]
      `forall s a. &0 < s /\ s * a <= &0 ==> a <= &0`) THEN
    EXISTS_TAC `s:real` THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`s:real`; `x:real`]) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `s * --(real_sgn(rp_cert_poly_fnz t) * rp_cert_peval t x) <
                x * --(real_sgn(rp_cert_poly_fnz t) * rp_cert_peval t x) /\
                s * (real_sgn(rp_cert_poly_fnz t) * rp_cert_peval t x) <=
                s * (real_sgn(rp_cert_poly_fnz t) * rp_cert_peval t s)` MP_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_RMUL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC];
    REWRITE_TAC[REAL_MUL_RNEG] THEN ASM_REAL_ARITH_TAC])];;

let RP_CERT_POLY_ONEROOT_POS = prove
 (`forall q s x. ~(ALL (\a. a = &0) q) /\ rp_cert_poly_var q <= 1 /\
           &0 < s /\ s < x /\ rp_cert_peval q s = &0 /\ rp_cert_peval q x = &0
           ==> false`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `q:(real)list` RP_CERT_POLY_VAR1_LEMMA) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`s:real`; `x:real`]) THEN
  ASM_REWRITE_TAC[REAL_MUL_RZERO; REAL_LE_REFL; REAL_LT_REFL]);;

let RP_CERT_POLY_MOB_ALG1 = prove
 (`forall b c d x. ~(c - d * x = &0)
     ==> d + d * ((d * x - b) / (c - d * x)) = (d * (c - b)) / (c - d * x)`,
  REPEAT GEN_TAC THEN CONV_TAC REAL_FIELD);;

let RP_CERT_POLY_MOB_ALG2 = prove
 (`forall b c d x. ~(c - d * x = &0) /\ ~(d = &0) /\ ~(c - b = &0)
     ==> (b + c * ((d * x - b) / (c - d * x))) / ((d * (c - b)) / (c - d * x)) = x`,
  REPEAT GEN_TAC THEN CONV_TAC REAL_FIELD);;

let RP_CERT_POLY_MOB_SUBST = prove
 (`forall (B:real) (C:real) (D:real) (x:real). &0 < D /\ B < C /\ B / D < x /\ x < C / D
     ==> &0 < (D * x - B) / (C - D * x) /\
         ~(D + D * ((D * x - B) / (C - D * x)) = &0) /\
         (B + C * ((D * x - B) / (C - D * x))) / (D + D * ((D * x - B) / (C - D * x))) = x`,
  REPEAT GEN_TAC THEN DISCH_THEN STRIP_ASSUME_TAC THEN
  SUBGOAL_THEN `(B:real) < D * x /\ D * (x:real) < C` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[REAL_LT_LDIV_EQ; REAL_LT_RDIV_EQ; REAL_MUL_SYM]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < (C:real) - D * x /\ &0 < (D:real) * (x:real) - B` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [ASM_SIMP_TAC[REAL_LT_DIV]; ALL_TAC] THEN
  SUBGOAL_THEN `(D:real) + D * ((D * (x:real) - B) / (C - D * x)) = (D * (C - B)) / (C - D * x)`
    SUBST1_TAC THENL
   [MATCH_MP_TAC RP_CERT_POLY_MOB_ALG1 THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LT_IMP_NZ THEN
    MATCH_MP_TAC REAL_LT_DIV THEN ASM_SIMP_TAC[REAL_LT_MUL; REAL_SUB_LT];
    MATCH_MP_TAC RP_CERT_POLY_MOB_ALG2 THEN ASM_REAL_ARITH_TAC]);;

let RP_CERT_POLY_MOB_MONO = prove
 (`forall (B:real) (C:real) (D:real) (x:real) (y:real). &0 < D /\ B / D < x /\ x < y /\ y < C / D
     ==> (D * x - B) / (C - D * x) < (D * y - B) / (C - D * y)`,
  REPEAT GEN_TAC THEN DISCH_THEN STRIP_ASSUME_TAC THEN
  SUBGOAL_THEN `(B:real) < D * (x:real) /\ D * (y:real) < C` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[REAL_LT_LDIV_EQ; REAL_LT_RDIV_EQ; REAL_MUL_SYM]; ALL_TAC] THEN
  SUBGOAL_THEN `(D:real) * (x:real) < D * y` ASSUME_TAC THENL [ASM_SIMP_TAC[REAL_LT_LMUL]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < (C:real) - D * (x:real) /\ &0 < C - D * (y:real)` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LT_DIV2_EQ; REAL_LT_LDIV_EQ; REAL_LT_RDIV_EQ] THEN
  ONCE_REWRITE_TAC[REAL_ARITH `a / b * c:real = (a * c) / b`] THEN
  ASM_SIMP_TAC[REAL_LT_RDIV_EQ] THEN
  REWRITE_TAC[REAL_ARITH `(D * x - B) * (C - D * y) < (D * y - B) * (C - D * x) <=>
                          &0 < (C - B) * (D * y - D * x)`] THEN
  MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC);;

let RP_CERT_POLY_ONEROOT = prove
 (`forall p (b:real) (c:real) (d:real) n.
     &0 < d /\ b < c /\ LENGTH p <= n + 1 /\
     ~(ALL (\a. a = &0) (rp_cert_poly_mobr b c d p n)) /\
     rp_cert_poly_var (rp_cert_poly_mobr b c d p n) <= 1
     ==> forall x y. b / d < x /\ x < y /\ y < c / d /\
               rp_cert_peval p x = &0 /\ rp_cert_peval p y = &0 ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC RP_CERT_POLY_ONEROOT_POS THEN
  EXISTS_TAC `rp_cert_poly_mobr b c d p n` THEN
  EXISTS_TAC `(d * x - b) / (c - d * x:real)` THEN
  EXISTS_TAC `(d * y - b) / (c - d * y:real)` THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`b:real`; `c:real`; `d:real`; `x:real`] RP_CERT_POLY_MOB_SUBST) THEN
  MP_TAC(SPECL [`b:real`; `c:real`; `d:real`; `y:real`] RP_CERT_POLY_MOB_SUBST) THEN
  MP_TAC(SPECL [`b:real`; `c:real`; `d:real`; `x:real`; `y:real`] RP_CERT_POLY_MOB_MONO) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `b / d < y /\ x < c / d` (fun th -> REWRITE_TAC[th]) THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[RP_CERT_POLY_EVAL_MOBR; REAL_MUL_RZERO]);;

let RP_CERT_POLY_NOROOT = prove
 (`forall p (b:real) (c:real) (d:real) n.
     &0 < d /\ b < c /\ LENGTH p <= n + 1 /\
     ~(ALL (\a. a = &0) (rp_cert_poly_mobr b c d p n)) /\
     rp_cert_poly_var (rp_cert_poly_mobr b c d p n) = 0
     ==> forall x. b / d < x /\ x < c / d ==> ~(rp_cert_peval p x = &0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`rp_cert_poly_mobr b c d p n`; `(d * x - b) / (c - d * x:real)`]
    RP_CERT_POLY_NOROOT_POS) THEN
  MP_TAC(SPECL [`b:real`; `c:real`; `d:real`; `x:real`] RP_CERT_POLY_MOB_SUBST) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[RP_CERT_POLY_EVAL_MOBR; REAL_MUL_RZERO]);;

(* ------------------------------------------------------------------------- *)
(* Continuity, IVT, Lipschitz.                                               *)
(* ------------------------------------------------------------------------- *)

let RP_CERT_POLY_CONTINUOUS = prove
 (`forall p x. (\x. rp_cert_peval p x) real_continuous atreal x`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[rp_cert_peval; REAL_CONTINUOUS_CONST] THEN
  GEN_TAC THEN MATCH_MP_TAC REAL_CONTINUOUS_ADD THEN
  REWRITE_TAC[REAL_CONTINUOUS_CONST] THEN MATCH_MP_TAC REAL_CONTINUOUS_MUL THEN
  ASM_REWRITE_TAC[REAL_CONTINUOUS_AT_ID]);;

let RP_CERT_POLY_CONTINUOUS_ON = prove
 (`forall p s. (\x. rp_cert_peval p x) real_continuous_on s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[REAL_CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_CONTINUOUS_ATREAL_WITHINREAL THEN
  REWRITE_TAC[RP_CERT_POLY_CONTINUOUS]);;

let RP_CERT_POLY_PROD_SIGN = prove
 (`forall u v:real. u * v <= &0 ==> (u <= &0 /\ &0 <= v) \/ (&0 <= u /\ v <= &0)`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN
  REWRITE_TAC[DE_MORGAN_THM; REAL_NOT_LE] THEN STRIP_TAC THEN
  TRY(MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC) THEN
  ONCE_REWRITE_TAC[GSYM REAL_NEG_MUL2] THEN MATCH_MP_TAC REAL_LT_MUL THEN
  ASM_REAL_ARITH_TAC);;

let RP_CERT_POLY_IVT = prove
 (`forall p a b. a <= b /\ rp_cert_peval p a * rp_cert_peval p b <= &0
           ==> exists x. a <= x /\ x <= b /\ rp_cert_peval p x = &0`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
    (DISJ_CASES_TAC o MATCH_MP RP_CERT_POLY_PROD_SIGN)) THENL
   [MP_TAC(ISPECL [`\x. rp_cert_peval p x`; `a:real`; `b:real`; `&0`]
      REAL_IVT_INCREASING);
    MP_TAC(ISPECL [`\x. rp_cert_peval p x`; `a:real`; `b:real`; `&0`]
      REAL_IVT_DECREASING)] THEN
  ASM_REWRITE_TAC[RP_CERT_POLY_CONTINUOUS_ON; IN_REAL_INTERVAL] THEN MESON_TAC[]);;

let rp_cert_poly_asum = define
 `(rp_cert_poly_asum [] = &0) /\
  (rp_cert_poly_asum (CONS (a:real) p) = abs a + rp_cert_poly_asum p)`;;

let rp_cert_poly_dnorm = define
 `(rp_cert_poly_dnorm [] = &0) /\
  (rp_cert_poly_dnorm (CONS (a:real) p) = rp_cert_poly_dnorm p + rp_cert_poly_asum p)`;;

let RP_CERT_POLY_ASUM_BOUND = prove
 (`forall p x. abs x <= &1 ==> abs(rp_cert_peval p x) <= rp_cert_poly_asum p`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[rp_cert_peval; rp_cert_poly_asum; REAL_ABS_0; REAL_LE_REFL] THEN
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(REAL_ARITH `forall a b c:real. abs(c) <= b ==> abs(a + c) <= abs a + b`) THEN
  REWRITE_TAC[REAL_ABS_MUL] THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
  MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_SIMP_TAC[REAL_ABS_POS]);;

let RP_CERT_POLY_LIPSCHITZ = prove
 (`forall p x y. abs x <= &1 /\ abs y <= &1
           ==> abs(rp_cert_peval p x - rp_cert_peval p y) <=
               rp_cert_poly_dnorm p * abs(x - y)`,
  LIST_INDUCT_TAC THEN
  REWRITE_TAC[rp_cert_peval; rp_cert_poly_dnorm; REAL_SUB_REFL; REAL_ABS_0;
              REAL_MUL_LZERO; REAL_LE_REFL] THEN
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[REAL_RING `(a + x * p) - (a + y * q):real = x * (p - q) + (x - y) * q`] THEN
  REWRITE_TAC[REAL_ADD_RDISTRIB] THEN
  MATCH_MP_TAC(REAL_ARITH `forall a b u v:real. abs a <= u /\ abs b <= v ==> abs(a + b) <= u + v`) THEN
  REWRITE_TAC[REAL_ABS_MUL] THEN CONJ_TAC THENL
   [GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_SIMP_TAC[REAL_ABS_POS];
    GEN_REWRITE_TAC RAND_CONV [REAL_MUL_SYM] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    ASM_SIMP_TAC[REAL_ABS_POS; RP_CERT_POLY_ASUM_BOUND]]);;

(* ------------------------------------------------------------------------- *)
(* Conversions on explicit lists of rational numerals.                       *)
(* ------------------------------------------------------------------------- *)

let rp_cert_poly_numconv = REAL_RAT_REDUCE_CONV;;

(* apply cv to every element of an explicit list *)
let rec rp_cert_poly_elems_conv cv tm =
  if is_comb tm && is_comb(rator tm) && fst(dest_const(rator(rator tm))) = "CONS" then
    COMB2_CONV (RAND_CONV cv) (rp_cert_poly_elems_conv cv) tm
  else REFL tm;;

let RP_CERT_POLY_ADD_CLAUSES = prove
 (`(forall q. rp_cert_poly_add [] q = q) /\
   (forall a p. rp_cert_poly_add (CONS (a:real) p) [] = CONS a p) /\
   (forall a b p q. rp_cert_poly_add (CONS (a:real) p) (CONS b q) =
              CONS (a + b) (rp_cert_poly_add p q))`,
  REWRITE_TAC[rp_cert_poly_add]);;

let RP_CERT_POLY_CMUL_CLAUSES = prove
 (`(forall c. rp_cert_poly_cmul (c:real) [] = []) /\
   (forall c a p. rp_cert_poly_cmul (c:real) (CONS a p) = CONS (c * a) (rp_cert_poly_cmul c p))`,
  REWRITE_TAC[rp_cert_poly_cmul]);;

let rp_cert_poly_add_conv =
  let [c1;c2;c3] = CONJUNCTS RP_CERT_POLY_ADD_CLAUSES in
  let rec raw tm =
    (REWR_CONV c1 ORELSEC REWR_CONV c2 ORELSEC
     (REWR_CONV c3 THENC RAND_CONV raw)) tm in
  fun tm -> (raw THENC rp_cert_poly_elems_conv rp_cert_poly_numconv) tm;;

(* rp_cert_poly_add with all elements already numerals is done elementwise;
   the conversion above re-reduces all elements, which is cheap for numerals *)

let rp_cert_poly_cmul_conv =
  let [c1;c2] = CONJUNCTS RP_CERT_POLY_CMUL_CLAUSES in
  let rec raw tm = (REWR_CONV c1 ORELSEC (REWR_CONV c2 THENC RAND_CONV raw)) tm in
  fun tm -> (raw THENC rp_cert_poly_elems_conv rp_cert_poly_numconv) tm;;

let RP_CERT_POLY_MUL_CLAUSES = prove
 (`(forall q. rp_cert_poly_mul [] q = []) /\
   (forall a p q. rp_cert_poly_mul (CONS (a:real) p) q =
     rp_cert_poly_add (rp_cert_poly_cmul a q) (CONS (&0) (rp_cert_poly_mul p q)))`,
  REWRITE_TAC[rp_cert_poly_mul]);;

let rec rp_cert_poly_mul_conv tm =
  let [c1;c2] = CONJUNCTS RP_CERT_POLY_MUL_CLAUSES in
  (REWR_CONV c1 ORELSEC
   (REWR_CONV c2 THENC
    COMB2_CONV (RAND_CONV rp_cert_poly_cmul_conv)
               (RAND_CONV rp_cert_poly_mul_conv) THENC
    rp_cert_poly_add_conv)) tm;;

(* general evaluator of closed list expressions *)
let rec rp_cert_poly_list_conv tm =
  match strip_comb tm with
    (Const("rp_cert_poly_add",_),[_;_]) ->
       (BINOP_CONV rp_cert_poly_list_conv THENC rp_cert_poly_add_conv) tm
  | (Const("rp_cert_poly_cmul",_),[_;_]) ->
       (RAND_CONV rp_cert_poly_list_conv THENC rp_cert_poly_cmul_conv) tm
  | (Const("rp_cert_poly_mul",_),[_;_]) ->
       (BINOP_CONV rp_cert_poly_list_conv THENC rp_cert_poly_mul_conv) tm
  | (Const("CONS",_),[_;_]) ->
       (RAND_CONV rp_cert_poly_list_conv THENC
        RATOR_CONV(RAND_CONV rp_cert_poly_numconv)) tm
  | _ -> REFL tm;;

(* powers (d + d t)^n, cached *)
let rp_cert_poly_pw_cache = ref ([] : ((term * int) * thm) list);;

let RP_CERT_POLY_PW_CLAUSES = prove
 (`(forall d. rp_cert_poly_pw d 0 = [&1]) /\
   (forall d n. rp_cert_poly_pw d (SUC n) = rp_cert_poly_mul [d; d] (rp_cert_poly_pw d n))`,
  REWRITE_TAC[rp_cert_poly_pw]);;

let rec rp_cert_poly_pw_thm d n =
  try assoc (d,n) !rp_cert_poly_pw_cache with Failure _ ->
  let th =
    if n = 0 then ISPEC d (CONJUNCT1 RP_CERT_POLY_PW_CLAUSES) else
    let th0 = rp_cert_poly_pw_thm d (n - 1) in
    let tm = mk_comb(mk_comb(`rp_cert_poly_pw`, d), mk_small_numeral n) in
    let eqn = (RAND_CONV num_CONV THENC REWR_CONV (CONJUNCT2 RP_CERT_POLY_PW_CLAUSES) THENC
               RAND_CONV(REWR_CONV th0) THENC rp_cert_poly_mul_conv) tm in
    eqn in
  rp_cert_poly_pw_cache := ((d,n),th) :: !rp_cert_poly_pw_cache; th;;

let RP_CERT_POLY_MOBR_CLAUSES = prove
 (`(forall b c d n. rp_cert_poly_mobr b c d [] n = []) /\
   (forall b c d a p n. rp_cert_poly_mobr b c d (CONS (a:real) p) n =
     rp_cert_poly_add (rp_cert_poly_cmul a (rp_cert_poly_pw d n))
                      (rp_cert_poly_mul [b; c] (rp_cert_poly_mobr b c d p (n - 1))))`,
  REWRITE_TAC[rp_cert_poly_mobr]);;

let rec rp_cert_poly_mobr_conv tm =
  let [c1;c2] = CONJUNCTS RP_CERT_POLY_MOBR_CLAUSES in
  match strip_comb tm with
    (_,[b;c;d;l;n]) ->
      if l = `[]:real list` then REWR_CONV c1 tm else
      let k = dest_small_numeral n in
      (REWR_CONV c2 THENC
       COMB2_CONV
         (RAND_CONV (COMB2_CONV (RAND_CONV REFL)
             (fun t -> rp_cert_poly_pw_thm d k) THENC rp_cert_poly_cmul_conv))
         (RAND_CONV (RAND_CONV NUM_SUB_CONV THENC rp_cert_poly_mobr_conv) THENC
          rp_cert_poly_mul_conv) THENC
       rp_cert_poly_add_conv) tm
  | _ -> failwith "rp_cert_poly_mobr_conv";;

let RP_CERT_POLY_FNZ_CLAUSES = prove
 (`(rp_cert_poly_fnz [] = &0) /\
   (forall a p. rp_cert_poly_fnz (CONS a p) = if a = &0 then rp_cert_poly_fnz p else a)`,
  REWRITE_TAC[rp_cert_poly_fnz]);;

let RP_CERT_POLY_VAR_CLAUSES = prove
 (`(rp_cert_poly_var [] = 0) /\
   (forall a p. rp_cert_poly_var (CONS a p) =
     (if (a < &0 /\ &0 < rp_cert_poly_fnz p) \/ (&0 < a /\ rp_cert_poly_fnz p < &0)
      then 1 else 0) + rp_cert_poly_var p)`,
  REWRITE_TAC[rp_cert_poly_var]);;

(* sign variation count and first nonzero: evaluate by rewriting with
   rational comparisons *)
let rp_cert_poly_var_conv tm =
  (REWRITE_CONV[RP_CERT_POLY_VAR_CLAUSES; RP_CERT_POLY_FNZ_CLAUSES] THENC
   DEPTH_CONV REAL_RAT_EQ_CONV THENC REWRITE_CONV[] THENC
   DEPTH_CONV REAL_RAT_LT_CONV THENC REWRITE_CONV[] THENC NUM_REDUCE_CONV) tm;;

let rp_cert_poly_allzero_conv tm =
  (REWRITE_CONV[ALL] THENC DEPTH_CONV BETA_CONV THENC DEPTH_CONV REAL_RAT_EQ_CONV THENC
   REWRITE_CONV[]) tm;;

let rp_cert_poly_eval_conv tm =
  (REWRITE_CONV[rp_cert_peval] THENC REAL_RAT_REDUCE_CONV) tm;;

(* integer Horner evaluation at m / d:  d^(LENGTH p - 1) * p(m/d) *)
let rp_cert_poly_hz = define
 `(rp_cert_poly_hz [] (m:real) (d:real) = &0) /\
  (rp_cert_poly_hz (CONS a p) m d = a * d pow (LENGTH p) + m * rp_cert_poly_hz p m d)`;;

let RP_CERT_POLY_HZ = prove
 (`forall p m d. ~(d = &0)
     ==> rp_cert_poly_hz p m d = d pow (LENGTH p - 1) * rp_cert_peval p (m / d)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[rp_cert_poly_hz; rp_cert_peval; REAL_MUL_RZERO] THEN
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[] THEN
  ASM_CASES_TAC `t:(real)list = []` THENL
   [ASM_REWRITE_TAC[LENGTH; rp_cert_poly_hz; rp_cert_peval; real_pow] THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[real_pow] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `exists k. LENGTH(t:(real)list) = SUC k` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[LENGTH_EQ_NIL; num_CASES]; ALL_TAC] THEN
  ASM_REWRITE_TAC[LENGTH; SUC_SUB1; real_pow] THEN
  UNDISCH_TAC `~(d = &0)` THEN CONV_TAC REAL_FIELD);;

let RP_CERT_POLY_HZ_CLAUSES = prove
 (`(forall m d. rp_cert_poly_hz [] (m:real) (d:real) = &0) /\
   (forall a p m d. rp_cert_poly_hz (CONS a p) m d = a * d pow (LENGTH p) + m * rp_cert_poly_hz p m d)`,
  REWRITE_TAC[rp_cert_poly_hz]);;

let rp_cert_poly_dpow_cache = ref ([] : ((term * int) * thm) list);;
let rec rp_cert_poly_dpow d k =
  try assoc (d,k) !rp_cert_poly_dpow_cache with Failure _ ->
  let tm = mk_binop `(pow):real->num->real` d (mk_small_numeral k) in
  let th = if k = 0 then REWRITE_CONV[real_pow] tm else
    let th0 = rp_cert_poly_dpow d (k-1) in
    (RAND_CONV num_CONV THENC REWR_CONV (CONJUNCT2 real_pow) THENC
     RAND_CONV (REWR_CONV th0) THENC REAL_RAT_MUL_CONV) tm in
  rp_cert_poly_dpow_cache := ((d,k),th) :: !rp_cert_poly_dpow_cache; th;;

(* |- rp_cert_poly_hz [explicit] m d = n *)
let rec rp_cert_poly_hz_conv tm =
  let [c1;c2] = CONJUNCTS RP_CERT_POLY_HZ_CLAUSES in
  match strip_comb tm with
    (_,[l;m;d]) ->
      if l = `[]:real list` then REWR_CONV c1 tm else
      let k = length(dest_list(rand l)) in
      (REWR_CONV c2 THENC
       COMB2_CONV (RAND_CONV (RAND_CONV (RAND_CONV LENGTH_CONV THENC
                   (fun t -> rp_cert_poly_dpow d k)) THENC REAL_RAT_MUL_CONV))
                  (RAND_CONV rp_cert_poly_hz_conv THENC REAL_RAT_MUL_CONV) THENC
       REAL_RAT_ADD_CONV) tm
  | _ -> failwith "rp_cert_poly_hz_conv";;

(* sign of p at m/d (d > 0 numeral):  |- &0 < rp_cert_peval p (m / d)  or
   |- rp_cert_peval p (m / d) < &0 *)
let RP_CERT_POLY_HZ_SIGN = prove
 (`forall p m d. &0 < d
     ==> (&0 < rp_cert_poly_hz p m d ==> &0 < rp_cert_peval p (m / d)) /\
         (rp_cert_poly_hz p m d < &0 ==> rp_cert_peval p (m / d) < &0)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  ASM_SIMP_TAC[RP_CERT_POLY_HZ; REAL_LT_IMP_NZ] THEN
  SUBGOAL_THEN `&0 < (d:real) pow (LENGTH (p:real list) - 1)` MP_TAC THENL
   [ASM_SIMP_TAC[REAL_POW_LT]; ALL_TAC] THEN
  SPEC_TAC(`(d:real) pow (LENGTH (p:real list) - 1)`,`e:real`) THEN
  SPEC_TAC(`rp_cert_peval p ((m:real) / (d:real))`,`v:real`) THEN
  MESON_TAC[REAL_LT_LMUL_EQ; REAL_MUL_RZERO]);;

let rp_cert_poly_sign_at p m d =
  let th = rp_cert_poly_hz_conv (list_mk_comb(`rp_cert_poly_hz`,[p;m;d])) in
  let v = rand(concl th) in
  let dpos = EQT_ELIM(REAL_RAT_LT_CONV(mk_binop `(<):real->real->bool` `&0` d)) in
  let sth = MATCH_MP (ISPECL [p;m;d] RP_CERT_POLY_HZ_SIGN) dpos in
  try let pos = EQT_ELIM(REAL_RAT_LT_CONV(mk_binop `(<):real->real->bool` `&0` v)) in
      MP (CONJUNCT1 sth) (EQ_MP (SYM(AP_TERM `(<) (&0)` th)) pos)
  with Failure _ ->
      let neg = EQT_ELIM(REAL_RAT_LT_CONV(mk_binop `(<):real->real->bool` v `&0`)) in
      MP (CONJUNCT2 sth) (EQ_MP (SYM(AP_THM (AP_TERM `(<):real->real->bool` th) `&0`)) neg);;

let RP_CERT_POLY_ASUM_POS = prove
 (`forall p. &0 <= rp_cert_poly_asum p`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[rp_cert_poly_asum; REAL_LE_REFL] THEN
  ASM_SIMP_TAC[REAL_LE_ADD; REAL_ABS_POS]);;

let RP_CERT_POLY_DNORM_POS = prove
 (`forall p. &0 <= rp_cert_poly_dnorm p`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[rp_cert_poly_dnorm; REAL_LE_REFL] THEN
  ASM_SIMP_TAC[REAL_LE_ADD; RP_CERT_POLY_ASUM_POS]);;
