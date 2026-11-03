(* ========================================================================= *)
(* rp_alg: Cauchy's double alternant in multiplicative variables,           *)
(*   det[1/(1 - t_i s_j)] = V(t) V(s) / prod_{i,j} (1 - t_i s_j).           *)
(* ========================================================================= *)

needs "src/catalan_rp_alg_det.ml";;

let RP_ALG_CAUCHY_MUL = prove
 (`forall n t s.
     (forall i j. i < n /\ j < n ==> ~(&1 - t i * s j = &0))
     ==> ndet {i:num | i < n} (\i j. inv(&1 - t i * s j)) *
         product {i:num | i < n} (\i. product {j:num | j < n} (\j. &1 - t i * s j)) =
         rp_vdm n t * rp_vdm n s`,
  INDUCT_TAC THENL
   [REWRITE_TAC[RP_ALG_NDET_EMPTY] THEN
    REWRITE_TAC[rp_vdm; LT; EMPTY_GSPEC; PRODUCT_CLAUSES] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`t:num->real`; `s:num->real`]) THEN
  ANTS_TAC THENL
   [ASM_MESON_TAC[ARITH_RULE `i < n ==> i < SUC n`]; DISCH_TAC] THEN
  (* Step 1: row operations, factor rows and columns *)
  SUBGOAL_THEN
   `ndet {i:num | i < SUC n} (\i j. inv(&1 - t i * s j)) =
    product {i:num | i < n} (\i. t i - t n) *
    (ndet {i:num | i < SUC n}
       (\i j. if i < n then s j * inv(&1 - t i * s j) else &1) *
     product {i:num | i < SUC n} (\j. inv(&1 - t n * s j)))`
  SUBST1_TAC THENL
   [MP_TAC(ISPECL [`{i:num | i < SUC n}`; `\i j. inv(&1 - (t:num->real) i * (s:num->real) j)`; `n:num`;
                   `\i:num. --(&1)`; `{i:num | i < n}`]
                  RP_ALG_NDET_ROWS_OPERATION) THEN
    REWRITE_TAC[FINITE_NUMSEG_LT; SUBSET; IN_ELIM_THM; LT_REFL] THEN
    ANTS_TAC THENL [ARITH_TAC; DISCH_THEN(SUBST1_TAC o SYM)] THEN
    TRANS_TAC EQ_TRANS
     `ndet {i:num | i < SUC n}
        (\i j. (\i. if i < n then t i - t n else &1) i *
               ((if i < n then s j * inv(&1 - t i * s j) else &1) *
                (\j. inv(&1 - t n * s j)) j))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC RP_ALG_NDET_EQ THEN REWRITE_TAC[IN_ELIM_THM] THEN
      MAP_EVERY X_GEN_TAC [`i:num`; `j:num`] THEN STRIP_TAC THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL
       [SUBGOAL_THEN `~(&1 - t (i:num) * s (j:num) = &0) /\
                      ~(&1 - t (n:num) * s j = &0)` MP_TAC THENL
         [ASM_MESON_TAC[ARITH_RULE `i < n ==> i < SUC n`;
                        ARITH_RULE `n < SUC n`];
          CONV_TAC REAL_FIELD];
        SUBGOAL_THEN `i:num = n` SUBST1_TAC THENL
         [ASM_ARITH_TAC; REAL_ARITH_TAC]];
      ALL_TAC] THEN
    SIMP_TAC[RP_ALG_NDET_ROWS_MUL; FINITE_NUMSEG_LT] THEN
    SIMP_TAC[RP_ALG_NDET_COLUMNS_MUL; FINITE_NUMSEG_LT] THEN
    REWRITE_TAC[ETA_AX] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[RP_ALG_PRODUCT_LT_SUC; LT_REFL; REAL_MUL_LID] THEN
    MATCH_MP_TAC PRODUCT_EQ THEN SIMP_TAC[IN_ELIM_THM];
    ALL_TAC] THEN
  (* Step 2: column operations and expansion along the last row *)
  SUBGOAL_THEN
   `ndet {i:num | i < SUC n}
       (\i j. if i < n then s j * inv(&1 - t i * s j) else &1) =
    product {i:num | i < n} (\i. inv(&1 - t i * s n)) *
    (ndet {i:num | i < n} (\i j. inv(&1 - t i * s j)) *
     product {i:num | i < n} (\j. s j - s n))`
  SUBST1_TAC THENL
   [MP_TAC(ISPECL [`{i:num | i < SUC n}`;
                   `\i j:num. if i < n then (s:num->real) j *
                                inv(&1 - (t:num->real) i * s j) else &1`;
                   `n:num`; `\j:num. --(&1)`; `{i:num | i < n}`]
                  RP_ALG_NDET_COLUMNS_OPERATION) THEN
    REWRITE_TAC[FINITE_NUMSEG_LT; SUBSET; IN_ELIM_THM; LT_REFL] THEN
    ANTS_TAC THENL [ARITH_TAC; DISCH_THEN(SUBST1_TAC o SYM)] THEN
    W(MP_TAC o PART_MATCH (lhand o rand) RP_ALG_NDET_LASTROW o lhand o snd) THEN
    REWRITE_TAC[LT_REFL] THEN ANTS_TAC THENL
     [REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
      DISCH_THEN SUBST1_TAC] THEN
    REWRITE_TAC[LT_REFL; REAL_MUL_LID] THEN
    TRANS_TAC EQ_TRANS
     `ndet {i:num | i < n}
        (\i j. (\i. inv(&1 - t i * s n)) i *
               (inv(&1 - t i * s j) * (\j. s j - s n) j))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC RP_ALG_NDET_EQ THEN REWRITE_TAC[IN_ELIM_THM] THEN
      MAP_EVERY X_GEN_TAC [`i:num`; `j:num`] THEN STRIP_TAC THEN
      ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `~(&1 - t (i:num) * s (j:num) = &0) /\
                    ~(&1 - t i * s (n:num) = &0)` MP_TAC THENL
       [ASM_MESON_TAC[ARITH_RULE `i < n ==> i < SUC n`;
                      ARITH_RULE `n < SUC n`];
        CONV_TAC REAL_FIELD];
      ALL_TAC] THEN
    SIMP_TAC[RP_ALG_NDET_ROWS_MUL; FINITE_NUMSEG_LT] THEN
    SIMP_TAC[RP_ALG_NDET_COLUMNS_MUL; FINITE_NUMSEG_LT] THEN
    REWRITE_TAC[ETA_AX];
    ALL_TAC] THEN
  (* Step 3: products *)
  SUBGOAL_THEN
   `product {i:num | i < SUC n} (\i. product {j:num | j < SUC n} (\j. &1 - t i * s j)) =
    (product {i:num | i < n} (\i. &1 - t i * s n) *
     product {i:num | i < n} (\i. product {j:num | j < n} (\j. &1 - t i * s j))) *
    ((&1 - t n * s n) * product {j:num | j < n} (\j. &1 - t n * s j))`
  SUBST1_TAC THENL
   [REWRITE_TAC[RP_ALG_PRODUCT_LT_SUC] THEN
    SIMP_TAC[PRODUCT_MUL; FINITE_NUMSEG_LT] THEN
    RP_ALG_GEN_CONSTS_TAC ["product"] THEN CONV_TAC REAL_RING;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `product {i:num | i < SUC n} (\j. inv(&1 - t n * s j)) =
    inv((&1 - t n * s n) * product {j:num | j < n} (\j. &1 - t n * s j))`
  SUBST1_TAC THENL
   [REWRITE_TAC[RP_ALG_PRODUCT_LT_SUC] THEN
    SIMP_TAC[PRODUCT_INV; FINITE_NUMSEG_LT; REAL_INV_MUL];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `product {i:num | i < n} (\i. inv(&1 - t i * s n)) =
    inv(product {i:num | i < n} (\i. &1 - t i * s n))`
  SUBST1_TAC THENL
   [SIMP_TAC[PRODUCT_INV; FINITE_NUMSEG_LT]; ALL_TAC] THEN
  SUBGOAL_THEN
   `product {i:num | i < n} (\i. t i - t n) * product {i:num | i < n} (\j. s j - s n) =
    product {i:num | i < n} (\i. t n - t i) * product {i:num | i < n} (\j. s n - s j)`
  MP_TAC THENL
   [SIMP_TAC[GSYM PRODUCT_MUL; FINITE_NUMSEG_LT] THEN
    MATCH_MP_TAC PRODUCT_EQ THEN REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
    CONV_TAC REAL_RING;
    ALL_TAC] THEN
  SUBGOAL_THEN `~(product {i:num | i < n} (\i. &1 - t i * s n) = &0) /\
                ~((&1 - t n * s n) * product {j:num | j < n} (\j. &1 - t n * s j)
                  = &0)` MP_TAC THENL
   [SIMP_TAC[PRODUCT_EQ_0; FINITE_NUMSEG_LT; REAL_ENTIRE; IN_ELIM_THM;
             DE_MORGAN_THM; NOT_EXISTS_THM] THEN
    ASM_MESON_TAC[ARITH_RULE `i < n ==> i < SUC n`; ARITH_RULE `n < SUC n`];
    ALL_TAC] THEN
  UNDISCH_TAC
   `ndet {i:num | i < n} (\i j. inv(&1 - t i * s j)) *
    product {i:num | i < n} (\i. product {j:num | j < n} (\j. &1 - t i * s j)) =
    rp_vdm n t * rp_vdm n s` THEN
  REWRITE_TAC[RP_ALG_VDM_SUC] THEN
  MAP_EVERY (fun t -> SPEC_TAC(t,genvar(type_of t)))
   [`product {i:num | i < n} (\i. product {j:num | j < n} (\j. &1 - t i * s j))`;
    `ndet {i:num | i < n} (\i j. inv(&1 - t i * s j))`;
    `(&1 - t n * s n) * product {j:num | j < n} (\j. &1 - t n * s j)`;
    `product {i:num | i < n} (\i. &1 - t i * s n)`;
    `product {i:num | i < n} (\i. t i - t n)`;
    `product {i:num | i < n} (\j. s j - s n)`;
    `product {i:num | i < n} (\i. t n - t i)`;
    `product {i:num | i < n} (\j. s n - s j)`;
    `rp_vdm n t`; `rp_vdm n s`] THEN
  CONV_TAC REAL_FIELD);;

let RP_ALG_CAUCHY = prove
 (`forall n t s.
     (forall i j. i < n /\ j < n ==> ~(&1 - t i * s j = &0))
     ==> ndet {i:num | i < n} (\i j. inv(&1 - t i * s j)) =
         rp_vdm n t * rp_vdm n s /
         product {i:num | i < n} (\i. product {j:num | j < n} (\j. &1 - t i * s j))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP RP_ALG_CAUCHY_MUL) THEN
  SUBGOAL_THEN
   `~(product {i:num | i < n} (\i. product {j:num | j < n} (\j. &1 - t i * s j)) =
      &0)` MP_TAC THENL
   [SIMP_TAC[PRODUCT_EQ_0; FINITE_NUMSEG_LT; IN_ELIM_THM] THEN
    ASM_MESON_TAC[];
    RP_ALG_GEN_CONSTS_TAC ["product"; "ndet"; "rp_vdm"] THEN
    CONV_TAC REAL_FIELD]);;
