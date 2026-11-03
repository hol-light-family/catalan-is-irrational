(* ========================================================================= *)
(* CAT_NONVANISHING, part G: gathering the reductions into the congruence of *)
(* the scaled filtered matrix with the block matrix.                         *)
(* ========================================================================= *)

needs "src/catalan_nv_misc.ml";;
needs "src/catalan_nv_iface.ml";;

(* Sums over consecutive blocks of length p. *)

let NV_SUM_BLOCKS = prove
 (`forall p f n. 1 <= p
           ==> sum (0..n) (\m. sum (0..p-1) (\e. f(m * p + e))) =
               sum (0..(n + 1) * p - 1) f`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN DISCH_TAC THENL
   [REWRITE_TAC[SUM_SING_NUMSEG; MULT_CLAUSES; ADD_CLAUSES; ETA_AX];
    ALL_TAC] THEN
  ASM_SIMP_TAC[SUM_CLAUSES_NUMSEG; LE_0] THEN
  SUBGOAL_THEN `p <= (n + 1) * p` MP_TAC THENL
   [REWRITE_TAC[ARITH_RULE `(n + 1) * p = p + n * p`] THEN ARITH_TAC; DISCH_TAC] THEN
  SUBGOAL_THEN `(SUC n + 1) * p - 1 = ((n + 1) * p - 1) + p` SUBST1_TAC THENL
   [REWRITE_TAC[ARITH_RULE `SUC n + 1 = (n + 1) + 1`; RIGHT_ADD_DISTRIB] THEN
    UNDISCH_TAC `p <= (n + 1) * p` THEN UNDISCH_TAC `1 <= p` THEN
    SPEC_TAC(`(n + 1) * p`,`q:num`) THEN ARITH_TAC;
    ALL_TAC] THEN
  SIMP_TAC[SUM_ADD_SPLIT; LE_0; ARITH_RULE `0 <= n + 1`] THEN AP_TERM_TAC THEN
  SUBGOAL_THEN `((n + 1) * p - 1) + 1 = 0 + SUC n * p /\ ((n + 1) * p - 1) + p = (p - 1) + SUC n * p`
  (fun th -> REWRITE_TAC[th; SUM_OFFSET]) THENL
   [REWRITE_TAC[ADD1] THEN
    UNDISCH_TAC `p <= (n + 1) * p` THEN UNDISCH_TAC `1 <= p` THEN
    SPEC_TAC(`(n + 1) * p`,`q:num`) THEN ARITH_TAC;
    REWRITE_TAC[ADD_SYM]]);;

let NV_SUM_NUMSEG_SAME = prove
 (`forall f m n m' n'. m' <= m /\ n <= n' /\
                 (forall x. m' <= x /\ x < m ==> f x = &0) /\ (forall x. n < x /\ x <= n' ==> f x = &0)
                 ==> sum (m..n) f = sum (m'..n') f`,
  REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC SUM_SUPERSET THEN
  REWRITE_TAC[SUBSET; IN_NUMSEG] THEN CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `x:num` THEN STRIP_TAC THEN
  ASM_CASES_TAC `x < m:num` THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC);;

let NV_REGROUP_M = prove
 (`forall p l (phi0:num->real). 1 <= p /\ l < p /\ (forall u. u < p ==> phi0 u = &0) /\
             (forall u. 65 * p <= u ==> phi0 u = &0)
             ==> sum (0..65 * p) phi0 =
                 sum (0..65) (\m. sum (0..p-1) (\d. phi0(((m + 1) * p + l) - 1 - d)))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `forall m. sum (0..p-1) (\d. (phi0:num->real)(((m + 1) * p + l) - 1 - d)) =
                    sum (0..p-1) (\e. (\w. phi0(w + l)) (m * p + e))`
   (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [SUM_REFLECT] THEN
    REWRITE_TAC[ARITH_RULE `~(p - 1 < 0)`; SUB_0] THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `e:num` THEN STRIP_TAC THEN
    REWRITE_TAC[] THEN AP_TERM_TAC THEN
    REWRITE_TAC[ARITH_RULE `(m + 1) * p = m * p + p`] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[NV_SUM_BLOCKS] THEN
  REWRITE_TAC[ARITH_RULE `65 + 1 = 66`] THEN
  ONCE_REWRITE_TAC[GSYM(SPEC `l:num` SUM_OFFSET)] THEN
  REWRITE_TAC[ADD_CLAUSES] THEN
  MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `sum (0..66 * p + l) (phi0:num->real)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC NV_SUM_NUMSEG_SAME THEN REPEAT CONJ_TAC THENL
     [ARITH_TAC; ARITH_TAC; ARITH_TAC;
      REPEAT STRIP_TAC THEN FIRST_ASSUM(fun th -> MATCH_MP_TAC th THEN ASM_ARITH_TAC)];
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC NV_SUM_NUMSEG_SAME THEN REPEAT CONJ_TAC THENL
     [ARITH_TAC; ASM_ARITH_TAC;
      REPEAT STRIP_TAC THEN FIRST_ASSUM(fun th -> MATCH_MP_TAC th THEN ASM_ARITH_TAC);
      REPEAT STRIP_TAC THEN FIRST_ASSUM(fun th -> MATCH_MP_TAC th THEN ASM_ARITH_TAC)]]);;

let NV_G_SUM_DELTA = prove
 (`forall s (a:A) f. sum s (\x. if x = a then f x else &0) = if a IN s then f a else &0`,
  REPEAT GEN_TAC THEN
  TRANS_TAC EQ_TRANS `sum s (\x. if x = a then (f:A->real) a else &0)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_EQ THEN SIMP_TAC[];
    REWRITE_TAC[SUM_DELTA]]);;

let NV_REGROUP_Z = prove
 (`forall p l (psi:num->real). 1 <= p /\ l < p /\ (forall u. 65 * p <= u ==> psi u = &0)
       ==> sum (0..65 * p) (\u. if u MOD p = l then psi u else &0) =
           sum (0..65) (\m. psi(m * p + l))`,
  REPEAT STRIP_TAC THEN
  TRANS_TAC EQ_TRANS `sum (0..(65 + 1) * p - 1) (\u. if u MOD p = l then (psi:num->real) u else &0)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC NV_SUM_NUMSEG_SAME THEN REPEAT CONJ_TAC THENL
     [ARITH_TAC; ASM_ARITH_TAC; ARITH_TAC;
      REPEAT STRIP_TAC THEN BETA_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN
      FIRST_ASSUM(fun th -> MATCH_MP_TAC th THEN ASM_ARITH_TAC)];
    ALL_TAC] THEN
  ASM_SIMP_TAC[GSYM NV_SUM_BLOCKS] THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN
  X_GEN_TAC `m:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  TRANS_TAC EQ_TRANS `sum (0..p-1) (\e. if e = l then (psi:num->real)(m * p + e) else &0)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `e:num` THEN STRIP_TAC THEN
    REWRITE_TAC[] THEN
    SUBGOAL_THEN `(m * p + e) MOD p = e` (fun th -> REWRITE_TAC[th]) THEN
    REWRITE_TAC[MOD_MULT_ADD] THEN MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC;
    REWRITE_TAC[NV_G_SUM_DELTA; IN_NUMSEG] THEN
    COND_CASES_TAC THEN REWRITE_TAC[] THEN ASM_ARITH_TAC]);;

let NV_SUM_MULTIPLES = prove
 (`forall p a (h:num->real). 1 <= p
       ==> sum (0..a * p) (\v. if p divides v then h (v DIV p) else &0) = sum (0..a) h`,
  REPEAT STRIP_TAC THEN
  TRANS_TAC EQ_TRANS `sum (0..(a + 1) * p - 1) (\v. if p divides v then (h:num->real) (v DIV p) else &0)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC NV_SUM_NUMSEG_SAME THEN REPEAT CONJ_TAC THENL
     [ARITH_TAC; REWRITE_TAC[ARITH_RULE `(a + 1) * p = a * p + p`] THEN ASM_ARITH_TAC; ARITH_TAC;
      X_GEN_TAC `x:num` THEN STRIP_TAC THEN BETA_TAC THEN
      COND_CASES_TAC THEN REWRITE_TAC[] THEN
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [divides]) THEN
      DISCH_THEN(X_CHOOSE_THEN `q:num` SUBST_ALL_TAC) THEN
      SUBGOAL_THEN `a * p < q * p /\ q * p < (a + 1) * p:num` MP_TAC THENL
       [ASM_ARITH_TAC; ALL_TAC] THEN
      ASM_SIMP_TAC[LT_MULT_RCANCEL; ARITH_RULE `1 <= p ==> ~(p = 0)`] THEN ARITH_TAC];
    ALL_TAC] THEN
  ASM_SIMP_TAC[GSYM NV_SUM_BLOCKS] THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN
  X_GEN_TAC `m:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  TRANS_TAC EQ_TRANS `sum (0..p-1) (\e. if e = 0 then (h:num->real) m else &0)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `e:num` THEN STRIP_TAC THEN
    REWRITE_TAC[DIVIDES_MOD; MOD_MULT_ADD] THEN
    SUBGOAL_THEN `e MOD p = e /\ (m * p + e) DIV p = m` (fun th -> REWRITE_TAC[th]) THEN
    SUBGOAL_THEN `e < p:num` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[MOD_LT; DIV_MULT_ADD; DIV_LT; ARITH_RULE `1 <= p ==> ~(p = 0)`; ADD_CLAUSES];
    REWRITE_TAC[SUM_DELTA; IN_NUMSEG; LE_0]]);;

let NV_ALPHA_NORM_CONV =
  let conv t =
    if is_abs t then
      let v = bndvar t in
      let v' = mk_var("nvbv",type_of v) in
      if v = v' then failwith "" else ALPHA_CONV v' t
    else failwith "" in
  ONCE_DEPTH_CONV (fun t -> try conv t with Failure _ -> failwith "") THENC
  TOP_DEPTH_CONV (fun t -> try conv t with Failure _ -> failwith "");;

let NV_G_CONG_EQ = prove
 (`forall p x y. prime p /\ x = y ==> nv_cong p x y`,
  MESON_TAC[NV_CONG_REFL]);;

(* Some arithmetic facts about the indices. *)

let NV_G_PRIME_FACTS = prove
 (`forall p. prime p /\ 260 < p
       ==> 1 <= p /\ ~(p = 0) /\ ~(p = 2) /\ ODD p /\ ~(p divides 2) /\ 3 <= p`,
  GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(p = 2)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ASM_ARITH_TAC; ASM_ARITH_TAC;
    ASM_MESON_TAC[PRIME_ODD];
    DISCH_THEN(MP_TAC o MATCH_MP DIVIDES_LE) THEN ASM_ARITH_TAC;
    ASM_ARITH_TAC]);;

let NV_G_INDEX = prove
 (`forall p m l d. 1 <= p /\ l < p /\ d < p
             ==> ((((m + 1) * p + l) - 1 - d) + 1 + d) MOD p = l /\
                 ((((m + 1) * p + l) - 1 - d) + 1 + d) DIV p - 1 = m`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(((m + 1) * p + l) - 1 - d) + 1 + d = (m + 1) * p + l` SUBST1_TAC THENL
   [REWRITE_TAC[ARITH_RULE `(m + 1) * p = m * p + p`] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[MOD_MULT_ADD; DIV_MULT_ADD; MOD_LT; DIV_LT; ARITH_RULE `1 <= p ==> ~(p = 0)`] THEN
  ARITH_TAC);;

let NV_G_MTERM = prove
 (`nv_if_ecoef /\ nv_if_m0
   ==> forall p r m l d J. prime p /\ 260 < p /\ r < 48 * p /\ l < p /\ d < p /\ J < 65 /\
                     nv_pint p (cat_M0 m J)
       ==> nv_cong p
            (cat_pcoef p r (((m + 1) * p + l) - 1 - d) *
             (&p pow 2 * cat_M0 (((m + 1) * p + l) - 1 - d) (J * p + l)))
            (cat_M0 m J * (nv_Ecoef p d * cat_pcoef p r (((m + 1) * p + l) - 1 - d)))`,
  (REWRITE_TAC[nv_if_ecoef; nv_if_m0] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ecoef") (LABEL_TAC "m0")) THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC `p:num` NV_G_PRIME_FACTS) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `g = ((m + 1) * p + l) - 1 - d` THEN
  MP_TAC(SPECL [`p:num`; `m:num`; `l:num`; `d:num`] NV_G_INDEX) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC)
  THEN (ASM_CASES_TAC `p <= g /\ g < 65 * p` THENL
   [ALL_TAC;
    SUBGOAL_THEN `cat_pcoef p r g = &0` (fun th -> REWRITE_TAC[th]) THENL
     [FIRST_X_ASSUM(DISJ_CASES_TAC o REWRITE_RULE[DE_MORGAN_THM; NOT_LE; NOT_LT]) THEN
      ASM_SIMP_TAC[NV_PCOEF_LOW; NV_PCOEF_HIGH];
      REWRITE_TAC[REAL_MUL_LZERO; REAL_MUL_RZERO] THEN ASM_SIMP_TAC[NV_CONG_REFL]]])
  THEN (FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC))
  THEN (SUBGOAL_THEN `J * p + l < 65 * p /\ (J * p + l) MOD p = l /\ (J * p + l) DIV p = J`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[MOD_MULT_ADD; DIV_MULT_ADD; MOD_LT; DIV_LT; ADD_CLAUSES] THEN
    SUBGOAL_THEN `J * p <= 64 * p:num` MP_TAC THENL
     [ASM_SIMP_TAC[LE_MULT_RCANCEL] THEN ASM_ARITH_TAC; ASM_ARITH_TAC];
    ALL_TAC])
  THEN (SUBGOAL_THEN `nv_cong p (&p pow 2 * cat_M0 g (J * p + l)) (nv_E d * cat_M0 m J)` ASSUME_TAC THENL
   [USE_THEN "m0" (MP_TAC o SPECL [`p:num`; `g:num`; `J * p + l:num`; `d:num`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    ALL_TAC])
  THEN (MATCH_MP_TAC NV_CONG_TRANS THEN
  EXISTS_TAC `cat_pcoef p r g * (nv_E d * cat_M0 m J)` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC NV_CONG_LMUL THEN ASM_SIMP_TAC[NV_PINT_INTEGER; NV_PCOEF_INT];
    ALL_TAC])
  THEN (SUBGOAL_THEN `cat_pcoef p r g * nv_E d * cat_M0 m J =
                    cat_M0 m J * (nv_E d * cat_pcoef p r g)` SUBST1_TAC THENL
   [REAL_ARITH_TAC; ALL_TAC])
  THEN (MATCH_MP_TAC NV_CONG_LMUL THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC NV_CONG_MUL THEN ASM_SIMP_TAC[NV_PINT_INTEGER; NV_PCOEF_INT; NV_CONG_REFL])
  THEN (CONJ_TAC THENL
   [MATCH_MP_TAC NV_PINT_INTEGER THEN ASM_REWRITE_TAC[nv_Ecoef] THEN
    COND_CASES_TAC THEN SIMP_TAC[INTEGER_CLOSED];
    ONCE_REWRITE_TAC[NV_CONG_SYM_EQ] THEN USE_THEN "ecoef" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]));;


let NV_G_MPART = prove
 (`nv_if_pal_p /\ nv_if_ecoef /\ nv_if_m0
   ==> forall p r0 i l J. prime p /\ 260 < p /\ r0 < 48 /\ i < p /\ l < p /\ J < 65 /\
                    (forall m. m <= 65 ==> nv_pint p (cat_M0 m J))
       ==> nv_cong p
             (sum (0..65 * p) (\u. cat_pcoef p (p * r0 + i) u * (&p pow 2 * cat_M0 u (J * p + l))))
             (nv_a p l i * sum (0..65) (\m. cat_pcoef 1 r0 m * cat_M0 m J) +
              nv_b p l i * sum (0..65) (\m. cat_pcoef 1 (r0 + 1) m * cat_M0 m J))`,
  STRIP_TAC THEN
  LABEL_TAC "palp" (REWRITE_RULE[nv_if_pal_p] (ASSUME `nv_if_pal_p`)) THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC `p:num` NV_G_PRIME_FACTS) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `p * r0 + i < 48 * p:num` ASSUME_TAC THENL
   [SUBGOAL_THEN `p * r0 <= p * 47:num` MP_TAC THENL
     [ASM_SIMP_TAC[LE_MULT_LCANCEL] THEN ASM_ARITH_TAC; ASM_ARITH_TAC];
    ALL_TAC] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) NV_REGROUP_M o lhand o snd) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THEN X_GEN_TAC `u:num` THEN DISCH_TAC THEN
    ASM_SIMP_TAC[NV_PCOEF_LOW; NV_PCOEF_HIGH; REAL_MUL_LZERO];
    DISCH_THEN SUBST1_TAC] THEN
  MATCH_MP_TAC NV_CONG_TRANS THEN
  EXISTS_TAC `sum (0..65) (\m. cat_M0 m J *
                 sum (0..p-1) (\d. nv_Ecoef p d * cat_pcoef p (p * r0 + i) (((m + 1) * p + l) - 1 - d)))` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC NV_CONG_SUM THEN ASM_REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
    X_GEN_TAC `m:num` THEN STRIP_TAC THEN REWRITE_TAC[GSYM SUM_LMUL] THEN
    MATCH_MP_TAC NV_CONG_SUM THEN ASM_REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
    X_GEN_TAC `d:num` THEN STRIP_TAC THEN BETA_TAC THEN
    MATCH_MP_TAC(MP NV_G_MTERM (CONJ (ASSUME `nv_if_ecoef`) (ASSUME `nv_if_m0`))) THEN
    ASM_SIMP_TAC[] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC NV_CONG_TRANS THEN
  EXISTS_TAC `sum (0..65) (\m. cat_M0 m J *
                 (nv_a p l i * cat_pcoef 1 r0 m + nv_b p l i * cat_pcoef 1 (r0 + 1) m))` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC NV_CONG_SUM THEN ASM_REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
    X_GEN_TAC `m:num` THEN STRIP_TAC THEN BETA_TAC THEN MATCH_MP_TAC NV_CONG_LMUL THEN
    ASM_SIMP_TAC[] THEN USE_THEN "palp" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC NV_G_CONG_EQ THEN
    ASM_REWRITE_TAC[GSYM SUM_LMUL; GSYM SUM_ADD_NUMSEG] THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN REPEAT STRIP_TAC THEN REAL_ARITH_TAC]);;

let NV_G_ZPART = prove
 (`nv_if_pal_d /\ nv_if_z0
   ==> forall p r0 i l J. prime p /\ 260 < p /\ r0 < 48 /\ i < p /\ l < p /\ J < 65 /\
                    (forall m. m <= 65 ==> nv_pint p (cat_Z0 m J))
       ==> nv_cong p
             (sum (0..65 * p) (\u. cat_dcoef p (p * r0 + i) u * (&p pow 2 * cat_Z0 u (J * p + l))))
             (nv_a p l i * sum (0..65) (\m. cat_dcoef 1 r0 m * cat_Z0 m J) +
              nv_b p l i * sum (0..65) (\m. cat_dcoef 1 (r0 + 1) m * cat_Z0 m J))`,
  REWRITE_TAC[nv_if_pal_d; nv_if_z0] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "pald") (LABEL_TAC "z0")) THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC `p:num` NV_G_PRIME_FACTS) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `J * p + l < 65 * p /\ (J * p + l) MOD p = l /\ (J * p + l) DIV p = J`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[MOD_MULT_ADD; DIV_MULT_ADD; MOD_LT; DIV_LT; ADD_CLAUSES] THEN
    SUBGOAL_THEN `J * p <= 64 * p:num` MP_TAC THENL
     [ASM_SIMP_TAC[LE_MULT_RCANCEL] THEN ASM_ARITH_TAC; ASM_ARITH_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC NV_CONG_TRANS THEN
  EXISTS_TAC `sum (0..65 * p) (\u. if u MOD p = l
                 then cat_dcoef p (p * r0 + i) u * cat_Z0 (u DIV p) J else &0)` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC NV_CONG_SUM THEN ASM_REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
    X_GEN_TAC `u:num` THEN STRIP_TAC THEN BETA_TAC THEN
    ASM_CASES_TAC `u < 65 * p` THENL
     [USE_THEN "z0" (MP_TAC o SPECL [`p:num`; `u:num`; `J * p + l:num`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      ONCE_REWRITE_TAC[MESON[REAL_MUL_RZERO]
        `(if b then x * y else &0) = x * (if b then y else &0)`] THEN
      MATCH_MP_TAC NV_CONG_LMUL THEN ASM_SIMP_TAC[NV_PINT_INTEGER; NV_PCOEF_INT];
      ASM_SIMP_TAC[NV_PCOEF_HIGH; ARITH_RULE `~(u < 65 * p) ==> 65 * p <= u`] THEN
      REWRITE_TAC[REAL_MUL_LZERO; COND_ID] THEN ASM_SIMP_TAC[NV_CONG_REFL]];
    ALL_TAC] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) NV_REGROUP_Z o lhand o snd) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `u:num` THEN DISCH_TAC THEN
    ASM_SIMP_TAC[NV_PCOEF_HIGH; REAL_MUL_LZERO];
    DISCH_THEN SUBST1_TAC] THEN
  ASM_SIMP_TAC[DIV_MULT_ADD; DIV_LT; ADD_CLAUSES] THEN
  MATCH_MP_TAC NV_CONG_TRANS THEN
  EXISTS_TAC `sum (0..65) (\m. (nv_a p l i * cat_dcoef 1 r0 m + nv_b p l i * cat_dcoef 1 (r0 + 1) m) *
                               cat_Z0 m J)` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC NV_CONG_SUM THEN ASM_REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
    X_GEN_TAC `m:num` THEN STRIP_TAC THEN BETA_TAC THEN
    MATCH_MP_TAC NV_CONG_MUL THEN REPEAT CONJ_TAC THEN ASM_SIMP_TAC[NV_CONG_REFL] THEN
    FIRST
     [MATCH_MP_TAC NV_PINT_INTEGER THEN ASM_REWRITE_TAC[nv_a; nv_b] THEN
      COND_CASES_TAC THEN SIMP_TAC[INTEGER_CLOSED; NV_CHEB_INT; NV_PCOEF_INT];
      USE_THEN "pald" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    MATCH_MP_TAC NV_G_CONG_EQ THEN
    ASM_REWRITE_TAC[GSYM SUM_LMUL; GSYM SUM_ADD_NUMSEG] THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN REPEAT STRIP_TAC THEN REAL_ARITH_TAC]);;

let NV_G_RAW = prove
 (`nv_if_pal_p /\ nv_if_pal_d /\ nv_if_c_pint /\ nv_if_ecoef /\ nv_if_m0 /\ nv_if_z0
   ==> forall p z r0 i l J. prime p /\ 260 < p /\ nv_pint p z /\
                      r0 < 48 /\ i < p /\ l < p /\ J < 65 /\
                      (forall m. m <= 65 ==> nv_pint p (cat_M0 m J) /\ nv_pint p (cat_Z0 m J))
       ==> nv_cong p (&p pow 2 * cat_rawq z p (p * r0 + i) (J * p + l))
                     (nv_a p l i * cat_rawq (&0) 1 r0 J + nv_b p l i * cat_rawq (&0) 1 (r0 + 1) J)`,
  STRIP_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC `p:num` NV_G_PRIME_FACTS) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `r = p * r0 + i:num` THEN ABBREV_TAC `j = J * p + l:num` THEN
  SUBGOAL_THEN
   `&p pow 2 * cat_rawq z p r j =
    sum (0..65 * p) (\u. cat_pcoef p r u * (&p pow 2 * cat_M0 u j)) +
    &p * (&p * &4 * z * sum (0..65 * p) (\u. cat_pcoef p r u * cat_ckern u j)) -
    &3 / &2 * sum (0..65 * p) (\u. cat_dcoef p r u * (&p pow 2 * cat_Z0 u j))`
  SUBST1_TAC THENL
   [REWRITE_TAC[cat_rawq; REAL_ADD_LDISTRIB; SUM_ADD_NUMSEG] THEN
    REWRITE_TAC[GSYM SUM_LMUL; REAL_SUB_LDISTRIB; GSYM SUM_ADD_NUMSEG; GSYM SUM_SUB_NUMSEG] THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN REPEAT STRIP_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[cat_rawq; ARITH_RULE `65 * 1 = 65`; REAL_MUL_LZERO; REAL_MUL_RZERO;
              REAL_ADD_RID] THEN
  MATCH_MP_TAC NV_CONG_TRANS THEN
  EXISTS_TAC `(nv_a p l i * sum (0..65) (\m. cat_pcoef 1 r0 m * cat_M0 m J) +
               nv_b p l i * sum (0..65) (\m. cat_pcoef 1 (r0 + 1) m * cat_M0 m J)) + &0 -
              &3 / &2 * (nv_a p l i * sum (0..65) (\m. cat_dcoef 1 r0 m * cat_Z0 m J) +
                         nv_b p l i * sum (0..65) (\m. cat_dcoef 1 (r0 + 1) m * cat_Z0 m J))` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC NV_G_CONG_EQ THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC NV_ALPHA_NORM_CONV THEN REAL_ARITH_TAC] THEN
  MATCH_MP_TAC NV_CONG_ADD THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MAP_EVERY EXPAND_TAC ["r"; "j"] THEN
    MATCH_MP_TAC(MP NV_G_MPART (CONJ (ASSUME `nv_if_pal_p`)
                     (CONJ (ASSUME `nv_if_ecoef`) (ASSUME `nv_if_m0`)))) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC NV_CONG_SUB THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC NV_CONG_PMUL_0 THEN ASM_REWRITE_TAC[] THEN
    REPEAT(MATCH_MP_TAC NV_PINT_MUL THEN ASM_REWRITE_TAC[] THEN TRY CONJ_TAC) THEN
    ASM_SIMP_TAC[NV_PINT_NUM] THEN
    MATCH_MP_TAC NV_PINT_SUM THEN ASM_REWRITE_TAC[FINITE_NUMSEG] THEN
    REPEAT STRIP_TAC THEN BETA_TAC THEN
    MATCH_MP_TAC NV_PINT_MUL THEN ASM_SIMP_TAC[NV_PINT_INTEGER; NV_PCOEF_INT] THEN
    REWRITE_TAC[cat_ckern] THEN COND_CASES_TAC THEN ASM_SIMP_TAC[NV_PINT_0] THEN
    UNDISCH_TAC `nv_if_c_pint` THEN REWRITE_TAC[nv_if_c_pint] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC NV_CONG_LMUL THEN ASM_SIMP_TAC[NV_PINT_DIV_NUM; NV_PINT_NUM] THEN
    MAP_EVERY EXPAND_TAC ["r"; "j"] THEN
    MATCH_MP_TAC(MP NV_G_ZPART (CONJ (ASSUME `nv_if_pal_d`) (ASSUME `nv_if_z0`))) THEN
    ASM_SIMP_TAC[]]);;

let NV_G_RAWX = prove
 (`nv_if_pal_p /\ nv_if_pal_d /\ nv_if_c_pint /\ nv_if_ecoef /\ nv_if_m0 /\ nv_if_z0
   ==> forall p z r0 i j. prime p /\ 260 < p /\ nv_pint p z /\
                    r0 < 48 /\ i < p /\ j < 65 * p /\
                    (forall r m J. r <= 48 /\ m <= 65 /\ J < 65
                             ==> nv_pint p (cat_M0 m J) /\ nv_pint p (cat_Z0 m J) /\
                                 nv_pint p (cat_rawq (&0) 1 r J))
       ==> nv_pint p (&p pow 2 * cat_rawq z p (p * r0 + i) j)`,
  STRIP_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC `p:num` NV_G_PRIME_FACTS) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`j:num`; `p:num`] DIVISION) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC) THEN
  SUBGOAL_THEN `j DIV p < 65` ASSUME_TAC THENL
   [ASM_SIMP_TAC[RDIV_LT_EQ] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC NV_CONG_PINT THEN
  EXISTS_TAC `nv_a p (j MOD p) i * cat_rawq (&0) 1 r0 (j DIV p) +
              nv_b p (j MOD p) i * cat_rawq (&0) 1 (r0 + 1) (j DIV p)` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC(MP NV_G_RAW (end_itlist CONJ (map ASSUME
      [`nv_if_pal_p`; `nv_if_pal_d`; `nv_if_c_pint`; `nv_if_ecoef`; `nv_if_m0`; `nv_if_z0`]))) THEN
    ASM_SIMP_TAC[] THEN X_GEN_TAC `m:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`0:num`; `m:num`; `j DIV p`]) THEN ASM_SIMP_TAC[LE_0];
    MATCH_MP_TAC NV_PINT_ADD THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THEN
    MATCH_MP_TAC NV_PINT_MUL THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THEN
    TRY(MATCH_MP_TAC NV_PINT_INTEGER THEN ASM_REWRITE_TAC[nv_a; nv_b] THEN
        TRY COND_CASES_TAC THEN SIMP_TAC[INTEGER_CLOSED; NV_CHEB_INT] THEN NO_TAC) THEN
    FIRST_ASSUM(MP_TAC o SPECL [`r0 + 1:num`; `0:num`; `j DIV p`]) THEN
    FIRST_ASSUM(MP_TAC o SPECL [`r0:num`; `0:num`; `j DIV p`]) THEN
    ASM_SIMP_TAC[LE_0; ARITH_RULE `r0 < 48 ==> r0 <= 48 /\ r0 + 1 <= 48`]]);;

let NV_G_IFACES = new_definition
 `nv_g_ifaces <=> nv_if_pal_p /\ nv_if_pal_d /\ nv_if_binom /\ nv_if_c_pint /\
                  nv_if_ecoef /\ nv_if_m0 /\ nv_if_z0`;;

let NV_G_ENTRY = prove
 (`nv_g_ifaces
   ==> forall p z r0 i l k0. prime p /\ 260 < p /\ nv_pint p z /\
                       r0 < 48 /\ i < p /\ l < p /\ k0 < 48 /\
                       (forall r m J. r <= 48 /\ m <= 65 /\ J < 65
                                ==> nv_pint p (cat_M0 m J) /\ nv_pint p (cat_Z0 m J) /\
                                    nv_pint p (cat_rawq (&0) 1 r J))
       ==> nv_cong p (&p pow 2 * cat_entryq z p (p * r0 + i) (p * k0 + l))
                     (nv_a p l i * cat_entryq (&0) 1 r0 k0 +
                      nv_b p l i * cat_entryq (&0) 1 (r0 + 1) k0)`,
  REWRITE_TAC[NV_G_IFACES] THEN STRIP_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC `p:num` NV_G_PRIME_FACTS) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `R = \w. nv_a p l i * cat_rawq (&0) 1 r0 (7 + k0 + w) +
                      nv_b p l i * cat_rawq (&0) 1 (r0 + 1) (7 + k0 + w)` THEN
  REWRITE_TAC[cat_entryq; GSYM SUM_LMUL] THEN
  MATCH_MP_TAC NV_CONG_TRANS THEN
  EXISTS_TAC `sum (0..4 * p) (\v. if p divides v
                 then (--(&1)) pow (v DIV p) * &(binom(4,v DIV p)) * (R:num->real) (v DIV p)
                 else &0)` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ALL_TAC;
    ASM_SIMP_TAC[NV_SUM_MULTIPLES] THEN
    MATCH_MP_TAC NV_G_CONG_EQ THEN ASM_REWRITE_TAC[] THEN EXPAND_TAC "R" THEN
    REWRITE_TAC[ARITH_RULE `4 * 1 = 4 /\ 7 * 1 = 7`] THEN
    REWRITE_TAC[GSYM SUM_LMUL; GSYM SUM_ADD_NUMSEG] THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN REPEAT STRIP_TAC THEN BETA_TAC THEN
    REWRITE_TAC[ADD_ASSOC] THEN REAL_ARITH_TAC] THEN
  MATCH_MP_TAC NV_CONG_SUM THEN ASM_REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
  X_GEN_TAC `v:num` THEN STRIP_TAC THEN BETA_TAC THEN
  ABBREV_TAC `Y0 = &p pow 2 * cat_rawq z p (p * r0 + i) (7 * p + (p * k0 + l) + v)` THEN
  SUBGOAL_THEN `nv_pint p Y0` ASSUME_TAC THENL
   [EXPAND_TAC "Y0" THEN
    MATCH_MP_TAC(MP NV_G_RAWX (end_itlist CONJ (map ASSUME
      [`nv_if_pal_p`; `nv_if_pal_d`; `nv_if_c_pint`; `nv_if_ecoef`; `nv_if_m0`; `nv_if_z0`]))) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `p * k0 <= p * 47:num` MP_TAC THENL
     [ASM_SIMP_TAC[LE_MULT_LCANCEL] THEN ASM_ARITH_TAC; ASM_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&p pow 2 * (--(&1)) pow v * &(binom(4 * p,v)) *
                cat_rawq z p (p * r0 + i) (7 * p + (p * k0 + l) + v) =
                ((--(&1)) pow v * &(binom(4 * p,v))) * Y0` SUBST1_TAC THENL
   [EXPAND_TAC "Y0" THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC NV_CONG_TRANS THEN
  EXISTS_TAC `(if p divides v then (--(&1)) pow (v DIV p) * &(binom(4,v DIV p)) else &0) *
              (if p divides v then (R:num->real) (v DIV p) else Y0)` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC NV_G_CONG_EQ THEN ASM_REWRITE_TAC[] THEN
    COND_CASES_TAC THEN REWRITE_TAC[REAL_MUL_LZERO; REAL_MUL_ASSOC]] THEN
  UNDISCH_TAC `nv_if_binom` THEN REWRITE_TAC[nv_if_binom] THEN
  DISCH_THEN(MP_TAC o SPECL [`p:num`; `4`; `v:num`]) THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN
  COND_CASES_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC NV_CONG_MUL THEN ASM_SIMP_TAC[NV_PINT_0; NV_CONG_REFL] THEN
    ONCE_REWRITE_TAC[GSYM(SPEC `(--(&1)) pow v` REAL_MUL_RZERO)] THEN
    MATCH_MP_TAC NV_CONG_LMUL THEN ASM_SIMP_TAC[NV_PINT_INTEGER; INTEGER_CLOSED] THEN
    UNDISCH_TAC `nv_cong p (&(binom (4 * p,v))) (if p divides v then &(binom (4,v DIV p)) else &0)` THEN
    ASM_REWRITE_TAC[]] THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `w:num` SUBST_ALL_TAC o GEN_REWRITE_RULE I [divides]) THEN
  SUBGOAL_THEN `(p * w) DIV p = w /\ w <= 4` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC DIV_MULT THEN ASM_REWRITE_TAC[];
      UNDISCH_TAC `p * w <= 4 * p` THEN REWRITE_TAC[ARITH_RULE `4 * p = p * 4`] THEN
      SIMP_TAC[LE_MULT_LCANCEL; ASSUME `~(p = 0)`]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `p divides p * w:num` ASSUME_TAC THENL
   [MESON_TAC[DIVIDES_RMUL; DIVIDES_REFL]; ALL_TAC] THEN
  UNDISCH_TAC `nv_cong p (&(binom (4 * p,p * w))) (if p divides p * w then &(binom (4,(p * w) DIV p)) else &0)` THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MATCH_MP_TAC NV_CONG_MUL THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
  FIRST (map (fun tac -> tac THEN NO_TAC)
   [MATCH_MP_TAC NV_PINT_INTEGER THEN ASM_REWRITE_TAC[] THEN SIMP_TAC[INTEGER_CLOSED];
    EXPAND_TAC "R" THEN BETA_TAC THEN
    SUBGOAL_THEN `forall r. r <= 48 ==> nv_pint p (cat_rawq (&0) 1 r (7 + k0 + w))` ASSUME_TAC THENL
     [REPEAT STRIP_TAC THEN
      FIRST_ASSUM(MP_TAC o SPECL [`r:num`; `0:num`; `7 + k0 + w:num`]) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; SIMP_TAC[]];
      ALL_TAC] THEN
    MATCH_MP_TAC NV_PINT_ADD THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THEN
    MATCH_MP_TAC NV_PINT_MUL THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THEN
    TRY(MATCH_MP_TAC NV_PINT_INTEGER THEN ASM_REWRITE_TAC[nv_a; nv_b] THEN
        TRY COND_CASES_TAC THEN SIMP_TAC[INTEGER_CLOSED; NV_CHEB_INT] THEN NO_TAC) THEN
    FIRST_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    SUBGOAL_THEN `(--(&1)) pow (p * w) = (--(&1)) pow w` SUBST1_TAC THENL
     [ONCE_REWRITE_TAC[MULT_SYM] THEN
      REWRITE_TAC[GSYM REAL_POW_POW; REAL_POW_NEG; REAL_POW_ONE; GSYM NOT_ODD; ODD_MULT] THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC NV_CONG_LMUL THEN ASM_SIMP_TAC[NV_PINT_INTEGER; INTEGER_CLOSED]];
    EXPAND_TAC "Y0" THEN EXPAND_TAC "R" THEN BETA_TAC THEN
    SUBGOAL_THEN `7 * p + (p * k0 + l) + p * w = (7 + k0 + w) * p + l:num` SUBST1_TAC THENL
     [ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC(MP NV_G_RAW (end_itlist CONJ (map ASSUME
      [`nv_if_pal_p`; `nv_if_pal_d`; `nv_if_c_pint`; `nv_if_ecoef`; `nv_if_m0`; `nv_if_z0`]))) THEN
    ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `m:num` THEN DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o SPECL [`0:num`; `m:num`; `7 + k0 + w:num`]) THEN
    ASM_SIMP_TAC[LE_0] THEN ANTS_TAC THENL [ASM_ARITH_TAC; SIMP_TAC[]]]));;

(* Finite families of rationals are p-integral for large p. *)

let NV_PINT_FAMILY = prove
 (`forall (f:A->real) s. FINITE s /\ (forall i. i IN s ==> rational(f i))
         ==> exists P. forall p. prime p /\ P <= p ==> forall i. i IN s ==> nv_pint p (f i)`,
  GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  REWRITE_TAC[NOT_IN_EMPTY; IN_INSERT] THEN
  MAP_EVERY X_GEN_TAC [`a:A`; `s:A->bool`] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN ANTS_TAC THENL
   [ASM_MESON_TAC[]; DISCH_THEN(X_CHOOSE_TAC `P1:num`)] THEN
  MP_TAC(SPEC `(f:A->real) a` NV_PINT_RATIONAL) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; DISCH_THEN(X_CHOOSE_TAC `P2:num`)] THEN
  EXISTS_TAC `P1 + P2:num` THEN REPEAT STRIP_TAC THEN
  ASM_MESON_TAC[ARITH_RULE `P1 + P2 <= p:num ==> P1 <= p /\ P2 <= p`]);;
