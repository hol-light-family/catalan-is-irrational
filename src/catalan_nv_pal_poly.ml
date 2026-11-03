(* ========================================================================= *)
(* CAT_NONVANISHING, part P (prefix nv_pal_): p-integral polynomial          *)
(* functions on the reals and congruences between them modulo p.            *)
(*   nv_pal_ip p f   : f is a polynomial function with p-integral coeffs     *)
(*   nv_pal_pc p f g : f = g + p * h with nv_pal_ip p h                      *)
(* ========================================================================= *)

needs "src/catalan_nv_base.ml";;

let nv_pal_ip = new_definition
 `nv_pal_ip p (f:real->real) <=>
    exists n c. (forall k. nv_pint p (c k)) /\ forall x. f x = sum(0..n) (\k. c k * x pow k)`;;

let nv_pal_pc = new_definition
 `nv_pal_pc p (f:real->real) (g:real->real) <=>
    exists h. nv_pal_ip p h /\ forall x. f x = g x + &p * h x`;;

(* ------------------------------------------------------------------------- *)
(* Generic sum lemmas.                                                       *)
(* ------------------------------------------------------------------------- *)

let NV_PAL_SUM_DELTA = prove
 (`forall j (c:real) (y:real) n. j <= n ==>
    sum(0..n) (\k. (if k = j then c else &0) * y pow k) = c * y pow j`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `sum(0..n) (\k. if k = j then c * (y:real) pow j else &0)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_EQ_NUMSEG THEN REPEAT STRIP_TAC THEN BETA_TAC THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[REAL_MUL_LZERO];
    REWRITE_TAC[SUM_DELTA; IN_NUMSEG] THEN ASM_REWRITE_TAC[LE_0]]);;

let NV_PAL_TRUNC = prove
 (`forall m n (c:num->real) (t:real). m <= n /\ (forall j. m < j ==> c j = &0)
    ==> sum(0..n) (\j. c j * t pow j) = sum(0..m) (\j. c j * t pow j)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUM_SUPERSET THEN
  REWRITE_TAC[SUBSET_NUMSEG; IN_NUMSEG] THEN
  CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(c:num->real) x = &0` SUBST1_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    REWRITE_TAC[REAL_MUL_LZERO]]);;

let NV_PAL_SUM_EXTEND = prove
 (`forall n N (a:num->real) (x:real). n <= N
    ==> sum(0..N) (\k. (if k <= n then a k else &0) * x pow k) =
        sum(0..n) (\k. a k * x pow k)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(BETA_RULE(ISPECL [`n:num`; `N:num`;
     `\k. if k <= n then (a:num->real) k else &0`; `x:real`] NV_PAL_TRUNC)) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN GEN_TAC THEN DISCH_TAC THEN
    COND_CASES_TAC THEN REWRITE_TAC[] THEN ASM_ARITH_TAC;
    DISCH_THEN SUBST1_TAC] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN SIMP_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Closure properties of nv_pal_ip.                                          *)
(* ------------------------------------------------------------------------- *)

let NV_PAL_IP_POLY = prove
 (`forall p f. nv_pal_ip p f ==> polynomial_function f`,
  REWRITE_TAC[nv_pal_ip; polynomial_function] THEN MESON_TAC[]);;

let NV_PAL_IP_CONST = prove
 (`forall p c. nv_pint p c ==> nv_pal_ip p (\x. c)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[nv_pal_ip] THEN
  MAP_EVERY EXISTS_TAC [`0`; `(\k. c):num->real`] THEN
  ASM_REWRITE_TAC[SUM_SING_NUMSEG; real_pow; REAL_MUL_RID]);;

let NV_PAL_IP_MONO = prove
 (`forall p c m. prime p /\ nv_pint p c ==> nv_pal_ip p (\x. c * x pow m)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[nv_pal_ip] THEN
  MAP_EVERY EXISTS_TAC [`m:num`; `\k:num. if k = m then c else &0`] THEN
  SIMP_TAC[NV_PAL_SUM_DELTA; LE_REFL] THEN GEN_TAC THEN
  COND_CASES_TAC THEN ASM_SIMP_TAC[NV_PINT_0]);;

let NV_PAL_IP_X = prove
 (`forall p. prime p ==> nv_pal_ip p (\x. x)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`p:num`; `&1`; `1`] NV_PAL_IP_MONO) THEN
  ASM_SIMP_TAC[NV_PINT_1; REAL_MUL_LID; REAL_POW_1]);;

let NV_PAL_IP_ADD = prove
 (`forall p f g. prime p /\ nv_pal_ip p f /\ nv_pal_ip p g
           ==> nv_pal_ip p (\x. f x + g x)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[nv_pal_ip] THEN STRIP_TAC THEN
  EXISTS_TAC `MAX n n'` THEN EXISTS_TAC
   `\i:num. (if i <= n then c i else &0) + (if i <= n' then c' i else &0)` THEN
  CONJ_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[] THEN MATCH_MP_TAC NV_PINT_ADD THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THEN COND_CASES_TAC THEN
    ASM_SIMP_TAC[NV_PINT_0];
    GEN_TAC THEN ASM_REWRITE_TAC[REAL_ADD_RDISTRIB; SUM_ADD_NUMSEG] THEN
    BINOP_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC NV_PAL_SUM_EXTEND THEN
    ARITH_TAC]);;

let NV_PAL_IP_CMUL = prove
 (`forall p c f. prime p /\ nv_pint p c /\ nv_pal_ip p f
           ==> nv_pal_ip p (\x. c * f x)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[nv_pal_ip] THEN STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`n:num`; `\k. c * (c':num->real) k`] THEN
  ASM_SIMP_TAC[NV_PINT_MUL; GSYM SUM_LMUL; REAL_MUL_ASSOC]);;

let NV_PAL_IP_NEG = prove
 (`forall p f. prime p /\ nv_pal_ip p f ==> nv_pal_ip p (\x. --(f x))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`p:num`; `--(&1)`; `f:real->real`] NV_PAL_IP_CMUL) THEN
  ASM_SIMP_TAC[NV_PINT_NEG; NV_PINT_1; REAL_MUL_LNEG; REAL_MUL_LID]);;

let NV_PAL_IP_SUB = prove
 (`forall p f g. prime p /\ nv_pal_ip p f /\ nv_pal_ip p g
           ==> nv_pal_ip p (\x. f x - g x)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[real_sub] THEN
  MP_TAC(SPECL [`p:num`; `f:real->real`; `\x. --((g:real->real) x)`]
    NV_PAL_IP_ADD) THEN
  ASM_SIMP_TAC[NV_PAL_IP_NEG]);;

let NV_PAL_IP_SUM = prove
 (`forall p (f:real->A->real) s.
        prime p /\ FINITE s /\ (forall i. i IN s ==> nv_pal_ip p (\x. f x i))
        ==> nv_pal_ip p (\x. sum s (f x))`,
  GEN_TAC THEN GEN_TAC THEN
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN DISCH_TAC THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  ASM_SIMP_TAC[SUM_CLAUSES; NV_PAL_IP_CONST; NV_PINT_0] THEN
  REWRITE_TAC[FORALL_IN_INSERT] THEN
  MAP_EVERY X_GEN_TAC [`a:A`; `t:A->bool`] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`p:num`; `\y. (f:real->A->real) y a`;
                 `\y. sum t ((f:real->A->real) y)`] NV_PAL_IP_ADD) THEN
  ASM_SIMP_TAC[]);;

let NV_PAL_IP_MUL = prove
 (`forall p f g. prime p /\ nv_pal_ip p f /\ nv_pal_ip p g
           ==> nv_pal_ip p (\x. f x * g x)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN DISCH_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [nv_pal_ip] THEN STRIP_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [nv_pal_ip] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(\x. (f:real->real) x * g x) =
                (\x. sum(0..n) (\j. sum(0..n') (\k. (c j * c' k) * x pow (j + k))))`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[REAL_MUL_SUM_NUMSEG] THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN REPEAT STRIP_TAC THEN BETA_TAC THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN REPEAT STRIP_TAC THEN BETA_TAC THEN
    REWRITE_TAC[REAL_POW_ADD] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC NV_PAL_IP_SUM THEN ASM_REWRITE_TAC[FINITE_NUMSEG] THEN
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC NV_PAL_IP_SUM THEN ASM_REWRITE_TAC[FINITE_NUMSEG] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC NV_PAL_IP_MONO THEN
  ASM_SIMP_TAC[NV_PINT_MUL]);;

let NV_PAL_IP_POW = prove
 (`forall p f n. prime p /\ nv_pal_ip p f ==> nv_pal_ip p (\x. f x pow n)`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN
  ASM_SIMP_TAC[real_pow; NV_PAL_IP_CONST; NV_PINT_1] THEN
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`p:num`; `f:real->real`; `\x. (f:real->real) x pow n`]
    NV_PAL_IP_MUL) THEN ASM_SIMP_TAC[]);;

let NV_PAL_IP_COMPOSE = prove
 (`forall p f g. prime p /\ nv_pal_ip p f /\ nv_pal_ip p g
           ==> nv_pal_ip p (\x. f (g x))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC)) THEN
  GEN_REWRITE_TAC (LAND_CONV) [nv_pal_ip] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC NV_PAL_IP_SUM THEN
  ASM_REWRITE_TAC[FINITE_NUMSEG] THEN REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`p:num`; `(c:num->real) i`; `\x. (g:real->real) x pow i`]
    NV_PAL_IP_CMUL) THEN
  ASM_SIMP_TAC[NV_PAL_IP_POW]);;

let NV_PAL_IP_INTPOLY = prove
 (`forall p n c. prime p /\ (forall k. integer(c k))
           ==> nv_pal_ip p (\x. sum(0..n) (\k. c k * x pow k))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[nv_pal_ip] THEN
  MAP_EVERY EXISTS_TAC [`n:num`; `c:num->real`] THEN
  ASM_SIMP_TAC[NV_PINT_INTEGER]);;

let NV_PAL_IP_PINTPOLY = prove
 (`forall p n c. prime p /\ (forall k. nv_pint p (c k))
           ==> nv_pal_ip p (\x. sum(0..n) (\k. c k * x pow k))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[nv_pal_ip] THEN
  MAP_EVERY EXISTS_TAC [`n:num`; `c:num->real`] THEN
  ASM_SIMP_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Congruences.                                                              *)
(* ------------------------------------------------------------------------- *)

let NV_PAL_PC_EQ = prove
 (`forall p f g. prime p /\ (forall x. f x = g x) ==> nv_pal_pc p f g`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[nv_pal_pc] THEN
  EXISTS_TAC `\x:real. &0` THEN
  ASM_SIMP_TAC[NV_PAL_IP_CONST; NV_PINT_0; REAL_MUL_RZERO; REAL_ADD_RID]);;

let NV_PAL_PC_REFL = prove
 (`forall p f. prime p ==> nv_pal_pc p f f`,
  SIMP_TAC[NV_PAL_PC_EQ]);;

let NV_PAL_PC_SYM = prove
 (`forall p f g. prime p /\ nv_pal_pc p f g ==> nv_pal_pc p g f`,
  REPEAT GEN_TAC THEN REWRITE_TAC[nv_pal_pc] THEN STRIP_TAC THEN
  EXISTS_TAC `\x. --((h:real->real) x)` THEN ASM_SIMP_TAC[NV_PAL_IP_NEG] THEN
  REAL_ARITH_TAC);;

let NV_PAL_PC_TRANS = prove
 (`forall p f g k. prime p /\ nv_pal_pc p f g /\ nv_pal_pc p g k ==> nv_pal_pc p f k`,
  REPEAT GEN_TAC THEN REWRITE_TAC[nv_pal_pc] THEN STRIP_TAC THEN
  EXISTS_TAC `\x. (h:real->real) x + h' x` THEN ASM_SIMP_TAC[NV_PAL_IP_ADD] THEN
  REAL_ARITH_TAC);;

let NV_PAL_PC_ADD = prove
 (`forall p f f' g g'. prime p /\ nv_pal_pc p f f' /\ nv_pal_pc p g g'
       ==> nv_pal_pc p (\x. f x + g x) (\x. f' x + g' x)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[nv_pal_pc] THEN STRIP_TAC THEN
  EXISTS_TAC `\x. (h:real->real) x + h' x` THEN ASM_SIMP_TAC[NV_PAL_IP_ADD] THEN
  REAL_ARITH_TAC);;

let NV_PAL_PC_SUB = prove
 (`forall p f f' g g'. prime p /\ nv_pal_pc p f f' /\ nv_pal_pc p g g'
       ==> nv_pal_pc p (\x. f x - g x) (\x. f' x - g' x)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[nv_pal_pc] THEN STRIP_TAC THEN
  EXISTS_TAC `\x. (h:real->real) x - h' x` THEN ASM_SIMP_TAC[NV_PAL_IP_SUB] THEN
  REAL_ARITH_TAC);;

let NV_PAL_PC_MUL = prove
 (`forall p f f' g g'. prime p /\ nv_pal_pc p f f' /\ nv_pal_pc p g g' /\
                 nv_pal_ip p f' /\ nv_pal_ip p g'
       ==> nv_pal_pc p (\x. f x * g x) (\x. f' x * g' x)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[nv_pal_pc] THEN STRIP_TAC THEN
  EXISTS_TAC `\x. (h:real->real) x * g' x + f' x * h' x + &p * h x * h' x` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC NV_PAL_IP_ADD THEN ASM_SIMP_TAC[NV_PAL_IP_MUL] THEN
    MATCH_MP_TAC NV_PAL_IP_ADD THEN ASM_SIMP_TAC[NV_PAL_IP_MUL] THEN
    MATCH_MP_TAC NV_PAL_IP_CMUL THEN ASM_SIMP_TAC[NV_PAL_IP_MUL; NV_PINT_NUM];
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC]);;

let NV_PAL_PC_POW = prove
 (`forall p f g n. prime p /\ nv_pal_pc p f g /\ nv_pal_ip p g
       ==> nv_pal_pc p (\x. f x pow n) (\x. g x pow n)`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN
  ASM_SIMP_TAC[real_pow; NV_PAL_PC_REFL] THEN REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`p:num`; `f:real->real`; `g:real->real`;
    `\x. (f:real->real) x pow n`; `\x. (g:real->real) x pow n`] NV_PAL_PC_MUL) THEN
  ASM_SIMP_TAC[NV_PAL_IP_POW]);;

let NV_PAL_PC_COMPOSE = prove
 (`forall p f g k. prime p /\ nv_pal_pc p f g /\ nv_pal_ip p k
       ==> nv_pal_pc p (\x. f (k x)) (\x. g (k x))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[nv_pal_pc] THEN STRIP_TAC THEN
  EXISTS_TAC `\x:real. (h:real->real) (k x)` THEN ASM_SIMP_TAC[NV_PAL_IP_COMPOSE]);;

let NV_PAL_PC_IP = prove
 (`forall p f g. prime p /\ nv_pal_pc p f g /\ nv_pal_ip p g ==> nv_pal_ip p f`,
  REPEAT GEN_TAC THEN REWRITE_TAC[nv_pal_pc] THEN STRIP_TAC THEN
  SUBGOAL_THEN `f = (\x. (g:real->real) x + &p * h x)` SUBST1_TAC THENL
   [ASM_REWRITE_TAC[FUN_EQ_THM]; ALL_TAC] THEN
  MATCH_MP_TAC NV_PAL_IP_ADD THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC NV_PAL_IP_CMUL THEN ASM_SIMP_TAC[NV_PINT_NUM]);;

let NV_PAL_PC_EQ_TRANS = prove
 (`forall p f g k. prime p /\ (forall x. f x = g x) /\ nv_pal_pc p g k ==> nv_pal_pc p f k`,
  MESON_TAC[NV_PAL_PC_EQ; NV_PAL_PC_TRANS]);;

let NV_PAL_PC_TRANS_EQ = prove
 (`forall p f g k. prime p /\ nv_pal_pc p f g /\ (forall x. g x = k x) ==> nv_pal_pc p f k`,
  MESON_TAC[NV_PAL_PC_EQ; NV_PAL_PC_TRANS]);;

(* ------------------------------------------------------------------------- *)
(* Polynomial identities extend from x > 1 to all x.                         *)
(* ------------------------------------------------------------------------- *)

let NV_PAL_PF_EXT = prove
 (`forall f g. polynomial_function f /\ polynomial_function g /\
         (forall x. &1 < x ==> f x = g x) ==> forall x. f x = g x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`\x. (f:real->real) x - g x`; `&0`]
    POLYNOMIAL_FUNCTION_FINITE_ROOTS) THEN
  ASM_SIMP_TAC[POLYNOMIAL_FUNCTION_SUB; REAL_SUB_0] THEN
  MATCH_MP_TAC(TAUT `~a ==> (a <=> ~b) ==> b`) THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL [`{x:real | &1 < x}`; `{x:real | (f:real->real) x = g x}`]
    FINITE_SUBSET) THEN
  ASM_REWRITE_TAC[FINITE_REAL_INTERVAL; SUBSET; IN_ELIM_THM] THEN
  ASM_SIMP_TAC[]);;

let NV_PAL_IP_EXT = prove
 (`forall p f g. nv_pal_ip p f /\ nv_pal_ip p g /\
         (forall x. &1 < x ==> f x = g x) ==> forall x. f x = g x`,
  MESON_TAC[NV_PAL_PF_EXT; NV_PAL_IP_POLY]);;

(* ------------------------------------------------------------------------- *)
(* Coefficient extraction.                                                   *)
(* ------------------------------------------------------------------------- *)

let NV_PAL_PC_COEFF = prove
 (`forall p n c d. prime p /\
     nv_pal_pc p (\x. sum(0..n) (\k. c k * x pow k))
                 (\x. sum(0..n) (\k. d k * x pow k))
     ==> forall k. k <= n ==> nv_cong p (c k) (d k)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[nv_pal_pc; nv_pal_ip] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `h:real->real` (CONJUNCTS_THEN2
    (X_CHOOSE_THEN `m:num` (X_CHOOSE_THEN `e:num->real` STRIP_ASSUME_TAC))
    ASSUME_TAC)) THEN
  SUBGOAL_THEN
   `forall x. sum(0..n+m) (\k. ((if k <= n then c k - d k else &0) -
                          &p * (if k <= m then e k else &0)) * x pow k) = &0`
  MP_TAC THENL
   [GEN_TAC THEN
    REWRITE_TAC[REAL_SUB_RDISTRIB; SUM_SUB_NUMSEG; GSYM REAL_MUL_ASSOC;
                SUM_LMUL] THEN
    SIMP_TAC[NV_PAL_SUM_EXTEND; ARITH_RULE `n <= n + m:num`;
             ARITH_RULE `m <= n + m:num`] THEN
    REWRITE_TAC[REAL_SUB_RDISTRIB; SUM_SUB_NUMSEG] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:real`) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:real`) THEN
    SIMP_TAC[] THEN REAL_ARITH_TAC;
    REWRITE_TAC[REAL_POLYFUN_EQ_0; IN_NUMSEG; LE_0]] THEN
  DISCH_TAC THEN X_GEN_TAC `k:num` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `k:num`) THEN
  ASM_SIMP_TAC[ARITH_RULE `k <= n ==> k <= n + m:num`] THEN
  REWRITE_TAC[REAL_SUB_0; nv_cong] THEN DISCH_THEN SUBST1_TAC THEN
  ASM_SIMP_TAC[REAL_FIELD `~(p = &0) ==> (p * a) / p = a`; NV_PRIME_NZ] THEN
  COND_CASES_TAC THEN ASM_SIMP_TAC[NV_PINT_0]);;
