(* ========================================================================= *)
(* CAT_NONVANISHING, part P: the key Frobenius congruences for Chebyshev     *)
(* polynomials: for an odd prime p, 0 <= i <= p and e >= 0, modulo p,        *)
(*   G T_(pe+i) == S_(p-i) T_e(x^p) + S_i T_(e+1)(x^p)                       *)
(*   S_(pe+i)   == S_(p-i) S_e(x^p) + S_i S_(e+1)(x^p)                       *)
(* where G = (x^2-1)^((p-1)/2) and S_n = U_(n-1).                            *)
(* ========================================================================= *)

needs "src/catalan_nv_pal_cheb.ml";;

let nv_pal_G = new_definition
 `nv_pal_G p (x:real) = (x pow 2 - &1) pow ((p - 1) DIV 2)`;;

let NV_PAL_G_IP = prove
 (`forall p. prime p ==> nv_pal_ip p (\x. nv_pal_G p x)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[nv_pal_G] THEN NV_PAL_IP_TAC);;

let NV_PAL_IPG_TAC =
  REPEAT(FIRST [MATCH_MP_TAC NV_PAL_G_IP THEN FIRST_ASSUM MATCH_ACCEPT_TAC;
                FIRST_ASSUM MATCH_ACCEPT_TAC; CONJ_TAC;
    MATCH_MP_TAC NV_PAL_T_IP; MATCH_MP_TAC NV_PAL_S_IP;
    MATCH_MP_TAC NV_PAL_T_IP_ETA; MATCH_MP_TAC NV_PAL_S_IP_ETA;
    MATCH_MP_TAC NV_PAL_IP_X;
    MATCH_MP_TAC NV_PAL_IP_CONST THEN NV_PAL_PINT_TAC;
    MATCH_MP_TAC NV_PAL_IP_ADD; MATCH_MP_TAC NV_PAL_IP_SUB;
    MATCH_MP_TAC NV_PAL_IP_MUL; MATCH_MP_TAC NV_PAL_IP_NEG;
    MATCH_MP_TAC NV_PAL_IP_POW;
    MATCH_MP_TAC NV_PAL_IP_COMPOSE]);;

let NV_PAL_FROB_G = prove
 (`forall p. prime p /\ ~(p = 2) ==> nv_pal_pc p (\x. nv_pal_S p x) (\x. nv_pal_G p x)`,
  REWRITE_TAC[nv_pal_G; NV_PAL_FROB_S]);;

let NV_PAL_CHAIN_TAC mid =
  MATCH_MP_TAC NV_PAL_PC_TRANS THEN EXISTS_TAC mid THEN
  CONJ_TAC THENL [FIRST_ASSUM MATCH_ACCEPT_TAC; CONJ_TAC];;

let NV_PAL_EQCHAIN_TAC mid =
  MATCH_MP_TAC NV_PAL_PC_EQ_TRANS THEN EXISTS_TAC mid THEN
  CONJ_TAC THENL [FIRST_ASSUM MATCH_ACCEPT_TAC; CONJ_TAC];;

let NV_PAL_PC_TAC ths =
  REPEAT(FIRST [FIRST_ASSUM MATCH_ACCEPT_TAC; CONJ_TAC;
     FIRST (map (fun th -> MATCH_MP_TAC th THEN ASM_REWRITE_TAC[] THEN NO_TAC) ths);
     MATCH_MP_TAC NV_PAL_PC_REFL THEN FIRST_ASSUM MATCH_ACCEPT_TAC;
     MATCH_MP_TAC NV_PAL_PC_ADD; MATCH_MP_TAC NV_PAL_PC_SUB;
     MATCH_MP_TAC NV_PAL_PC_MUL;
     (fun (asl,w) -> if fst(strip_comb w) = `nv_pal_ip` then NV_PAL_IPG_TAC (asl,w)
                     else failwith "NV_PAL_PC_TAC")]);;

(* T_n = x S_n - S_(n-1) *)
let NV_PAL_T_VIA_S = prove
 (`forall n x. nv_pal_T (n + 1) x = x * nv_pal_S (n + 1) x - nv_pal_S n x`,
  REPEAT GEN_TAC THEN REWRITE_TAC[NV_PAL_ADD_T; NV_PAL_ADD_S] THEN
  REWRITE_TAC[NV_PAL_T_1; NV_PAL_S_1] THEN REAL_ARITH_TAC);;

let NV_PAL_KEY0 = prove
 (`forall p i. prime p /\ ~(p = 2) /\ i <= p
     ==> nv_pal_pc p (\x. nv_pal_G p x * nv_pal_T i x - x pow p * nv_pal_S i x)
                     (\x. nv_pal_S (p - i) x)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `1 <= p` ASSUME_TAC THENL
   [ASM_MESON_TAC[PRIME_0; ARITH_RULE `1 <= p <=> ~(p = 0)`]; ALL_TAC] THEN
  ABBREV_TAC `V = \i x. nv_pal_G p x * nv_pal_T i x - x pow p * nv_pal_S i x` THEN
  SUBGOAL_THEN `forall j. j + 1 <= p ==>
     nv_pal_pc p (\x. V j x) (\x. nv_pal_S (p - j) x) /\
     nv_pal_pc p (\x. V (j + 1) x) (\x. nv_pal_S (p - (j + 1)) x)` MP_TAC THENL
   [ALL_TAC;
    DISCH_TAC THEN ASM_CASES_TAC `i = p:num` THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `p - 1`) THEN
      ASM_SIMP_TAC[SUB_ADD; LE_REFL] THEN EXPAND_TAC "V" THEN SIMP_TAC[];
      FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN ANTS_TAC THENL
       [ASM_ARITH_TAC; EXPAND_TAC "V" THEN SIMP_TAC[]]]] THEN
  INDUCT_TAC THENL
   [DISCH_TAC THEN CONJ_TAC THENL
     [EXPAND_TAC "V" THEN REWRITE_TAC[SUB_0; NV_PAL_T_0; NV_PAL_S_0] THEN
      MATCH_MP_TAC NV_PAL_PC_SYM THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC NV_PAL_PC_TRANS_EQ THEN EXISTS_TAC `\x. nv_pal_G p x` THEN
      ASM_SIMP_TAC[NV_PAL_FROB_G] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    EXPAND_TAC "V" THEN REWRITE_TAC[ADD_CLAUSES; NV_PAL_T_1; NV_PAL_S_1] THEN
    MATCH_MP_TAC NV_PAL_PC_SYM THEN ASM_REWRITE_TAC[] THEN
    NV_PAL_EQCHAIN_TAC `\x. x * nv_pal_S p x - nv_pal_T p x` THENL
     [GEN_TAC THEN MP_TAC(SPECL [`p - 1`; `x:real`] NV_PAL_T_VIA_S) THEN
      ASM_SIMP_TAC[SUB_ADD] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC NV_PAL_PC_TRANS_EQ THEN
    EXISTS_TAC `\x. x * nv_pal_G p x - x pow p` THEN
    CONJ_TAC THENL [ASM_REWRITE_TAC[]; CONJ_TAC THENL [ALL_TAC; REAL_ARITH_TAC]] THEN
    MATCH_MP_TAC NV_PAL_PC_SUB THEN ASM_SIMP_TAC[NV_PAL_FROB_T] THEN
    MATCH_MP_TAC NV_PAL_PC_MUL THEN ASM_SIMP_TAC[NV_PAL_FROB_G; NV_PAL_PC_REFL] THEN
    NV_PAL_IPG_TAC;
    ALL_TAC] THEN
  DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; STRIP_TAC] THEN
  ASM_REWRITE_TAC[ADD1] THEN
  REWRITE_TAC[ARITH_RULE `(j + 1) + 1 = j + 2`] THEN
  NV_PAL_EQCHAIN_TAC `\x. &2 * x * V (j + 1) x - (V:num->real->real) j x` THENL
   [EXPAND_TAC "V" THEN REWRITE_TAC[NV_PAL_T_REC; NV_PAL_S_REC] THEN
    CONV_TAC REAL_RING;
    ALL_TAC] THEN
  MATCH_MP_TAC NV_PAL_PC_TRANS_EQ THEN
  EXISTS_TAC `\x. &2 * x * nv_pal_S (p - (j + 1)) x - nv_pal_S (p - j) x` THEN
  CONJ_TAC THENL [ASM_REWRITE_TAC[]; CONJ_TAC] THENL
   [NV_PAL_PC_TAC [];
    GEN_TAC THEN
    SUBGOAL_THEN `p - j = (p - (j + 2)) + 2 /\ p - (j + 1) = (p - (j + 2)) + 1`
    (CONJUNCTS_THEN SUBST1_TAC) THENL
     [ASM_ARITH_TAC; REWRITE_TAC[NV_PAL_S_REC] THEN CONV_TAC REAL_RING]]);;

let NV_PAL_KEYB0 = prove
 (`forall p i. prime p /\ ~(p = 2) /\ i <= p
     ==> nv_pal_pc p (\x. nv_pal_G p x * nv_pal_T i x)
                     (\x. nv_pal_S (p - i) x + x pow p * nv_pal_S i x)`,
  REPEAT STRIP_TAC THEN
  NV_PAL_EQCHAIN_TAC `\x. (nv_pal_G p x * nv_pal_T i x - x pow p * nv_pal_S i x) +
                          x pow p * nv_pal_S i x` THENL
   [REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`p:num`; `i:num`] NV_PAL_KEY0) THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN NV_PAL_PC_TAC []);;

let NV_PAL_W = prove
 (`forall p. prime p /\ ~(p = 2)
     ==> nv_pal_pc p (\x. (x pow 2 - &1) * nv_pal_G p x * nv_pal_S p x)
                     (\x. (x pow p) pow 2 - &1)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `p:num` NV_PAL_FROB_G) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o MATCH_MP NV_PAL_PC_SYM o CONJ (ASSUME `prime p`)) THEN
  DISCH_TAC THEN
  NV_PAL_CHAIN_TAC `\x. (x pow 2 - &1) * nv_pal_S p x * nv_pal_S p x` THENL
   [NV_PAL_PC_TAC []; ALL_TAC] THEN
  NV_PAL_EQCHAIN_TAC `\x. nv_pal_T p x pow 2 - &1` THENL
   [REWRITE_TAC[NV_PAL_PELL] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC NV_PAL_PC_SUB THEN ASM_SIMP_TAC[NV_PAL_PC_REFL] THEN
  MATCH_MP_TAC NV_PAL_PC_POW THEN ASM_SIMP_TAC[NV_PAL_FROB_T] THEN NV_PAL_IPG_TAC);;

let NV_PAL_KEY = prove
 (`forall p i e. prime p /\ ~(p = 2) /\ i <= p
     ==> nv_pal_pc p (\x. nv_pal_G p x * nv_pal_T (p * e + i) x)
           (\x. nv_pal_S (p - i) x * nv_pal_T e (x pow p) +
                nv_pal_S i x * nv_pal_T (e + 1) (x pow p)) /\
         nv_pal_pc p (\x. nv_pal_S (p * e + i) x)
           (\x. nv_pal_S (p - i) x * nv_pal_S e (x pow p) +
                nv_pal_S i x * nv_pal_S (e + 1) (x pow p))`,
  GEN_TAC THEN GEN_TAC THEN
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN REPEAT DISCH_TAC THEN
  MP_TAC(SPECL [`p:num`; `i:num`] NV_PAL_KEYB0) THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN
  MP_TAC(SPEC `p:num` NV_PAL_W) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPEC `p:num` NV_PAL_FROB_T) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPEC `p:num` NV_PAL_FROB_G) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MATCH_MP_TAC(MESON[] `(forall e. P e /\ P (e + 1)) ==> (forall e. P e)`) THEN
  INDUCT_TAC THENL
   [REWRITE_TAC[ARITH; MULT_CLAUSES; ADD_CLAUSES; MULT_CLAUSES] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC NV_PAL_PC_TRANS_EQ THEN
      EXISTS_TAC `\x. nv_pal_S (p - i) x + x pow p * nv_pal_S i x` THEN
      ASM_REWRITE_TAC[NV_PAL_T_0; NV_PAL_T_1] THEN REAL_ARITH_TAC;
      MATCH_MP_TAC NV_PAL_PC_EQ THEN
      ASM_REWRITE_TAC[NV_PAL_S_0; NV_PAL_S_1] THEN REAL_ARITH_TAC;
      NV_PAL_EQCHAIN_TAC `\x. nv_pal_T p x * (nv_pal_G p x * nv_pal_T i x) +
          ((x pow 2 - &1) * nv_pal_G p x * nv_pal_S p x) * nv_pal_S i x` THENL
       [REWRITE_TAC[NV_PAL_ADD_T] THEN REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC NV_PAL_PC_TRANS_EQ THEN
      EXISTS_TAC `\x. x pow p * (nv_pal_S (p - i) x + x pow p * nv_pal_S i x) +
                      ((x pow p) pow 2 - &1) * nv_pal_S i x` THEN
      CONJ_TAC THENL [ASM_REWRITE_TAC[]; CONJ_TAC] THENL
       [NV_PAL_PC_TAC [];
        REWRITE_TAC[NV_PAL_T_1; NV_PAL_T_2] THEN REAL_ARITH_TAC];
      NV_PAL_EQCHAIN_TAC `\x. nv_pal_T p x * nv_pal_S i x +
                              nv_pal_S p x * nv_pal_T i x` THENL
       [REWRITE_TAC[NV_PAL_ADD_S]; ALL_TAC] THEN
      NV_PAL_CHAIN_TAC `\x. x pow p * nv_pal_S i x + nv_pal_G p x * nv_pal_T i x` THENL
       [NV_PAL_PC_TAC []; ALL_TAC] THEN
      MATCH_MP_TAC NV_PAL_PC_TRANS_EQ THEN
      EXISTS_TAC `\x. x pow p * nv_pal_S i x +
                      (nv_pal_S (p - i) x + x pow p * nv_pal_S i x)` THEN
      CONJ_TAC THENL [ASM_REWRITE_TAC[]; CONJ_TAC] THENL
       [NV_PAL_PC_TAC [];
        REWRITE_TAC[NV_PAL_S_1; NV_PAL_S_2] THEN REAL_ARITH_TAC]];
    ALL_TAC] THEN
  POP_ASSUM STRIP_ASSUME_TAC THEN ASM_REWRITE_TAC[ADD1] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ARITH_RULE `(e + 1) + 1 = e + 2`]) THEN
  REWRITE_TAC[ARITH_RULE `(e + 1) + 1 = e + 2`] THEN
  REWRITE_TAC[ARITH_RULE `(e + 1) + 2 = e + 3`; ARITH_RULE `e + 2 + 1 = e + 3`] THEN
  SUBGOAL_THEN `p * (e + 2) + i = (p * e + i) + p + p /\
                p * (e + 1) + i = (p * e + i) + p` STRIP_ASSUME_TAC THENL
   [ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL
   [NV_PAL_EQCHAIN_TAC `\x. &2 * nv_pal_T p x * (nv_pal_G p x * nv_pal_T (p * (e + 1) + i) x) -
                            nv_pal_G p x * nv_pal_T (p * e + i) x` THENL
     [ASM_REWRITE_TAC[NV_PAL_STEP_T] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC NV_PAL_PC_TRANS_EQ THEN
    EXISTS_TAC `\x. &2 * x pow p * (nv_pal_S (p - i) x * nv_pal_T (e + 1) (x pow p) +
                                     nv_pal_S i x * nv_pal_T (e + 2) (x pow p)) -
                    (nv_pal_S (p - i) x * nv_pal_T e (x pow p) +
                     nv_pal_S i x * nv_pal_T (e + 1) (x pow p))` THEN
    CONJ_TAC THENL [ASM_REWRITE_TAC[]; CONJ_TAC] THENL
     [NV_PAL_PC_TAC [];
      GEN_TAC THEN BETA_TAC THEN
      MP_TAC(SPECL [`e + 1`; `(x:real) pow p`] NV_PAL_T_REC) THEN
      MP_TAC(SPECL [`e:num`; `(x:real) pow p`] NV_PAL_T_REC) THEN
      REWRITE_TAC[ARITH_RULE `(e + 1) + 2 = e + 3 /\ (e + 1) + 1 = e + 2`] THEN
      CONV_TAC REAL_RING];
    NV_PAL_EQCHAIN_TAC `\x. &2 * nv_pal_T p x * nv_pal_S (p * (e + 1) + i) x -
                            nv_pal_S (p * e + i) x` THENL
     [ASM_REWRITE_TAC[NV_PAL_STEP_S] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC NV_PAL_PC_TRANS_EQ THEN
    EXISTS_TAC `\x. &2 * x pow p * (nv_pal_S (p - i) x * nv_pal_S (e + 1) (x pow p) +
                                     nv_pal_S i x * nv_pal_S (e + 2) (x pow p)) -
                    (nv_pal_S (p - i) x * nv_pal_S e (x pow p) +
                     nv_pal_S i x * nv_pal_S (e + 1) (x pow p))` THEN
    CONJ_TAC THENL [ASM_REWRITE_TAC[]; CONJ_TAC] THENL
     [NV_PAL_PC_TAC [];
      GEN_TAC THEN BETA_TAC THEN
      MP_TAC(SPECL [`e + 1`; `(x:real) pow p`] NV_PAL_S_REC) THEN
      MP_TAC(SPECL [`e:num`; `(x:real) pow p`] NV_PAL_S_REC) THEN
      REWRITE_TAC[ARITH_RULE `(e + 1) + 2 = e + 3 /\ (e + 1) + 1 = e + 2`] THEN
      CONV_TAC REAL_RING]]);;
