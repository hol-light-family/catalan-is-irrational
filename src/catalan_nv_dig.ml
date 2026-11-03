(* ========================================================================= *)
(* CAT_NONVANISHING, part La (prefix nv_dig_): the interface statements      *)
(* NV_DIG_C_PINT, NV_DIG_ECOEF, NV_DIG_M, NV_DIG_KMINUS, NV_DIG_KPLUS        *)
(* (paper Equations (32)-(35), with the explicit formulas (18)-(19)).        *)
(* ========================================================================= *)

needs "src/catalan_nv_base.ml";;
needs "src/catalan_nv_iface.ml";;
needs "src/catalan_nv_dig_k.ml";;

let NV_DIG_C_PINT = prove
 (`forall p l. prime p /\ ~(p = 2) ==> nv_pint p (cat_c l)`,
  SIMP_TAC[GSYM NV_DIG_ZP_PINT; NV_DIG_FIN_DIG_C_ZP]);;

let NV_DIG_ECOEF = prove
 (`forall p d. prime p /\ ~(p = 2) /\ d < p ==> nv_cong p (nv_Ecoef p d) (nv_E d)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[nv_Ecoef; nv_E] THEN COND_CASES_TAC THENL
   [MATCH_MP_TAC NV_DIG_CG_CONG THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(SPECL [`p:num`; `d:num`] NV_DIG_FIN_DIG_E_CG) THEN ASM_REWRITE_TAC[nv_dig_fin_E];
    ASM_SIMP_TAC[NV_CONG_REFL]]);;

let NV_DIG_DECOMP = prove
 (`forall p z. prime p /\ 260 < p /\ z <= 65 * p
         ==> exists s P r. 2 * s + 1 = p /\ P + 2 < p /\ r < p /\ z = P * p + r /\
                     z DIV p = P /\ z MOD p = r`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `p:num` NV_DIG_FIN_DIG_C_ODD) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `s:num` (ASSUME_TAC o SYM)) THEN
  MAP_EVERY EXISTS_TAC [`s:num`; `z DIV p`; `z MOD p`] THEN
  SUBGOAL_THEN `~(p = 0)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `z DIV p < 66` ASSUME_TAC THENL
   [ASM_SIMP_TAC[RDIV_LT_EQ] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[DIVISION] THEN ASM_ARITH_TAC);;

let NV_DIG_M = prove
 (`forall p z. prime p /\ 260 < p /\ 1 <= z /\ z <= 65 * p
         ==> nv_pint p (if z DIV p = 0 then &0 else cat_m (z DIV p - 1)) /\
             nv_cong p (&p * cat_m (z - 1))
               (nv_E (p - 1 - z MOD p) *
                (if z DIV p = 0 then &0 else cat_m (z DIV p - 1)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`p:num`; `z:num`] NV_DIG_DECOMP) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `s:num` (X_CHOOSE_THEN `P:num`
    (X_CHOOSE_THEN `r:num` STRIP_ASSUME_TAC))) THEN
  REWRITE_TAC[ASSUME `z DIV p = P`; ASSUME `z MOD p = r`] THEN
  REWRITE_TAC[ASSUME `z = P * p + (r:num)`] THEN
  MP_TAC(SPECL [`p:num`; `s:num`; `P:num`; `r:num`] NV_DIG_M_FIN) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[NV_DIG_ZP_PINT] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC NV_DIG_CG_CONG THEN ASM_REWRITE_TAC[]);;

let NV_DIG_KMINUS = prove
 (`forall p u. prime p /\ 260 < p /\ u <= 65 * p
         ==> nv_pint p (cat_kminus (u DIV p)) /\
             nv_cong p (&p pow 2 * cat_kminus u)
               (nv_E (p - 1 - u MOD p) * cat_kminus (u DIV p))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`p:num`; `u:num`] NV_DIG_DECOMP) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `s:num` (X_CHOOSE_THEN `P:num`
    (X_CHOOSE_THEN `r:num` STRIP_ASSUME_TAC))) THEN
  REWRITE_TAC[ASSUME `u DIV p = P`; ASSUME `u MOD p = r`] THEN
  REWRITE_TAC[ASSUME `u = P * p + (r:num)`] THEN
  MP_TAC(SPECL [`p:num`; `s:num`; `P:num`; `r:num`] NV_DIG_KM_FIN) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[NV_DIG_ZP_PINT] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC NV_DIG_CG_CONG THEN ASM_REWRITE_TAC[]);;

let NV_DIG_KPLUS = prove
 (`forall p u. prime p /\ 260 < p /\ u <= 65 * p
         ==> nv_pint p (cat_kplus (u DIV p + 1)) /\
             nv_cong p (&p pow 2 * cat_kplus (u + 1))
               (nv_E (u MOD p) * cat_kplus (u DIV p + 1))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`p:num`; `u:num`] NV_DIG_DECOMP) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `s:num` (X_CHOOSE_THEN `P:num`
    (X_CHOOSE_THEN `r:num` STRIP_ASSUME_TAC))) THEN
  REWRITE_TAC[ASSUME `u DIV p = P`; ASSUME `u MOD p = r`] THEN
  REWRITE_TAC[ASSUME `u = P * p + (r:num)`] THEN
  MP_TAC(SPECL [`p:num`; `s:num`; `P:num`; `r:num`] NV_DIG_KP_FIN) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[NV_DIG_ZP_PINT] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC NV_DIG_CG_CONG THEN ASM_REWRITE_TAC[]);;

let NV_DIG_IF_C_PINT = prove
 (`nv_if_c_pint`,
  REWRITE_TAC[nv_if_c_pint; NV_DIG_C_PINT]);;

let NV_DIG_IF_ECOEF = prove
 (`nv_if_ecoef`,
  REWRITE_TAC[nv_if_ecoef; NV_DIG_ECOEF]);;
