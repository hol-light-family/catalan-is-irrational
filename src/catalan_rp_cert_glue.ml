(* ========================================================================= *)
(* CERT / GLUE: derivatives of rp_X, rp_Y in rational form.                 *)
(* ========================================================================= *)

needs "src/catalan_rp_cert_ser.ml";;
needs "src/catalan_rp_cert_poly.ml";;
needs "src/catalan_rp_cert_sup.ml";;

let RP_CERT_GLUE_LOGABS = prove
 (`forall x. ~(x = &0) ==> ((\x. log(abs x)) has_real_derivative inv x) (atreal x)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < x \/ x < &0` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC HAS_REAL_DERIVATIVE_TRANSFORM_ATREAL THEN
    EXISTS_TAC `\x. log x` THEN EXISTS_TAC `x:real` THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN AP_TERM_TAC THEN ASM_REAL_ARITH_TAC;
                    REWRITE_TAC[ETA_AX] THEN ASM_SIMP_TAC[HAS_REAL_DERIVATIVE_LOG]];
    MATCH_MP_TAC HAS_REAL_DERIVATIVE_TRANSFORM_ATREAL THEN
    EXISTS_TAC `\x. log(--x)` THEN EXISTS_TAC `--x:real` THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL [REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN AP_TERM_TAC THEN ASM_REAL_ARITH_TAC;
                    ALL_TAC] THEN
    REAL_DIFF_TAC THEN ASM_REWRITE_TAC[REAL_ARITH `&0 < --x <=> x < &0`] THEN
    REWRITE_TAC[REAL_INV_NEG] THEN REAL_ARITH_TAC]);;

let RP_CERT_GLUE_W_DERIV = prove
 (`forall kappa lam x. ~(x = &0) /\ x < &1
     ==> ((\x. &19 / &48 * log(abs x) + &1 / &12 * log(&1 - x) -
               (kappa / &2 + &17 / &48) * log(&1 + x pow 2) +
               lam * (&1 / &6 - &2 * x pow 2 / (&1 + x pow 2)))
          has_real_derivative
          (&19 / &48 * inv x - &1 / &12 * inv(&1 - x) -
           (kappa / &2 + &17 / &48) * (&2 * x / (&1 + x pow 2)) -
           lam * (&4 * x / (&1 + x pow 2) pow 2))) (atreal x)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < &1 + x pow 2` ASSUME_TAC THENL
   [MP_TAC(SPEC `x:real` REAL_LE_POW_2) THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < x \/ x < &0` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC HAS_REAL_DERIVATIVE_TRANSFORM_ATREAL THEN
    EXISTS_TAC `\x. &19 / &48 * log(x) + &1 / &12 * log(&1 - x) -
               (kappa / &2 + &17 / &48) * log(&1 + x pow 2) +
               lam * (&1 / &6 - &2 * x pow 2 / (&1 + x pow 2))` THEN
    EXISTS_TAC `x:real` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
      SUBGOAL_THEN `abs x' = x'` (fun th -> REWRITE_TAC[th]) THEN ASM_REAL_ARITH_TAC;
      REAL_DIFF_TAC THEN ASM_REWRITE_TAC[REAL_SUB_LT] THEN
      SUBGOAL_THEN `~(&1 - x = &0) /\ ~(&1 + x pow 2 = &0)` MP_TAC THENL
       [ASM_REAL_ARITH_TAC; CONV_TAC REAL_FIELD]];
    MATCH_MP_TAC HAS_REAL_DERIVATIVE_TRANSFORM_ATREAL THEN
    EXISTS_TAC `\x. &19 / &48 * log(--x) + &1 / &12 * log(&1 - x) -
               (kappa / &2 + &17 / &48) * log(&1 + x pow 2) +
               lam * (&1 / &6 - &2 * x pow 2 / (&1 + x pow 2))` THEN
    EXISTS_TAC `--x:real` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
      SUBGOAL_THEN `abs x' = --x'` (fun th -> REWRITE_TAC[th]) THEN ASM_REAL_ARITH_TAC;
      REAL_DIFF_TAC THEN ASM_REWRITE_TAC[REAL_SUB_LT] THEN
      SUBGOAL_THEN `&0 < --x /\ ~(x = &0) /\ ~(&1 - x = &0) /\ ~(&1 + x pow 2 = &0)` MP_TAC THENL
       [ASM_REAL_ARITH_TAC; CONV_TAC REAL_FIELD]]]);;

let RP_CERT_GLUE_X_DERIV = prove
 (`forall kappa lam lp tp lv tv x.
     rp_cert_ok tp /\ rp_cert_ok tv /\ --(&1) < x /\ x < &1 /\ ~(x = &0)
     ==> (rp_X kappa lam (rp_cert_seq lp tp) (rp_cert_seq lv tv) has_real_derivative
          ((&19 / &48 * inv x - &1 / &12 * inv(&1 - x) -
            (kappa / &2 + &17 / &48) * (&2 * x / (&1 + x pow 2)) -
            lam * (&4 * x / (&1 + x pow 2) pow 2)) -
           &2 * kappa * (sum (1..LENGTH lp) (\k. EL (k - 1) lp * rp_cert_chebu (k - 1) x) +
                         rp_cert_dttail tp x) -
           (sum (1..LENGTH lv) (\k. EL (k - 1) lv * x pow (k - 1)) + rp_cert_dstail tv x)))
         (atreal x)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `rp_X kappa lam (rp_cert_seq lp tp) (rp_cert_seq lv tv) =
     (\x. (&19 / &48 * log(abs x) + &1 / &12 * log(&1 - x) -
               (kappa / &2 + &17 / &48) * log(&1 + x pow 2) +
               lam * (&1 / &6 - &2 * x pow 2 / (&1 + x pow 2))) -
          &2 * kappa * rp_Tser (rp_cert_seq lp tp) x - rp_Sser (rp_cert_seq lv tv) x)`
    SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; rp_X] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC HAS_REAL_DERIVATIVE_SUB THEN CONJ_TAC THENL
   [MATCH_MP_TAC HAS_REAL_DERIVATIVE_SUB THEN CONJ_TAC THENL
     [MP_TAC(SPECL [`kappa:real`; `lam:real`; `x:real`] RP_CERT_GLUE_W_DERIV) THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC HAS_REAL_DERIVATIVE_LMUL_ATREAL THEN
      MATCH_MP_TAC HAS_REAL_DERIVATIVE_LMUL_ATREAL THEN
      REWRITE_TAC[ETA_AX] THEN ASM_SIMP_TAC[RP_CERT_ST_DERIV_AT]];
    REWRITE_TAC[ETA_AX] THEN ASM_SIMP_TAC[RP_CERT_SS_DERIV_AT]]);;

let RP_CERT_GLUE_Y_DERIV = prove
 (`forall lv tv s.
     rp_cert_ok tv /\ &0 < s /\ s < &1
     ==> (rp_Y (rp_cert_seq lv tv) has_real_derivative
          ((&7 / &48 * inv s - &1 / &12 * inv(&1 - s)) +
           &2 * (sum (1..LENGTH lv) (\k. EL (k - 1) lv * rp_cert_chebu (k - 1) s) +
                 rp_cert_dttail tv s))) (atreal s)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `rp_Y (rp_cert_seq lv tv) =
     (\s. (&7 / &48 * log s + &1 / &12 * log(&1 - s)) + &2 * rp_Tser (rp_cert_seq lv tv) s)`
    SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; rp_Y] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC HAS_REAL_DERIVATIVE_ADD THEN CONJ_TAC THENL
   [REAL_DIFF_TAC THEN ASM_REWRITE_TAC[REAL_SUB_LT] THEN REAL_ARITH_TAC;
    MATCH_MP_TAC HAS_REAL_DERIVATIVE_LMUL_ATREAL THEN
    REWRITE_TAC[ETA_AX] THEN MATCH_MP_TAC RP_CERT_ST_DERIV_AT THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]);;

(* rational forms of the tail derivative terms *)
let RP_CERT_GLUE_RE_TDIV = prove
 (`forall c z x. Re(c * z / (Cx(&1) - Cx(&2 * x) * z + z pow 2)) =
     (Re(c * z) * (&1 - &2 * x * Re z + Re(z pow 2)) +
      Im(c * z) * (Im(z pow 2) - &2 * x * Im z)) /
     ((&1 - &2 * x * Re z + Re(z pow 2)) pow 2 + (Im(z pow 2) - &2 * x * Im z) pow 2)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[complex_div; COMPLEX_MUL_ASSOC] THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [complex_mul] THEN
  REWRITE_TAC[complex_inv; RE; IM] THEN
  REWRITE_TAC[RE_ADD; RE_SUB; IM_ADD; IM_SUB; RE_CX; IM_CX; RE_MUL_CX; IM_MUL_CX] THEN
  REWRITE_TAC[real_div] THEN REAL_ARITH_TAC);;

let RP_CERT_GLUE_RE_SDIV = prove
 (`forall c z x. Re(c * z / (Cx(&1) - Cx x * z)) =
     (Re(c * z) * (&1 - x * Re z) + Im(c * z) * (--(x * Im z))) /
     ((&1 - x * Re z) pow 2 + (--(x * Im z)) pow 2)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[complex_div; COMPLEX_MUL_ASSOC] THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [complex_mul] THEN
  REWRITE_TAC[complex_inv; RE; IM] THEN
  REWRITE_TAC[RE_ADD; RE_SUB; IM_ADD; IM_SUB; RE_CX; IM_CX; RE_MUL_CX; IM_MUL_CX] THEN
  REWRITE_TAC[real_div] THEN REAL_ARITH_TAC);;

let RP_CERT_GLUE_RE_TDIV_REAL = prove
 (`forall a r x. Re(Cx a * Cx r / (Cx(&1) - Cx(&2 * x) * Cx r + Cx r pow 2)) =
           (a * r) / (&1 - &2 * x * r + r pow 2)`,
  REWRITE_TAC[GSYM CX_MUL; GSYM CX_POW; GSYM CX_SUB; GSYM CX_ADD; GSYM CX_DIV; RE_CX] THEN
  REWRITE_TAC[real_div; REAL_MUL_ASSOC]);;

let RP_CERT_GLUE_RE_SDIV_REAL = prove
 (`forall a r x. Re(Cx a * Cx r / (Cx(&1) - Cx x * Cx r)) = (a * r) / (&1 - x * r)`,
  REWRITE_TAC[GSYM CX_MUL; GSYM CX_SUB; GSYM CX_DIV; RE_CX] THEN
  REWRITE_TAC[real_div; REAL_MUL_ASSOC]);;

(* fractions over a common denominator *)
let RP_CERT_GLUE_FRAC_TERM = prove
 (`forall n d r q x. rp_cert_poly_mul d r = q /\ ~(rp_cert_peval q x = &0)
     ==> rp_cert_peval n x / rp_cert_peval d x =
         rp_cert_peval (rp_cert_poly_mul n r) x / rp_cert_peval q x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `~(rp_cert_peval q x = &0)` THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[RP_CERT_POLY_EVAL_MUL; REAL_ENTIRE; DE_MORGAN_THM] THEN CONV_TAC REAL_FIELD);;

let RP_CERT_GLUE_FRAC_ADD = prove
 (`forall a b q x. rp_cert_peval a x / rp_cert_peval q x + rp_cert_peval b x / rp_cert_peval q x =
             rp_cert_peval (rp_cert_poly_add a b) x / rp_cert_peval q x`,
  REWRITE_TAC[RP_CERT_POLY_EVAL_ADD; real_div] THEN REAL_ARITH_TAC);;

let RP_CERT_GLUE_FRAC_CMUL = prove
 (`forall k n d x. k * (rp_cert_peval n x / rp_cert_peval d x) =
             rp_cert_peval (rp_cert_poly_cmul k n) x / rp_cert_peval d x`,
  REWRITE_TAC[RP_CERT_POLY_EVAL_CMUL; real_div; REAL_MUL_ASSOC]);;

let RP_CERT_GLUE_FRAC_POLY = prove
 (`forall p q x. ~(rp_cert_peval q x = &0)
     ==> rp_cert_peval p x = rp_cert_peval (rp_cert_poly_mul p q) x / rp_cert_peval q x`,
  REWRITE_TAC[RP_CERT_POLY_EVAL_MUL] THEN CONV_TAC REAL_FIELD);;

let RP_CERT_GLUE_FRAC_SCALE = prove
 (`forall a q s x. &0 < s
     ==> rp_cert_peval a x / rp_cert_peval q x =
         rp_cert_peval (rp_cert_poly_cmul s a) x / (s * rp_cert_peval q x)`,
  REWRITE_TAC[RP_CERT_POLY_EVAL_CMUL] THEN REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `rp_cert_peval q x = &0` THEN
  ASM_REWRITE_TAC[real_div; REAL_MUL_RZERO; REAL_INV_0] THEN
  UNDISCH_TAC `&0 < s` THEN UNDISCH_TAC `~(rp_cert_peval q x = &0)` THEN
  CONV_TAC REAL_FIELD);;

(* finite trial sequences: closed forms and derivatives for every x *)
let RP_CERT_GLUE_TSER_FIN = prove
 (`forall l x. rp_Tser (rp_cert_seq l []) x = sum (1..LENGTH l) (\k. EL (k - 1) l * rp_cheb k x / &k)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[rp_Tser; rp_cert_seq; rp_cert_tail; REAL_ADD_RID] THEN
  MATCH_MP_TAC REAL_INFSUM_UNIQUE THEN
  MP_TAC(ISPECL [`l:real list`; `\k. rp_cheb k x / &k`] RP_CERT_SER_FIN_PART) THEN
  REWRITE_TAC[]);;

let RP_CERT_GLUE_SSER_FIN = prove
 (`forall l x. rp_Sser (rp_cert_seq l []) x = sum (1..LENGTH l) (\k. EL (k - 1) l * x pow k / &k)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[rp_Sser; rp_cert_seq; rp_cert_tail; REAL_ADD_RID] THEN
  MATCH_MP_TAC REAL_INFSUM_UNIQUE THEN
  MP_TAC(ISPECL [`l:real list`; `\k. x pow k / &k`] RP_CERT_SER_FIN_PART) THEN
  REWRITE_TAC[]);;

let RP_CERT_GLUE_X_DERIV_FIN = prove
 (`forall kappa lam lp lv x. x < &1 /\ ~(x = &0)
     ==> (rp_X kappa lam (rp_cert_seq lp []) (rp_cert_seq lv []) has_real_derivative
          ((&19 / &48 * inv x - &1 / &12 * inv(&1 - x) -
            (kappa / &2 + &17 / &48) * (&2 * x / (&1 + x pow 2)) -
            lam * (&4 * x / (&1 + x pow 2) pow 2)) -
           &2 * kappa * (sum (1..LENGTH lp) (\k. EL (k - 1) lp * rp_cert_chebu (k - 1) x) +
                         rp_cert_dttail [] x) -
           (sum (1..LENGTH lv) (\k. EL (k - 1) lv * x pow (k - 1)) + rp_cert_dstail [] x)))
         (atreal x)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[rp_cert_dttail; rp_cert_dstail; REAL_ADD_RID] THEN
  SUBGOAL_THEN `rp_X kappa lam (rp_cert_seq lp []) (rp_cert_seq lv []) =
     (\x. (&19 / &48 * log(abs x) + &1 / &12 * log(&1 - x) -
               (kappa / &2 + &17 / &48) * log(&1 + x pow 2) +
               lam * (&1 / &6 - &2 * x pow 2 / (&1 + x pow 2))) -
          &2 * kappa * sum (1..LENGTH lp) (\k. EL (k - 1) lp * rp_cheb k x / &k) -
          sum (1..LENGTH lv) (\k. EL (k - 1) lv * x pow k / &k))`
    SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; rp_X; RP_CERT_GLUE_TSER_FIN; RP_CERT_GLUE_SSER_FIN] THEN
    REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC HAS_REAL_DERIVATIVE_SUB THEN CONJ_TAC THENL
   [MATCH_MP_TAC HAS_REAL_DERIVATIVE_SUB THEN CONJ_TAC THENL
     [MP_TAC(SPECL [`kappa:real`; `lam:real`; `x:real`] RP_CERT_GLUE_W_DERIV) THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC HAS_REAL_DERIVATIVE_LMUL_ATREAL THEN
      MATCH_MP_TAC HAS_REAL_DERIVATIVE_LMUL_ATREAL THEN
      REWRITE_TAC[RP_CERT_SER_TFIN_DERIV]];
    REWRITE_TAC[RP_CERT_SER_SFIN_DERIV]]);;
