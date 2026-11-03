(* ========================================================================= *)
(* CERT / SUP: from derivative signs on gaps and bracket estimates to       *)
(* global upper bounds (paper Section 7.4).                                 *)
(* ========================================================================= *)

needs "src/catalan_rp_cert_poly.ml";;

let RP_CERT_SUP_CONT_ON = prove
 (`forall f g (u:real) v x.
     u <= x /\ x < v /\
     (forall y. u < y /\ y < v ==> (f has_real_derivative g y) (atreal y)) /\
     (forall y. u <= y /\ y < v ==> f real_continuous (atreal y within real_interval[u,v])) /\
     f real_continuous (atreal v within real_interval[u,v])
     ==> f real_continuous_on real_interval[x,v]`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[REAL_CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN] THEN
  X_GEN_TAC `y:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
  MATCH_MP_TAC REAL_CONTINUOUS_WITHINREAL_SUBSET THEN
  EXISTS_TAC `real_interval[u,v]` THEN
  REWRITE_TAC[SUBSET_REAL_INTERVAL] THEN
  CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
  ASM_CASES_TAC `y:real = v` THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC);;

(* increasing on (u,v), continuous at v from the left: f <= f(v) on (u,v] *)
let RP_CERT_SUP_INC = prove
 (`forall f g (u:real) v.
     (forall y. u < y /\ y < v ==> (f has_real_derivative g y) (atreal y) /\ &0 < g y) /\
     f real_continuous (atreal v within real_interval[u,v])
     ==> forall x. u < x /\ x <= v ==> f x <= f v`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `x:real = v` THEN
  ASM_REWRITE_TAC[REAL_LE_REFL] THEN
  MP_TAC(SPECL [`f:real->real`; `g:real->real`; `x:real`; `v:real`] REAL_MVT) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      REWRITE_TAC[REAL_CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN; IN_REAL_INTERVAL] THEN
      X_GEN_TAC `y:real` THEN STRIP_TAC THEN
      ASM_CASES_TAC `y:real = v` THENL
       [MATCH_MP_TAC REAL_CONTINUOUS_WITHINREAL_SUBSET THEN
        EXISTS_TAC `real_interval[u,v]` THEN
        ASM_REWRITE_TAC[SUBSET_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_CONTINUOUS_ATREAL_WITHINREAL THEN
        MATCH_MP_TAC HAS_REAL_DERIVATIVE_IMP_CONTINUOUS_ATREAL THEN
        EXISTS_TAC `(g:real->real) y` THEN
        FIRST_X_ASSUM(MP_TAC o SPEC `y:real`) THEN
        ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]]];
      REWRITE_TAC[IN_REAL_INTERVAL] THEN REPEAT STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `x':real`) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]]];
    REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x':real`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
    SUBGOAL_THEN `&0 <= (g:real->real) x' * (v - x)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC]]);;

(* decreasing on (u,v), continuous at u from the right: f <= f(u) on [u,v) *)
let RP_CERT_SUP_DEC = prove
 (`forall f g (u:real) v.
     (forall y. u < y /\ y < v ==> (f has_real_derivative g y) (atreal y) /\ g y < &0) /\
     f real_continuous (atreal u within real_interval[u,v])
     ==> forall x. u <= x /\ x < v ==> f x <= f u`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `x:real = u` THEN
  ASM_REWRITE_TAC[REAL_LE_REFL] THEN
  MP_TAC(SPECL [`f:real->real`; `g:real->real`; `u:real`; `x:real`] REAL_MVT) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      REWRITE_TAC[REAL_CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN; IN_REAL_INTERVAL] THEN
      X_GEN_TAC `y:real` THEN STRIP_TAC THEN
      ASM_CASES_TAC `y:real = u` THENL
       [MATCH_MP_TAC REAL_CONTINUOUS_WITHINREAL_SUBSET THEN
        EXISTS_TAC `real_interval[u,v]` THEN
        ASM_REWRITE_TAC[SUBSET_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_CONTINUOUS_ATREAL_WITHINREAL THEN
        MATCH_MP_TAC HAS_REAL_DERIVATIVE_IMP_CONTINUOUS_ATREAL THEN
        EXISTS_TAC `(g:real->real) y` THEN
        FIRST_X_ASSUM(MP_TAC o SPEC `y:real`) THEN
        ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]]];
      REWRITE_TAC[IN_REAL_INTERVAL] THEN REPEAT STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `x':real`) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]]];
    REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x':real`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
    SUBGOAL_THEN `(g:real->real) x' * (x - u) <= &0` MP_TAC THENL
     [REWRITE_TAC[REAL_ARITH `a * b <= &0 <=> &0 <= --a * b`] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC]]);;

(* bracket: |f'| <= L on [m, m + w] *)
let RP_CERT_SUP_BRACKET = prove
 (`forall f g (m:real) w L.
     &0 < w /\
     (forall y. m <= y /\ y <= m + w ==> (f has_real_derivative g y) (atreal y) /\ abs(g y) <= L)
     ==> forall x. m <= x /\ x <= m + w ==> f x <= f m + L * w`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `x:real = m` THENL
   [ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= a ==> b <= b + a`) THEN
    MATCH_MP_TAC REAL_LE_MUL THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `m:real`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC]; ALL_TAC] THEN
  MP_TAC(SPECL [`f:real->real`; `g:real->real`; `m:real`; `x:real`] REAL_MVT) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      REWRITE_TAC[REAL_CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN; IN_REAL_INTERVAL] THEN
      X_GEN_TAC `y:real` THEN STRIP_TAC THEN
      MATCH_MP_TAC REAL_CONTINUOUS_ATREAL_WITHINREAL THEN
      MATCH_MP_TAC HAS_REAL_DERIVATIVE_IMP_CONTINUOUS_ATREAL THEN
      EXISTS_TAC `(g:real->real) y` THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `y:real`) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
      REWRITE_TAC[IN_REAL_INTERVAL] THEN REPEAT STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `x':real`) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]]];
    REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x':real`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
    SUBGOAL_THEN `abs((g:real->real) x' * (x - m)) <= L * w` MP_TAC THENL
     [REWRITE_TAC[REAL_ABS_MUL] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
      ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC]]);;

(* closed versions: continuity at both ends *)
let RP_CERT_SUP_CONT_CLOSED = prove
 (`forall f g (u:real) v.
     (forall y. u < y /\ y < v ==> (f has_real_derivative g y) (atreal y)) /\
     f real_continuous (atreal u within real_interval[u,v]) /\
     f real_continuous (atreal v within real_interval[u,v])
     ==> forall a b. u <= a /\ b <= v ==> f real_continuous_on real_interval[a,b]`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[REAL_CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN; IN_REAL_INTERVAL] THEN
  X_GEN_TAC `y:real` THEN STRIP_TAC THEN
  ASM_CASES_TAC `y:real = u` THENL
   [MATCH_MP_TAC REAL_CONTINUOUS_WITHINREAL_SUBSET THEN EXISTS_TAC `real_interval[u,v]` THEN
    ASM_REWRITE_TAC[SUBSET_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `y:real = v` THENL
   [MATCH_MP_TAC REAL_CONTINUOUS_WITHINREAL_SUBSET THEN EXISTS_TAC `real_interval[u,v]` THEN
    ASM_REWRITE_TAC[SUBSET_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_CONTINUOUS_ATREAL_WITHINREAL THEN
  MATCH_MP_TAC HAS_REAL_DERIVATIVE_IMP_CONTINUOUS_ATREAL THEN
  EXISTS_TAC `(g:real->real) y` THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC);;

let RP_CERT_SUP_INC2 = prove
 (`forall f g (u:real) v.
     (forall y. u < y /\ y < v ==> (f has_real_derivative g y) (atreal y) /\ &0 < g y) /\
     f real_continuous (atreal u within real_interval[u,v]) /\
     f real_continuous (atreal v within real_interval[u,v])
     ==> forall x. u <= x /\ x <= v ==> f x <= f v`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `x:real` THEN STRIP_TAC THEN
  ASM_CASES_TAC `x:real = v` THEN ASM_REWRITE_TAC[REAL_LE_REFL] THEN
  MP_TAC(SPECL [`f:real->real`; `g:real->real`; `x:real`; `v:real`] REAL_MVT) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN CONJ_TAC THENL
     [MP_TAC(SPECL [`f:real->real`; `g:real->real`; `u:real`; `v:real`] RP_CERT_SUP_CONT_CLOSED) THEN
      ASM_SIMP_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[IN_REAL_INTERVAL] THEN REPEAT STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `x':real`) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]]];
    REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x':real`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
    SUBGOAL_THEN `&0 <= (g:real->real) x' * (v - x)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC]]);;

let RP_CERT_SUP_DEC2 = prove
 (`forall f g (u:real) v.
     (forall y. u < y /\ y < v ==> (f has_real_derivative g y) (atreal y) /\ g y < &0) /\
     f real_continuous (atreal u within real_interval[u,v]) /\
     f real_continuous (atreal v within real_interval[u,v])
     ==> forall x. u <= x /\ x <= v ==> f x <= f u`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `x:real` THEN STRIP_TAC THEN
  ASM_CASES_TAC `x:real = u` THEN ASM_REWRITE_TAC[REAL_LE_REFL] THEN
  MP_TAC(SPECL [`f:real->real`; `g:real->real`; `u:real`; `x:real`] REAL_MVT) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN CONJ_TAC THENL
     [MP_TAC(SPECL [`f:real->real`; `g:real->real`; `u:real`; `v:real`] RP_CERT_SUP_CONT_CLOSED) THEN
      ASM_SIMP_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[IN_REAL_INTERVAL] THEN REPEAT STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `x':real`) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]]];
    REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x':real`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
    SUBGOAL_THEN `(g:real->real) x' * (x - u) <= &0` MP_TAC THENL
     [REWRITE_TAC[REAL_ARITH `a * b <= &0 <=> &0 <= --a * b`] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC]]);;

(* constant sign of a root-free polynomial *)
let RP_CERT_SUP_GAPSIGN = prove
 (`forall p u v. (forall y. u <= y /\ y <= v ==> ~(rp_cert_peval p y = &0)) /\ u <= v
     ==> (&0 < rp_cert_peval p u ==> forall y. u <= y /\ y <= v ==> &0 < rp_cert_peval p y) /\
         (rp_cert_peval p u < &0 ==> forall y. u <= y /\ y <= v ==> rp_cert_peval p y < &0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THEN DISCH_TAC THEN
  X_GEN_TAC `y:real` THEN STRIP_TAC THEN
  (SUBGOAL_THEN `~(rp_cert_peval p y = &0)` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC]) THEN
  MATCH_MP_TAC(TAUT `(~a ==> false) ==> a`) THEN DISCH_TAC THEN
  MP_TAC(SPECL [`p:real list`; `u:real`; `y:real`] RP_CERT_POLY_IVT) THEN
  (ANTS_TAC THENL
    [ASM_REWRITE_TAC[] THEN
     (SUBGOAL_THEN `(&0 < rp_cert_peval p u /\ rp_cert_peval p y < &0) \/
                   (rp_cert_peval p u < &0 /\ &0 < rp_cert_peval p y)` MP_TAC THENL
      [ASM_REAL_ARITH_TAC; ALL_TAC]) THEN
     STRIP_TAC THEN
     MATCH_MP_TAC REAL_LT_IMP_LE THEN
     ASM_MESON_TAC[REAL_MUL_POS_LT; REAL_ARITH `forall a b:real. a * b < &0 <=> &0 < --(a * b)`;
                   REAL_MUL_RNEG; REAL_MUL_LNEG; REAL_LT_MUL; REAL_ARITH `forall a:real. &0 < --a <=> a < &0`];
     ALL_TAC]) THEN
  STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `x:real`) THEN
  (ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[]]));;

let RP_CERT_SUP_EXTEND = prove
 (`forall P (a:real) b c B.
     (forall x. a < x /\ x <= b ==> P x <= B) /\ (forall x. b <= x /\ x <= c ==> P x <= B)
     ==> (forall x. a < x /\ x <= c ==> P x <= B)`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `x <= b` THEN
  ASM_MESON_TAC[REAL_LE_TOTAL]);;

let RP_CERT_SUP_EXTEND_C = prove
 (`forall P (a:real) b c B.
     (forall x. a <= x /\ x <= b ==> P x <= B) /\ (forall x. b <= x /\ x <= c ==> P x <= B)
     ==> (forall x. a <= x /\ x <= c ==> P x <= B)`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `x <= b` THEN
  ASM_MESON_TAC[REAL_LE_TOTAL]);;

let RP_CERT_SUP_EXTEND_LAST = prove
 (`forall P (a:real) b c B.
     (forall x. a < x /\ x <= b ==> P x <= B) /\ (forall x. b <= x /\ x < c ==> P x <= B)
     ==> (forall x. a < x /\ x < c ==> P x <= B)`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `x <= b` THEN
  ASM_MESON_TAC[REAL_LE_TOTAL; REAL_LT_IMP_LE]);;

let RP_CERT_SUP_EXTEND_LAST_C = prove
 (`forall P (a:real) b c B.
     (forall x. a <= x /\ x <= b ==> P x <= B) /\ (forall x. b <= x /\ x < c ==> P x <= B)
     ==> (forall x. a <= x /\ x < c ==> P x <= B)`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `x <= b` THEN
  ASM_MESON_TAC[REAL_LE_TOTAL; REAL_LT_IMP_LE]);;

let RP_CERT_SUP_EXCL = prove
 (`forall p (b:real) c r.
     (forall x y. b < x /\ x < y /\ y < c /\ rp_cert_peval p x = &0 /\ rp_cert_peval p y = &0 ==> false) /\
     b < r /\ r < c /\ rp_cert_peval p r = &0
     ==> forall y. b < y /\ y < c /\ ~(y = r) ==> ~(rp_cert_peval p y = &0)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `y < r \/ r < y` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ASM_MESON_TAC[]; ASM_MESON_TAC[]]);;




let RP_CERT_SUP_BRK_DERIV = rp_cert_steps
 `forall a q s m w r ka kq q0 y.
     &0 < s /\ &0 < w /\ --(&1) <= m /\ m + w <= &1 /\
     m <= r /\ r <= m + w /\ rp_cert_peval a r = &0 /\ m <= y /\ y <= m + w /\
     rp_cert_poly_dnorm a <= ka /\ rp_cert_poly_dnorm q <= kq /\
     &0 < q0 /\ q0 <= abs(rp_cert_peval q m) - kq * w
     ==> abs(rp_cert_peval a y / (s * rp_cert_peval q y)) <= (ka * w) / (s * q0)`
 [(REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `abs y <= &1 /\ abs r <= &1 /\ abs m <= &1 /\ abs(y - r) <= w /\ abs(y - m) <= w`
    STRIP_ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC]);
  (SUBGOAL_THEN `abs(rp_cert_peval a y) <= ka * w` ASSUME_TAC THENL
   [MP_TAC(SPECL [`a:real list`; `y:real`; `r:real`] RP_CERT_POLY_LIPSCHITZ) THEN
    ASM_REWRITE_TAC[REAL_SUB_RZERO] THEN
    MP_TAC(SPECL [`rp_cert_poly_dnorm a`; `ka:real`; `abs(y - r)`; `w:real`] REAL_LE_MUL2) THEN
    ASM_REWRITE_TAC[RP_CERT_POLY_DNORM_POS; REAL_ABS_POS] THEN REAL_ARITH_TAC;
    ALL_TAC]);
  (SUBGOAL_THEN `q0 <= abs(rp_cert_peval q y)` ASSUME_TAC THENL
   [MP_TAC(SPECL [`q:real list`; `y:real`; `m:real`] RP_CERT_POLY_LIPSCHITZ) THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(SPECL [`rp_cert_poly_dnorm q`; `kq:real`; `abs(y - m)`; `w:real`] REAL_LE_MUL2) THEN
    ASM_REWRITE_TAC[RP_CERT_POLY_DNORM_POS; REAL_ABS_POS] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC]);
  (REWRITE_TAC[REAL_ABS_DIV; REAL_ABS_MUL; real_div] THEN
  SUBGOAL_THEN `abs s = s` SUBST1_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[REAL_ABS_POS; REAL_LE_INV_EQ] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_LE_INV2 THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC]])];;

let RP_CERT_SUP_SIGN_ON_GAP = prove
 (`forall p (u:real) v c.
     (forall y. u < y /\ y < v ==> ~(rp_cert_peval p y = &0)) /\ u <= c /\ c <= v
     ==> (&0 < rp_cert_peval p c ==> forall y. u < y /\ y < v ==> &0 < rp_cert_peval p y) /\
         (rp_cert_peval p c < &0 ==> forall y. u < y /\ y < v ==> rp_cert_peval p y < &0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THEN DISCH_TAC THEN
  X_GEN_TAC `y:real` THEN STRIP_TAC THEN
  ((SUBGOAL_THEN `~(rp_cert_peval p y = &0)` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC]) THEN
  MATCH_MP_TAC(TAUT `(~a ==> false) ==> a`) THEN DISCH_TAC) THEN
  ((SUBGOAL_THEN `rp_cert_peval p c * rp_cert_peval p y <= &0` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_IMP_LE THEN
    (SUBGOAL_THEN `(&0 < rp_cert_peval p c /\ rp_cert_peval p y < &0) \/
                   (rp_cert_peval p c < &0 /\ &0 < rp_cert_peval p y)` MP_TAC THENL
      [ASM_REAL_ARITH_TAC; ALL_TAC]) THEN
    ASM_MESON_TAC[REAL_MUL_POS_LT; REAL_ARITH `forall a b:real. a * b < &0 <=> &0 < --(a * b)`;
                  REAL_MUL_RNEG; REAL_MUL_LNEG; REAL_LT_MUL; REAL_ARITH `forall a:real. &0 < --a <=> a < &0`];
    ALL_TAC])) THEN
  (ASM_CASES_TAC `c <= y:real` THENL
   [MP_TAC(SPECL [`p:real list`; `c:real`; `y:real`] RP_CERT_POLY_IVT);
    MP_TAC(SPECL [`p:real list`; `y:real`; `c:real`] RP_CERT_POLY_IVT)]) THEN
  (ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC]) THEN
  (STRIP_TAC THEN
   (SUBGOAL_THEN `~(x:real = c)` ASSUME_TAC THENL
     [DISCH_THEN SUBST_ALL_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC]) THEN
   FIRST_X_ASSUM(MP_TAC o SPEC `x:real` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> t = `v:real`)) (concl th))) THEN
   ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC));;

let RP_CERT_SUP_POS_FROM_NOROOT = prove
 (`forall p (a:real) b c.
     (forall y. a < y /\ y < b ==> ~(rp_cert_peval p y = &0)) /\ a < c /\ c < b /\
     &0 < rp_cert_peval p c
     ==> forall y. a < y /\ y < b ==> &0 < rp_cert_peval p y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`p:real list`; `a:real`; `b:real`; `c:real`] RP_CERT_SUP_SIGN_ON_GAP) THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE]);;

let RP_CERT_SUP_QUOT_SIGN = prove
 (`forall a q s. &0 < s
     ==> (&0 < a * q ==> &0 < a / (s * q)) /\ (a * q < &0 ==> a / (s * q) < &0)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN CONJ_TAC THEN DISCH_TAC THEN
  (SUBGOAL_THEN `~(q:real = &0)` ASSUME_TAC THENL
    [DISCH_THEN SUBST_ALL_TAC THEN POP_ASSUM MP_TAC THEN REAL_ARITH_TAC; ALL_TAC]) THEN
  (SUBGOAL_THEN `(a:real) / ((s:real) * (q:real)) = (a * q) / (s * q pow 2)` SUBST1_TAC THENL
    [UNDISCH_TAC `~(q:real = &0)` THEN UNDISCH_TAC `&0 < (s:real)` THEN CONV_TAC REAL_FIELD; ALL_TAC]) THEN
  (SUBGOAL_THEN `&0 < (s:real) * (q:real) pow 2` ASSUME_TAC THENL
    [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[] THEN
     ASM_SIMP_TAC[REAL_LT_POW_2]; ALL_TAC]) THEN
  ASM_SIMP_TAC[REAL_LT_DIV; REAL_LT_LDIV_EQ; REAL_MUL_LZERO]);;

let RP_CERT_SUP_BRK_DERIV2 = prove
 (`forall a q s m w ka kq q0 y.
     &0 < s /\ &0 < w /\ --(&1) <= m /\ m + w <= &1 /\
     rp_cert_peval a m * rp_cert_peval a (m + w) <= &0 /\ m <= y /\ y <= m + w /\
     rp_cert_poly_dnorm a <= ka /\ rp_cert_poly_dnorm q <= kq /\
     &0 < q0 /\ q0 <= abs(rp_cert_peval q m) - kq * w
     ==> abs(rp_cert_peval a y / (s * rp_cert_peval q y)) <= (ka * w) / (s * q0)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`a:real list`; `m:real`; `m + w:real`] RP_CERT_POLY_IVT) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  MATCH_MP_TAC(SPECL [`a:real list`; `q:real list`; `s:real`; `m:real`; `w:real`; `x:real`]
    RP_CERT_SUP_BRK_DERIV) THEN
  EXISTS_TAC `kq:real` THEN ASM_REWRITE_TAC[]);;

let RP_CERT_SUP_BRK_EXCL = prove
 (`forall p (b:real) c m w.
     (forall x y. b < x /\ x < y /\ y < c /\ rp_cert_peval p x = &0 /\ rp_cert_peval p y = &0 ==> false) /\
     b < m /\ m + w < c /\ &0 < w /\ rp_cert_peval p m * rp_cert_peval p (m + w) < &0
     ==> forall y. b < y /\ y < c /\ (y < m \/ m + w < y) ==> ~(rp_cert_peval p y = &0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`p:real list`; `m:real`; `m + w:real`] RP_CERT_POLY_IVT) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  SUBGOAL_THEN `~(x:real = m) /\ ~(x = m + w)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC `rp_cert_peval p m * rp_cert_peval p (m + w) < &0` THEN
    ASM_REWRITE_TAC[REAL_MUL_LZERO; REAL_MUL_RZERO; REAL_LT_REFL]; ALL_TAC] THEN
  MP_TAC(SPECL [`p:real list`; `b:real`; `c:real`; `x:real`] RP_CERT_SUP_EXCL) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `y:real`) THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

let RP_CERT_SUP_COMB = prove
 (`forall P (u:real) c v.
     (forall y. u < y /\ y < c ==> P y) /\ P c /\ (forall y. c < y /\ y < v ==> P y)
     ==> forall y. u < y /\ y < v ==> P y`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `y < c \/ y = c \/ c < y` STRIP_ASSUME_TAC THENL
   [REAL_ARITH_TAC; ASM_MESON_TAC[]; ASM_MESON_TAC[]; ASM_MESON_TAC[]]);;

let RP_CERT_SUP_WEAKEN = prove
 (`forall P (b:real) c u v. (forall y. b < y /\ y < c ==> P y) /\ b <= u /\ v <= c
     ==> forall y. u < y /\ y < v ==> P y`,
  MESON_TAC[REAL_LET_TRANS; REAL_LTE_TRANS]);;

let RP_CERT_SUP_GSIGN = prove
 (`forall a q s u v ea eq.
     &0 < s /\ (forall y. u < y /\ y < v ==> &0 < ea * rp_cert_peval a y) /\
     (forall y. u < y /\ y < v ==> &0 < eq * rp_cert_peval q y) /\
     (ea = &1 \/ ea = --(&1)) /\ (eq = &1 \/ eq = --(&1))
     ==> forall y. u < y /\ y < v ==>
             &0 < (ea * eq) * (rp_cert_peval a y / (s * rp_cert_peval q y))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `y:real` THEN STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o SPEC `y:real` o check (is_forall o concl))) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`rp_cert_peval a y`; `rp_cert_peval q y`; `s:real`] RP_CERT_SUP_QUOT_SIGN) THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT(FIRST_X_ASSUM DISJ_CASES_TAC) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[REAL_MUL_LID; REAL_MUL_LNEG; REAL_MUL_RNEG; REAL_NEG_NEG; REAL_MUL_RID] THEN
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
  ASM_SIMP_TAC[REAL_LT_MUL; REAL_ARITH `forall x:real. &0 < --x <=> x < &0`] THEN
  TRY(DISCH_THEN MATCH_MP_TAC) THEN
  REPEAT(POP_ASSUM MP_TAC) THEN
  MESON_TAC[REAL_LT_MUL; REAL_MUL_LNEG; REAL_MUL_RNEG; REAL_NEG_NEG;
            REAL_ARITH `forall x:real. &0 < --x <=> x < &0`; REAL_NEG_MUL2]);;
