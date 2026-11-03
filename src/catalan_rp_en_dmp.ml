needs "src/catalan_rp_en_defs.ml";;

(* ========================================================================= *)
(* EN part: damping estimates (83)-(85) and diagonal bounds.                 *)
(* ========================================================================= *)

let RP_EN_DMP_LOG_LE_SUB1 = prove
 (`forall z. &0 < z ==> log z <= z - &1`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `z - &1` LOG_LE_STRONG) THEN
  REWRITE_TAC[REAL_ARITH `&1 + (z - &1) = z`] THEN ASM_REWRITE_TAC[]);;

let RP_EN_DMP_P_EQ = prove
 (`forall r u v. rp_en_P r u v =
           (&1 - r) pow 2 * ((&1 - r) pow 2 + &4 * r * (&1 - u * v)) +
           &4 * r pow 2 * (u - v) pow 2`,
  REWRITE_TAC[rp_en_P] THEN REAL_ARITH_TAC);;

let RP_EN_DMP_ONE_SUB_MUL = prove
 (`forall u v. abs u <= &1 /\ abs v <= &1 ==> &0 <= &1 - u * v`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `abs u * abs v <= &1 * &1` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[REAL_ABS_POS];
    REWRITE_TAC[GSYM REAL_ABS_MUL] THEN REAL_ARITH_TAC]);;

let RP_EN_DMP_P_LOWER = prove
 (`forall r u v. &0 <= r /\ r <= &1 /\ abs u <= &1 /\ abs v <= &1
         ==> (&1 - r) pow 4 <= rp_en_P r u v /\
             &4 * r pow 2 * (u - v) pow 2 <= rp_en_P r u v`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[RP_EN_DMP_P_EQ] THEN
  SUBGOAL_THEN `&0 <= &1 - u * v` ASSUME_TAC THENL
   [MATCH_MP_TAC RP_EN_DMP_ONE_SUB_MUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= (&1 - r) pow 2 * (&4 * r * (&1 - u * v))` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= &4 * r pow 2 * (u - v) pow 2` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_LE_POW_2];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= (&1 - r) pow 2 * (&1 - r) pow 2` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_LE_POW_2]; ALL_TAC] THEN
  REAL_ARITH_TAC);;

let RP_EN_DMP_COS_CMP = prove
 (`forall r u v. &0 < r /\ r <= &1 /\ abs u <= &1 /\ abs v <= &1 /\ ~(u = v)
         ==> log(abs(u - v)) <= rp_en_L r u v - log r`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`r:real`; `u:real`; `v:real`] RP_EN_DMP_P_LOWER) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  SUBGOAL_THEN `&0 < abs(u - v)` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&4 * r pow 2 * (u - v) pow 2 = (&2 * r * abs(u - v)) pow 2`
   SUBST_ALL_TAC THENL
   [REWRITE_TAC[REAL_POW_MUL; REAL_POW2_ABS] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &2 * r * abs(u - v)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `log((&2 * r * abs(u - v)) pow 2) <= log(rp_en_P r u v)`
   MP_TAC THENL
   [MATCH_MP_TAC LOG_MONO_LE_IMP THEN ASM_SIMP_TAC[REAL_POW_LT]; ALL_TAC] THEN
  ASM_SIMP_TAC[LOG_POW; LOG_MUL; REAL_LT_MUL; REAL_ARITH `&0 < &2`] THEN
  REWRITE_TAC[rp_en_L] THEN REAL_ARITH_TAC);;

let RP_EN_DMP_COS_DIAG = prove
 (`forall r u. &0 <= r /\ r < &1 /\ abs u <= &1
         ==> --log(&2) + &2 * log(&1 - r) <= rp_en_L r u u`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`r:real`; `u:real`; `u:real`] RP_EN_DMP_P_LOWER) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  SUBGOAL_THEN `&0 < &1 - r` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `log((&1 - r) pow 4) <= log(rp_en_P r u u)` MP_TAC THENL
   [MATCH_MP_TAC LOG_MONO_LE_IMP THEN ASM_SIMP_TAC[REAL_POW_LT]; ALL_TAC] THEN
  ASM_SIMP_TAC[LOG_POW] THEN REWRITE_TAC[rp_en_L] THEN REAL_ARITH_TAC);;

let RP_EN_DMP_LOGR = prove
 (`forall e r. &0 < e /\ e < &1 / &8 /\ (&1 - e) pow 2 <= r /\ r <= &1
         ==> --log r <= &4 * e`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&1 - &2 * e <= r` ASSUME_TAC THENL
   [MP_TAC(SPEC `e:real` REAL_LE_POW_2) THEN
    UNDISCH_TAC `(&1 - e) pow 2 <= r` THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < r` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPEC `inv(r:real)` RP_EN_DMP_LOG_LE_SUB1) THEN
  ASM_SIMP_TAC[REAL_LT_INV_EQ; LOG_INV] THEN
  MATCH_MP_TAC(REAL_ARITH `y <= z ==> x <= y ==> x <= z`) THEN
  REWRITE_TAC[REAL_ARITH `inv r - &1 <= &4 * e <=> inv r <= &1 + &4 * e`] THEN
  SUBGOAL_THEN `inv r = &1 / r` SUBST1_TAC THENL
   [REWRITE_TAC[real_div; REAL_MUL_LID]; ALL_TAC] THEN
   ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
  SUBGOAL_THEN `&0 <= e * (&1 - &4 * e)` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= e * (r - (&1 - &2 * e))` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Damping factor bounds and the power kernel (84).                          *)
(* ------------------------------------------------------------------------- *)

let RP_EN_DMP_RHO_BOUNDS = prove
 (`forall e x. &0 < e /\ e < &1 / &8 /\ --(&1) < x /\ x < &1
         ==> &1 - &2 * e < rp_en_rho e x /\ rp_en_rho e x < &1 /\
             &0 < rp_en_rho e x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[rp_en_rho] THEN
  SUBGOAL_THEN `&0 < e * (&1 - x) /\ &0 < e * (&1 + x)` MP_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

let RP_EN_DMP_POW_CORE = prove
 (`forall e q u. &0 < e /\ &0 < q /\ q <= &1 /\ &1 - q <= &4 * e /\ abs u < &1
           ==> log(&1 - u) <= log(&1 - q * u) + &4 * e`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `&0 <= u` THENL
   [SUBGOAL_THEN `log(&1 - u) <= log(&1 - q * u)` MP_TAC THENL
     [MATCH_MP_TAC LOG_MONO_LE_IMP THEN
      SUBGOAL_THEN `&0 <= (&1 - q) * u` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= q * --u` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &1 - q * u /\ &0 < &1 - u` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPEC `(&1 - u) / (&1 - q * u)` RP_EN_DMP_LOG_LE_SUB1) THEN
  ASM_SIMP_TAC[REAL_LT_DIV; LOG_DIV] THEN
  SUBGOAL_THEN `(&1 - u) / (&1 - q * u) <= &2 - q` MP_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
    SUBGOAL_THEN `&0 <= (&1 + u) * (&1 - q)` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= (&1 - q) * (&1 + u * (&1 - q))` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REAL_ARITH_TAC;
    ASM_REAL_ARITH_TAC]);;

let RP_EN_DMP_POW_CMP = prove
 (`forall e x y. &0 < e /\ e < &1 / &8 /\
           --(&1) < x /\ x < &1 /\ --(&1) < y /\ y < &1
         ==> log(&1 - x * y) <=
             log(&1 - (rp_en_rho e x * x) * (rp_en_rho e y * y)) + &4 * e`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`e:real`; `x:real`] RP_EN_DMP_RHO_BOUNDS) THEN
  MP_TAC(SPECL [`e:real`; `y:real`] RP_EN_DMP_RHO_BOUNDS) THEN
  ASM_REWRITE_TAC[] THEN
  SPEC_TAC(`rp_en_rho e y`,`b:real`) THEN
  SPEC_TAC(`rp_en_rho e x`,`a:real`) THEN
  REPEAT GEN_TAC THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(a * x) * (b * y) = (a * b) * (x * y:real)` SUBST1_TAC THENL
   [REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC RP_EN_DMP_POW_CORE THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[];
    SUBGOAL_THEN `&0 <= a * (&1 - b)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    SUBGOAL_THEN `&0 <= (&1 - a) * (&1 - b)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    REWRITE_TAC[REAL_ABS_MUL] THEN
    SUBGOAL_THEN `&0 <= abs x * (&1 - abs y)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Diagonal bounds.                                                          *)
(* ------------------------------------------------------------------------- *)

let RP_EN_DMP_POW_DIAG = prove
 (`forall e x. &0 < e /\ e < &1 / &8 /\ --(&1) < x /\ x < &1
         ==> e * (&1 - x) / &2 <= &1 - (rp_en_rho e x * x) pow 2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`e:real`; `x:real`] RP_EN_DMP_RHO_BOUNDS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN REWRITE_TAC[REAL_POW_MUL] THEN
  ASM_CASES_TAC `&0 <= x` THENL
   [SUBGOAL_THEN `rp_en_rho e x pow 2 <= &1` ASSUME_TAC THENL
     [SUBGOAL_THEN `&0 <= rp_en_rho e x * (&1 - rp_en_rho e x)` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= (&1 - rp_en_rho e x pow 2) * x pow 2` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= x * (&1 - x)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= (&1 - x) * (&1 - e / &2)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `rp_en_rho e x <= &1 - e` ASSUME_TAC THENL
   [REWRITE_TAC[rp_en_rho] THEN
    SUBGOAL_THEN `&0 <= e * --x` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= (&1 - e - rp_en_rho e x) * (&1 - e + rp_en_rho e x)`
   MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= (&1 - x) * (&1 + x)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= rp_en_rho e x pow 2 * (&1 - x pow 2)` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= e * (&1 - e)` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= e * (&1 + x)` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REAL_ARITH_TAC);;

let RP_EN_DMP_SQRT_ONE_SUB = prove
 (`forall s. &0 < s /\ s < &1
       ==> &0 <= sqrt(&1 - s) /\ sqrt(&1 - s) pow 2 = &1 - s /\
           sqrt(&1 - s) <= &1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_SIMP_TAC[SQRT_POS_LE; SQRT_POW_2; REAL_ARITH `s < &1 ==> &0 <= &1 - s`] THEN
  MATCH_MP_TAC REAL_LE_LSQRT THEN REWRITE_TAC[REAL_POW_ONE] THEN
  ASM_REAL_ARITH_TAC);;

let RP_EN_DMP_SIG_DIAG = prove
 (`forall e s. &0 < e /\ e < &1 / &8 /\ &0 < s /\ s < &1
         ==> e * sqrt(&1 - s) <= &1 - rp_en_sig e s pow 2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC `s:real` RP_EN_DMP_SQRT_ONE_SUB) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[rp_en_sig] THEN SPEC_TAC(`sqrt(&1 - s)`,`b:real`) THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= e * b /\ &0 <= e * (&1 - b)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= (e * b) * (&1 - e * b)` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The cross kernel (85), avoiding complex numbers.                          *)
(* ------------------------------------------------------------------------- *)

let RP_EN_DMP_QPOS = prove
 (`forall x s. &0 < s /\ s < &1 ==> &0 < &1 - &2 * x * s + x pow 2`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < s * (&1 - s)` MP_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPEC `x - s:real` REAL_LE_POW_2) THEN ASM_REAL_ARITH_TAC);;

let RP_EN_DMP_SQ_LE = prove
 (`forall a q. &0 <= q /\ a pow 2 <= q pow 2 ==> a <= q`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`a:real`; `q:real`] REAL_LE_SQUARE_ABS) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(SPEC `a:real` REAL_ABS_LE) THEN ASM_REAL_ARITH_TAC);;

let RP_EN_DMP_REL_SIZE_CORE = prove
 (`forall x s b q. --(&1) < x /\ x < &1 /\ &0 < s /\ s < &1 /\
             &0 <= b /\ b pow 2 = &1 - s /\ b <= &1 /\
             &0 <= q /\ q pow 2 = &1 - &2 * x * s + x pow 2
             ==> abs x * ((&1 - x) + b) <= &3 * q`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `&0 <= x` THENL
   [SUBGOAL_THEN `&1 - x <= q` ASSUME_TAC THENL
     [MATCH_MP_TAC RP_EN_DMP_SQ_LE THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `&0 <= x * (&1 - s)` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `x * b <= q` ASSUME_TAC THENL
     [MATCH_MP_TAC RP_EN_DMP_SQ_LE THEN ASM_REWRITE_TAC[REAL_POW_MUL] THEN
      SUBGOAL_THEN `&0 <= x * (&2 - x) * (&1 - s)` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
         [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      MP_TAC(SPEC `&1 - x:real` REAL_LE_POW_2) THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 <= x ==> abs x = x`] THEN
    MP_TAC(SPEC `&1 - x:real` REAL_LE_POW_2) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&1 <= q` ASSUME_TAC THENL
   [MATCH_MP_TAC RP_EN_DMP_SQ_LE THEN ASM_REWRITE_TAC[REAL_POW_ONE] THEN
    SUBGOAL_THEN `&0 <= --x * s` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(SPEC `x:real` REAL_LE_POW_2) THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= (&1 - abs x) * ((&1 - x) + b)` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

let RP_EN_DMP_NODE_ERR_CORE = prove
 (`forall e x s b q. &0 < e /\ e < &1 / &8 /\ --(&1) < x /\ x < &1 /\
               &0 < s /\ s < &1 /\
               &0 <= b /\ b pow 2 = &1 - s /\ b <= &1 /\
               &0 <= q /\ q pow 2 = &1 - &2 * x * s + x pow 2
               ==> abs(x - (&1 - e * (&1 - x)) * (&1 - e * b) * x)
                   <= &3 * e * q`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`x:real`; `s:real`; `b:real`; `q:real`]
    RP_EN_DMP_REL_SIZE_CORE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `x - (&1 - e * (&1 - x)) * (&1 - e * b) * x =
                (e * (&1 - x) + (e * b) * (&1 - e * (&1 - x))) * x`
   SUBST1_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= e * (&1 - x) /\ &0 <= e * (&1 + x) /\ &0 <= e * b`
   STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= (e * b) * (&1 - e * (&1 - x)) /\
                &0 <= (e * b) * (e * (&1 - x))` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= e * (&1 - x) + (e * b) * (&1 - e * (&1 - x))`
   ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[REAL_ABS_MUL] THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 <= c ==> abs c = c`] THEN
  SUBGOAL_THEN `&0 <= ((e * b) * (e * (&1 - x))) * abs x` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[REAL_ABS_POS]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= e * (&3 * q - abs x * ((&1 - x) + b))` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REAL_ARITH_TAC);;

let RP_EN_DMP_QUAD_CORE = prove
 (`forall e x s u q. &0 < s /\ s < &1 /\ &0 <= e /\ &0 <= q /\
               q pow 2 = &1 - &2 * x * s + x pow 2 /\
               abs(x - u) <= &3 * e * q
               ==> &1 - &2 * u * s + u pow 2 <=
                   (&1 + &3 * e) pow 2 * (&1 - &2 * x * s + x pow 2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `abs(s - x) <= q` ASSUME_TAC THENL
   [MATCH_MP_TAC RP_EN_DMP_SQ_LE THEN ASM_REWRITE_TAC[REAL_POW2_ABS] THEN
    SUBGOAL_THEN `&0 <= (&1 - s) * (&1 + s)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= &3 * e * q` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `abs(x - u) * abs(s - x) <= (&3 * e * q) * q` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[REAL_ABS_POS]; ALL_TAC] THEN
  SUBGOAL_THEN `abs(x - u) * abs(x - u) <= (&3 * e * q) * (&3 * e * q)`
   MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[REAL_ABS_POS]; ALL_TAC] THEN
  SUBGOAL_THEN `(&1 + &3 * e) pow 2 * (&1 - &2 * x * s + x pow 2) =
                (&1 + &3 * e) pow 2 * q pow 2` SUBST1_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_ABS_MUL] THEN
  MP_TAC(SPEC `(x - u) * (s - x):real` REAL_ABS_LE) THEN
  MP_TAC(SPEC `(x - u) * (x - u):real` REAL_ABS_LE) THEN
  UNDISCH_TAC `q pow 2 = &1 - &2 * x * s + x pow 2` THEN
  REAL_ARITH_TAC);;

let RP_EN_DMP_KERNEL_CORE = prove
 (`forall e x s u. &0 < e /\ &0 < s /\ s < &1 /\
             &1 - &2 * u * s + u pow 2 <=
             (&1 + &3 * e) pow 2 * (&1 - &2 * x * s + x pow 2)
             ==> --log(&1 - &2 * x * s + x pow 2) <=
                 --log(&1 - &2 * u * s + u pow 2) + &6 * e`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`x:real`; `s:real`] RP_EN_DMP_QPOS) THEN
  MP_TAC(SPECL [`u:real`; `s:real`] RP_EN_DMP_QPOS) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < &1 + &3 * e` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `log(&1 - &2 * u * s + u pow 2) <=
                log((&1 + &3 * e) pow 2 * (&1 - &2 * x * s + x pow 2))`
   MP_TAC THENL
   [MATCH_MP_TAC LOG_MONO_LE_IMP THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[LOG_MUL; REAL_POW_LT; LOG_POW] THEN
  MP_TAC(SPEC `&3 * e` LOG_LE_STRONG) THEN ASM_REWRITE_TAC[] THEN
  REAL_ARITH_TAC);;

let RP_EN_DMP_CROSS_CMP = prove
 (`forall e x s. &0 < e /\ e < &1 / &8 /\
           --(&1) < x /\ x < &1 /\ &0 < s /\ s < &1
         ==> --log(&1 - &2 * x * s + x pow 2) <=
             --log(&1 - &2 * (rp_en_rho e x * rp_en_sig e s * x) * s +
                   (rp_en_rho e x * rp_en_sig e s * x) pow 2) + &6 * e`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC RP_EN_DMP_KERNEL_CORE THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(SPEC `s:real` RP_EN_DMP_SQRT_ONE_SUB) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  MP_TAC(SPECL [`x:real`; `s:real`] RP_EN_DMP_QPOS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MATCH_MP_TAC RP_EN_DMP_QUAD_CORE THEN
  EXISTS_TAC `sqrt(&1 - &2 * x * s + x pow 2)` THEN
  ASM_SIMP_TAC[SQRT_POS_LE; SQRT_POW_2; REAL_LT_IMP_LE] THEN
  TRY(CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC]) THEN
  REWRITE_TAC[rp_en_rho; rp_en_sig] THEN
  MATCH_MP_TAC RP_EN_DMP_NODE_ERR_CORE THEN EXISTS_TAC `s:real` THEN
  ASM_SIMP_TAC[SQRT_POS_LE; SQRT_POW_2; REAL_LT_IMP_LE]);;
