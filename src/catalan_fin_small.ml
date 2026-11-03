(* ========================================================================= *)
(* CAT_FINITE_PLACE: the "omitted small odd primes" bound (Proposition 3.4). *)
(* At an odd prime p every raw entry has v_p >= -(k + 5 floor(log_p 65N))    *)
(* where v_p(z) >= -k; hence v_p(Delta_N) >= -240 N (k + floor(log_p 65N)).  *)
(* ========================================================================= *)

needs "src/catalan_fin_bdry.ml";;

(* ------------------------------------------------------------------------- *)
(* A small valuation calculus.                                               *)
(* ------------------------------------------------------------------------- *)

let fin_sm_arith_tac = ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;;

let FIN_SM_VMUL = prove
 (`forall p k l m x y. prime p /\ fin_vge p k x /\ fin_vge p l y /\ m <= k + l
                 ==> fin_vge p m (x * y)`,
  MESON_TAC[FIN_VGE_MUL; FIN_VGE_MONO]);;

let FIN_SM_VDIV = prove
 (`forall p k l m x y. prime p /\ fin_vge p k x /\ fin_vge p l (inv y) /\ m <= k + l
                 ==> fin_vge p m (x / y)`,
  REWRITE_TAC[real_div] THEN MESON_TAC[FIN_SM_VMUL]);;

let FIN_SM_VINVMUL = prove
 (`forall p k l m x y. prime p /\ fin_vge p k (inv x) /\ fin_vge p l (inv y) /\
                 m <= k + l
                 ==> fin_vge p m (inv(x * y))`,
  REWRITE_TAC[REAL_INV_MUL] THEN MESON_TAC[FIN_SM_VMUL]);;

let FIN_SM_VPOW2 = prove
 (`forall p k m x. prime p /\ fin_vge p k x /\ m <= &2 * k
             ==> fin_vge p m (x pow 2)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[REAL_POW_2] THEN
  MATCH_MP_TAC FIN_SM_VMUL THEN
  MAP_EVERY EXISTS_TAC [`k:real`; `k:real`] THEN ASM_REWRITE_TAC[] THEN
  ASM_REAL_ARITH_TAC);;

let FIN_SM_VINVPOW2 = prove
 (`forall p k m x. prime p /\ fin_vge p k (inv x) /\ m <= &2 * k
             ==> fin_vge p m (inv(x pow 2))`,
  REWRITE_TAC[GSYM REAL_POW_INV] THEN MESON_TAC[FIN_SM_VPOW2]);;

let FIN_SM_VZP = prove
 (`forall p m x. prime p /\ fin_zp p x /\ m <= &0 ==> fin_vge p m x`,
  MESON_TAC[FIN_VGE_ZP; FIN_VGE_MONO]);;

let FIN_SM_VINT = prove
 (`forall p m x. prime p /\ integer x /\ m <= &0 ==> fin_vge p m x`,
  MESON_TAC[FIN_SM_VZP; FIN_ZP_INTEGER]);;

let FIN_SM_VMONO = prove
 (`forall p k m x. fin_vge p k x /\ m <= k ==> fin_vge p m x`,
  MESON_TAC[FIN_VGE_MONO]);;

let FIN_SM_NOT_DIV2 = prove
 (`forall p. prime p /\ ~(p = 2) ==> ~(p divides 2)`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP DIVIDES_LE) THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP PRIME_GE_2) THEN fin_sm_arith_tac);;

let FIN_SM_NOT_DIV4 = prove
 (`forall p l. prime p /\ ~(p = 2) ==> ~(p divides (4 EXP l))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `p divides 4` MP_TAC THENL
   [ASM_MESON_TAC[PRIME_DIVEXP]; ALL_TAC] THEN
  REWRITE_TAC[ARITH_RULE `4 = 2 * 2`] THEN DISCH_TAC THEN
  SUBGOAL_THEN `p divides 2` MP_TAC THENL
   [ASM_MESON_TAC[PRIME_DIVPROD]; ASM_SIMP_TAC[FIN_SM_NOT_DIV2]]);;

(* ------------------------------------------------------------------------- *)
(* Atoms: c_l, 1/c_l, m_n, H*_z.                                             *)
(* ------------------------------------------------------------------------- *)

let FIN_SM_ZP_C = prove
 (`forall p l. prime p /\ ~(p = 2) ==> fin_zp p (cat_c l)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[cat_c; REAL_OF_NUM_POW] THEN
  MATCH_MP_TAC FIN_ZP_DIV_NUM THEN ASM_SIMP_TAC[FIN_ZP_NUM; FIN_SM_NOT_DIV4]);;

let FIN_SM_ZP_3HALF = prove
 (`forall p. prime p /\ ~(p = 2) ==> fin_zp p (&3 / &2)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC FIN_ZP_DIV_NUM THEN
  ASM_SIMP_TAC[FIN_ZP_NUM; FIN_SM_NOT_DIV2]);;

let FIN_SM_INV_C = prove
 (`forall p l H. prime p /\ 2 * l <= H
           ==> fin_vge p (--(&(fin_flog p H))) (inv(cat_c l))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[cat_c; REAL_INV_DIV] THEN REWRITE_TAC[real_div] THEN
  MATCH_MP_TAC FIN_VGE_ZP_MUL THEN
  ASM_SIMP_TAC[FIN_ZP_POW; FIN_ZP_NUM; FIN_BDRY_BINOM_VAL]);;

let FIN_SM_INV_NUM = prove
 (`forall p n H. prime p /\ 1 <= n /\ n <= H
           ==> fin_vge p (--(&(fin_flog p H))) (inv(&n))`,
  MATCH_ACCEPT_TAC FIN_BDRY_NUM_VAL);;

let FIN_SM_M = prove
 (`forall p n H. prime p /\ ~(p = 2) /\ n + 1 <= H
           ==> fin_vge p (--(&2 * &(fin_flog p H))) (cat_m n)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[cat_m] THEN COND_CASES_TAC THEN
  ASM_SIMP_TAC[FIN_VGE_0] THEN
  REWRITE_TAC[real_div] THEN MATCH_MP_TAC FIN_VGE_ZP_MUL THEN
  ASM_SIMP_TAC[FIN_ZP_NUM] THEN MATCH_MP_TAC FIN_SM_VINVMUL THEN
  MAP_EVERY EXISTS_TAC [`--(&(fin_flog p H))`; `--(&(fin_flog p H))`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC FIN_SM_INV_NUM THEN fin_sm_arith_tac;
    MATCH_MP_TAC FIN_SM_INV_C THEN fin_sm_arith_tac;
    REAL_ARITH_TAC]);;

let FIN_SM_H_EVEN = prove
 (`forall p z. prime p /\ ~(p = 2) /\ EVEN z ==> fin_zp p (fin_hstar z)`,
  SIMP_TAC[fin_hstar; FIN_SM_ZP_C]);;

let FIN_SM_H = prove
 (`forall p z H. prime p /\ ~(p = 2) /\ z <= H
           ==> fin_vge p (--(&2 * &(fin_flog p H))) (fin_hstar z)`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `EVEN z` THENL
   [MATCH_MP_TAC FIN_SM_VZP THEN ASM_SIMP_TAC[FIN_SM_H_EVEN] THEN
    REWRITE_TAC[REAL_ARITH `--(&2 * x) <= &0 <=> &0 <= x`; REAL_POS];
    ASM_REWRITE_TAC[fin_hstar] THEN MATCH_MP_TAC FIN_SM_VINVMUL THEN
    MAP_EVERY EXISTS_TAC [`--(&(fin_flog p H))`; `--(&(fin_flog p H))`] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC FIN_SM_INV_NUM THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `~EVEN z` THEN
      ASM_CASES_TAC `z = 0` THEN ASM_REWRITE_TAC[ARITH] THEN fin_sm_arith_tac;
      MATCH_MP_TAC FIN_SM_INV_C THEN fin_sm_arith_tac;
      REAL_ARITH_TAC]]);;

let FIN_SM_HINV = prove
 (`forall p z H. prime p /\ ~(p = 2) /\ z <= H
           ==> fin_vge p (--(&(fin_flog p H))) (inv(fin_hstar z))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[fin_hstar] THEN COND_CASES_TAC THENL
   [MATCH_MP_TAC FIN_SM_INV_C THEN fin_sm_arith_tac;
    REWRITE_TAC[REAL_INV_INV] THEN MATCH_MP_TAC FIN_SM_VZP THEN
    ASM_SIMP_TAC[FIN_ZP_MUL; FIN_ZP_NUM; FIN_SM_ZP_C] THEN
    REWRITE_TAC[REAL_NEG_LE0; REAL_POS]]);;

(* ------------------------------------------------------------------------- *)
(* Boundary values via the explicit formulas (19).                           *)
(* ------------------------------------------------------------------------- *)

let FIN_SM_KMINUS = prove
 (`forall p u H. prime p /\ ~(p = 2) /\ u <= H
           ==> fin_vge p (--(&4 * &(fin_flog p H))) (cat_kminus u)`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `L = &(fin_flog p H)` THEN
  SUBGOAL_THEN `&0 <= L` ASSUME_TAC THENL
   [EXPAND_TAC "L" THEN REWRITE_TAC[REAL_POS]; ALL_TAC] THEN
  DISJ_CASES_TAC(SPEC `u:num` EVEN_OR_ODD) THENL
   [ASM_SIMP_TAC[FIN_BDRY_KMINUS_EVEN] THEN MATCH_MP_TAC FIN_VGE_ZP_MUL THEN
    ASM_SIMP_TAC[FIN_SM_H_EVEN] THEN MATCH_MP_TAC FIN_VGE_SUM THEN
    ASM_REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
    X_GEN_TAC `z:num` THEN STRIP_TAC THEN COND_CASES_TAC THEN
    ASM_SIMP_TAC[FIN_VGE_0] THEN
    REWRITE_TAC[real_div] THEN MATCH_MP_TAC FIN_VGE_ZP_MUL THEN
    ASM_SIMP_TAC[FIN_ZP_NUM] THEN MATCH_MP_TAC FIN_SM_VINVMUL THEN
    MAP_EVERY EXISTS_TAC [`--(&2 * (L:real))`; `--(&2 * (L:real))`] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC FIN_SM_VINVPOW2 THEN EXISTS_TAC `--(L:real)` THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [EXPAND_TAC "L" THEN MATCH_MP_TAC FIN_SM_INV_NUM THEN fin_sm_arith_tac;
        REAL_ARITH_TAC];
      MATCH_MP_TAC FIN_SM_VINVPOW2 THEN EXISTS_TAC `--(L:real)` THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [EXPAND_TAC "L" THEN MATCH_MP_TAC FIN_SM_HINV THEN fin_sm_arith_tac;
        REAL_ARITH_TAC];
      REAL_ARITH_TAC];
    ASM_SIMP_TAC[FIN_BDRY_KMINUS_ODD] THEN MATCH_MP_TAC FIN_SM_VMUL THEN
    MAP_EVERY EXISTS_TAC [`--(&2 * (L:real))`; `--(L:real)`] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [EXPAND_TAC "L" THEN MATCH_MP_TAC FIN_SM_H THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC FIN_VGE_SUM THEN
      ASM_REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
      X_GEN_TAC `z:num` THEN STRIP_TAC THEN COND_CASES_TAC THEN
      ASM_SIMP_TAC[FIN_VGE_0] THEN
      REWRITE_TAC[real_div] THEN MATCH_MP_TAC FIN_VGE_ZP_MUL THEN
      ASM_SIMP_TAC[FIN_ZP_NUM] THEN
      EXPAND_TAC "L" THEN MATCH_MP_TAC FIN_SM_INV_NUM THEN fin_sm_arith_tac;
      ASM_REAL_ARITH_TAC]]);;

let FIN_SM_KPLUS = prove
 (`forall p u H. prime p /\ ~(p = 2) /\ u + 1 <= H
           ==> fin_vge p (--(&5 * &(fin_flog p H))) (cat_kplus (u + 1))`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `L = &(fin_flog p H)` THEN
  SUBGOAL_THEN `&0 <= L` ASSUME_TAC THENL
   [EXPAND_TAC "L" THEN REWRITE_TAC[REAL_POS]; ALL_TAC] THEN
  REWRITE_TAC[FIN_BDRY_KPLUS] THEN MATCH_MP_TAC FIN_SM_VMUL THEN
  MAP_EVERY EXISTS_TAC [`--(&2 * (L:real))`; `--(&3 * (L:real))`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [EXPAND_TAC "L" THEN MATCH_MP_TAC FIN_SM_H THEN ASM_REWRITE_TAC[] THEN
    fin_sm_arith_tac;
    MATCH_MP_TAC FIN_VGE_SUM THEN
    ASM_REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
    X_GEN_TAC `z:num` THEN STRIP_TAC THEN COND_CASES_TAC THEN
    ASM_SIMP_TAC[FIN_VGE_0] THEN
    REWRITE_TAC[real_div] THEN MATCH_MP_TAC FIN_VGE_ZP_MUL THEN
    ASM_SIMP_TAC[FIN_ZP_NUM] THEN MATCH_MP_TAC FIN_SM_VINVMUL THEN
    MAP_EVERY EXISTS_TAC [`--(&2 * (L:real))`; `--(L:real)`] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC FIN_SM_VINVPOW2 THEN EXISTS_TAC `--(L:real)` THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [EXPAND_TAC "L" THEN MATCH_MP_TAC FIN_SM_INV_NUM THEN fin_sm_arith_tac;
        REAL_ARITH_TAC];
      EXPAND_TAC "L" THEN MATCH_MP_TAC FIN_SM_HINV THEN fin_sm_arith_tac;
      REAL_ARITH_TAC];
    ASM_REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* M'(i,j) and Z'(i,j) for i, j <= H.                                        *)
(* ------------------------------------------------------------------------- *)

let FIN_SM_M0 = prove
 (`forall p i j H. prime p /\ ~(p = 2) /\ i <= H /\ j <= H
             ==> fin_vge p (--(&5 * &(fin_flog p H))) (cat_M0 i j)`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `L = &(fin_flog p H)` THEN
  SUBGOAL_THEN `&0 <= L` ASSUME_TAC THENL
   [EXPAND_TAC "L" THEN REWRITE_TAC[REAL_POS]; ALL_TAC] THEN
  REWRITE_TAC[cat_M0] THEN COND_CASES_TAC THEN
  MATCH_MP_TAC FIN_VGE_SUB THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC FIN_SM_VMONO THEN EXISTS_TAC `--(&4 * (L:real))` THEN
    CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
    EXPAND_TAC "L" THEN MATCH_MP_TAC FIN_SM_KMINUS THEN fin_sm_arith_tac;
    MATCH_MP_TAC FIN_VGE_SUM THEN
    ASM_REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
    X_GEN_TAC `k:num` THEN STRIP_TAC THEN
    MATCH_MP_TAC FIN_SM_VDIV THEN
    MAP_EVERY EXISTS_TAC [`--(&2 * (L:real))`; `--(L:real)`] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [EXPAND_TAC "L" THEN MATCH_MP_TAC FIN_SM_M THEN fin_sm_arith_tac;
      EXPAND_TAC "L" THEN MATCH_MP_TAC FIN_SM_INV_NUM THEN fin_sm_arith_tac;
      ASM_REAL_ARITH_TAC];
    SUBGOAL_THEN `j - i = (j - i - 1) + 1` SUBST1_TAC THENL
     [fin_sm_arith_tac; ALL_TAC] THEN
    EXPAND_TAC "L" THEN MATCH_MP_TAC FIN_SM_KPLUS THEN fin_sm_arith_tac;
    MATCH_MP_TAC FIN_VGE_SUM THEN
    ASM_REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
    X_GEN_TAC `k:num` THEN STRIP_TAC THEN
    MATCH_MP_TAC FIN_SM_VDIV THEN
    MAP_EVERY EXISTS_TAC [`--(&2 * (L:real))`; `--(L:real)`] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [EXPAND_TAC "L" THEN MATCH_MP_TAC FIN_SM_M THEN fin_sm_arith_tac;
      EXPAND_TAC "L" THEN MATCH_MP_TAC FIN_SM_INV_NUM THEN fin_sm_arith_tac;
      ASM_REAL_ARITH_TAC]]);;

let FIN_SM_HARM1 = prove
 (`forall p n H. prime p /\ n <= H
           ==> fin_vge p (--(&(fin_flog p H))) (cat_harm 1 n)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[cat_harm] THEN
  MATCH_MP_TAC FIN_VGE_SUM THEN ASM_REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
  X_GEN_TAC `k:num` THEN STRIP_TAC THEN
  REWRITE_TAC[REAL_POW_1; real_div; REAL_MUL_LID] THEN
  MATCH_MP_TAC FIN_SM_INV_NUM THEN fin_sm_arith_tac);;

let FIN_SM_HARM2 = prove
 (`forall p n H. prime p /\ n <= H
           ==> fin_vge p (--(&2 * &(fin_flog p H))) (cat_harm 2 n)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[cat_harm] THEN
  MATCH_MP_TAC FIN_VGE_SUM THEN ASM_REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
  X_GEN_TAC `k:num` THEN STRIP_TAC THEN
  REWRITE_TAC[real_div; REAL_MUL_LID] THEN
  MATCH_MP_TAC FIN_SM_VINVPOW2 THEN EXISTS_TAC `--(&(fin_flog p H))` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC FIN_SM_INV_NUM THEN fin_sm_arith_tac; REAL_ARITH_TAC]);;

let FIN_SM_INV_DIFF = prove
 (`forall p i j H. prime p /\ i <= H /\ j <= H /\ ~(i = j)
             ==> fin_vge p (--(&(fin_flog p H))) (inv(&i - &j))`,
  REPEAT STRIP_TAC THEN
  DISJ_CASES_TAC(ARITH_RULE `j <= i \/ i <= j:num`) THENL
   [ASM_SIMP_TAC[REAL_OF_NUM_SUB] THEN
    MATCH_MP_TAC FIN_SM_INV_NUM THEN fin_sm_arith_tac;
    ONCE_REWRITE_TAC[REAL_ARITH `&i - &j = --(&j - &i)`] THEN
    ASM_SIMP_TAC[REAL_OF_NUM_SUB; REAL_INV_NEG; FIN_VGE_NEG_EQ] THEN
    MATCH_MP_TAC FIN_SM_INV_NUM THEN fin_sm_arith_tac]);;

let FIN_SM_Z0 = prove
 (`forall p i j H. prime p /\ i <= H /\ j <= H
             ==> fin_vge p (--(&2 * &(fin_flog p H))) (cat_Z0 i j)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[cat_Z0] THEN COND_CASES_TAC THENL
   [REWRITE_TAC[FIN_VGE_NEG_EQ] THEN ASM_SIMP_TAC[FIN_SM_HARM2];
    MATCH_MP_TAC FIN_SM_VDIV THEN
    MAP_EVERY EXISTS_TAC [`--(&(fin_flog p H))`; `--(&(fin_flog p H))`] THEN
    ASM_SIMP_TAC[FIN_VGE_SUB; FIN_SM_HARM1; FIN_SM_INV_DIFF] THEN
    REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Integrality of the row coefficients.                                      *)
(* ------------------------------------------------------------------------- *)

let FIN_SM_CHEB_T_INT = prove
 (`forall d k. integer(cheb_T d k)`,
  SUBGOAL_THEN `forall d. (forall k. integer(cheb_T d k)) /\ (forall k. integer(cheb_T (SUC d) k))`
   (fun th -> MESON_TAC[th]) THEN
  INDUCT_TAC THEN ASM_REWRITE_TAC[cheb_T] THENL
   [CONJ_TAC THEN GEN_TAC THEN COND_CASES_TAC THEN SIMP_TAC[INTEGER_CLOSED];
    GEN_TAC THEN COND_CASES_TAC THEN ASM_SIMP_TAC[INTEGER_CLOSED]]);;

let FIN_SM_CHEB_U_INT = prove
 (`forall d k. integer(cheb_U d k)`,
  SUBGOAL_THEN `forall d. (forall k. integer(cheb_U d k)) /\ (forall k. integer(cheb_U (SUC d) k))`
   (fun th -> MESON_TAC[th]) THEN
  INDUCT_TAC THEN ASM_REWRITE_TAC[cheb_U] THENL
   [CONJ_TAC THEN GEN_TAC THEN COND_CASES_TAC THEN SIMP_TAC[INTEGER_CLOSED];
    GEN_TAC THEN COND_CASES_TAC THEN ASM_SIMP_TAC[INTEGER_CLOSED]]);;

let FIN_SM_MULFAC_INT = prove
 (`forall h c i. (forall m. integer(c m)) ==> integer(cat_mulfac h c i)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[cat_mulfac] THEN
  MATCH_MP_TAC INTEGER_SUM THEN X_GEN_TAC `v:num` THEN DISCH_TAC THEN
  BETA_TAC THEN COND_CASES_TAC THEN ASM_SIMP_TAC[INTEGER_CLOSED]);;

let FIN_SM_REVC_INT = prove
 (`forall C c m. (forall m. integer(c m)) ==> integer(cat_revc C c m)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[cat_revc] THEN
  COND_CASES_TAC THEN ASM_SIMP_TAC[INTEGER_CLOSED]);;

let FIN_SM_PCOEF_INT = prove
 (`forall N r i. integer(cat_pcoef N r i)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[cat_pcoef] THEN
  MATCH_MP_TAC FIN_SM_MULFAC_INT THEN GEN_TAC THEN
  MATCH_MP_TAC FIN_SM_REVC_INT THEN REWRITE_TAC[FIN_SM_CHEB_T_INT]);;

let FIN_SM_DCOEF_INT = prove
 (`forall N r i. integer(cat_dcoef N r i)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[cat_dcoef] THEN
  MATCH_MP_TAC(MESON[INTEGER_CLOSED]
    `integer x /\ integer y ==> integer(x * y)`) THEN CONJ_TAC THENL
   [REWRITE_TAC[cat_sgn] THEN REPEAT COND_CASES_TAC THEN
    SIMP_TAC[INTEGER_CLOSED];
    MATCH_MP_TAC FIN_SM_MULFAC_INT THEN GEN_TAC THEN
    MATCH_MP_TAC FIN_SM_REVC_INT THEN REWRITE_TAC[FIN_SM_CHEB_U_INT]]);;

(* ------------------------------------------------------------------------- *)
(* Raw entries, filtered entries, determinant.                               *)
(* ------------------------------------------------------------------------- *)

let FIN_SM_RAWQ = prove
 (`forall p z N r j k. prime p /\ ~(p = 2) /\ j <= 65 * N /\ fin_vge p (--(&k)) z
                 ==> fin_vge p (--(&k + &5 * &(fin_flog p (65 * N))))
                               (cat_rawq z N r j)`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `L = &(fin_flog p (65 * N))` THEN
  SUBGOAL_THEN `&0 <= L` ASSUME_TAC THENL
   [EXPAND_TAC "L" THEN REWRITE_TAC[REAL_POS]; ALL_TAC] THEN
  REWRITE_TAC[cat_rawq] THEN MATCH_MP_TAC FIN_VGE_SUB THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC FIN_VGE_SUM THEN ASM_REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    MATCH_MP_TAC FIN_VGE_ZP_MUL THEN
    ASM_SIMP_TAC[FIN_ZP_INTEGER; FIN_SM_PCOEF_INT] THEN
    MATCH_MP_TAC FIN_VGE_ADD THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC FIN_SM_VMONO THEN EXISTS_TAC `--(&5 * (L:real))` THEN
      CONJ_TAC THENL
       [EXPAND_TAC "L" THEN MATCH_MP_TAC FIN_SM_M0 THEN ASM_REWRITE_TAC[];
        MP_TAC(SPEC `k:num` REAL_POS) THEN REAL_ARITH_TAC];
      REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN MATCH_MP_TAC FIN_VGE_ZP_MUL THEN
      ASM_SIMP_TAC[FIN_ZP_NUM] THEN MATCH_MP_TAC FIN_SM_VMUL THEN
      MAP_EVERY EXISTS_TAC [`--(&k)`; `&0`] THEN ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL
       [ASM_SIMP_TAC[FIN_VGE_ZP] THEN REWRITE_TAC[cat_ckern] THEN
        COND_CASES_TAC THEN ASM_SIMP_TAC[FIN_ZP_0; FIN_SM_ZP_C];
        ASM_REAL_ARITH_TAC]];
    MATCH_MP_TAC FIN_VGE_ZP_MUL THEN ASM_SIMP_TAC[FIN_SM_ZP_3HALF] THEN
    MATCH_MP_TAC FIN_VGE_SUM THEN ASM_REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    MATCH_MP_TAC FIN_VGE_ZP_MUL THEN
    ASM_SIMP_TAC[FIN_ZP_INTEGER; FIN_SM_DCOEF_INT] THEN
    MATCH_MP_TAC FIN_SM_VMONO THEN EXISTS_TAC `--(&2 * (L:real))` THEN
    CONJ_TAC THENL
     [EXPAND_TAC "L" THEN MATCH_MP_TAC FIN_SM_Z0 THEN ASM_REWRITE_TAC[];
      MP_TAC(SPEC `k:num` REAL_POS) THEN ASM_REAL_ARITH_TAC]]);;

let FIN_SM_ENTRYQ = prove
 (`forall p z N r q k. prime p /\ ~(p = 2) /\ 1 <= N /\ q < 48 * N /\
                 fin_vge p (--(&k)) z
                 ==> fin_vge p (--(&k + &5 * &(fin_flog p (65 * N))))
                               (cat_entryq z N r q)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[cat_entryq] THEN
  MATCH_MP_TAC FIN_VGE_SUM THEN ASM_REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
  X_GEN_TAC `v:num` THEN STRIP_TAC THEN
  REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC FIN_VGE_ZP_MUL THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC FIN_ZP_INTEGER THEN ASM_REWRITE_TAC[] THEN
    SIMP_TAC[INTEGER_CLOSED];
    ALL_TAC] THEN
  MATCH_MP_TAC FIN_SM_RAWQ THEN ASM_REWRITE_TAC[] THEN fin_sm_arith_tac);;

let FIN_SM_BOUND_EXPLICIT = prove
 (`forall z N p k. 1 <= N /\ prime p /\ ~(p = 2) /\ fin_vge p (--(&k)) z
             ==> fin_vge p (--(&240 * &N * (&k + &(fin_flog p (65 * N)))))
                           (cat_detq z N)`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `L = &(fin_flog p (65 * N))` THEN
  SUBGOAL_THEN `&0 <= L` ASSUME_TAC THENL
   [EXPAND_TAC "L" THEN REWRITE_TAC[REAL_POS]; ALL_TAC] THEN
  REWRITE_TAC[cat_detq] THEN
  MP_TAC(ISPECL [`p:num`; `0..48 * N - 1`; `cat_entryq z N`;
                 `\q:num. --(&k + &5 * L)`] FIN_VGE_NDET_COLS) THEN
  ASM_REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG; SUM_CONST_NUMSEG; BETA_THM] THEN
  ANTS_TAC THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "L" THEN MATCH_MP_TAC FIN_SM_ENTRYQ THEN
    ASM_REWRITE_TAC[] THEN fin_sm_arith_tac;
    ALL_TAC] THEN
  DISCH_TAC THEN MATCH_MP_TAC FIN_SM_VMONO THEN
  EXISTS_TAC `&((48 * N - 1 + 1) - 0) * --(&k + &5 * (L:real))` THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(48 * N - 1 + 1) - 0 = 48 * N` SUBST1_TAC THENL
   [fin_sm_arith_tac; ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_MUL] THEN
  MP_TAC(SPECL [`&N`; `&k`] REAL_LE_MUL) THEN
  MP_TAC(SPECL [`&N`; `L:real`] REAL_LE_MUL) THEN
  ASM_REWRITE_TAC[REAL_POS] THEN REAL_ARITH_TAC);;

let FIN_SM_BOUND = prove
 (`forall z. rational z
   ==> exists c. forall N p k. 1 <= N /\ prime p /\ ~(p = 2) /\ fin_vge p (--(&k)) z
               ==> fin_vge p (--(&c * &N * (&k + &(fin_flog p (65 * N)))))
                             (cat_detq z N)`,
  GEN_TAC THEN DISCH_TAC THEN EXISTS_TAC `240` THEN
  REWRITE_TAC[FIN_SM_BOUND_EXPLICIT]);;
