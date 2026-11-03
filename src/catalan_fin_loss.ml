(* fin_loss N p <= N * fin_dfun(p / N) *)
needs "src/catalan_fin_base.ml";;
needs "src/catalan_fin_pnt.ml";;

let FIN_LOSS_NAT = prove
 (`forall N p. p <= 65 * N ==>
  (p <= 25 * N ==> fin_loss N p <= 96 * N) /\
  (25 * N <= p /\ p <= 29 * N ==> fin_loss N p + 2 * p <= 146 * N) /\
  (29 * N <= p /\ 2 * p <= 65 * N ==> fin_loss N p <= 88 * N) /\
  (65 * N <= 2 * p /\ 2 * p <= 69 * N ==> fin_loss N p + 2 * p <= 153 * N) /\
  (69 * N <= 2 * p /\ p <= 40 * N ==> fin_loss N p + 4 * p <= 222 * N) /\
  (40 * N <= p /\ p <= 58 * N ==> fin_loss N p + 3 * p <= 182 * N) /\
  (58 * N <= p /\ p <= 59 * N ==> fin_loss N p + 2 * p <= 124 * N) /\
  (59 * N <= p ==> fin_loss N p + p <= 65 * N)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[fin_loss; LET_DEF; LET_END_DEF] THEN
  REPEAT CONJ_TAC THEN DISCH_TAC THEN
  ASM_CASES_TAC `2 * p <= 65 * N` THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[MIN; MAX] THEN REPEAT COND_CASES_TAC THEN ASM_ARITH_TAC);;



let FIN_DFUN_REAL = prove
 (`forall N p l. &0 < N /\ &0 <= p /\ p <= &65 * N /\
  (p <= &25 * N ==> l <= &96 * N) /\
  (&25 * N <= p /\ p <= &29 * N ==> l + &2 * p <= &146 * N) /\
  (&29 * N <= p /\ &2 * p <= &65 * N ==> l <= &88 * N) /\
  (&65 * N <= &2 * p /\ &2 * p <= &69 * N ==> l + &2 * p <= &153 * N) /\
  (&69 * N <= &2 * p /\ p <= &40 * N ==> l + &4 * p <= &222 * N) /\
  (&40 * N <= p /\ p <= &58 * N ==> l + &3 * p <= &182 * N) /\
  (&58 * N <= p /\ p <= &59 * N ==> l + &2 * p <= &124 * N) /\
  (&59 * N <= p ==> l + p <= &65 * N)
  ==> l <= N * fin_dfun(p / N)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[fin_dfun] THEN ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
  REPEAT COND_CASES_TAC THEN
  ASM_SIMP_TAC[REAL_FIELD `&0 < n ==> n * (a - b * p / n) = a * n - b * p`;
               REAL_FIELD `&0 < n ==> n * (a - p / n) = a * n - p`] THEN
  ASM_REAL_ARITH_TAC);;

let FIN_LOSS_LE_DFUN = prove
 (`forall N p. 1 <= N /\ p <= 65 * N ==> &(fin_loss N p) <= &N * fin_dfun(&p / &N)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC FIN_DFUN_REAL THEN
  MP_TAC(SPECL [`N:num`; `p:num`] FIN_LOSS_NAT) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[REAL_OF_NUM_LE; REAL_OF_NUM_MUL; REAL_OF_NUM_ADD; REAL_OF_NUM_LT] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[LE_0] THEN ASM_ARITH_TAC);;
