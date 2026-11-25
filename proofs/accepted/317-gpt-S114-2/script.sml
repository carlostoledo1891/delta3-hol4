Theory attempt
Ancestors
  arithmetic list integer real intreal delta3_check delta3_check2 delta3_sem delta3_stmts
Libs
  intLib realLib


Theorem lower_nonpos[local]:
  !p q. p <= 0 /\ 0 < q ==> qv p q <= 0
Proof
  rpt strip_tac >> simp[qv_def, REAL_LE_LDIV_EQ] >>
  mp_tac (SIMP_RULE bool_ss [intrealTheory.real_of_int_num] (INST [“m:int” |-> “p:int”, “n:int” |-> “0:int”] intrealTheory.real_of_int_le)) >> metis_tac[]
QED
Theorem S114_as_constants[local]:
  S053 ==> S114
Proof
  rewrite_tac[S114_def] >> strip_tac >> gen_tac >>
  Cases_on ‘ivs’ >- simp[cover_all_def] >>
  PairCases_on ‘h’ >> simp[cover_all_def,in_some_def] >> rpt strip_tac >>
  ‘qv h0 h1 <= 0’ by (irule lower_nonpos >> simp[]) >>
  Cases_on ‘m <= qv h2 h3’ >- metis_tac[REAL_LE_TRANS] >>
  disj2_tac >> fs[S053_def] >> metis_tac[REAL_NOT_LE]
QED

Theorem S114 = CONV_RULE (RAND_CONV (REWR_CONV S114_def)) S114_as_constants


