Theory attempt
Ancestors
  arithmetic list integer real intreal delta3_check delta3_check2 delta3_sem delta3_stmts
Libs
  intLib realLib RealField

Theorem qv_le[local]:
  0 < q /\ 0 < s /\ p * &s <= r * &q ==> qv p q <= qv r s
Proof
  strip_tac >>
  simp [qv_def,REAL_LE_LDIV_EQ] >>
  TRY (ONCE_REWRITE_TAC [RealField.REAL_FIELD “x / y * z = (x * z) / y:real”]) >>
  simp [REAL_LE_RDIV_EQ] >>
  asm_simp_tac bool_ss [GSYM real_of_int_num,GSYM real_of_int_mul,real_of_int_le]
QED
Theorem covers[local]:
  !ivs ap aq. cover ap aq ivs ==> !m:real. qv ap aq < m /\ m <= 1/2 ==> in_some m ivs
Proof
  Induct
  >- (rpt gen_tac >> rewrite_tac [cover_def] >> strip_tac >> gen_tac >> strip_tac >>
      ‘qv 1 2 <= qv ap aq’ by
        (irule qv_le >> fs [INT_MUL_COMM] >> intLib.ARITH_TAC) >>
      ‘qv 1 2 = 1/2’ by simp [qv_def] >>
      rewrite_tac [in_some_def] >> RealField.REAL_ASM_ARITH_TAC) >>
  rpt gen_tac >> PairCases_on ‘h’ >>
  Cases_on ‘ap * &h3 < h2 * &aq’
  >| [asm_simp_tac bool_ss [cover_def,in_some_def] >> rpt strip_tac >>
      ‘qv h0 h1 <= qv ap aq’ by metis_tac [qv_le] >>
      Cases_on ‘m <= qv h2 h3’
      >- (disj1_tac >> metis_tac [REAL_LET_TRANS,REAL_LT_IMP_LE]) >>
      disj2_tac >> metis_tac [REAL_NOT_LE],
      asm_simp_tac bool_ss [cover_def,in_some_def] >> metis_tac []]
QED
Theorem S053_const[local]:
  S053
Proof
  rewrite_tac [S053_def] >> metis_tac [covers]
QED
Theorem S053 = EQ_MP S053_def S053_const
