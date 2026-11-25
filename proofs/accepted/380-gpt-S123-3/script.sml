Theory attempt
Ancestors
  arithmetic list integer real intreal delta3_check delta3_check2 delta3_sem delta3_stmts
Libs
  intLib realLib

Theorem box_squares[local]:
  !y. EVERY (\x:real. 0 <= x /\ x <= 1) y ==> sumsq y <= &(LENGTH y)
Proof
  Induct >- simp[sumsq_def] >>
  qx_gen_tac ‘z’ >> simp_tac (srw_ss()) [sumsq_def,GSYM REAL_OF_NUM_SUC] >>
  strip_tac >> ‘sumsq y <= &(LENGTH y)’ by metis_tac[] >>
  mp_tac (Q.SPECL [‘z’,‘1’,‘z’,‘1’] REAL_LE_MUL2) >>
  asm_simp_tac (srw_ss()) [] >>
  qpat_x_assum ‘sumsq y <= _’ mp_tac >> rpt (pop_assum kall_tac) >>
  pure_rewrite_tac[GSYM REAL_OF_NUM_ADD] >> REAL_ARITH_TAC
QED

Theorem S123_as_constants[local]:
  S123
Proof
  rewrite_tac[S123_def,in_box_def] >> metis_tac[box_squares]
QED

Theorem S123 = EQ_MP S123_def S123_as_constants



