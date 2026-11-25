Theory attempt
Ancestors
  arithmetic list integer real intreal delta3_check delta3_check2 delta3_sem delta3_stmts
Libs
  intLib realLib


Theorem S078_as_constants[local]:
  S078
Proof
  rewrite_tac [S078_def] >> Induct >> simp [widths_def] >>
  Cases_on `grid` >> fs [widths_def]
QED

Theorem S078 = EQ_MP S078_def S078_as_constants
