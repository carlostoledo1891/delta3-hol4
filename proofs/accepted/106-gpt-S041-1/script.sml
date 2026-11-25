Theory attempt
Ancestors
  arithmetic list integer real intreal delta3_check delta3_check2 delta3_sem delta3_stmts
Libs
  intLib realLib RealField

Theorem addl_action[local]:
  !l n v y. LENGTH (addl n v l) = LENGTH l /\
    (n < LENGTH l /\ LENGTH (y:real list) = LENGTH l ==>
     ldot (addl n v l) y = ldot l y + real_of_int v * EL n y)
Proof
  Induct >> simp [addl_def] >>
  rpt gen_tac >> Cases_on ‘n’ >> Cases_on ‘y’ >>
  simp [addl_def, ldot_def] >> rpt strip_tac >>
  fs [] >> TRY (res_tac >> fs []) >> RealField.REAL_ASM_ARITH_TAC
QED

Theorem S041_const[local]:
  S041
Proof
  rewrite_tac [S041_def] >> metis_tac [addl_action]
QED
Theorem S041 = EQ_MP S041_def S041_const
