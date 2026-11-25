Theory attempt
Ancestors
  arithmetic list integer real intreal delta3_check delta3_check2 delta3_sem delta3_stmts
Libs
  intLib realLib

Theorem lin_dot[local]:
  !ws g y. LENGTH ws = LENGTH g /\ LENGTH y = LENGTH g ==>
    ldot (lin c ws g) y = ldot g y + real_of_int c * ldot ws y
Proof
  Induct >> Cases_on `g` >> Cases_on `y` >>
  simp [lin_def, ldot_def] >> rw [] >> fs [] >> REAL_ARITH_TAC
QED

Theorem zero_dot[local]:
  !l y. all_zero l ==> ldot l y = 0
Proof
  Induct >> Cases_on `y` >> simp [ldot_def, all_zero_def] >> rw [] >> fs []
QED

Theorem S058_as_constants[local]:
  S038 ==> S058
Proof
  simp [S058_def, lin_dot, zero_dot]
QED

Theorem S058 = CONV_RULE (RAND_CONV (REWR_CONV S058_def)) S058_as_constants
