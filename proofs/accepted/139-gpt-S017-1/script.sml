Theory attempt
Ancestors
  arithmetic list integer real intreal delta3_check delta3_check2 delta3_sem delta3_stmts
Libs
  intLib realLib

open delta3_stmtsTheory delta3_checkTheory delta3_check2Theory delta3_semTheory
open realTheory intrealTheory integerTheory arithmeticTheory listTheory


Theorem S017_as_constants[local]:
  S017
Proof
  rewrite_tac[S017_def] >> rpt gen_tac >> strip_tac >>
  ‘0 < q’ by (Cases_on ‘q’ >> fs[]) >>
  ‘D DIV q * q = D’ by metis_tac[DIVISION,ADD_0] >>
  ‘(&(D DIV q):real) * &q = &D’ by simp[] >>
  ‘(&q:real) <> 0’ by simp[] >>
  simp[sc_def,qv_def] >>
  qpat_assum ‘(&(D DIV q):real) * &q = &D’ mp_tac >>
  qpat_assum ‘(&q:real) <> 0’ mp_tac >>
  RealField.REAL_FIELD_TAC
QED

Theorem S017 = EQ_MP S017_def S017_as_constants
