Theory attempt
Ancestors
  arithmetic list integer real intreal delta3_check delta3_check2 delta3_sem delta3_stmts
Libs
  intLib realLib

open delta3_stmtsTheory delta3_checkTheory delta3_check2Theory delta3_semTheory
open realTheory intrealTheory integerTheory arithmeticTheory listTheory

Theorem zld[local]:
  !n y. ldot (REPLICATE n 0) y = 0
Proof
  Induct >> simp[rich_listTheory.REPLICATE,ldot_def] >>
  Cases >> simp[ldot_def]
QED

Theorem zq[local]:
  !k u n y. qform (REPLICATE k (REPLICATE n 0)) u y = 0
Proof
  Induct >> simp[rich_listTheory.REPLICATE,qform_def] >>
  Cases >> simp[zld,qform_def]
QED
Theorem S005_as_constants[local]:
  S005
Proof
  simp[S005_def,st0_def,st_wf_def,st_val_def,zld,zq,rich_listTheory.EVERY_REPLICATE]
QED

Theorem S005 = EQ_MP S005_def S005_as_constants
