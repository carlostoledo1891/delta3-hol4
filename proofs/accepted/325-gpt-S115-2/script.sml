Theory attempt
Ancestors
  arithmetic list integer real intreal delta3_check delta3_check2 delta3_sem delta3_stmts
Libs
  intLib realLib


Theorem nonneg_int[local]:
  !p. 0 <= p ==> 0 <= real_of_int p
Proof
  gen_tac >>
  mp_tac (SIMP_RULE bool_ss [intrealTheory.real_of_int_num] (INST [“m:int” |-> “0:int”, “n:int” |-> “p:int”] intrealTheory.real_of_int_le)) >> metis_tac[]
QED

Theorem widths_pos[local]:
  !grid. increasing grid ==> EVERY (\w. 0 <= w) (widths grid)
Proof
  Induct >> simp[increasing_def,widths_def] >>
  Cases_on ‘grid’ >> simp[increasing_def,widths_def] >> rpt strip_tac >>
  TRY (intLib.COOPER_TAC) >> fs[increasing_def,widths_def]
QED

Theorem dot_pos[local]:
  !ws y. EVERY (\w. 0 <= w) ws /\ EVERY (\x. 0 <= x /\ x <= 1) y ==>
      0 <= ldot ws y
Proof
  Induct >> simp[ldot_def] >> gen_tac >> Cases_on ‘y’ >>
  simp[ldot_def] >> rpt strip_tac >> irule REAL_LE_ADD >>
  metis_tac[REAL_LE_MUL,nonneg_int]
QED
Theorem S115_as_constants[local]:
  S078 ==> S115
Proof
  rewrite_tac[S115_def,in_box_def,mval_def] >> rpt strip_tac >>
  irule REAL_LE_DIV >> simp[] >> metis_tac[dot_pos,widths_pos]
QED

Theorem S115 = CONV_RULE (RAND_CONV (REWR_CONV S115_def)) S115_as_constants


