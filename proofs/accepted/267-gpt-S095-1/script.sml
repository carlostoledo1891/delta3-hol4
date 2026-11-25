Theory attempt
Ancestors
  arithmetic list integer real intreal delta3_check delta3_check2 delta3_sem delta3_stmts
Libs
  intLib realLib

Theorem bad_flag[local]:
  !st. FST (bad st) = F
Proof
  gen_tac >> PairCases_on `st` >> simp [bad_def]
QED

Theorem term_flag[local]:
  !D n tag i j p q st. tag <= 5 ==>
    (FST (add_term D n tag i j p q st) <=>
     FST st /\ D MOD q = 0 /\ i < n /\ j < n)
Proof
  rpt gen_tac >> PairCases_on `st` >> rw [add_term_def] >> decide_tac
QED

Theorem S095_as_constants[local]:
  S110 ==> S095
Proof
  disch_tac >> rewrite_tac [S095_def] >> rpt gen_tac >>
  simp_tac (srw_ss()) [add_form_def,add_zz_def,form_idx_ok_def] >>
  rpt IF_CASES_TAC >>
  fs [term_flag,bad_flag] >> rpt strip_tac >> fs [] >>
  TRY intLib.COOPER_TAC >> metis_tac []
QED

Theorem S095 = CONV_RULE (RAND_CONV (REWR_CONV S095_def)) S095_as_constants
