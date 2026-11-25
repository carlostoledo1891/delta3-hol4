Theory attempt
Ancestors
  arithmetic list integer real intreal delta3_check delta3_check2 delta3_sem delta3_stmts
Libs
  intLib realLib

Theorem box_el[local]:
  !n y i. in_box n y /\ i < n ==> 0 <= EL i y /\ EL i y <= 1
Proof
  simp [in_box_def, EVERY_EL] >> metis_tac []
QED

Theorem sub_sq[local]:
  !x:real. x - x*x = x*(1-x)
Proof
  RealField.REAL_ARITH_TAC
QED

Theorem kind_cases[local]:
  !kind:num. kind <= 13 ==> kind = 0 \/ kind = 1 \/ kind = 2 \/ kind = 3 \/ kind = 4 \/ kind = 5 \/ kind = 6 \/ kind = 7 \/ kind = 8 \/ kind = 9 \/ kind = 10 \/ kind = 11 \/ kind = 12 \/ kind = 13
Proof
  decide_tac
QED

Theorem S152_as_constants[local]:
  S152
Proof
  rewrite_tac [S152_def] >> rpt strip_tac >>
  qpat_x_assum ‘kind <= 13’ (strip_assume_tac o MATCH_MP kind_cases) >>
  fs [form_idx_ok_def, form_val_def, sub_sq] >>
  TRY (imp_res_tac box_el) >>
  TRY (match_mp_tac REAL_LE_MUL) >>
  rpt conj_tac >> TRY RealField.REAL_ASM_ARITH_TAC >>
  goalStack.print_tac "form inequality" >>
  metis_tac [box_el, REAL_SUB_LE, REAL_LE_MUL]
QED

Theorem S152 = EQ_MP S152_def S152_as_constants


