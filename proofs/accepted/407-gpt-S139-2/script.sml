Theory attempt
Ancestors
  arithmetic list integer real intreal delta3_check delta3_check2 delta3_sem delta3_stmts
Libs
  intLib realLib

val shape = CONJUNCT1 (SPEC_ALL (EQ_MP S110_def (ASSUME “S110”)))
val guards = CONJUNCT2 (SPEC_ALL (EQ_MP S110_def (ASSUME “S110”)))
val effect = SPEC_ALL (EQ_MP S042_def (ASSUME “S042”))

Theorem bad_flag[local]:
  !st. ~FST (bad st)
Proof
  gen_tac >> PairCases_on ‘st’ >> simp [bad_def]
QED

Theorem positive_qv[local]:
  0 <= p ==> 0 <= qv p k
Proof
  strip_tac >> rewrite_tac [qv_def] >> irule REAL_LE_DIV >>
  ‘real_of_int 0 = 0’ by simp [] >>
  simp [] >> metis_tac [real_of_int_le]
QED

Theorem nn_entry_pos[local]:
  in_box n y /\ i < n /\ j < n /\ 0 <= p ==>
  0 <= (if i = j then 1 else 2) * qv p k * (EL i y * EL j y)
Proof
  strip_tac >>
  ‘0 <= EL i y /\ 0 <= EL j y’ by
    (fs [in_box_def, EVERY_EL] >> metis_tac []) >>
  ‘0 <= (if i = j then 1r else 2)’ by (Cases_on ‘i = j’ >> simp []) >>
  metis_tac [REAL_LE_MUL, positive_qv]
QED

Theorem nn[local]:
  S110 /\ S042 ==> !nn st.
    0 < D /\ st_wf n st /\ LENGTH (y:real list) = n /\ FST (add_nn D n nn st) ==>
    FST st /\ st_wf n (add_nn D n nn st) /\
    st_val ws (add_nn D n nn st) y = st_val ws st y - &D * nn_val nn y /\
    (in_box n y ==> 0 <= nn_val nn y)
Proof
  strip_tac >> Induct
  >- simp [add_nn_def, nn_val_def]
  >> rpt gen_tac >> rename1 ‘add_nn D n (hh::rest) st’ >> PairCases_on ‘hh’ >>
  Cases_on ‘hh2 < 0 \/ hh1 < hh0’
  >- simp [add_nn_def, bad_flag]
  >> asm_simp_tac bool_ss [add_nn_def, nn_val_def] >> strip_tac >>
  ‘st_wf n (add_term D n 2 hh0 hh1 (-(if hh0 = hh1 then hh2 else 2 * hh2)) hh3 st)’ by metis_tac [shape] >>
  first_x_assum (qspec_then ‘add_term D n 2 hh0 hh1 (-(if hh0 = hh1 then hh2 else 2 * hh2)) hh3 st’ mp_tac) >>
  asm_rewrite_tac [] >> strip_tac >>
  ‘FST st /\ hh0 < n /\ hh1 < n’ by metis_tac [guards] >>
  ‘st_val ws (add_term D n 2 hh0 hh1 (-(if hh0 = hh1 then hh2 else 2 * hh2)) hh3 st) y = st_val ws st y +
     &D * qv (-(if hh0 = hh1 then hh2 else 2 * hh2)) hh3 * mono ws 2 hh0 hh1 y’
     by metis_tac [effect] >>
  asm_rewrite_tac [] >> conj_tac
  >- (Cases_on ‘hh0 = hh1’ >> simp [qv_def, real_div, mono_def] >> CONV_TAC (EQT_INTRO o RealField.REAL_RING))
  >> strip_tac >> goalStack.print_tac "Positivity" >>
  ‘0 <= hh2’ by intLib.ARITH_TAC >>
  irule REAL_LE_ADD >> conj_tac
  >- (match_mp_tac (GEN_ALL nn_entry_pos) >> metis_tac []) >>
  metis_tac []
QED

Theorem S139_as_constants[local]:
  S110 /\ S042 ==> S139
Proof
  PURE_REWRITE_TAC [S139_def] >>
  disch_then (fn d => rpt gen_tac >> MATCH_ACCEPT_TAC (SPEC_ALL (MP nn d)))
QED

Theorem S139 = CONV_RULE (RAND_CONV (REWR_CONV S139_def)) S139_as_constants
