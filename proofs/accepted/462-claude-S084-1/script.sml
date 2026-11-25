Theory attempt
Ancestors
  arithmetic list integer real intreal delta3_check delta3_check2 delta3_sem delta3_stmts
Libs
  intLib realLib

Theorem addl_len[local]:
  !l n v. LENGTH (addl n v l) = LENGTH l
Proof
  Induct >> rw [addl_def]
QED

Theorem addm_len[local]:
  !Cm i j v. LENGTH (addm i j v Cm) = LENGTH Cm
Proof
  Induct >> rw [addm_def]
QED

Theorem addm_every[local]:
  !Cm i j v m. EVERY (\r. LENGTH r = m) (addm i j v Cm) <=> EVERY (\r. LENGTH r = m) Cm
Proof
  Induct >> rw [addm_def, addl_len]
QED

Theorem wf_at_eq[local]:
  !n D tag i j p q st. st_wf n (add_term D n tag i j p q st) <=> st_wf n st
Proof
  rpt gen_tac >> PairCases_on `st` >>
  `tag = 0 \/ tag = 1 \/ tag = 2 \/ tag = 3 \/ tag = 4 \/ tag = 5 \/
   (tag <> 0 /\ tag <> 1 /\ tag <> 2 /\ tag <> 3 /\ tag <> 4 /\ tag <> 5)` by decide_tac >>
  pop_assum strip_assume_tac >>
  FIRST [simp [add_term_def, LET_THM, st_wf_def, addl_len, addm_len, addm_every] >> NO_TAC,
         asm_simp_tac std_ss [add_term_def, LET_THM, st_wf_def, addl_len, addm_len, addm_every] >> NO_TAC,
         (rw [add_term_def, LET_THM, st_wf_def, addl_len, addm_len, addm_every] >> fs []) >> NO_TAC]
QED

Theorem fst_at[local]:
  !D n tag i j p q st.
    FST (add_term D n tag i j p q st) <=>
    FST st /\ D MOD q = 0 /\ i < n /\ j < n /\ tag <= 5
Proof
  rpt gen_tac >> PairCases_on `st` >>
  `tag = 0 \/ tag = 1 \/ tag = 2 \/ tag = 3 \/ tag = 4 \/ tag = 5 \/
   (tag <> 0 /\ tag <> 1 /\ tag <> 2 /\ tag <> 3 /\ tag <> 4 /\ tag <> 5 /\ ~(tag <= 5))`
    by decide_tac >>
  pop_assum strip_assume_tac >>
  FIRST [simp [add_term_def, LET_THM] >> NO_TAC,
         asm_simp_tac std_ss [add_term_def, LET_THM] >> NO_TAC,
         (rw [add_term_def, LET_THM] >> fs []) >> NO_TAC]
QED

Theorem fst_bad[local]:
  !st. FST (bad st) = F
Proof
  gen_tac >> PairCases_on `st` >> simp [bad_def]
QED

Theorem qv_neg[local]:
  !p q. qv (-p) q = -qv p q
Proof
  rpt gen_tac >>
  FIRST [rewrite_tac [qv_def, real_of_int_neg, real_div, REAL_MUL_LNEG] >> NO_TAC,
         simp [qv_def, real_div] >> NO_TAC,
         (simp [qv_def, real_div] >> REAL_ARITH_TAC) >> NO_TAC]
QED

Theorem qv_mul[local]:
  !a p q. qv (a * p) q = real_of_int a * qv p q
Proof
  rpt gen_tac >>
  FIRST [rewrite_tac [qv_def, real_of_int_mul, real_div, REAL_MUL_ASSOC] >> NO_TAC,
         (simp [qv_def, real_div] >> REAL_ARITH_TAC) >> NO_TAC,
         simp [qv_def, real_div, REAL_MUL_ASSOC] >> NO_TAC]
QED

Theorem val_at[local]:
  S042 ==>
  !D n st y tag i j p q ws.
    0 < D /\ st_wf n st /\ LENGTH (y:real list) = n /\ FST (add_term D n tag i j p q st) ==>
    st_val ws (add_term D n tag i j p q st) y = st_val ws st y + &D * qv p q * mono ws tag i j y
Proof
  rewrite_tac [S042_def] >> metis_tac []
QED

fun step_tac ths =
  FIRST [(asm_simp_tac std_ss ths >> rpt strip_tac >> REAL_ARITH_TAC) >> NO_TAC,
         (simp ths >> rpt strip_tac >> REAL_ARITH_TAC) >> NO_TAC,
         (simp (ths @ [qv_def, real_div]) >> rpt strip_tac >> REAL_ARITH_TAC) >> NO_TAC];

val v2_tac =
  FIRST [metis_tac [val_at],
         rpt strip_tac >> irule (UNDISCH val_at) >> asm_rewrite_tac []];

Theorem S084_as_constants[local]:
  S110 /\ S042 ==> S084
Proof
  strip_tac >> rewrite_tac [S084_def] >> rpt gen_tac >> strip_tac >>
  `!st tag i j p q. st_wf n st /\ FST (add_term D n tag i j p q st) ==>
      st_val ws (add_term D n tag i j p q st) y =
      st_val ws st y + &D * qv p q * mono ws tag i j y` by v2_tac >>
  `~(mp < 0)`
    by (strip_tac >> qpat_x_assum `FST _` mp_tac >> asm_simp_tac std_ss [add_form_def, fst_bad]) >>
  `kind = 0 \/ kind = 1 \/ kind = 2 \/ kind = 3 \/ kind = 4 \/ kind = 5 \/ kind = 6`
    by (qpat_x_assum `kind <= 6` mp_tac >> rpt (pop_assum kall_tac) >> decide_tac) >>
  qpat_x_assum `FST _` mp_tac >>
  pop_assum strip_assume_tac >>
  step_tac [add_form_def, fst_at, wf_at_eq, form_val_def, mono_def, qv_neg, qv_mul, real_of_int_num]
QED

Theorem S084 = CONV_RULE (RAND_CONV (REWR_CONV S084_def)) S084_as_constants
