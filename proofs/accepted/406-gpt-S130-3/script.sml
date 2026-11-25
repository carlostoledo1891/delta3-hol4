Theory attempt
Ancestors
  arithmetic list integer real intreal delta3_check delta3_check2 delta3_sem delta3_stmts
Libs
  intLib realLib

val shape = CONJUNCT1 (SPEC_ALL (EQ_MP S110_def (ASSUME “S110”)))
val guards = CONJUNCT2 (SPEC_ALL (EQ_MP S110_def (ASSUME “S110”)))
val effect = SPEC_ALL (EQ_MP S042_def (ASSUME “S042”))

Theorem cells[local]:
  S110 /\ S042 ==> !ab i st.
    0 < D /\ st_wf n st /\ LENGTH (y:real list) = n /\ FST (add_cells D n i ab st) ==>
    FST st /\ st_wf n (add_cells D n i ab st) /\
    st_val ws (add_cells D n i ab st) y = st_val ws st y + &D * cells_val i ab y
Proof
  strip_tac >> Induct
  >- simp [add_cells_def, cells_val_def]
  >> rpt gen_tac >> rename1 ‘add_cells D n i (hh::rest) st’ >> PairCases_on ‘hh’ >>
  PURE_REWRITE_TAC [add_cells_def, cells_val_def] >> strip_tac >>
  `st_wf n (add_term D n 1 i 0 hh0 hh1 st)` by (irule shape >> asm_rewrite_tac []) >>
  `st_wf n (add_term D n 2 i i hh2 hh3 (add_term D n 1 i 0 hh0 hh1 st))` by (irule shape >> asm_rewrite_tac []) >>
  first_x_assum (qspecl_then [`i+1`, `add_term D n 2 i i hh2 hh3 (add_term D n 1 i 0 hh0 hh1 st)`] mp_tac) >>
  asm_rewrite_tac [] >> strip_tac >>
  `FST (add_term D n 1 i 0 hh0 hh1 st)` by metis_tac [guards] >>
  `FST st` by metis_tac [guards] >>
  `st_val ws (add_term D n 1 i 0 hh0 hh1 st) y = st_val ws st y + &D * qv hh0 hh1 * mono ws 1 i 0 y` by (irule effect >> asm_rewrite_tac []) >>
  `st_val ws (add_term D n 2 i i hh2 hh3 (add_term D n 1 i 0 hh0 hh1 st)) y = st_val ws (add_term D n 1 i 0 hh0 hh1 st) y + &D * qv hh2 hh3 * mono ws 2 i i y` by (irule effect >> asm_rewrite_tac []) >>
  asm_simp_tac (srw_ss()) [mono_def] >> CONV_TAC (EQT_INTRO o RealField.REAL_RING)
QED

Theorem S130_as_constants[local]:
  S110 /\ S042 ==> S130
Proof
  PURE_REWRITE_TAC [S130_def] >>
  disch_then (fn d => rpt gen_tac >> MATCH_ACCEPT_TAC (SPEC_ALL (MP cells d)))
QED

Theorem S130 = CONV_RULE (RAND_CONV (REWR_CONV S130_def)) S130_as_constants
