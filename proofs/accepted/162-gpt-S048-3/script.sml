Theory attempt
Ancestors
  arithmetic list integer real intreal delta3_check delta3_check2 delta3_sem delta3_stmts
Libs
  intLib realLib RealField

fun trace_goal label ((asl,w):goal) =
  print (label ^ "\n" ^ String.concatWith "\n" (map term_to_string (rev asl)) ^
         "\n|- " ^ term_to_string w ^ "\n")
fun stage label tac g c = tac g c handle e => (trace_goal label g; raise e)
fun inspect label g c = (trace_goal label g; ALL_TAC g c)
fun dep th = SPEC_ALL (EQ_MP th (ASSUME (lhs (concl th))))
val well = CONJUNCT1 (dep S110_def)
val back = CONJUNCT2 (dep S110_def)
val act = dep S042_def
Theorem bad_fst[local]:
  !st. ~FST (bad st)
Proof
  gen_tac >> PairCases_on ‘st’ >> simp [bad_def]
QED
Theorem cut_ok[local]:
  S110 ==> !cs st. FST (add_cut0 D n u cs st) ==> FST st
Proof
  strip_tac >> Induct >- simp [add_cut0_def] >> rpt gen_tac >> stage "pair head" (PairCases_on ‘h’) >>
  Cases_on ‘h2 = 1’ >> Cases_on ‘h2 = -1’ >>
  simp [add_cut0_def] >> stage "back" (metis_tac [back,bad_fst])
QED
Theorem cut_alg[local]:
  a = z + d * qv (-&w) (1096 * 1096) * (x*y) /\ b = a + d * v ==>
  b = z + d * (-(&w / &(1096 * 1096) * (x*y)) + v)
Proof
  simp_tac bool_ss [qv_def,real_div,real_of_int_neg,real_of_int_num] >>
  RealField.REAL_ARITH_TAC
QED
Theorem cut_action[local]:
  S110 /\ S042 ==> !cs st.
     0 < D /\ st_wf n st /\ LENGTH y = n /\ FST (add_cut0 D n (1096*1096) cs st) ==>
     FST st /\ st_wf n (add_cut0 D n (1096*1096) cs st) /\
     st_val ws (add_cut0 D n (1096*1096) cs st) y = st_val ws st y + &D * cut0_val cs y
Proof
  strip_tac >> Induct >- simp [add_cut0_def,cut0_val_def] >>
  rpt gen_tac >> PairCases_on ‘h’ >>
  Cases_on ‘h2 = 1’
  >- (asm_simp_tac bool_ss [add_cut0_def,cut0_val_def,REAL_ADD_LID] >> metis_tac []) >>
  Cases_on ‘h2 = -1’
  >| [ALL_TAC, asm_simp_tac bool_ss [add_cut0_def,cut0_val_def] >> metis_tac [bad_fst,cut_ok]] >>
  asm_simp_tac bool_ss [add_cut0_def,cut0_val_def] >>
  qabbrev_tac ‘t1 = add_term D n 2 h0 h1 (-&h3) (1096*1096) st’ >>
  strip_tac >>
  ‘FST t1’ by metis_tac [cut_ok] >>
  ‘FST st’ by (qunabbrev_tac ‘t1’ >> metis_tac [back]) >>
  ‘st_wf n t1’ by (qunabbrev_tac ‘t1’ >> metis_tac [well]) >>
  ‘st_val ws t1 y = st_val ws st y + &D * qv (-&h3) (1096*1096) * (EL h0 y * EL h1 y)’
     by (qunabbrev_tac ‘t1’ >> metis_tac [act,EVAL “mono ws 2 h0 h1 y”]) >>
  first_x_assum (qspec_then ‘t1’ mp_tac) >>
  asm_rewrite_tac [] >> strip_tac >> metis_tac [cut_alg]
QED
Theorem S048_const[local]:
  S110 /\ S042 ==> S048
Proof
  rewrite_tac [S048_def] >> metis_tac [cut_action]
QED
Theorem S048 = CONV_RULE (RAND_CONV (REWR_CONV S048_def)) S048_const
