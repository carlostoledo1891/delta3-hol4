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
Theorem cc_ok[local]:
  S110 ==> !cc i st. FST (add_cc D n i cc st) ==> FST st
Proof
  strip_tac >> Induct >- simp [add_cc_def] >> rpt gen_tac >> stage "pair head" (PairCases_on ‘h’) >>
  Cases_on ‘h0 < 0’ >> simp [add_cc_def,bad_fst] >> stage "back" (metis_tac [back])
QED
Theorem cc_nonneg[local]:
  ~(p < 0:int) /\ i < n /\ in_box n y ==> 0 <= qv p q * EL i y
Proof
  strip_tac >>
  ‘0 <= EL i y’ by (fs [in_box_def,EVERY_EL] >> metis_tac []) >>
  ‘0 <= p’ by metis_tac [INT_NOT_LT] >>
  ‘0 <= real_of_int p’ by metis_tac [real_of_int_le,real_of_int_num] >>
  irule REAL_LE_MUL >> asm_rewrite_tac [] >>
  rewrite_tac [qv_def] >> irule REAL_LE_DIV >> simp []
QED
Theorem cc_alg[local]:
  a = z + d * qv (-p) q * x /\ b = a - d * v ==>
  b = z - d * (qv p q * x + v)
Proof
  simp_tac bool_ss [qv_def,real_div,real_of_int_neg] >> RealField.REAL_ARITH_TAC
QED
Theorem cc_action[local]:
  S110 /\ S042 ==> !cc i st.
     0 < D /\ st_wf n st /\ LENGTH y = n /\ FST (add_cc D n i cc st) ==>
     FST st /\ st_wf n (add_cc D n i cc st) /\
     st_val ws (add_cc D n i cc st) y = st_val ws st y - &D * cc_val i cc y /\
     (in_box n y ==> 0 <= cc_val i cc y)
Proof
  strip_tac >> Induct >- simp [add_cc_def,cc_val_def] >>
  rpt gen_tac >> PairCases_on ‘h’ >>
  Cases_on ‘h0 < 0’ >- simp [add_cc_def,bad_fst] >>
  asm_simp_tac bool_ss [add_cc_def,cc_val_def] >>
  qabbrev_tac ‘t1 = add_term D n 1 i 0 (-h0) h1 st’ >>
  strip_tac >>
  ‘FST t1’ by metis_tac [cc_ok] >>
  ‘FST st /\ i < n’ by (qunabbrev_tac ‘t1’ >> metis_tac [back]) >>
  ‘st_wf n t1’ by (qunabbrev_tac ‘t1’ >> metis_tac [well]) >>
  ‘st_val ws t1 y = st_val ws st y + &D * qv (-h0) h1 * EL i y’
    by (qunabbrev_tac ‘t1’ >> metis_tac [act,EVAL “mono ws 1 i 0 y”]) >>
  first_x_assum (qspecl_then [‘i+1’, ‘t1’] mp_tac) >>
  asm_rewrite_tac [] >> strip_tac >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  TRY (metis_tac [cc_alg] >> NO_TAC) >>
  strip_tac >> irule REAL_LE_ADD >> metis_tac [cc_nonneg]
QED
Theorem S047_const[local]:
  S110 /\ S042 ==> S047
Proof
  rewrite_tac [S047_def] >> metis_tac [cc_action]
QED
Theorem S047 = CONV_RULE (RAND_CONV (REWR_CONV S047_def)) S047_const
