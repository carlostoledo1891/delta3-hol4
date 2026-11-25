Theory attempt
Ancestors
  arithmetic list integer real intreal delta3_check delta3_check2 delta3_sem delta3_stmts
Libs
  intLib realLib

val inp = SPEC_ALL (UNDISCH (fst (EQ_IMP_RULE S110_def)))
val keep_shape = CONJUNCT1 inp
val keep_ok = CONJUNCT2 inp
val term_value = SPEC_ALL (UNDISCH (fst (EQ_IMP_RULE S042_def)))
fun collect_flags th =
  let val prev = CONJUNCT1 (MATCH_MP keep_ok th)
  in ASSUME_TAC prev >> collect_flags prev end
  handle HOL_ERR _ => ALL_TAC
fun trace_goal label (g as (asl,w)) =
  (print (label ^ "\n" ^ String.concatWith "\n" (map term_to_string (rev asl)) ^
          "\n|- " ^ term_to_string w ^ "\n"); ALL_TAC g)

Theorem S100_as_constants[local]:
  S110 /\ S042 ==> S100
Proof
  strip_tac >> trace_goal "phase 1" >> rewrite_tac [S100_def] >> trace_goal "phase 2" >> rpt gen_tac >> trace_goal "phase 3" >>
  map_every qid_spec_tac [`st`,`full`] >> trace_goal "phase 4" >> Induct
  >- simp [add_full_def,full_val_def] >> trace_goal "phase 5" >>
  rpt gen_tac >> trace_goal "phase 6" >> PairCases_on `h` >> trace_goal "phase 7" >>
  pure_rewrite_tac [add_full_def,full_val_def] >> trace_goal "phase 8" >> strip_tac >> trace_goal "phase 9" >>
  `st_wf n (add_term D n 2 h0 h1 h2 (1096*1096) st)` by metis_tac [keep_shape] >> trace_goal "phase 10" >>
  qpat_x_assum `!st. _` (qspec_then `add_term D n 2 h0 h1 h2 (1096*1096) st` mp_tac) >> trace_goal "phase 11" >>
  impl_tac >- asm_rewrite_tac [] >> trace_goal "phase 12" >> strip_tac >> trace_goal "phase 13" >>
  conj_tac >- metis_tac [keep_ok] >> trace_goal "phase 14" >>
  asm_rewrite_tac [] >> trace_goal "phase 15" >> 
  asm_simp_tac (srw_ss()) [term_value,mono_def] >> trace_goal "phase 16" >>
  RealField.REAL_ARITH_TAC
QED

Theorem S100 = CONV_RULE (RAND_CONV (REWR_CONV S100_def)) S100_as_constants
