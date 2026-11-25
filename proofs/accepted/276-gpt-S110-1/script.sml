Theory attempt
Ancestors
  arithmetic list integer real intreal delta3_check delta3_check2 delta3_sem delta3_stmts
Libs
  intLib realLib

val addl_len = GEN_ALL (CONJUNCT1 (SPEC_ALL (REWRITE_RULE[S041_def] (ASSUME “S041”))))
val mat_parts = CONJUNCTS (SPEC_ALL (REWRITE_RULE[S021_def] (ASSUME “S021”)))
val addm_len = GEN_ALL (hd mat_parts)
val addm_shape = GEN_ALL (hd (tl mat_parts))

Theorem S110_as_constants[local]:
  S041 /\ S021 ==> S110
Proof
  rewrite_tac[S110_def] >> strip_tac >> rpt gen_tac >> PairCases_on ‘st’ >>
  rw[add_term_def,st_wf_def,LET_THM,addl_len,addm_len,addm_shape] >>
  gvs[st_wf_def,addl_len,addm_len,addm_shape] >> decide_tac
QED

Theorem S110 = CONV_RULE (RAND_CONV (REWR_CONV S110_def)) S110_as_constants

