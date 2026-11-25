Theory attempt
Ancestors
  arithmetic list integer real intreal delta3_check delta3_check2 delta3_sem delta3_stmts
Libs
  intLib realLib


val step_wf = GEN_ALL (CONJUNCT1 (SPEC_ALL (REWRITE_RULE[S110_def] (ASSUME “S110”))))
val step_guard = GEN_ALL (CONJUNCT2 (SPEC_ALL (REWRITE_RULE[S110_def] (ASSUME “S110”))))
val step_value = REWRITE_RULE[S042_def] (ASSUME “S042”)

fun first_guard th =
  let val h = fst (dest_imp (concl th))
  in GEN_ALL (DISCH h (CONJUNCT1 (UNDISCH th))) end

val guard_back = first_guard (SPEC_ALL step_guard)

fun trace_guard th =
  case total (MATCH_MP guard_back) th of
     NONE => ALL_TAC
   | SOME parent => ASSUME_TAC parent THEN trace_guard parent

Theorem S117_as_constants[local]:
  S110 /\ S042 ==> S117
Proof
  strip_tac >> rewrite_tac[S117_def,add_zz_def] >> rpt gen_tac >> strip_tac >>
  qpat_assum ‘FST (add_term _ _ _ _ _ _ _ _)’ trace_guard >>
  asm_simp_tac (srw_ss()) [step_wf,step_value,mono_def,qv_def,real_div] >>
  FIRST [REAL_ARITH_TAC,CONV_TAC RealField.REAL_RING]
QED

Theorem S117 = CONV_RULE (RAND_CONV (REWR_CONV S117_def)) S117_as_constants

