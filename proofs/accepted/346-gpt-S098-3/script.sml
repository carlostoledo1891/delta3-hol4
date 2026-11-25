Theory attempt
Ancestors
  arithmetic list integer real intreal delta3_check delta3_check2 delta3_sem delta3_stmts
Libs
  intLib realLib

val inp = SPEC_ALL (UNDISCH (fst (EQ_IMP_RULE S110_def)))
val keep_shape = CONJUNCT1 inp
val keep_ok = CONJUNCT2 inp
val term_value = SPEC_ALL (UNDISCH (fst (EQ_IMP_RULE S042_def)))
Theorem bad_flag[local]:
  !st. FST (bad st) = F
Proof
  gen_tac >> PairCases_on `st` >> simp [bad_def]
QED

fun evaluate_terms pos len base ok =
  let val state = rand (concl ok)
  in if aconv state (rand (concl base)) then (base,NONE)
     else
       let val prior_ok = CONJUNCT1 (MATCH_MP keep_ok ok)
           val (prior,eqn) = evaluate_terms pos len base prior_ok
           val shape = mk_comb (rator (concl prior),state)
           val wf = MP (PART_MATCH (snd o dest_imp) keep_shape shape) prior
           val r = PART_MATCH (List.last o strip_conj o fst o dest_imp) term_value (concl ok)
           val v = MP r (LIST_CONJ [pos,prior,len,ok])
           val v' = case eqn of NONE => v | SOME e => CONV_RULE (RAND_CONV (LAND_CONV (REWR_CONV e))) v
       in (wf,SOME v') end
  end
fun record_terms pos len base ok =
  let val (wf,eqn) = evaluate_terms pos len base ok
  in ASSUME_TAC wf >> ASSUME_TAC (valOf eqn) end

Theorem range_cases[local]:
  !kind:num. 7 <= kind /\ kind <= 13 ==>
    kind = 7 \/ kind = 8 \/ kind = 9 \/ kind = 10 \/ kind = 11 \/ kind = 12 \/ kind = 13
Proof
  decide_tac
QED

fun split_kinds th =
  if is_disj (concl th) then DISJ_CASES_THEN split_kinds th
  else SUBST_ALL_TAC th

fun add_flags ok =
  let val t = rand (concl ok)
  in if is_var t then ASSUME_TAC ok
     else ASSUME_TAC ok >> add_flags (CONJUNCT1 (MATCH_MP keep_ok ok))
  end

val algebra =
  simp_tac (bool_ss ++ numSimps.REDUCE_ss)
    [mono_def,qv_def,real_div,real_of_int_num,real_of_int_neg,real_of_int_mul,
     real_of_int_add,real_of_int_sub,GSYM REAL_OF_NUM_MUL,REAL_INV_MUL'] >>
  (CONV_TAC (BINOP_CONV RealField.REAL_POLY_CONV) >> REFL_TAC
   ORELSE RealField.REAL_ARITH_TAC)
fun trace_goal label (g as (asl,w)) =
  (print (label ^ "\n" ^ String.concatWith "\n" (map term_to_string (rev asl)) ^
          "\n|- " ^ term_to_string w ^ "\n"); ALL_TAC g)

Theorem S098_as_constants[local]:
  S110 /\ S042 ==> S098
Proof
  strip_tac >> rewrite_tac [S098_def] >> rpt gen_tac >> strip_tac >>
  mp_tac (Q.SPEC `kind` range_cases) >> impl_tac >- asm_rewrite_tac [] >>
  disch_then split_kinds >>
  qpat_x_assum `FST _` mp_tac >> Cases_on `mp < 0` >>
  asm_simp_tac (srw_ss()) [add_form_def,bad_flag,form_val_def] >>
  trace_goal "case" >>
  ((qpat_assum `0 < D` (fn pos => qpat_assum `LENGTH y = n` (fn len =>
      qpat_assum `st_wf n st` (fn base => disch_then (record_terms pos len base)))) >>
    asm_rewrite_tac [] >> trace_goal "identity" >> algebra >> NO_TAC)
   ORELSE
   (disch_then add_flags >>
    asm_simp_tac (srw_ss()) [keep_shape,term_value,mono_def] >>
    trace_goal "identity by rewriting" >> algebra))
QED

Theorem S098 = CONV_RULE (RAND_CONV (REWR_CONV S098_def)) S098_as_constants
