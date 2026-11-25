Theory attempt
Ancestors
  arithmetic list integer real intreal delta3_check delta3_check2 delta3_sem delta3_stmts
Libs
  intLib realLib

Theorem forms_ok[local]:
  S095 ==> !forms D n lp lq hp hq st.
    FST (add_forms D n 1096 lp lq hp hq forms st) ==> FST st
Proof
  strip_tac >> Induct >> rpt gen_tac
  >- simp [add_forms_def]
  >> PairCases_on ‘h’ >> rewrite_tac [add_forms_def] >>
  metis_tac [S095_def]
QED

Theorem one_form[local]:
  S095 /\ S084 /\ S098 /\ S089 ==>
  !D n st ws y lp lq hp hq kind i j k s1 s2 s3 mp mq.
    0 < D /\ st_wf n st /\ LENGTH (y:real list) = n /\
    FST (add_form D n 1096 lp lq hp hq kind i j k s1 s2 s3 mp mq st) ==>
    FST st /\ st_wf n (add_form D n 1096 lp lq hp hq kind i j k s1 s2 s3 mp mq st) /\
    st_val ws (add_form D n 1096 lp lq hp hq kind i j k s1 s2 s3 mp mq st) y =
    st_val ws st y - &D * qv mp mq *
      form_val (ldot ws y / 1096) (qv lp lq) (qv hp hq) kind i j k s1 s2 s3 y
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  ‘FST st /\ kind <= 14’ by metis_tac [S095_def] >>
  Cases_on ‘kind <= 6’ >- metis_tac [S084_def] >>
  Cases_on ‘kind = 14’ >- metis_tac [S089_def] >>
  ‘7 <= kind /\ kind <= 13’ by decide_tac >>
  metis_tac [S098_def]
QED

Theorem S146_as_constants[local]:
  S095 /\ S084 /\ S098 /\ S089 ==> S146
Proof
  strip_tac >> rewrite_tac [S146_def] >> rpt gen_tac >>
  qid_spec_tac ‘st’ >> Induct_on ‘forms’
  >- simp [add_forms_def, forms_val_def] >>
  rpt gen_tac >> PairCases_on ‘h’ >>
  rewrite_tac [add_forms_def, forms_val_def] >> strip_tac >>
  ‘FST (add_form D n 1096 lp lq hp hq h0 h1 h2 h3 h4 h5 h6 h7 h8 st)’ by metis_tac [forms_ok] >>
  mp_tac (Q.SPECL [‘D’,‘n’,‘st’,‘ws’,‘y’,‘lp’,‘lq’,‘hp’,‘hq’,‘h0’,‘h1’,‘h2’,‘h3’,‘h4’,‘h5’,‘h6’,‘h7’,‘h8’]
            (MATCH_MP one_form (LIST_CONJ (map ASSUME [“S095”,“S084”,“S098”,“S089”])))) >>
  impl_tac >- simp [] >> strip_tac >>
  qpat_x_assum ‘!st. _’ (qspec_then ‘add_form D n 1096 lp lq hp hq h0 h1 h2 h3 h4 h5 h6 h7 h8 st’ mp_tac) >>
  impl_tac >- simp [] >> strip_tac >> asm_rewrite_tac [] >>
  realLib.REAL_ARITH_TAC
QED

Theorem S146 = CONV_RULE (RAND_CONV (REWR_CONV S146_def)) S146_as_constants

