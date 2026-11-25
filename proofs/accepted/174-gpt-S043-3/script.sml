Theory attempt
Ancestors
  arithmetic list integer real intreal delta3_check delta3_check2 delta3_sem delta3_stmts
Libs
  intLib realLib RealField

fun dep th = SPEC_ALL (EQ_MP th (ASSUME (lhs (concl th))))
val well = CONJUNCT1 (dep S110_def)
val back = CONJUNCT2 (dep S110_def)
val act = dep S042_def
Theorem bad_fst[local]:
  !st. ~FST (bad st)
Proof
  gen_tac >> PairCases_on ‘st’ >> simp [bad_def]
QED
Theorem kap_eq[local]:
  (z + d * qv (-(kp * rp)) (kq * rq * 1096) * x) +
   d * qv kp (kq * (1096*1096)) * (x*x) =
   z - d * qv kp kq * ((x / 1096) * (qv rp rq - x / 1096))
Proof
  simp_tac bool_ss [qv_def,real_div,GSYM REAL_OF_NUM_MUL,REAL_INV_MUL',
                    real_of_int_mul,real_of_int_neg] >>
  RealField.REAL_ARITH_TAC
QED
Theorem S043_const[local]:
  S110 /\ S042 ==> S043
Proof
  rewrite_tac [S043_def] >> strip_tac >> rpt gen_tac >>
  Cases_on ‘kp < 0’ >- simp [add_kap_def,bad_fst] >>
  asm_simp_tac bool_ss [add_kap_def] >>
  qabbrev_tac ‘t1 = add_term D n 3 0 0 (-(kp*rp)) (kq*rq*1096) st’ >>
  qabbrev_tac ‘t2 = add_term D n 5 0 0 kp (kq*(1096*1096)) t1’ >>
  strip_tac >>
  ‘FST t1’ by (qunabbrev_tac ‘t2’ >> metis_tac [back]) >>
  ‘FST st’ by (qunabbrev_tac ‘t1’ >> metis_tac [back]) >>
  ‘st_wf n t1’ by (qunabbrev_tac ‘t1’ >> metis_tac [well]) >>
  ‘st_wf n t2’ by (qunabbrev_tac ‘t2’ >> metis_tac [well]) >>
  ‘0 <= kp’ by metis_tac [INT_NOT_LT] >>
  ‘st_val ws t1 y = st_val ws st y + &D * qv (-(kp*rp)) (kq*rq*1096) * ldot ws y’
    by (qunabbrev_tac ‘t1’ >> metis_tac [act,EVAL “mono ws 3 0 0 y”]) >>
  ‘st_val ws t2 y = st_val ws t1 y + &D * qv kp (kq*(1096*1096)) * (ldot ws y * ldot ws y)’
    by (qunabbrev_tac ‘t2’ >> metis_tac [act,EVAL “mono ws 5 0 0 y”]) >>
  asm_rewrite_tac [] >> TRY (MATCH_ACCEPT_TAC kap_eq) >> metis_tac [kap_eq]
QED
Theorem S043 = CONV_RULE (RAND_CONV (REWR_CONV S043_def)) S043_const
