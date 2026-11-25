Theory attempt
Ancestors
  arithmetic list integer real intreal delta3_check delta3_check2 delta3_sem delta3_stmts
Libs
  intLib realLib RealField

fun dep th = SPEC_ALL (EQ_MP th (ASSUME (lhs (concl th))))
val d17 = dep S017_def
val d41 = CONJUNCT2 (dep S041_def)
val d21 = CONJUNCT2 (CONJUNCT2 (dep S021_def))
val back = CONJUNCT2 (dep S110_def)
Theorem nstep[local]:
  S017 /\ S041 /\ S021 /\ S110 ==> !D n st y tag i j p q ws.
  0 < D /\ st_wf n st /\ LENGTH y = n /\ FST (add_term D n tag i j p q st) ==>
  st_val ws (add_term D n tag i j p q st) y = st_val ws st y + &D * qv p q * mono ws tag i j y
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  ‘D MOD q = 0 /\ i < n /\ j < n /\ tag <= 5’ by metis_tac [back] >>
  ‘real_of_int (sc D p q) = &D * qv p q’ by metis_tac [d17] >>
  PairCases_on ‘st’ >>
  ‘LENGTH st2 = n /\ LENGTH st3 = n /\ EVERY (\r. LENGTH r = n) st3 /\ LENGTH st5 = n’
    by fs [st_wf_def] >>
  ‘ldot (addl i (sc D p q) st2) y = ldot st2 y + real_of_int (sc D p q) * EL i y’
     by metis_tac [d41] >>
  ‘ldot (addl i (sc D p q) st5) y = ldot st5 y + real_of_int (sc D p q) * EL i y’
     by metis_tac [d41] >>
  ‘qform (addm i j (sc D p q) st3) y y =
     qform st3 y y + real_of_int (sc D p q) * (EL i y * EL j y)’
     by metis_tac [d21] >>
  ‘tag = 0 \/ tag = 1 \/ tag = 2 \/ tag = 3 \/ tag = 4 \/ tag = 5’ by decide_tac >>
  fs [add_term_def,st_val_def,mono_def] >> TRY (CONV_TAC (EQT_INTRO o RealField.REAL_RING))
QED
Theorem S042_const[local]:
  S017 /\ S041 /\ S021 /\ S110 ==> S042
Proof
  rewrite_tac [S042_def] >> metis_tac [nstep]
QED
Theorem S042 = CONV_RULE (RAND_CONV (REWR_CONV S042_def)) S042_const
