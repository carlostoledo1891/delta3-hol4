Theory attempt
Ancestors
  arithmetic list integer real intreal delta3_check delta3_check2 delta3_sem delta3_stmts
Libs
  intLib realLib RealField

Theorem split_rows[local]:
  !rs:int list list. EVERY (\r. LENGTH r = SUC n) rs ==>
    heads rs = MAP HD rs /\ tails rs = MAP TL rs /\
    EVERY (\r. LENGTH r = n) (tails rs)
Proof
  Induct >> simp [heads_def,tails_def] >> Cases_on ‘h’ >>
  simp [heads_def,tails_def] >> metis_tac []
QED
Theorem tr0[local]:
  transp 0 rs = []
Proof
  CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [transp_def])) >> simp []
QED
Theorem trS[local]:
  transp (SUC n) rs = heads rs :: transp n (tails rs)
Proof
  CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [transp_def])) >> simp []
QED
Theorem trans[local]:
  !n rs. EVERY (\r. LENGTH r = n) rs ==>
    LENGTH (transp n rs) = n /\ EVERY (\r. LENGTH r = LENGTH rs) (transp n rs) /\
    !i j. i < n /\ j < LENGTH rs ==> EL j (EL i (transp n rs)) = EL i (EL j rs)
Proof
  Induct >- simp [tr0] >>
  gen_tac >> strip_tac >>
  ‘heads rs = MAP HD rs /\ tails rs = MAP TL rs /\
   EVERY (\r. LENGTH r = n) (MAP TL rs)’ by metis_tac [split_rows] >>
  first_x_assum (qspec_then ‘MAP TL rs’ mp_tac) >>
  asm_simp_tac (srw_ss()) [] >> strip_tac >>
  asm_simp_tac (srw_ss()) [trS] >>
  rpt strip_tac >> Cases_on ‘i’ >>
  fs [EL,EL_MAP] >>
  TRY (qpat_x_assum ‘!i j. _’ (qspecl_then [‘n'’,‘j’] mp_tac) >>
       asm_simp_tac (srw_ss()) [EL_MAP]) >>
  metis_tac [EL_MAP]
QED
Theorem S052_const[local]:
  S052
Proof
  rewrite_tac [S052_def] >> metis_tac [trans]
QED
Theorem S052 = EQ_MP S052_def S052_const
