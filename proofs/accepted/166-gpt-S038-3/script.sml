Theory attempt
Ancestors
  arithmetic list integer real intreal delta3_check delta3_check2 delta3_sem delta3_stmts
Libs
  intLib realLib RealField

Theorem lin_law[local]:
  !ws g (c:int). LENGTH ws = LENGTH g ==>
    LENGTH (lin c ws g) = LENGTH g /\
    !i. i < LENGTH g ==> EL i (lin c ws g) = EL i g + c * EL i ws
Proof
  Induct
  >- (Cases >> simp [lin_def]) >>
  rpt gen_tac >> namedCases_on ‘g’ ["","z zs"]
  >- simp [lin_def] >>
  first_x_assum (qspecl_then [‘zs’,‘c’] mp_tac) >>
  Cases_on ‘LENGTH ws = LENGTH zs’ >> simp_tac (srw_ss()) [lin_def] >>
  asm_simp_tac (srw_ss()) [] >> rpt strip_tac >>
  TRY (first_assum ACCEPT_TAC) >>
  Cases_on ‘i’ >> fs []
QED
Theorem S038_const[local]:
  S038
Proof
  rewrite_tac [S038_def] >> rpt strip_tac >> metis_tac [lin_law]
QED
Theorem S038 = EQ_MP S038_def S038_const
