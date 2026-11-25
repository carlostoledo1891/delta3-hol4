Theory attempt
Ancestors
  arithmetic list integer real intreal delta3_check delta3_check2 delta3_sem delta3_stmts
Libs
  intLib realLib RealField

Theorem plus_cube[local]:
  !x y z:real. -1 <= x /\ x <= 1 /\ -1 <= y /\ y <= 1 /\ -1 <= z /\ z <= 1 ==>
     0 <= 1 + x*y + y*z + x*z
Proof
  rpt strip_tac >>
  ‘0 <= (1+x)*((1+y)*(1+z))’ by
    (irule REAL_LE_MUL >> conj_tac >- RealField.REAL_ASM_ARITH_TAC >>
     irule REAL_LE_MUL >> RealField.REAL_ASM_ARITH_TAC) >>
  ‘0 <= (1-x)*((1-y)*(1-z))’ by
    (irule REAL_LE_MUL >> conj_tac >- RealField.REAL_ASM_ARITH_TAC >>
     irule REAL_LE_MUL >> RealField.REAL_ASM_ARITH_TAC) >>
  RealField.REAL_ASM_ARITH_TAC
QED
Theorem S054_const[local]:
  S054
Proof
  rewrite_tac [S054_def] >> rpt gen_tac >> strip_tac >>
  gvs [] >> MAP_EVERY (fn q => mp_tac (Q.SPECL q plus_cube))
   [[‘a’,‘b’,‘c’],[‘-a’,‘b’,‘c’],[‘a’,‘b’,‘-c’],[‘-a’,‘b’,‘-c’]] >>
  simp [] >> RealField.REAL_ASM_ARITH_TAC
QED
Theorem S054 = EQ_MP S054_def S054_const
