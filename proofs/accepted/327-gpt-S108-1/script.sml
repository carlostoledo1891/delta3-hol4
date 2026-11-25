Theory attempt
Ancestors
  arithmetic list integer real intreal delta3_check delta3_check2 delta3_sem delta3_stmts
Libs
  intLib realLib

Theorem clear_denoms[local]:
  !a b e t x y z:real.
    0 < x /\ 0 < y /\ 0 < z /\ a*y*z <= (b*z-e*t*y)*x ==>
    a/x <= b/y - e/z*t
Proof
  rpt gen_tac >> strip_tac >>
  `0 < x*y*z` by (rpt (irule REAL_LT_MUL >> conj_tac) >> asm_rewrite_tac []) >>
  `x <> 0 /\ y <> 0 /\ z <> 0` by realLib.REAL_ASM_ARITH_TAC >>
  `(a/x)*(x*y*z) = a*y*z` by
    metis_tac [RealField.REAL_FIELD ``!a x y z:real. x <> 0 ==> (a/x)*(x*y*z)=a*y*z``] >>
  `(b/y - e/z*t)*(x*y*z) = (b*z-e*t*y)*x` by
    metis_tac [RealField.REAL_FIELD
      ``!b e t x y z:real. y <> 0 /\ z <> 0 ==>
       (b/y-e/z*t)*(x*y*z)=(b*z-e*t*y)*x``] >>
  metis_tac [REAL_LE_RMUL]
QED

Theorem S108_as_constants[local]:
  S108
Proof
  rewrite_tac [S108_def,qv_def] >> rpt gen_tac >> strip_tac >>
  irule clear_denoms >> simp [] >>
  qpat_x_assum `(_ : int) <= _` (mp_tac o REWRITE_RULE [GSYM real_of_int_le]) >>
  rewrite_tac [real_of_int_mul,real_of_int_sub,real_of_int_num] >> simp []
QED

Theorem S108 = EQ_MP S108_def S108_as_constants
