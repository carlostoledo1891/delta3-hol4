Theory attempt
Ancestors
  arithmetic list integer real intreal delta3_check delta3_check2 delta3_sem delta3_stmts
Libs
  intLib realLib

Theorem bad_flag[local]:
  !st. ~FST (bad st)
Proof
  gen_tac >> PairCases_on `st` >> simp [bad_def]
QED

Theorem nonneg_ratio[local]:
  0 <= (p:int) ==> 0 <= qv p q
Proof
  strip_tac >> rw [qv_def] >> irule REAL_LE_DIV >>
  metis_tac [real_of_int_le, real_of_int_num, REAL_POS]
QED

Theorem nu_coeff[local]:
  qv (-(p * rp)) (q * rq) = -(qv p q * qv rp rq) /\
  qv p (q * 1096) = qv p q / 1096
Proof
  conj_tac >> rewrite_tac [qv_def, real_div, real_of_int_neg, real_of_int_mul,
    GSYM REAL_OF_NUM_MUL, REAL_INV_MUL'] >> CONV_TAC (EQT_INTRO o RealField.REAL_RING)
QED

Theorem nu_algebra[local]:
  a + &D * qv (-(p * rp)) (q * rq) * mono ws 1 j 0 y +
      &D * qv p (q * 1096) * mono ws 4 j 0 y - &D * b =
  a - &D * (qv p q * (EL j y * (qv rp rq - ldot ws y / 1096)) + b)
Proof
  rewrite_tac [nu_coeff] >>
  simp_tac (srw_ss()) [mono_def] >>
  rewrite_tac [real_div] >> CONV_TAC (EQT_INTRO o RealField.REAL_RING)
QED

Theorem boxed_entry[local]:
  !n y j. in_box n y /\ j < n ==> 0 <= EL j y
Proof
  rewrite_tac [in_box_def, EVERY_EL] >> simp_tac bool_ss [] >> metis_tac []
QED

Theorem nu_sign[local]:
  ~(p < 0) /\ j < n /\ (in_box n y /\ m <= rin ==> 0 <= b) ==>
  (in_box n y /\ m <= rin ==> 0 <= qv p q * (EL j y * (rin-m)) + b)
Proof
  rewrite_tac [INT_NOT_LT] >> rpt strip_tac >>
  irule REAL_LE_ADD >> conj_tac
  >- (irule REAL_LE_MUL >> conj_tac
      >- (irule nonneg_ratio >> asm_rewrite_tac []) >>
      irule REAL_LE_MUL >> conj_tac
      >- metis_tac [boxed_entry] >>
      asm_rewrite_tac [REAL_SUB_LE]) >>
  metis_tac []
QED

Theorem nu_induction[local]:
  S110 /\ S042 ==>
  !nu j st. 0 < D /\ st_wf n st /\ LENGTH y = n /\
    FST (add_nu D n 1096 rp rq j nu st) ==>
    FST st /\ st_wf n (add_nu D n 1096 rp rq j nu st) /\
    st_val ws (add_nu D n 1096 rp rq j nu st) y =
      st_val ws st y - &D * nu_val (ldot ws y / 1096) (qv rp rq) j nu y /\
    (in_box n y /\ m <= rin ==> 0 <= nu_val m rin j nu y)
Proof
  strip_tac >> Induct >- (simp [add_nu_def, nu_val_def] >> metis_tac []) >>
  rpt gen_tac >> goalStack.print_tac "successor case" >> PairCases_on `h` >>
  Cases_on `h0 < 0` >> asm_simp_tac bool_ss [add_nu_def, nu_val_def, bad_flag] >>
  strip_tac >>
  qabbrev_tac `s = add_term D n 1 j 0 (-(h0 * rp)) (h1 * rq) st` >>
  qabbrev_tac `t = add_term D n 4 j 0 h0 (h1 * 1096) s` >>
  goalStack.print_tac "intermediate states" >>
  `st_wf n s` by (fs [Abbr`s`] >> metis_tac [S110_def]) >>
  `st_wf n t` by (fs [Abbr`t`] >> metis_tac [S110_def]) >>
  goalStack.print_tac "induction step" >>
  first_x_assum (qspecl_then [`j+1`, `t`] mp_tac) >>
  impl_tac >- asm_rewrite_tac [] >> strip_tac >>
  `FST s /\ j < n` by (fs [Abbr`t`] >> metis_tac [S110_def]) >>
  `FST st` by (fs [Abbr`s`] >> metis_tac [S110_def]) >>
  `st_val ws s y = st_val ws st y +
     &D * qv (-(h0 * rp)) (h1 * rq) * mono ws 1 j 0 y`
    by (fs [Abbr`s`] >> metis_tac [S042_def]) >>
  `st_val ws t y = st_val ws s y +
     &D * qv h0 (h1 * 1096) * mono ws 4 j 0 y`
    by (fs [Abbr`t`] >> metis_tac [S042_def]) >>
  asm_rewrite_tac [] >> goalStack.print_tac "value and sign" >> conj_tac
  >- MATCH_ACCEPT_TAC nu_algebra >>
  MATCH_MP_TAC nu_sign >> asm_rewrite_tac []
QED

Theorem S059_as_constants[local]:
  S110 /\ S042 ==> S059
Proof
  strip_tac >> rewrite_tac [S059_def] >> rpt gen_tac >>
  MATCH_ACCEPT_TAC (SPEC_ALL (MATCH_MP nu_induction
    (CONJ (ASSUME “S110”) (ASSUME “S042”))))
QED

Theorem S059 = CONV_RULE (RAND_CONV (REWR_CONV S059_def)) S059_as_constants
