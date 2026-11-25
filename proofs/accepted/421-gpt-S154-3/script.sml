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

Theorem box_sign[local]:
  !n y i. in_box n y /\ i < n ==>
          -1 <= 1 - 2 * EL i y /\ 1 - 2 * EL i y <= 1
Proof
  rpt gen_tac >> simp [in_box_def, EVERY_EL] >> strip_tac >>
  ‘0 <= EL i y /\ EL i y <= 1’ by metis_tac [] >>
  RealField.REAL_ASM_ARITH_TAC
QED

val int_nonnegative = REWRITE_RULE [real_of_int_num]
  (INST [“m:int” |-> “0:int”] real_of_int_le)

Theorem qv_nonnegative[local]:
  !p q. 0 <= p ==> 0 <= qv p q
Proof
  rpt gen_tac >> strip_tac >> rewrite_tac [qv_def] >>
  match_mp_tac REAL_LE_DIV >> simp [int_nonnegative] >>
  goalStack.print_tac "cast nonnegativity" >>
  metis_tac [int_nonnegative, REAL_POS]
QED

Theorem triangle_value[local]:
  !m lo hi i j k s1 s2 s3 y.
    form_val m lo hi 14 i j k s1 s2 s3 y =
      1 + real_of_int s1 * ((1-2*EL i y)*(1-2*EL j y))
        + real_of_int s2 * ((1-2*EL j y)*(1-2*EL k y))
        + real_of_int s3 * ((1-2*EL i y)*(1-2*EL k y))
Proof
  simp [form_val_def]
QED

val guard_info = EQ_MP S095_def (ASSUME “S095”)
val ordinary_bound = EQ_MP S152_def (ASSUME “S152”)
val triangle_bound = EQ_MP S054_def (ASSUME “S054”)

Theorem triangle_nonnegative[local]:
  S054 ==> !n y m lo hi i j k s1 s2 s3.
    in_box n y /\ i < n /\ j < n /\ k < n /\
    (s1 = 1 \/ s1 = -1) /\ (s2 = 1 \/ s2 = -1) /\
    (s3 = 1 \/ s3 = -1) /\ s1*s2*s3 = 1 ==>
    0 <= form_val m lo hi 14 i j k s1 s2 s3 y
Proof
  disch_tac >> rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  rewrite_tac [triangle_value] >> match_mp_tac triangle_bound >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> metis_tac [box_sign]
QED

Theorem head_nonnegative[local]:
  S095 /\ S152 /\ S054 ==>
  !D n lp lq hp hq kind i j k s1 s2 s3 mp mq st y m lo hi.
   FST (add_form D n 1096 lp lq hp hq kind i j k s1 s2 s3 mp mq st) /\
   in_box n y /\ lo <= m /\ m <= hi ==>
   0 <= qv mp mq * form_val m lo hi kind i j k s1 s2 s3 y
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  first_assum (strip_assume_tac o MATCH_MP guard_info) >>
  match_mp_tac REAL_LE_MUL >> conj_tac >- metis_tac [qv_nonnegative] >>
  Cases_on ‘kind = 14’
  >- (TRY (qpat_x_assum ‘kind = 14’ SUBST_ALL_TAC) >>
      ‘i < n /\ j < n /\ k < n’ by fs [form_idx_ok_def] >>
      match_mp_tac (UNDISCH triangle_nonnegative) >> qexists_tac ‘n’ >>
      metis_tac []) >>
  ‘kind <= 13’ by decide_tac >>
  match_mp_tac ordinary_bound >> qexists_tac ‘n’ >> asm_rewrite_tac []
QED

Theorem S154_as_constants[local]:
  S095 /\ S152 /\ S054 ==> S154
Proof
  strip_tac >> rewrite_tac [S154_def] >> rpt gen_tac >> qid_spec_tac ‘st’ >>
  Induct_on ‘forms’ >- simp [forms_val_def] >>
  rpt gen_tac >> PairCases_on ‘h’ >>
  rewrite_tac [add_forms_def, forms_val_def] >> strip_tac >>
  ‘FST (add_form D n 1096 lp lq hp hq h0 h1 h2 h3 h4 h5 h6 h7 h8 st)’ by metis_tac [forms_ok] >>
  match_mp_tac REAL_LE_ADD >> conj_tac >- metis_tac [head_nonnegative] >> metis_tac []
QED

Theorem S154 = CONV_RULE (RAND_CONV (REWR_CONV S154_def)) S154_as_constants



