Theory attempt
Ancestors
  arithmetic list integer real intreal delta3_check delta3_check2 delta3_sem delta3_stmts
Libs
  intLib realLib

Theorem lin_dot[local]:
  !ws g y. LENGTH ws = LENGTH g /\ LENGTH y = LENGTH g ==>
    ldot (lin c ws g) y = ldot g y + real_of_int c * ldot ws y
Proof
  Induct >> Cases_on `g` >> Cases_on `y` >>
  simp [lin_def, ldot_def] >> rw [] >> fs [] >> REAL_ARITH_TAC
QED

Theorem dot_nil[local]:
  !g. ldot g [] = 0
Proof
  Cases >> simp [ldot_def]
QED

Theorem form_nil[local]:
  !cm u. qform cm u [] = 0
Proof
  Induct >> Cases_on `u` >> simp [qform_def, dot_nil]
QED

Theorem col_split[local]:
  !cm u. qform cm u (x::xs) =
    x * ldot (heads cm) u + qform (tails cm) u xs
Proof
  Induct >- simp [qform_def, heads_def, tails_def, ldot_def] >>
  gen_tac >> Cases_on `u` >> Cases_on `h` >>
  simp [qform_def, heads_def, tails_def, ldot_def] >> REAL_ARITH_TAC
QED

Theorem transp_form[local]:
  !u cm. qform (transp (LENGTH u) cm) u y = qform cm y u
Proof
  Induct >> rpt gen_tac >> once_rewrite_tac [transp_def] >>
  simp [qform_def, form_nil, Once col_split]
QED

Definition pulse_def:
  pulse i (j:num) ([]:real list) = 0r /\
  pulse i j (x::xs) = (if i = j then x else 0) + pulse i (j+1) xs
End

Theorem pulse_before[local]:
  !xs j. i < j ==> pulse i j xs = 0
Proof
  Induct >> rw [pulse_def] >> fs []
QED

Theorem pulse_at[local]:
  !xs j k. k < LENGTH xs ==> pulse (j+k) j xs = EL k xs
Proof
  Induct >> simp [pulse_def] >> Cases_on `k` >>
  simp [pulse_before, EL, ADD_CLAUSES] >>
  metis_tac [ADD1, ADD_CLAUSES]
QED

Theorem pulse_zero[local]:
  i < LENGTH xs ==> pulse i 0 xs = EL i xs
Proof
  metis_tac [pulse_at, ADD_CLAUSES]
QED

Theorem row_dot[local]:
  !cr ct ws ms y j. LENGTH cr = LENGTH y /\ LENGTH ct = LENGTH y /\
    LENGTH ws = LENGTH y /\ LENGTH ms = LENGTH y ==>
    ldot (qrow wi myi mwi e2 i j cr ct ws ms) y =
      ldot cr y + ldot ct y + real_of_int wi * ldot ms y +
      (real_of_int myi + real_of_int mwi) * ldot ws y +
      real_of_int e2 * pulse i j y
Proof
  Induct >> rpt gen_tac >> Cases_on `ct` >> Cases_on `ws` >>
  Cases_on `ms` >> Cases_on `y` >>
  simp_tac (srw_ss()) [Once qrow_def, ldot_def, pulse_def] >>
  rw [] >> fs [] >> REAL_ARITH_TAC
QED

Definition aligned_def:
  aligned i [] (y:real list) = T /\
  aligned i (x::xs) y =
    (i < LENGTH y /\ EL i y = x /\ aligned (i+1) xs y)
End

Theorem shift_aligned[local]:
  !u i. aligned (SUC i) u (x::y) = aligned i u y
Proof
  Induct >> simp [aligned_def, ADD_CLAUSES, EL]
QED

Theorem one_aligned[local]:
  aligned 1 u (x::y) = aligned 0 u y
Proof
  metis_tac [shift_aligned, ONE]
QED

Theorem self_aligned[local]:
  !y. aligned 0 y y
Proof
  Induct >> simp [aligned_def, one_aligned]
QED

Theorem block_form[local]:
  !cm ct ws ms g u i.
    EVERY (\r. LENGTH r = LENGTH y) cm /\
    EVERY (\r. LENGTH r = LENGTH y) ct /\
    LENGTH cm = LENGTH u /\ LENGTH ct = LENGTH u /\
    LENGTH ws = LENGTH u /\ LENGTH ms = LENGTH u /\ LENGTH g = LENGTH u /\
    LENGTH wall = LENGTH y /\ LENGTH myall = LENGTH y /\ aligned i u y ==>
    qform (qrows mM e2 i cm ct wall ws myall ms g) u (1::y) =
      ldot g u + qform cm u y + qform ct u y +
      ldot ws u * ldot myall y + ldot ms u * ldot wall y +
      2 * real_of_int mM * ldot ws u * ldot wall y +
      real_of_int e2 * sumsq u
Proof
  Induct >> rpt gen_tac >> Cases_on `u` >> simp [] >>
  Cases_on `ct` >> Cases_on `ws` >> Cases_on `ms` >> Cases_on `g` >>
  simp_tac (srw_ss()) [Once qrows_def, aligned_def, qform_def, ldot_def, sumsq_def] >>
  rw [] >> fs [row_dot, pulse_zero] >>
  goalStack.print_tac "block polynomial" >> TRY REAL_ARITH_TAC
QED

Theorem S057_as_constants[local]:
  S052 /\ S038 ==> S057
Proof
  rewrite_tac [S057_def] >> strip_tac >> rpt gen_tac >> strip_tac >>
  PairCases_on `st` >> fs [st_wf_def] >>
  `LENGTH (transp n st3) = n /\
    EVERY (\r. LENGTH r = n) (transp n st3)` by metis_tac [S052_def] >>
  `LENGTH (lin st4 ws st2) = n` by metis_tac [S038_def] >>
  `aligned 0 y y` by simp [self_aligned] >>
  goalStack.print_tac "matrix dimensions" >>
  simp [slab_matrix_def, st_val_def, qform_def, ldot_def, block_form,
        lin_dot] >>
  `qform (transp n st3) y y = qform st3 y y` by metis_tac [transp_form] >>
  fs [] >> goalStack.print_tac "final polynomial" >> TRY REAL_ARITH_TAC
QED

Theorem S057 = CONV_RULE (RAND_CONV (REWR_CONV S057_def)) S057_as_constants
