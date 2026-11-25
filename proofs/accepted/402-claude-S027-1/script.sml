(* S027 -- the matrix M = 2D(S + eps I) is (n+1) x (n+1) and symmetric.  Agent claude-b2.
   Route: lemmas about qrow and qrows by induction (lengths, entries, the rows' lengths); an
   entry of M below row 0 is C_st + C_ts + w_s my_t + w_t my_s + 2 mM w_s w_t (+ e2 on the
   diagonal), symmetric once the transpose is read through S052; row/column 0 is g1 = lin mL ws g
   (its length from S038). *)
Theory attempt
Ancestors
  arithmetic list integer real intreal delta3_check delta3_check2 delta3_sem delta3_stmts
Libs
  intLib realLib

Theorem add_suc[local]:
  !a b. a + SUC b = a + 1 + b
Proof
  rpt gen_tac >> DECIDE_TAC
QED

Theorem qrow_len[local]:
  !crow ctrow ws mys wi myi mwi e2 i j.
    LENGTH ctrow = LENGTH crow /\ LENGTH ws = LENGTH crow /\ LENGTH mys = LENGTH crow ==>
    LENGTH (qrow wi myi mwi e2 i j crow ctrow ws mys) = LENGTH crow
Proof
  Induct
  >- (rpt gen_tac >> once_rewrite_tac [qrow_def] >> rewrite_tac [list_case_def, LENGTH])
  >> gen_tac >> Cases >> Cases >> Cases >>
  rewrite_tac [LENGTH, SUC_NOT, prim_recTheory.INV_SUC_EQ] >>
  rpt gen_tac >> strip_tac >>
  once_rewrite_tac [qrow_def] >> rewrite_tac [list_case_def] >> BETA_TAC >>
  rewrite_tac [LENGTH, prim_recTheory.INV_SUC_EQ] >>
  first_x_assum irule >> asm_rewrite_tac []
QED

Theorem qrow_len2[local]:
  !crow ctrow ws mys wi myi mwi e2 i j m.
    LENGTH crow = m /\ LENGTH ctrow = m /\ LENGTH ws = m /\ LENGTH mys = m ==>
    LENGTH (qrow wi myi mwi e2 i j crow ctrow ws mys) = m
Proof
  rpt strip_tac >>
  qspecl_then [`crow`, `ctrow`, `ws`, `mys`, `wi`, `myi`, `mwi`, `e2`, `i`, `j`] mp_tac qrow_len >>
  asm_rewrite_tac []
QED

Theorem qrow_el[local]:
  !crow ctrow ws mys x wi myi mwi e2 i j.
    LENGTH ctrow = LENGTH crow /\ LENGTH ws = LENGTH crow /\ LENGTH mys = LENGTH crow /\
    x < LENGTH crow ==>
    EL x (qrow wi myi mwi e2 i j crow ctrow ws mys) =
    EL x crow + EL x ctrow + wi * EL x mys + EL x ws * myi + mwi * EL x ws +
    (if i = j + x then e2 else 0)
Proof
  Induct
  >- rewrite_tac [LENGTH, prim_recTheory.NOT_LESS_0]
  >> gen_tac >> Cases >> Cases >> Cases >>
  rewrite_tac [LENGTH, SUC_NOT, prim_recTheory.INV_SUC_EQ] >>
  Cases
  >- (rpt gen_tac >> strip_tac >>
      once_rewrite_tac [qrow_def] >> rewrite_tac [list_case_def] >> BETA_TAC >>
      rewrite_tac [EL, HD, ADD_CLAUSES])
  >> rpt gen_tac >> rewrite_tac [LESS_MONO_EQ] >> strip_tac >>
  once_rewrite_tac [qrow_def] >> rewrite_tac [list_case_def] >> BETA_TAC >>
  rewrite_tac [EL, TL, add_suc] >>
  first_x_assum irule >> asm_rewrite_tac []
QED

Theorem qrows_len[local]:
  !Cm Ct ws mys g mM e2 i wall myall.
    LENGTH Ct = LENGTH Cm /\ LENGTH ws = LENGTH Cm /\ LENGTH mys = LENGTH Cm /\ LENGTH g = LENGTH Cm ==>
    LENGTH (qrows mM e2 i Cm Ct wall ws myall mys g) = LENGTH Cm
Proof
  Induct
  >- (rpt gen_tac >> once_rewrite_tac [qrows_def] >> rewrite_tac [list_case_def, LENGTH])
  >> gen_tac >> Cases >> Cases >> Cases >> Cases >>
  rewrite_tac [LENGTH, SUC_NOT, prim_recTheory.INV_SUC_EQ] >>
  rpt gen_tac >> strip_tac >>
  once_rewrite_tac [qrows_def] >> rewrite_tac [list_case_def] >> BETA_TAC >>
  rewrite_tac [LENGTH, prim_recTheory.INV_SUC_EQ] >>
  first_x_assum irule >> asm_rewrite_tac []
QED

Theorem qrows_len2[local]:
  !Cm Ct ws mys g mM e2 i wall myall m.
    LENGTH Cm = m /\ LENGTH Ct = m /\ LENGTH ws = m /\ LENGTH mys = m /\ LENGTH g = m ==>
    LENGTH (qrows mM e2 i Cm Ct wall ws myall mys g) = m
Proof
  rpt strip_tac >>
  qspecl_then [`Cm`, `Ct`, `ws`, `mys`, `g`, `mM`, `e2`, `i`, `wall`, `myall`] mp_tac qrows_len >>
  asm_rewrite_tac []
QED

Theorem qrows_el[local]:
  !Cm Ct ws mys g x mM e2 i wall myall.
    LENGTH Ct = LENGTH Cm /\ LENGTH ws = LENGTH Cm /\ LENGTH mys = LENGTH Cm /\ LENGTH g = LENGTH Cm /\
    x < LENGTH Cm ==>
    EL x (qrows mM e2 i Cm Ct wall ws myall mys g) =
    EL x g :: qrow (EL x ws) (EL x mys) (2 * mM * EL x ws) e2 (i + x) 0 (EL x Cm) (EL x Ct) wall myall
Proof
  Induct
  >- rewrite_tac [LENGTH, prim_recTheory.NOT_LESS_0]
  >> gen_tac >> Cases >> Cases >> Cases >> Cases >>
  rewrite_tac [LENGTH, SUC_NOT, prim_recTheory.INV_SUC_EQ] >>
  Cases
  >- (rpt gen_tac >> strip_tac >>
      once_rewrite_tac [qrows_def] >> rewrite_tac [list_case_def] >> BETA_TAC >>
      rewrite_tac [EL, HD, ADD_CLAUSES])
  >> rpt gen_tac >> rewrite_tac [LESS_MONO_EQ] >> strip_tac >>
  once_rewrite_tac [qrows_def] >> rewrite_tac [list_case_def] >> BETA_TAC >>
  rewrite_tac [EL, TL, add_suc] >>
  first_x_assum irule >> asm_rewrite_tac []
QED

Theorem qrows_hd[local]:
  !Cm Ct ws mys g x mM e2 i wall myall.
    LENGTH Ct = LENGTH Cm /\ LENGTH ws = LENGTH Cm /\ LENGTH mys = LENGTH Cm /\ LENGTH g = LENGTH Cm /\
    x < LENGTH Cm ==>
    HD (EL x (qrows mM e2 i Cm Ct wall ws myall mys g)) = EL x g
Proof
  rpt strip_tac >>
  qspecl_then [`Cm`, `Ct`, `ws`, `mys`, `g`, `x`, `mM`, `e2`, `i`, `wall`, `myall`] mp_tac qrows_el >>
  impl_tac >- asm_rewrite_tac [] >>
  disch_then SUBST1_TAC >> rewrite_tac [HD]
QED

Theorem qrows_tl[local]:
  !Cm Ct ws mys g x mM e2 i wall myall.
    LENGTH Ct = LENGTH Cm /\ LENGTH ws = LENGTH Cm /\ LENGTH mys = LENGTH Cm /\ LENGTH g = LENGTH Cm /\
    x < LENGTH Cm ==>
    TL (EL x (qrows mM e2 i Cm Ct wall ws myall mys g)) =
    qrow (EL x ws) (EL x mys) (2 * mM * EL x ws) e2 (i + x) 0 (EL x Cm) (EL x Ct) wall myall
Proof
  rpt strip_tac >>
  qspecl_then [`Cm`, `Ct`, `ws`, `mys`, `g`, `x`, `mM`, `e2`, `i`, `wall`, `myall`] mp_tac qrows_el >>
  impl_tac >- asm_rewrite_tac [] >>
  disch_then SUBST1_TAC >> rewrite_tac [TL]
QED

Theorem qrows_every[local]:
  !Cm Ct ws mys g mM e2 i wall myall m.
    LENGTH Ct = LENGTH Cm /\ LENGTH ws = LENGTH Cm /\ LENGTH mys = LENGTH Cm /\ LENGTH g = LENGTH Cm /\
    EVERY (\r. LENGTH r = m) Cm /\ EVERY (\r. LENGTH r = m) Ct /\ LENGTH wall = m /\ LENGTH myall = m ==>
    EVERY (\r. LENGTH r = m + 1) (qrows mM e2 i Cm Ct wall ws myall mys g)
Proof
  Induct
  >- (rpt gen_tac >> once_rewrite_tac [qrows_def] >> rewrite_tac [list_case_def, EVERY_DEF])
  >> gen_tac >> Cases >> Cases >> Cases >> Cases >>
  rewrite_tac [LENGTH, SUC_NOT, prim_recTheory.INV_SUC_EQ, EVERY_DEF] >> BETA_TAC >>
  rpt gen_tac >> strip_tac >>
  once_rewrite_tac [qrows_def] >> rewrite_tac [list_case_def] >> BETA_TAC >>
  rewrite_tac [EVERY_DEF] >> BETA_TAC >> conj_tac
  >- (rewrite_tac [LENGTH, GSYM ADD1, prim_recTheory.INV_SUC_EQ] >>
      irule qrow_len2 >> asm_rewrite_tac [])
  >> first_x_assum irule >> asm_rewrite_tac []
QED

Theorem entry_sym[local]:
  !(Cm:int list list) (Ct:int list list) (ws:int list) (mY:int list) (mM:int) (e2:int) s t.
    EVERY (\r. LENGTH r = LENGTH ws) Cm /\ EVERY (\r. LENGTH r = LENGTH ws) Ct /\
    LENGTH Cm = LENGTH ws /\ LENGTH Ct = LENGTH ws /\ LENGTH mY = LENGTH ws /\
    (!i j. i < LENGTH ws /\ j < LENGTH ws ==> EL j (EL i Ct) = EL i (EL j Cm)) /\
    s < LENGTH ws /\ t < LENGTH ws ==>
    EL t (qrow (EL s ws) (EL s mY) (2 * mM * EL s ws) e2 (0 + s) 0 (EL s Cm) (EL s Ct) ws mY) =
    EL s (qrow (EL t ws) (EL t mY) (2 * mM * EL t ws) e2 (0 + t) 0 (EL t Cm) (EL t Ct) ws mY)
Proof
  rpt strip_tac >>
  `LENGTH (EL s Cm) = LENGTH ws /\ LENGTH (EL t Cm) = LENGTH ws /\
   LENGTH (EL s Ct) = LENGTH ws /\ LENGTH (EL t Ct) = LENGTH ws` by
     (rpt (qpat_x_assum `EVERY _ _` mp_tac) >> rewrite_tac [EVERY_EL] >> BETA_TAC >>
      metis_tac []) >>
  qspecl_then [`EL s Cm`, `EL s Ct`, `ws`, `mY`, `t`, `EL s ws`, `EL s mY`, `2 * mM * EL s ws`,
               `e2`, `0 + s`, `0`] mp_tac qrow_el >>
  impl_tac >- asm_rewrite_tac [] >> disch_then SUBST1_TAC >>
  qspecl_then [`EL t Cm`, `EL t Ct`, `ws`, `mY`, `s`, `EL t ws`, `EL t mY`, `2 * mM * EL t ws`,
               `e2`, `0 + t`, `0`] mp_tac qrow_el >>
  impl_tac >- asm_rewrite_tac [] >> disch_then SUBST1_TAC >>
  `EL t (EL s Ct) = EL s (EL t Cm) /\ EL s (EL t Ct) = EL t (EL s Cm)` by metis_tac [] >>
  asm_rewrite_tac [ADD_CLAUSES] >>
  Cases_on `s = t` >> asm_rewrite_tac [] >>
  `~(t = s)` by (strip_tac >> qpat_x_assum `~(s = t)` mp_tac >> asm_rewrite_tac []) >>
  asm_rewrite_tac [] >>
  ONCE_REWRITE_TAC [GSYM real_of_int_11] >>
  rewrite_tac [real_of_int_add, real_of_int_mul, real_of_int_num] >>
  REAL_ARITH_TAC
QED

Theorem sym_lemma[local]:
  !(a:int) (g1:int list) Q i j.
    (!s. s < LENGTH Q ==> HD (EL s Q) = EL s g1) /\
    (!s t. s < LENGTH Q /\ t < LENGTH Q ==> EL t (TL (EL s Q)) = EL s (TL (EL t Q))) /\
    i < LENGTH Q + 1 /\ j < LENGTH Q + 1 ==>
    EL j (EL i ((a :: g1) :: Q)) = EL i (EL j ((a :: g1) :: Q))
Proof
  rpt gen_tac >> Cases_on `i` >> Cases_on `j` >>
  rewrite_tac [EL, HD, TL, GSYM ADD1, LESS_MONO_EQ, prim_recTheory.LESS_0] >>
  rpt strip_tac >> metis_tac []
QED

Theorem S027_as_constants[local]:
  S052 /\ S038 ==> S027
Proof
  rewrite_tac [S052_def, S038_def, S027_def] >> strip_tac >>
  rpt gen_tac >> PairCases_on `st` >>
  rewrite_tac [st_wf_def, slab_matrix_def, pairTheory.pair_CASE_def, LET_THM] >> BETA_TAC >>
  rewrite_tac [pairTheory.FST, pairTheory.SND] >>
  strip_tac >>
  qpat_assum `LENGTH st3 = n` (fn th => rewrite_tac [th]) >>
  `LENGTH (lin st4 ws st2) = n` by
     (first_assum (qspecl_then [`ws`, `st2`, `st4`] mp_tac) >>
      impl_tac >- asm_rewrite_tac [] >>
      disch_then (fn th => rewrite_tac [CONJUNCT1 th]) >> asm_rewrite_tac []) >>
  `LENGTH (transp n st3) = n /\ EVERY (\r. LENGTH r = n) (transp n st3) /\
   !i j. i < n /\ j < n ==> EL j (EL i (transp n st3)) = EL i (EL j st3)` by
     (first_assum (qspecl_then [`n`, `st3`] mp_tac) >>
      impl_tac >- first_assum ACCEPT_TAC >>
      asm_rewrite_tac []) >>
  `LENGTH (qrows st6 (2 * sc D ep eq) 0 st3 (transp n st3) ws ws st5 st5 (lin st4 ws st2)) = n` by
     (irule qrows_len2 >> asm_rewrite_tac []) >>
  `!s. s < n ==>
       HD (EL s (qrows st6 (2 * sc D ep eq) 0 st3 (transp n st3) ws ws st5 st5 (lin st4 ws st2))) =
       EL s (lin st4 ws st2)` by
     (rpt strip_tac >> irule qrows_hd >> asm_rewrite_tac []) >>
  `!s t. s < n /\ t < n ==>
     EL t (TL (EL s (qrows st6 (2 * sc D ep eq) 0 st3 (transp n st3) ws ws st5 st5 (lin st4 ws st2)))) =
     EL s (TL (EL t (qrows st6 (2 * sc D ep eq) 0 st3 (transp n st3) ws ws st5 st5 (lin st4 ws st2))))` by
     (rpt strip_tac >>
      qspecl_then [`st3`, `transp n st3`, `ws`, `st5`, `lin st4 ws st2`, `s`, `st6`, `2 * sc D ep eq`,
                   `0`, `ws`, `st5`] mp_tac qrows_tl >>
      impl_tac >- asm_rewrite_tac [] >> disch_then SUBST1_TAC >>
      qspecl_then [`st3`, `transp n st3`, `ws`, `st5`, `lin st4 ws st2`, `t`, `st6`, `2 * sc D ep eq`,
                   `0`, `ws`, `st5`] mp_tac qrows_tl >>
      impl_tac >- asm_rewrite_tac [] >> disch_then SUBST1_TAC >>
      irule entry_sym >> asm_rewrite_tac []) >>
  rpt conj_tac
  >- asm_rewrite_tac [LENGTH, ADD1]
  >- (rewrite_tac [EVERY_DEF] >> BETA_TAC >> conj_tac
      >- asm_rewrite_tac [LENGTH, ADD1]
      >> irule qrows_every >> asm_rewrite_tac [])
  >> rpt strip_tac >> irule sym_lemma >> asm_rewrite_tac []
QED

Theorem S027 = CONV_RULE (RAND_CONV (REWR_CONV S027_def)) S027_as_constants
