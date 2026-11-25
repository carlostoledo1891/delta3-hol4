Theory attempt
Ancestors
  arithmetic list integer real intreal delta3_check delta3_check2 delta3_sem delta3_stmts
Libs
  intLib realLib

(* NON-BLIND. Written after the blind run was scored and the key opened, by the builder agent
   (hol4/delta3/assembly/, 2026-11-25). It is claude-b9's third judged script for S149
   (harness/work/claude/claude-b9/S149-prove.sml, sha256 in assembly/SOURCES.tsv) with ONE change,
   in the last step of S149_as_constants: irule top_arith generalised the free variables of the
   instantiated lemma and left an existential goal; the lemma is now instantiated in all ten
   variables and used by mp_tac + impl_tac. Every other line is claude-b9's. *)

(* ---- small facts ---- *)
Theorem mod_pos[local]:
  !D q. 0 < D /\ D MOD q = 0 ==> 0 < q
Proof
  rpt gen_tac >> Cases_on `q` >> simp [] >> decide_tac
QED

Theorem qv_nonneg[local]:
  !p q. 0 <= p ==> 0 <= qv p q
Proof
  rpt strip_tac >>
  `?k. p = &k` by metis_tac [NUM_POSINT_EXISTS] >>
  pop_assum SUBST_ALL_TAC >>
  rewrite_tac [qv_def, real_of_int_num] >>
  irule REAL_LE_DIV >> rewrite_tac [REAL_POS]
QED

Theorem pos_mul_cancel[local]:
  !d x:real. 0 < d /\ 0 <= d * x ==> 0 <= x
Proof
  rpt strip_tac >>
  `d * 0 <= d * x` by (rewrite_tac [REAL_MUL_RZERO] >> first_assum ACCEPT_TAC) >>
  metis_tac [REAL_LE_LMUL]
QED

(* ---- the final arithmetic: from v^T M v >= 0 to the claim ---- *)
Theorem top_arith[local]:
  !Dr Ev Qv Nr Nr1 Sv Bv Fv Cv Lv.
    0 < Dr /\ 0 <= Fv /\ 0 <= Ev /\ Qv <= Nr /\ Nr1 = Nr + 1 /\
    Sv = Dr * (Lv - Bv - Fv) /\ 0 <= 2 * Sv + 2 * (Dr * Ev) * (1 + Qv) /\
    Cv <= Bv - Ev * Nr1 ==> Cv <= (Lv:real)
Proof
  rpt strip_tac >>
  qpat_x_assum `Nr1 = _` SUBST_ALL_TAC >>
  qpat_x_assum `Sv = _` SUBST_ALL_TAC >>
  `0 <= Dr * (Lv - Bv - Fv + Ev * (1 + Qv))` by REAL_ASM_ARITH_TAC >>
  `0 <= Lv - Bv - Fv + Ev * (1 + Qv)` by metis_tac [pos_mul_cancel] >>
  `0 <= Ev * (Nr - Qv)` by (irule REAL_LE_MUL >> REAL_ASM_ARITH_TAC) >>
  REAL_ASM_ARITH_TAC
QED

(* ---- the matrix part: S027 (shape), S040 (dominance => v^T M v >= 0),
        S057 (v^T M v with v = 1::y), S017 (the scaled eps) ---- *)
Theorem top_gen[local]:
  S017 /\ S027 /\ S057 /\ S040 ==>
  !n st ws D ep eq T2 Lw ds y.
    st_wf n st /\ LENGTH ws = n /\ LENGTH (y:real list) = n /\ 0 < D /\ D MOD eq = 0 /\
    LENGTH Lw = n + 1 /\ LENGTH ds = n + 1 /\
    dd_rows (&(4 ** T2)) (&(2 * D)) 0 (slab_matrix D ep eq ws st) Lw Lw ds ds ==>
    0 <= 2 * st_val ws st y + 2 * (&D * qv ep eq) * (1 + sumsq y)
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  qspecl_then [`n`, `st`, `ws`, `D`, `ep`, `eq`] mp_tac (EQ_MP S027_def (ASSUME ``S027``)) >>
  impl_tac >- simp [] >> strip_tac >>
  qspecl_then [`&(4 ** T2)`, `&(2 * D)`, `slab_matrix D ep eq ws st`, `Lw`, `ds`] mp_tac
    (EQ_MP S040_def (ASSUME ``S040``)) >>
  impl_tac >- (asm_rewrite_tac [] >> simp []) >>
  disch_then (qspec_then `1 :: y` mp_tac) >>
  impl_tac >- simp [] >>
  qspecl_then [`n`, `st`, `ws`, `y`, `D`, `ep`, `eq`] mp_tac (EQ_MP S057_def (ASSUME ``S057``)) >>
  impl_tac >- simp [] >>
  disch_then SUBST1_TAC >>
  qspecl_then [`D`, `eq`, `ep`] mp_tac (EQ_MP S017_def (ASSUME ``S017``)) >>
  impl_tac >- simp [] >>
  disch_then SUBST1_TAC >> simp []
QED

Theorem slab_forms_fst[local]:
  !D n ab cuts full Bp Bq lp lq hp hq theta forms.
    FST (slab_poly D n ab cuts full Bp Bq lp lq hp hq theta forms) ==>
    ?sx. FST (add_forms D n 1096 lp lq hp hq forms sx)
Proof
  rewrite_tac [slab_poly_def] >> metis_tac []
QED

(* the facts of slab_check that the proof needs, in the exact form used below *)
Theorem s149_unpack[local]:
  !ab cuts full grid lp lq hp hq Bp Bq ep eq cp cq theta forms D T2 ds Lw.
    slab_check ab cuts full grid lp lq hp hq Bp Bq ep eq cp cq theta forms D T2 ds Lw ==>
    FST (slab_poly D (LENGTH grid - 1) ab cuts full Bp Bq lp lq hp hq theta forms) /\
    0 < D /\ D MOD eq = 0 /\ 0 <= ep /\ 0 < cq /\
    cp * &Bq * &eq <= (Bp * &eq - ep * &(LENGTH grid - 1 + 1) * &Bq) * &cq /\
    LENGTH Lw = LENGTH grid - 1 + 1 /\ LENGTH ds = LENGTH grid - 1 + 1 /\
    dd_rows (&(4 ** T2)) (&(2 * D)) 0
      (slab_matrix D ep eq (widths grid)
         (slab_poly D (LENGTH grid - 1) ab cuts full Bp Bq lp lq hp hq theta forms))
      Lw Lw ds ds
Proof
  rpt gen_tac >> simp_tac bool_ss [slab_check_def, LET_THM] >>
  rpt strip_tac >> TRY (first_assum ACCEPT_TAC) >> fs []
QED

Theorem S149_as_constants[local]:
  S017 /\ S154 /\ S019 /\ S027 /\ S057 /\ S123 /\ S078 /\ S040 /\ S108 ==> S149
Proof
  strip_tac >> rewrite_tac [S149_def] >> rpt strip_tac >>
  drule s149_unpack >> strip_tac >>
  `LENGTH y = LENGTH grid - 1` by
     FIRST [(qpat_x_assum `in_box _ _` mp_tac >> rewrite_tac [in_box_def] >> rpt strip_tac >>
             first_assum ACCEPT_TAC) >> NO_TAC,
            fs [in_box_def] >> NO_TAC] >>
  `LENGTH (widths grid) = LENGTH grid - 1`
    by FIRST [qspec_then `grid` ACCEPT_TAC (EQ_MP S078_def (ASSUME ``S078``)),
              rewrite_tac [EQ_MP S078_def (ASSUME ``S078``)]] >>
  (* S019: the state is wf and stands for D (L_theta - B - forms) *)
  qspecl_then [`D`, `y`, `LENGTH grid - 1`, `ab`, `cuts`, `full`, `Bp`, `Bq`, `lp`, `lq`, `hp`, `hq`,
               `theta`, `forms`, `widths grid`] mp_tac (EQ_MP S019_def (ASSUME ``S019``)) >>
  impl_tac >- (rpt conj_tac >> FIRST [first_assum ACCEPT_TAC, simp [] >> NO_TAC]) >> strip_tac >>
  (* the matrix: 0 <= 2 st_val + 2 D eps (1 + |y|^2) *)
  qspecl_then [`LENGTH grid - 1`,
               `slab_poly D (LENGTH grid - 1) ab cuts full Bp Bq lp lq hp hq theta forms`,
               `widths grid`, `D`, `ep`, `eq`, `T2`, `Lw`, `ds`, `y`] mp_tac
    (MP top_gen (LIST_CONJ [ASSUME ``S017``, ASSUME ``S027``, ASSUME ``S057``, ASSUME ``S040``])) >>
  impl_tac >- (rpt conj_tac >> FIRST [first_assum ACCEPT_TAC, simp [] >> NO_TAC]) >> strip_tac >>
  (* S154: the forms are >= 0 on the region *)
  qspecl_then [`D`, `LENGTH grid - 1`, `ab`, `cuts`, `full`, `Bp`, `Bq`, `lp`, `lq`, `hp`, `hq`,
               `theta`, `forms`] mp_tac slab_forms_fst >>
  impl_tac >- FIRST [first_assum ACCEPT_TAC, simp [] >> NO_TAC] >> strip_tac >>
  qpat_x_assum `qv lp lq <= mval grid y` (assume_tac o REWRITE_RULE [mval_def]) >>
  qpat_x_assum `mval grid y <= qv hp hq` (assume_tac o REWRITE_RULE [mval_def]) >>
  qspecl_then [`D`, `LENGTH grid - 1`, `lp`, `lq`, `hp`, `hq`, `forms`, `sx`, `y`, `qv lp lq`,
               `ldot (widths grid) y / 1096`, `qv hp hq`] mp_tac (EQ_MP S154_def (ASSUME ``S154``)) >>
  impl_tac >- (rpt conj_tac >> FIRST [first_assum ACCEPT_TAC, simp [] >> NO_TAC]) >> strip_tac >>
  (* S123: |y|^2 <= n *)
  qspecl_then [`LENGTH grid - 1`, `y`] mp_tac (EQ_MP S123_def (ASSUME ``S123``)) >>
  impl_tac >- FIRST [first_assum ACCEPT_TAC, simp [] >> NO_TAC] >> strip_tac >>
  (* S108: the claim is below B - eps (n + 1) *)
  qspecl_then [`D`, `Bq`] mp_tac mod_pos >>
  impl_tac >- (conj_tac >> FIRST [first_assum ACCEPT_TAC, simp [] >> NO_TAC]) >> strip_tac >>
  qspecl_then [`D`, `eq`] mp_tac mod_pos >>
  impl_tac >- (conj_tac >> FIRST [first_assum ACCEPT_TAC, simp [] >> NO_TAC]) >> strip_tac >>
  qspecl_then [`Bq`, `eq`, `cq`, `cp`, `Bp`, `ep`, `LENGTH grid - 1`] mp_tac
    (EQ_MP S108_def (ASSUME ``S108``)) >>
  impl_tac >- (rpt conj_tac >> FIRST [first_assum ACCEPT_TAC, simp [] >> NO_TAC]) >> strip_tac >>
  qspecl_then [`ep`, `eq`] mp_tac qv_nonneg >>
  impl_tac >- FIRST [first_assum ACCEPT_TAC, simp [] >> NO_TAC] >> strip_tac >>
  qspecl_then [`&D`, `qv ep eq`, `sumsq y`, `&(LENGTH grid - 1)`, `&(LENGTH grid - 1 + 1)`,
               `st_val (widths grid) (slab_poly D (LENGTH grid - 1) ab cuts full Bp Bq lp lq hp hq theta forms) y`,
               `qv Bp Bq`, `forms_val (ldot (widths grid) y / 1096) (qv lp lq) (qv hp hq) forms y`,
               `qv cp cq`, `Ltheta ab cuts full theta y`]
    mp_tac top_arith >>
  impl_tac >-
    (rpt conj_tac >>
     FIRST [first_assum ACCEPT_TAC, rewrite_tac [GSYM REAL_ADD] >> NO_TAC, simp [] >> NO_TAC]) >>
  disch_then ACCEPT_TAC
QED

Theorem S149 = CONV_RULE (RAND_CONV (REWR_CONV S149_def)) S149_as_constants
