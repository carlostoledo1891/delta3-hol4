Theory attempt
Ancestors
  arithmetic list integer real intreal delta3_check delta3_check2 delta3_sem delta3_stmts
Libs
  intLib realLib

(* ---- clean equations for the recursive definitions (safe to use with simp) ---- *)

Theorem ldot_eqs[local]:
  (!y. ldot [] y = 0) /\ (!g gs. ldot (g::gs) [] = 0) /\
  (!g gs x xs. ldot (g::gs) (x::xs) = real_of_int g * x + ldot gs xs)
Proof
  simp_tac bool_ss [ldot_def, list_case_def]
QED

Theorem qform_eqs[local]:
  (!u y. qform [] u y = 0) /\ (!r rs y. qform (r::rs) [] y = 0) /\
  (!r rs x xs y. qform (r::rs) (x::xs) y = x * ldot r y + qform rs xs y)
Proof
  simp_tac bool_ss [qform_def, list_case_def]
QED

Theorem tails_eqs[local]:
  tails [] = [] /\ (!rs. tails ([]::rs) = [] :: tails rs) /\
  (!x xs rs. tails ((x::xs)::rs) = xs :: tails rs)
Proof
  simp_tac bool_ss [tails_def, list_case_def]
QED

Theorem heads_eqs[local]:
  heads [] = [] /\ (!rs. heads ([]::rs) = 0 :: heads rs) /\
  (!x xs rs. heads ((x::xs)::rs) = x :: heads rs)
Proof
  simp_tac bool_ss [heads_def, list_case_def]
QED

Theorem transp_eqs[local]:
  (!m. transp 0 m = []) /\ (!n m. transp (SUC n) m = heads m :: transp n (tails m))
Proof
  conj_tac >> rpt gen_tac >>
  CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [transp_def])) >> simp []
QED

Theorem qrow_nil[local]:
  !wi myi mwi e2 i j ctrow ws mys. qrow wi myi mwi e2 i j [] ctrow ws mys = []
Proof
  rpt gen_tac >> CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [qrow_def])) >>
  simp_tac bool_ss [list_case_def]
QED

Theorem qrow_cons[local]:
  !wi myi mwi e2 i j c cr ct ctr w wr my myr.
    qrow wi myi mwi e2 i j (c::cr) (ct::ctr) (w::wr) (my::myr) =
    (c + ct + wi * my + w * myi + mwi * w + (if i = j then e2 else 0)) ::
    qrow wi myi mwi e2 i (j + 1) cr ctr wr myr
Proof
  rpt gen_tac >> CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [qrow_def])) >>
  simp_tac bool_ss [list_case_def]
QED

Theorem qrows_nil[local]:
  !mM e2 i Ct wall ws myall mys g. qrows mM e2 i [] Ct wall ws myall mys g = []
Proof
  rpt gen_tac >> CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [qrows_def])) >>
  simp_tac bool_ss [list_case_def]
QED

Theorem qrows_cons[local]:
  !mM e2 i crow Cr ctrow Ctr wall wi wr myall myi myr gi gr.
    qrows mM e2 i (crow::Cr) (ctrow::Ctr) wall (wi::wr) myall (myi::myr) (gi::gr) =
    (gi :: qrow wi myi (2 * mM * wi) e2 i 0 crow ctrow wall myall) ::
    qrows mM e2 (i + 1) Cr Ctr wall wr myall myr gr
Proof
  rpt gen_tac >> CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [qrows_def])) >>
  simp_tac bool_ss [list_case_def]
QED

(* ---- one row of the matrix: length, entries, and its dot product ---- *)

Theorem qrow_len[local]:
  !crow wi myi mwi e2 i ctrow ws mys j.
    LENGTH ctrow = LENGTH crow /\ LENGTH ws = LENGTH crow /\ LENGTH mys = LENGTH crow ==>
    LENGTH (qrow wi myi mwi e2 i j crow ctrow ws mys) = LENGTH crow
Proof
  Induct >> rpt gen_tac >> Cases_on `ctrow` >> Cases_on `ws` >> Cases_on `mys` >>
  simp [qrow_nil, qrow_cons]
QED

Theorem qrow_el[local]:
  !crow wi myi mwi i ctrow ws mys j k.
    LENGTH ctrow = LENGTH crow /\ LENGTH ws = LENGTH crow /\ LENGTH mys = LENGTH crow /\
    k < LENGTH crow ==>
    EL k (qrow wi myi mwi 0 i j crow ctrow ws mys) =
    EL k crow + EL k ctrow + wi * EL k mys + EL k ws * myi + mwi * EL k ws
Proof
  Induct >> rpt gen_tac >> Cases_on `ctrow` >> Cases_on `ws` >> Cases_on `mys` >> Cases_on `k` >>
  simp [qrow_nil, qrow_cons]
QED

Theorem qrow_ldot[local]:
  !crow wi myi mwi i ctrow ws mys j y.
    LENGTH ctrow = LENGTH crow /\ LENGTH ws = LENGTH crow /\ LENGTH mys = LENGTH crow /\
    LENGTH y = LENGTH crow ==>
    ldot (qrow wi myi mwi 0 i j crow ctrow ws mys) y =
    ldot crow y + ldot ctrow y + real_of_int wi * ldot mys y + real_of_int myi * ldot ws y +
    real_of_int mwi * ldot ws y
Proof
  Induct >> rpt gen_tac >> Cases_on `ctrow` >> Cases_on `ws` >> Cases_on `mys` >> Cases_on `y` >>
  simp [qrow_nil, qrow_cons, ldot_eqs] >> rpt strip_tac >> REAL_ARITH_TAC
QED

(* ---- the block of rows that inner_matrix keeps (tails drops the g column) ---- *)

Theorem IM_len[local]:
  !Cm mM e2 i Ct wall ws myall mys g.
    LENGTH Ct = LENGTH Cm /\ LENGTH ws = LENGTH Cm /\ LENGTH mys = LENGTH Cm /\
    LENGTH g = LENGTH Cm ==>
    LENGTH (tails (qrows mM e2 i Cm Ct wall ws myall mys g)) = LENGTH Cm
Proof
  Induct >> rpt gen_tac >> Cases_on `Ct` >> Cases_on `ws` >> Cases_on `mys` >> Cases_on `g` >>
  simp [qrows_nil, qrows_cons, tails_eqs]
QED

Theorem IM_every[local]:
  !Cm mM e2 i Ct wall ws myall mys g m.
    LENGTH Ct = LENGTH Cm /\ LENGTH ws = LENGTH Cm /\ LENGTH mys = LENGTH Cm /\
    LENGTH g = LENGTH Cm /\ EVERY (\r. LENGTH r = m) Cm /\ EVERY (\r. LENGTH r = m) Ct /\
    LENGTH wall = m /\ LENGTH myall = m ==>
    EVERY (\r. LENGTH r = m) (tails (qrows mM e2 i Cm Ct wall ws myall mys g))
Proof
  Induct >> rpt gen_tac >> Cases_on `Ct` >> Cases_on `ws` >> Cases_on `mys` >> Cases_on `g` >>
  simp [qrows_nil, qrows_cons, tails_eqs, qrow_len]
QED

Theorem IM_el[local]:
  !Cm mM i Ct wall ws myall mys g a b.
    LENGTH Ct = LENGTH Cm /\ LENGTH ws = LENGTH Cm /\ LENGTH mys = LENGTH Cm /\
    LENGTH g = LENGTH Cm /\ EVERY (\r. LENGTH r = LENGTH wall) Cm /\
    EVERY (\r. LENGTH r = LENGTH wall) Ct /\ LENGTH myall = LENGTH wall /\
    a < LENGTH Cm /\ b < LENGTH wall ==>
    EL b (EL a (tails (qrows mM 0 i Cm Ct wall ws myall mys g))) =
    EL b (EL a Cm) + EL b (EL a Ct) + EL a ws * EL b myall + EL b wall * EL a mys +
    2 * mM * EL a ws * EL b wall
Proof
  Induct >> rpt gen_tac >> Cases_on `Ct` >> Cases_on `ws` >> Cases_on `mys` >> Cases_on `g` >>
  Cases_on `a` >> simp [qrows_nil, qrows_cons, tails_eqs, qrow_el]
QED

Theorem IM_qform[local]:
  !Cm mM i Ct wall ws myall mys g u y.
    LENGTH Ct = LENGTH Cm /\ LENGTH ws = LENGTH Cm /\ LENGTH mys = LENGTH Cm /\
    LENGTH g = LENGTH Cm /\ LENGTH u = LENGTH Cm /\
    EVERY (\r. LENGTH r = LENGTH y) Cm /\ EVERY (\r. LENGTH r = LENGTH y) Ct /\
    LENGTH wall = LENGTH y /\ LENGTH myall = LENGTH y ==>
    qform (tails (qrows mM 0 i Cm Ct wall ws myall mys g)) u y =
    qform Cm u y + qform Ct u y + ldot ws u * ldot myall y + ldot mys u * ldot wall y +
    2 * real_of_int mM * ldot ws u * ldot wall y
Proof
  Induct >> rpt gen_tac >> Cases_on `Ct` >> Cases_on `ws` >> Cases_on `mys` >> Cases_on `g` >>
  Cases_on `u` >> simp [qrows_nil, qrows_cons, tails_eqs, qform_eqs, ldot_eqs, qrow_ldot] >>
  rpt strip_tac >> REAL_ARITH_TAC
QED

(* ---- the transpose leaves the quadratic form unchanged ---- *)

Theorem transp_len[local]:
  !n m. LENGTH (transp n m) = n
Proof
  Induct >> simp [transp_eqs]
QED

Theorem tails_every[local]:
  !rs n. EVERY (\x. LENGTH x = SUC n) rs ==> EVERY (\x. LENGTH x = n) (tails rs)
Proof
  Induct >- simp [tails_eqs] >>
  Cases >> simp [tails_eqs]
QED

Theorem transp_cons[local]:
  !n r rs. LENGTH r = n /\ EVERY (\x. LENGTH x = n) rs ==>
    transp n (r::rs) = MAP2 CONS r (transp n rs)
Proof
  Induct >- simp [transp_eqs] >>
  rpt gen_tac >> Cases_on `r` >> simp [transp_eqs, heads_eqs, tails_eqs, tails_every]
QED

Theorem qform_map2[local]:
  !r tt u y0 ys. LENGTH tt = LENGTH r /\ LENGTH u = LENGTH r ==>
    qform (MAP2 CONS r tt) u (y0::ys) = y0 * ldot r u + qform tt u ys
Proof
  Induct >> rpt gen_tac >> Cases_on `tt` >> Cases_on `u` >>
  simp [qform_eqs, ldot_eqs] >> rpt strip_tac >> REAL_ARITH_TAC
QED

Theorem qform_transp_nil[local]:
  !n u y. qform (transp n []) u y = 0
Proof
  Induct >> rpt gen_tac >> simp [transp_eqs, heads_eqs, tails_eqs, qform_eqs] >>
  Cases_on `u` >> simp [qform_eqs, ldot_eqs]
QED

Theorem qform_transp[local]:
  !Cm n u y. EVERY (\r. LENGTH r = n) Cm /\ LENGTH u = n /\ LENGTH y = LENGTH Cm ==>
    qform (transp n Cm) u y = qform Cm y u
Proof
  Induct >- (rpt gen_tac >> Cases_on `y` >> simp [qform_transp_nil, qform_eqs]) >>
  rpt gen_tac >> Cases_on `y` >> simp [qform_eqs] >> rpt strip_tac >>
  simp [transp_cons, qform_map2, transp_len]
QED

(* ---- the statement ---- *)

Theorem S109_as_constants[local]:
  S052 /\ S038 ==> S109
Proof
  strip_tac >> rewrite_tac [S109_def] >> rpt gen_tac >> strip_tac >>
  `LENGTH g = n /\ LENGTH Cm = n /\ EVERY (\r. LENGTH r = n) Cm /\ LENGTH mY = n`
    by fs [st_wf_def] >>
  `LENGTH (transp n Cm) = n /\ EVERY (\r. LENGTH r = n) (transp n Cm) /\
   !i j. i < n /\ j < n ==> EL j (EL i (transp n Cm)) = EL i (EL j Cm)`
    by (qpat_x_assum `S052` mp_tac >> rewrite_tac [S052_def] >>
        disch_then (qspecl_then [`n`, `Cm`] mp_tac) >> simp []) >>
  `LENGTH (lin mL ws g) = n`
    by (qpat_x_assum `S038` mp_tac >> rewrite_tac [S038_def] >>
        disch_then (qspecl_then [`ws`, `g`, `mL`] mp_tac) >> simp []) >>
  `qform (transp n Cm) y y = qform Cm y y` by (irule qform_transp >> simp []) >>
  simp [inner_matrix_def] >>
  rpt conj_tac
  >- simp [IM_len]
  >- (match_mp_tac IM_every >> simp [])
  >- (rpt strip_tac >> simp [IM_el] >> intLib.INT_RING_TAC) >>
  simp [IM_qform] >> REAL_ARITH_TAC
QED

Theorem S109 = CONV_RULE (RAND_CONV (REWR_CONV S109_def)) S109_as_constants
