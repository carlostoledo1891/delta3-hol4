# lemma_source.py — PRIVATE (git-ignored folder). The single source of the soundness lemmas AND of the
# planted false variants, with their truth values and counterexamples. Proving agents must never see
# this file, key.json, or LEMMAS.md: they get hol4/delta3/agents/ only (neutral ids).
# Each true lemma: (id, name, deps, purpose, statement). Each false variant: (of, kind, statement, why, instance).
PRE = r"0 < D /\ st_wf n st /\ LENGTH (y:real list) = n"
AF = "add_form D n 1096 lp lq hp hq kind i j k s1 s2 s3 mp mq st"
AFS = "add_forms D n 1096 lp lq hp hq forms st"
SP = "slab_poly D n ab cuts full Bp Bq lp lq hp hq theta forms"
IP = "inner_poly D n ab cuts full rp rq lam nu kp kq nn cc"
SM = "slab_matrix D ep eq ws st"
ST7 = "(ok,k,g,Cm,mL,mY,mM)"
DOM = (r"LENGTH Lw = LENGTH M /\ LENGTH ds = LENGTH M /\ EVERY (\r. LENGTH r = LENGTH M) M /\ "
       r"(!i j. i < LENGTH M /\ j < LENGTH M ==> EL j (EL i M) = EL i (EL j M)) /\ 0 < c1 /\ 0 <= c2")
def fold(fn, spec, sign="+"):
    return (PRE + rf" /\ FST ({fn}) ==> FST st /\ st_wf n ({fn}) /\ "
            rf"st_val ws ({fn}) y = st_val ws st y {sign} &D * {spec}")

T = []   # true lemmas
def L(id, name, deps, purpose, stmt): T.append(dict(id=id, name=name, deps=deps, purpose=purpose, stmt=" ".join(stmt.split())))
F = []   # planted false variants
def X(of, kind, stmt, why, inst): F.append(dict(of=of, kind=kind, stmt=" ".join(stmt.split()), why=why, inst=inst))

L("L01", "sc_exact", [], "the integer p * (D DIV q) is exactly D * p/q when q divides D",
  r"0 < D /\ D MOD q = 0 ==> real_of_int (sc D p q) = &D * qv p q")
X("L01", "dropped hypothesis", r"0 < D ==> real_of_int (sc D p q) = &D * qv p q",
  "D = 1, q = 2, p = 1: sc = 1 * &(1 DIV 2) = 0, but D * p/q = 1/2", dict(D="1", q="2", p="1"))

L("L02", "addl_spec", [], "adding v at position n of a list adds v * y_n to its dot product",
  r"LENGTH (addl n v l) = LENGTH l /\ (n < LENGTH l /\ LENGTH (y:real list) = LENGTH l ==> "
  r"ldot (addl n v l) y = ldot l y + real_of_int v * EL n y)")
X("L02", "mutated constant", r"LENGTH (addl n v l) = LENGTH l /\ (n < LENGTH l /\ LENGTH (y:real list) = LENGTH l ==> "
  r"ldot (addl n v l) y = ldot l y + 2 * real_of_int v * EL n y)",
  "l = [0], n = 0, v = 1, y = [1]: left 1, right 2", dict(n="0", v="1", l="[0]", y="[1]"))

L("L03", "addm_spec", ["L02"], "adding v at (i, j) of a matrix adds v * u_i * y_j to its bilinear form, shape kept",
  r"LENGTH (addm i j v Cm) = LENGTH Cm /\ (EVERY (\r. LENGTH r = n) Cm ==> EVERY (\r. LENGTH r = n) (addm i j v Cm)) /\ "
  r"(i < LENGTH Cm /\ j < n /\ EVERY (\r. LENGTH r = n) Cm /\ LENGTH (u:real list) = LENGTH Cm /\ LENGTH (y:real list) = n ==> "
  r"qform (addm i j v Cm) u y = qform Cm u y + real_of_int v * (EL i u * EL j y))")
X("L03", "mutated index", r"LENGTH (addm i j v Cm) = LENGTH Cm /\ (EVERY (\r. LENGTH r = n) Cm ==> EVERY (\r. LENGTH r = n) (addm i j v Cm)) /\ "
  r"(i < LENGTH Cm /\ j < n /\ EVERY (\r. LENGTH r = n) Cm /\ LENGTH (u:real list) = LENGTH Cm /\ LENGTH (y:real list) = n ==> "
  r"qform (addm i j v Cm) u y = qform Cm u y + real_of_int v * (EL j u * EL i y))",
  "Cm = 2x2 zero, i = 0, j = 1, v = 1, u = [1;0], y = [0;1]: left 1, right 0",
  dict(i="0", j="1", v="1", Cm="[[0;0];[0;0]]", n="2", u="[1;0]", y="[0;1]"))

L("L04", "add_term_guard", ["L02", "L03"], "add_term keeps the state well-formed, and an ok result means every guard held",
  r"(st_wf n st ==> st_wf n (add_term D n tag i j p q st)) /\ "
  r"(FST (add_term D n tag i j p q st) ==> FST st /\ D MOD q = 0 /\ i < n /\ j < n /\ tag <= 5)")
X("L04", "inequality turned strict", r"(st_wf n st ==> st_wf n (add_term D n tag i j p q st)) /\ "
  r"(FST (add_term D n tag i j p q st) ==> FST st /\ D MOD q = 0 /\ i < n /\ j < n /\ tag < 5)",
  "tag = 5 is accepted: D = 1, n = 1, i = j = 0, p = 0, q = 1 on the empty state",
  dict(D="1", n="1", tag="5", i="0", j="0", p="0", q="1", st="st0 1"))

L("L05", "add_term_val", ["L01", "L02", "L03", "L04"], "one accepted term adds exactly D * (p/q) * its monomial",
  PRE + r" /\ FST (add_term D n tag i j p q st) ==> "
  r"st_val ws (add_term D n tag i j p q st) y = st_val ws st y + &D * qv p q * mono ws tag i j y")
X("L05", "dropped hypothesis", PRE + r" ==> "
  r"st_val ws (add_term D n tag i j p q st) y = st_val ws st y + &D * qv p q * mono ws tag i j y",
  "without the ok flag q need not divide D: D = 1, q = 2, p = 1, tag 0: value 0, claimed 1/2",
  dict(D="1", n="1", tag="0", i="0", j="0", p="1", q="2", st="st0 1", y="[0]", ws="[0]"))

L("L06", "init_state", [], "the empty state is well-formed, ok, and stands for the zero polynomial",
  r"st_wf n (st0 n) /\ FST (st0 n) /\ (LENGTH (y:real list) = n ==> st_val ws (st0 n) y = 0)")
X("L06", "mutated constant", r"st_wf n (st0 n) /\ FST (st0 n) /\ (LENGTH (y:real list) = n ==> st_val ws (st0 n) y = 1)",
  "n = 0, y = []: the value is 0", dict(n="0", y="[]", ws="[]"))

L("L07", "add_cells_sound", ["L04", "L05"], "the per-cell terms a_i y_i + b_i y_i^2 enter exactly",
  fold("add_cells D n i ab st", "cells_val i ab y"))
X("L07", "mutated index", fold("add_cells D n i ab st", "cells_val (i + 1) ab y"),
  "n = 2, i = 0, ab = [(1,1,0,1)], y = [1;0]: value 1, claimed 0",
  dict(D="1", n="2", i="0", ab="[(1,1,0,1)]", st="st0 2", y="[1;0]", ws="[0;0]"))

L("L08", "add_full_sound", ["L04", "L05"], "the full pairs enter exactly",
  fold("add_full D n (1096 * 1096) full st", "full_val full y"))
X("L08", "mutated constant", fold("add_full D n 1096 full st", "full_val full y"),
  "with 1096 for 1096^2: D = 1096^2, full = [(0,0,1)], y = [1]: value 1096, claimed 1",
  dict(D="1096 * 1096", n="1", full="[(0,0,1)]", st="st0 1", y="[1]", ws="[0]"))

L("L09", "add_cut_sound", ["L04", "L05"], "the cut pairs enter exactly as theta*bound1 + (1-theta)*bound2, and every theta is in [0,1]",
  fold("add_cut D n (1096 * 1096) zs st", "cut_val zs y") +
  r" /\ EVERY (\z. 0 <= FST (SND z) /\ FST (SND z) <= &(SND (SND z))) zs")
X("L09", "inequality turned strict", fold("add_cut D n (1096 * 1096) zs st", "cut_val zs y") +
  r" /\ EVERY (\z. 0 <= FST (SND z) /\ FST (SND z) < &(SND (SND z))) zs",
  "theta = 1 is accepted: zs = [((0,0,1,1,0),(1,1))], D = 4*1096^2",
  dict(D="4 * (1096 * 1096)", n="1", zs="[((0,0,1,1,0),(1,1))]", st="st0 1", y="[0]", ws="[0]"))

L("L10", "add_zz_sound", ["L04", "L05"], "the helper of the triangle form subtracts c/q * z_a z_b, z = 1 - 2y",
  fold("add_zz D n c q a b st", "qv c q * ((1 - 2 * EL a y) * (1 - 2 * EL b y))", "-"))
X("L10", "sign flipped", fold("add_zz D n c q a b st", "qv c q * ((1 - 2 * EL a y) * (1 - 2 * EL b y))", "+"),
  "D = 1, c = q = 1, a = b = 0, y = [0]: value -1, claimed +1",
  dict(D="1", n="1", c="1", q="1", a="0", b="0", st="st0 1", y="[0]", ws="[0]"))

GUARD = (r"FST st /\ {mp} /\ kind <= 14 /\ form_idx_ok n kind i j k /\ (kind = 14 ==> (s1 = 1 \/ s1 = -1) /\ "
         r"(s2 = 1 \/ s2 = -1) /\ (s3 = 1 \/ s3 = -1) /\ s1 * s2 * s3 = 1)")
L("L11", "add_form_guard", ["L04"], "an accepted form has a non-negative multiplier, a known kind, indices in range, and a legal triangle sign pattern",
  rf"FST ({AF}) ==> " + GUARD.format(mp="0 <= mp"))
X("L11", "inequality turned strict", rf"FST ({AF}) ==> " + GUARD.format(mp="0 < mp"),
  "a zero multiplier is accepted: kind 5, mp = 0",
  dict(D="1", n="1", lp="0", lq="1", hp="1", hq="1", kind="5", i="0", j="0", k="0", s1="1", s2="1", s3="1", mp="0", mq="1", st="st0 1"))

FV = rf"st_wf n ({AF}) /\ st_val ws ({AF}) y = st_val ws st y - &D * qv mp mq * form_val {{m}} {{lo}} {{hi}} {{kind}} i j k s1 s2 s3 y"
L("L12", "add_form_val_y", ["L04", "L05"], "forms in the y's alone (kinds 0-6) subtract exactly mu * f(y)",
  PRE + rf" /\ kind <= 6 /\ FST ({AF}) ==> " + FV.format(m="m", lo="lo", hi="hi", kind="kind"))
X("L12", "wrong bound", PRE + rf" /\ kind <= 7 /\ FST ({AF}) ==> " + FV.format(m="m", lo="lo", hi="hi", kind="kind"),
  "kind 7 depends on m, which is free here: D = 1096, mp = 1, m = 5, lo = 0, y = [0]: value 0, claimed -5480",
  dict(D="1096", n="1", lp="0", lq="1", hp="1", hq="1", kind="7", i="0", j="0", k="0", s1="1", s2="1", s3="1", mp="1", mq="1",
       st="st0 1", y="[0]", ws="[0]", m="5", lo="0", hi="1"))

L("L13", "add_form_val_m", ["L04", "L05"], "forms in m (kinds 7-13) subtract exactly mu * f(y), with m = (SUM W y)/1096, lo = lp/lq, hi = hp/hq",
  PRE + rf" /\ 7 <= kind /\ kind <= 13 /\ FST ({AF}) ==> " + FV.format(m="(ldot ws y / 1096)", lo="(qv lp lq)", hi="(qv hp hq)", kind="kind"))
X("L13", "mutated constant", PRE + rf" /\ 7 <= kind /\ kind <= 13 /\ FST ({AF}) ==> " + FV.format(m="(ldot ws y / 548)", lo="(qv lp lq)", hi="(qv hp hq)", kind="kind"),
  "with 548 for 1096: kind 7, D = 1096, ws = [1096], y = [1]: value -1096, claimed -2192",
  dict(D="1096", n="1", lp="0", lq="1", hp="1", hq="1", kind="7", i="0", j="0", k="0", s1="1", s2="1", s3="1", mp="1", mq="1",
       st="st0 1", y="[1]", ws="[1096]"))

L("L14", "add_form_val_tri", ["L04", "L05", "L10"], "the triangle form (kind 14) subtracts exactly mu * (1 + s1 z_i z_j + s2 z_j z_k + s3 z_i z_k)",
  PRE + rf" /\ kind = 14 /\ FST ({AF}) ==> " + FV.format(m="m", lo="lo", hi="hi", kind="kind"))
X("L14", "mutated index", PRE + rf" /\ kind = 14 /\ FST ({AF}) ==> " +
  rf"st_wf n ({AF}) /\ st_val ws ({AF}) y = st_val ws st y - &D * qv mp mq * form_val m lo hi kind i k j s1 s2 s3 y",
  "j and k swapped: s = (1,-1,-1), y = [0;0;1]: the form is 4, the swapped one 0",
  dict(D="1", n="3", lp="0", lq="1", hp="1", hq="1", kind="14", i="0", j="1", k="2", s1="1", s2="-1", s3="-1", mp="1", mq="1",
       st="st0 3", y="[0;0;1]", ws="[0;0;0]", m="0", lo="0", hi="1"))

L("L15", "add_forms_sound", ["L11", "L12", "L13", "L14"], "the whole list of forms subtracts exactly SUM mu_f f(y)",
  fold(AFS, "forms_val (ldot ws y / 1096) (qv lp lq) (qv hp hq) forms y", "-"))
X("L15", "sign flipped", fold(AFS, "forms_val (ldot ws y / 1096) (qv lp lq) (qv hp hq) forms y", "+"),
  "one form y_0 with mu = 1, y = [1]: value -1, claimed +1",
  dict(D="1", n="1", lp="0", lq="1", hp="1", hq="1", forms="[(5,0,0,0,1,1,1,1,1)]", st="st0 1", y="[1]", ws="[0]"))

L("L16", "form_nonneg_box", [], "every non-triangle form is non-negative on the region",
  r"in_box n y /\ lo <= m /\ m <= hi /\ kind <= 13 /\ form_idx_ok n kind i j k ==> 0 <= form_val m lo hi kind i j k s1 s2 s3 y")
X("L16", "dropped hypothesis", r"in_box n y /\ m <= hi /\ kind <= 13 /\ form_idx_ok n kind i j k ==> 0 <= form_val m lo hi kind i j k s1 s2 s3 y",
  "kind 7 is m - lo: m = 0, lo = 1", dict(n="0", y="[]", m="0", lo="1", hi="2", kind="7", i="0", j="0", k="0", s1="1", s2="1", s3="1"))

TRIH = (r"-1 <= a /\ a <= 1 /\ -1 <= b /\ b <= 1 /\ -1 <= c /\ c <= (1:real) /\ (s1 = 1 \/ s1 = -1) /\ (s2 = 1 \/ s2 = -1) /\ "
        r"(s3 = 1 \/ s3 = -1)")
TRIC = r"1 + real_of_int s1 * (a * b) + real_of_int s2 * (b * c) + real_of_int s3 * (a * c)"
L("L17", "tri_nonneg", [], "the triangle inequality 1 + s1 ab + s2 bc + s3 ac >= 0 on the cube when s1 s2 s3 = 1",
  TRIH + r" /\ s1 * s2 * s3 = (1:int) ==> 0 <= " + TRIC)
X("L17", "dropped hypothesis", TRIH.replace("s1 = 1", "(s1:int) = 1") + r" ==> 0 <= " + TRIC,
  "s = (-1,-1,-1), a = b = c = 1: the value is -2", dict(a="1", b="1", c="1", s1="-1", s2="-1", s3="-1"))
X("L17", "inequality turned strict", TRIH + r" /\ s1 * s2 * s3 = (1:int) ==> 0 < " + TRIC,
  "s = (1,1,1), a = b = 1, c = -1: the value is 0", dict(a="1", b="1", c="-1", s1="1", s2="1", s3="1"))

L("L18", "forms_val_nonneg", ["L11", "L16", "L17"], "the accepted forms sum to something non-negative on the region",
  rf"FST ({AFS}) /\ in_box n y /\ lo <= m /\ m <= hi ==> 0 <= forms_val m lo hi forms y")
X("L18", "dropped hypothesis", rf"FST ({AFS}) /\ LENGTH (y:real list) = n /\ lo <= m /\ m <= hi ==> 0 <= forms_val m lo hi forms y",
  "outside the box: one form y_0 with mu = 1, y = [-1]",
  dict(D="1", n="1", lp="0", lq="1", hp="1", hq="1", forms="[(5,0,0,0,1,1,1,1,1)]", st="st0 1", y="[-1]", m="0", lo="0", hi="0"))

SPV = rf"st_wf n ({SP}) /\ D MOD Bq = 0 /\ st_val ws ({SP}) y = &D * (Ltheta ab cuts full theta y {{s}} qv Bp Bq - forms_val (ldot ws y / 1096) (qv lp lq) (qv hp hq) forms y)"
L("L19", "slab_poly_sound", ["L04", "L05", "L06", "L07", "L08", "L09", "L15"], "the rebuilt slab polynomial is D * (L_theta - B - SUM mu_f f)",
  rf"0 < D /\ LENGTH (y:real list) = n /\ FST ({SP}) ==> " + SPV.format(s="-"))
X("L19", "sign flipped", rf"0 < D /\ LENGTH (y:real list) = n /\ FST ({SP}) ==> " + SPV.format(s="+"),
  "everything empty but B = 1, n = 1, y = [0]: value -1, claimed +1",
  dict(D="1", n="1", ab="[]", cuts="[]", full="[]", Bp="1", Bq="1", lp="0", lq="1", hp="1", hq="1", theta="[]", forms="[]", y="[0]", ws="[0]"))

L("L20", "transp_spec", [], "transp is the transpose",
  r"EVERY (\r. LENGTH r = n) (Cm:int list list) ==> LENGTH (transp n Cm) = n /\ EVERY (\r. LENGTH r = LENGTH Cm) (transp n Cm) /\ "
  r"!i j. i < n /\ j < LENGTH Cm ==> EL j (EL i (transp n Cm)) = EL i (EL j Cm)")
X("L20", "mutated index", r"EVERY (\r. LENGTH r = n) (Cm:int list list) ==> LENGTH (transp n Cm) = n /\ EVERY (\r. LENGTH r = LENGTH Cm) (transp n Cm) /\ "
  r"!i j. i < n /\ j < LENGTH Cm ==> EL j (EL i (transp n Cm)) = EL j (EL i Cm)",
  "Cm = [[1;2];[3;4]]: entry (0,1) of the transpose is 3, not 2", dict(n="2", Cm="[[1;2];[3;4]]", i="0", j="1"))

L("L21", "lin_spec", [], "lin c ws g is g + c * ws entrywise",
  r"LENGTH (ws:int list) = LENGTH g ==> LENGTH (lin c ws g) = LENGTH g /\ !i. i < LENGTH g ==> EL i (lin c ws g) = EL i g + c * EL i ws")
X("L21", "mutated constant", r"LENGTH (ws:int list) = LENGTH g ==> LENGTH (lin c ws g) = LENGTH g /\ !i. i < LENGTH g ==> EL i (lin c ws g) = EL i g + EL i ws",
  "ws = [1], g = [1], c = 2: entry 3, claimed 2", dict(ws="[1]", g="[1]", c="2", i="0"))

SMS = (rf"LENGTH ({SM}) = {{len}} /\ EVERY (\r. LENGTH r = n + 1) ({SM}) /\ "
       rf"!i j. i < n + 1 /\ j < n + 1 ==> EL j (EL i ({SM})) = EL i (EL j ({SM}))")
L("L22", "slab_matrix_shape_sym", ["L20", "L21"], "the matrix M = 2D(S + eps I) is (n+1) x (n+1) and symmetric",
  r"st_wf n st /\ LENGTH (ws:int list) = n ==> " + SMS.format(len="n + 1"))
X("L22", "mutated constant", r"st_wf n st /\ LENGTH (ws:int list) = n ==> " + SMS.format(len="n"),
  "n = 0: the matrix is 1 x 1", dict(n="0", st="st0 0", ws="[]", D="1", ep="0", eq="1"))

L("L23", "slab_matrix_val", ["L20", "L21"], "v^T M v at v = (1, y) is 2 * (the state polynomial) + 2 D eps |v|^2",
  rf"st_wf n st /\ LENGTH (ws:int list) = n /\ LENGTH (y:real list) = n ==> "
  rf"qform ({SM}) (1 :: y) (1 :: y) = 2 * st_val ws st y + 2 * real_of_int (sc D ep eq) * (1 + sumsq y)")
X("L23", "mutated constant", rf"st_wf n st /\ LENGTH (ws:int list) = n /\ LENGTH (y:real list) = n ==> "
  rf"qform ({SM}) (1 :: y) (1 :: y) = 2 * st_val ws st y + 2 * real_of_int (sc D ep eq) * sumsq y",
  "n = 0, eps = 1: the form is 2, claimed 0", dict(n="0", st="st0 0", ws="[]", y="[]", D="1", ep="1", eq="1"))

L("L24", "sumsq_le", [], "|y|^2 <= n on the box", r"in_box n y ==> sumsq y <= &n")
X("L24", "inequality turned strict", r"in_box n y ==> sumsq y < &n", "n = 1, y = [1]", dict(n="1", y="[1]"))

L("L25", "widths_len", [], "a grid of n+1 points has n widths", r"LENGTH (widths grid) = LENGTH grid - 1")
X("L25", "mutated constant", r"LENGTH (widths grid) = LENGTH grid", "grid = [0]: no width", dict(grid="[0]"))

L("L26", "dd_rows_psd", [], "CRITICAL PATH: weighted diagonal dominance of 4^T M - 2D Lw Lw^T makes v^T M v >= 0",
  r"dd_rows c1 c2 0 M Lw Lw ds ds /\ " + DOM + r" ==> !v:real list. LENGTH v = LENGTH M ==> 0 <= qform M v v")
X("L26", "dropped hypothesis", r"dd_rows c1 c2 0 M Lw Lw ds ds /\ LENGTH Lw = LENGTH M /\ LENGTH ds = LENGTH M /\ "
  r"EVERY (\r. LENGTH r = LENGTH M) M /\ 0 < c1 /\ 0 <= c2 ==> !v:real list. LENGTH v = LENGTH M ==> 0 <= qform M v v",
  "without symmetry: M = [[1;-1];[-3;3]] is row-dominated, v = [2;1] gives -1",
  dict(c1="1", c2="0", M="[[1;-1];[-3;3]]", Lw="[[];[]]", ds="[1;1]", v="[2;1]"))
X("L26", "dropped hypothesis", r"dd_rows c1 c2 0 M Lw Lw ds ds /\ LENGTH Lw = LENGTH M /\ LENGTH ds = LENGTH M /\ "
  r"EVERY (\r. LENGTH r = LENGTH M) M /\ (!i j. i < LENGTH M /\ j < LENGTH M ==> EL j (EL i M) = EL i (EL j M)) /\ 0 <= c2 ==> "
  r"!v:real list. LENGTH v = LENGTH M ==> 0 <= qform M v v",
  "with c1 = 0 the test says nothing about M: M = [[-1]], v = [1]",
  dict(c1="0", c2="0", M="[[-1]]", Lw="[[]]", ds="[1]", v="[1]"))

CLB = r"(cp:int) * &(Bq:num) * &(eq:num) <= (Bp * &eq - ep * &(n + 1) * &Bq) * &(cq:num) ==> qv cp cq <= qv Bp Bq - qv ep eq * &(n + 1)"
L("L27", "claim_le_bound", [], "the integer test claim <= B - eps(1+n) means what it says in rationals",
  r"0 < Bq /\ 0 < eq /\ 0 < cq /\ " + CLB)
X("L27", "dropped hypothesis", r"0 < Bq /\ 0 < eq /\ " + CLB,
  "cq = 0: the integer test passes, the claim reads 0 and the bound is -1",
  dict(cp="0", Bq="1", eq="1", Bp="-1", ep="0", n="0", cq="0"))

SC = "slab_check ab cuts full grid lp lq hp hq Bp Bq ep eq cp cq theta forms D T2 ds Lw"
L("L28", "slab_check_sound", ["L01", "L18", "L19", "L22", "L23", "L24", "L25", "L26", "L27"],
  "TOP (slabs): if the check returns T then L_theta >= the claim everywhere on the region",
  rf"{SC} ==> !y. in_box (LENGTH grid - 1) y /\ qv lp lq <= mval grid y /\ mval grid y <= qv hp hq ==> qv cp cq <= Ltheta ab cuts full theta y")
X("L28", "dropped hypothesis", rf"{SC} ==> !y. in_box (LENGTH grid - 1) y /\ mval grid y <= qv hp hq ==> qv cp cq <= Ltheta ab cuts full theta y",
  "below the slab the bound fails: one cell, L_theta = 10y, region [1/2,1], form 10(m - 1/2), B = claim = 4; at y = 0 L_theta = 0 < 4",
  dict(ab="[(10,1,0,1)]", cuts="[]", full="[]", grid="[0;1096]", lp="1", lq="2", hp="1", hq="1", Bp="4", Bq="1", ep="0", eq="1",
       cp="4", cq="1", theta="[]", forms="[(7,0,0,0,1,1,1,10,1)]", D="1096", T2="0", ds="[1;1]", Lw="[[];[]]", y="[0]"))

PD = r"!v:real list. LENGTH v = LENGTH M ==> 0 <= qform M v v /\ (EXISTS (\x. x <> 0) v ==> 0 < qform M v v)"
L("L29", "sdd_rows_pd", ["L26"], "strict weighted dominance makes v^T M v > 0 for v <> 0 (strictness without leading minors)",
  r"sdd_rows c1 c2 0 M Lw Lw ds ds /\ " + DOM + " ==> " + PD)
X("L29", "inequality turned non-strict", r"dd_rows c1 c2 0 M Lw Lw ds ds /\ " + DOM + " ==> " + PD,
  "non-strict dominance allows the zero matrix: M = [[0]], v = [1]",
  dict(c1="1", c2="0", M="[[0]]", Lw="[[]]", ds="[1]", v="[1]"))

L("L30", "add_cut0_sound", ["L04", "L05"], "the cut pairs of L0 (the bound that vanishes at 0) enter exactly",
  fold("add_cut0 D n (1096 * 1096) cuts st", "cut0_val cuts y"))
X("L30", "sign flipped", fold("add_cut0 D n (1096 * 1096) cuts st", "cut0_val cuts y", "-"),
  "one pair with s_i s_j = -1, y = [1]: value -1, claimed +1",
  dict(D="1096 * 1096", n="1", cuts="[(0,0,-1,1,0)]", st="st0 1", y="[1]", ws="[0]"))

def mult(fn, spec, box, extra=""):
    return fold(fn, spec, "-") + rf" /\ ({box} ==> 0 <= {spec if not extra else extra})"
L("L31", "add_lam_sound", ["L04", "L05"], "the lam terms lam_ij y_i (1 - y_j) are subtracted exactly and are >= 0 on the box",
  mult("add_lam D n lam st", "lam_val lam y", "in_box n y"))
X("L31", "dropped hypothesis", fold("add_lam D n lam st", "lam_val lam y", "-") + r" /\ 0 <= lam_val lam y",
  "outside the box: lam = [(0,0,1,1)], y = [2] gives -2",
  dict(D="1", n="1", lam="[(0,0,1,1)]", st="st0 1", y="[2]", ws="[0]"))

NU = "add_nu D n 1096 rp rq j nu st"
L("L32", "add_nu_sound", ["L04", "L05"], "the nu terms nu_j y_j (rin - m) are subtracted exactly and are >= 0 on the region",
  fold(NU, "nu_val (ldot ws y / 1096) (qv rp rq) j nu y", "-") + r" /\ (in_box n y /\ m <= rin ==> 0 <= nu_val m rin j nu y)")
X("L32", "dropped hypothesis", fold(NU, "nu_val (ldot ws y / 1096) (qv rp rq) j nu y", "-") + r" /\ (in_box n y ==> 0 <= nu_val m rin j nu y)",
  "beyond the radius: nu = [(1,1)], y = [1], m = 2, rin = 1 gives -1",
  dict(D="1096", n="1", rp="1", rq="1", j="0", nu="[(1,1)]", st="st0 1", y="[1]", ws="[0]", m="2", rin="1"))

KAP = "add_kap D n 1096 rp rq kp kq st"
KV = (PRE + rf" /\ FST ({KAP}) ==> FST st /\ {{kp}} /\ st_wf n ({KAP}) /\ st_val ws ({KAP}) y = st_val ws st y - "
      r"&D * qv kp kq * ((ldot ws y / 1096) * (qv rp rq - ldot ws y / 1096))")
L("L33", "add_kap_sound", ["L04", "L05"], "the kap term kap m (rin - m) is subtracted exactly, kap >= 0", KV.format(kp="0 <= kp"))
X("L33", "inequality turned strict", KV.format(kp="0 < kp"), "kap = 0 is accepted",
  dict(D="1096 * 1096", n="1", rp="1", rq="1", kp="0", kq="1", st="st0 1", y="[0]", ws="[0]"))

L("L34", "add_nn_sound", ["L04", "L05"], "y^T N y (upper triangle given) is subtracted exactly and is >= 0 on the box",
  mult("add_nn D n nn st", "nn_val nn y", "in_box n y"))
X("L34", "mutated constant", fold("add_nn D n nn st", "(2 * nn_val nn y)", "-") + r" /\ (in_box n y ==> 0 <= nn_val nn y)",
  "nn = [(0,0,1,1)], y = [1]: value -1, claimed -2", dict(D="1", n="1", nn="[(0,0,1,1)]", st="st0 1", y="[1]", ws="[0]"))

L("L35", "add_cc_sound", ["L04", "L05"], "the linear terms c_i y_i are subtracted exactly and are >= 0 on the box",
  mult("add_cc D n i cc st", "cc_val i cc y", "in_box n y"))
X("L35", "mutated index", fold("add_cc D n i cc st", "cc_val (i + 1) cc y", "-") + r" /\ (in_box n y ==> 0 <= cc_val i cc y)",
  "n = 2, i = 0, cc = [(1,1)], y = [1;0]: value -1, claimed 0",
  dict(D="1", n="2", i="0", cc="[(1,1)]", st="st0 2", y="[1;0]", ws="[0;0]"))

IPV = (rf"0 < D /\ LENGTH (y:real list) = n /\ FST ({IP}) ==> st_wf n ({IP}) /\ "
       rf"st_val ws ({IP}) y = &D * (L0 ab cuts full y {{s}} mults_val (ldot ws y / 1096) (qv rp rq) lam nu (qv kp kq) nn cc y) /\ "
       r"(in_box n y /\ 0 <= m /\ m <= rin ==> 0 <= mults_val m rin lam nu (qv kp kq) nn cc y)")
L("L36", "inner_poly_sound", ["L06", "L07", "L08", "L30", "L31", "L32", "L33", "L34", "L35"],
  "the rebuilt inner polynomial is D * (L0 - every multiplier term), and the multiplier terms are >= 0 on the region",
  IPV.format(s="-"))
X("L36", "sign flipped", IPV.format(s="+"), "only c = [1], y = [1]: value -D, claimed +D",
  dict(D="1096 * 1096", n="1", ab="[]", cuts="[]", full="[]", rp="1", rq="1", lam="[]", nu="[]", kp="0", kq="1", nn="[]", cc="[(1,1)]",
       y="[1]", ws="[0]", m="0", rin="1"))

IM = f"inner_matrix ws {ST7}"
IMV = (rf"st_wf n {ST7} /\ LENGTH (ws:int list) = n /\ LENGTH (y:real list) = n ==> LENGTH ({IM}) = n /\ "
       rf"EVERY (\r. LENGTH r = n) ({IM}) /\ (!i j. i < n /\ j < n ==> EL j (EL i ({IM})) = EL i (EL j ({IM}))) /\ "
       rf"qform ({IM}) y y = {{c}}(qform Cm y y + ldot mY y * ldot ws y + real_of_int mM * (ldot ws y * ldot ws y))")
L("L37", "inner_matrix_val", ["L20", "L21"], "the matrix 2DP is n x n, symmetric, and y^T (2DP) y is twice the quadratic part of the state",
  IMV.format(c="2 * "))
X("L37", "mutated constant", IMV.format(c=""), "Cm = [[1]], y = [1]: the form is 2, claimed 1",
  dict(n="1", ok="T", k="0", g="[0]", Cm="[[1]]", mL="0", mY="[0]", mM="0", ws="[0]", y="[1]"))

LZ = (r"(LENGTH (ws:int list) = LENGTH g /\ LENGTH (y:real list) = LENGTH g ==> ldot (lin mL ws g) y = ldot g y {s} real_of_int mL * ldot ws y) /\ "
      r"(all_zero l ==> ldot l y = 0)")
L("L38", "lin_ldot", ["L21"], "the linear part after expanding m, and: an all-zero list has dot product 0", LZ.format(s="+"))
X("L38", "sign flipped", LZ.format(s="-"), "ws = [1], g = [0], mL = 1, y = [1]: value 1, claimed -1",
  dict(ws="[1]", g="[0]", mL="1", y="[1]", l="[]"))

L("L39", "mval_nonneg", ["L25"], "m >= 0 on the box when the grid increases",
  r"increasing grid /\ in_box (LENGTH grid - 1) y ==> 0 <= mval grid y")
X("L39", "dropped hypothesis", r"in_box (LENGTH grid - 1) y ==> 0 <= mval grid y",
  "a decreasing grid has a negative width: grid = [1096;0], y = [1] gives m = -1", dict(grid="[1096;0]", y="[1]"))

IC = "inner_check ab cuts full grid rp rq lam nu kp kq nn cc D T2 ds Lw"
ICV = rf"{IC} ==> !y. in_box (LENGTH grid - 1) y /\ mval grid y <= qv rp rq ==> {{c}} /\ (L0 ab cuts full y = 0 ==> EVERY (\x. x = 0) y)"
L("L40", "inner_check_sound", ["L25", "L29", "L36", "L37", "L38", "L39"],
  "TOP (inner): if the check returns T then L0 >= 0 on the region, with equality only at y = 0",
  ICV.format(c="0 <= L0 ab cuts full y"))
X("L40", "inequality turned strict", ICV.format(c="0 < L0 ab cuts full y"),
  "at y = 0, L0 = 0: one cell with L0 = y^2",
  dict(ab="[(0,1,1,1)]", cuts="[]", full="[]", grid="[0;1096]", rp="1", rq="1", lam="[]", nu="[(0,1)]", kp="0", kq="1", nn="[]", cc="[(0,1)]",
       D="1096 * 1096", T2="0", ds="[1]", Lw="[[]]", y="[0]"))

L("L41", "cover_step", [], "cover a ivs: every m with a < m <= 1/2 lies in one of the intervals",
  r"cover ap aq ivs ==> !m:real. qv ap aq < m /\ m <= 1 / 2 ==> in_some m ivs")
X("L41", "inequality turned non-strict", r"cover ap aq ivs ==> !m:real. qv ap aq <= m /\ m <= 1 / 2 ==> in_some m ivs",
  "a = 1/2, no interval left, m = 1/2", dict(ap="1", aq="2", ivs="[]", m="1 / 2"))

L("L42", "cover_all_sound", ["L41"], "TOP (cover): the regions cover every m in [0, 1/2]",
  r"cover_all ivs ==> !m:real. 0 <= m /\ m <= 1 / 2 ==> in_some m ivs")
X("L42", "wrong bound", r"cover_all ivs ==> !m:real. 0 <= m /\ m <= 1 ==> in_some m ivs",
  "ivs = [[0, 1/2]], m = 1", dict(ivs="[(0,1,1,2)]", m="1"))
