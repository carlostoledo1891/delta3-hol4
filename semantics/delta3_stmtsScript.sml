(*
  delta3_stmts — the statements the proving agents are given, each as a boolean constant
  Snn defined to be its statement (universally closed).  GENERATED (harness/gen-statements.py); do not edit.
  hol4/delta3 · cert-machine · the re-keyed benchmark

  Some of these statements are FALSE on purpose.  Which ones is not recorded in this
  folder.  The harness accepts a proof of Snn only as the kernel theorem
      |- (deps) ==> <statement of Snn>
  where deps are the constants of the statements it may use (harness/lemmas.json),
  and a refutation only as  |- ~<statement of Snn>.
  Nothing here is a theorem: these are definitions of propositions.
*)
Theory delta3_stmts
Ancestors
  arithmetic list integer real intreal delta3_check delta3_check2 delta3_sem
Libs
  intLib realLib

fun stmt nm tm =
  ignore (new_definition (nm ^ "_def",
            mk_eq (mk_var (nm, bool), list_mk_forall (free_vars_lr tm, tm))));

val _ = stmt "S001" “0 < D /\ st_wf n st /\ LENGTH (y:real list) = n /\ FST (add_cut D n (1096 * 1096) zs st) ==> FST st /\ st_wf n (add_cut D n (1096 * 1096) zs st) /\ st_val ws (add_cut D n (1096 * 1096) zs st) y = st_val ws st y + &D * cut_val zs y /\ EVERY (\z. 0 <= FST (SND z) /\ FST (SND z) <= &(SND (SND z))) zs”;

val _ = stmt "S002" “0 < D /\ st_wf n st /\ LENGTH (y:real list) = n /\ FST (add_lam D n lam st) ==> FST st /\ st_wf n (add_lam D n lam st) /\ st_val ws (add_lam D n lam st) y = st_val ws st y - &D * lam_val lam y /\ (in_box n y ==> 0 <= lam_val lam y)”;

val _ = stmt "S003" “0 < D /\ st_wf n st /\ LENGTH (y:real list) = n /\ FST (add_cc D n i cc st) ==> FST st /\ st_wf n (add_cc D n i cc st) /\ st_val ws (add_cc D n i cc st) y = st_val ws st y - &D * cc_val (i + 1) cc y /\ (in_box n y ==> 0 <= cc_val i cc y)”;

val _ = stmt "S004" “st_wf n (ok,k,g,Cm,mL,mY,mM) /\ LENGTH (ws:int list) = n /\ LENGTH (y:real list) = n ==> LENGTH (inner_matrix ws (ok,k,g,Cm,mL,mY,mM)) = n /\ EVERY (\r. LENGTH r = n) (inner_matrix ws (ok,k,g,Cm,mL,mY,mM)) /\ (!i j. i < n /\ j < n ==> EL j (EL i (inner_matrix ws (ok,k,g,Cm,mL,mY,mM))) = EL i (EL j (inner_matrix ws (ok,k,g,Cm,mL,mY,mM)))) /\ qform (inner_matrix ws (ok,k,g,Cm,mL,mY,mM)) y y = 2 * (qform Cm y y + ldot mY y * ldot ws y + real_of_int mM * (ldot ws y * ldot ws y))”;

val _ = stmt "S005" “st_wf n (st0 n) /\ FST (st0 n) /\ (LENGTH (y:real list) = n ==> st_val ws (st0 n) y = 0)”;

val _ = stmt "S006" “0 < D /\ st_wf n st /\ LENGTH (y:real list) = n /\ 7 <= kind /\ kind <= 13 /\ FST (add_form D n 1096 lp lq hp hq kind i j k s1 s2 s3 mp mq st) ==> st_wf n (add_form D n 1096 lp lq hp hq kind i j k s1 s2 s3 mp mq st) /\ st_val ws (add_form D n 1096 lp lq hp hq kind i j k s1 s2 s3 mp mq st) y = st_val ws st y - &D * qv mp mq * form_val (ldot ws y / 1096) (qv lp lq) (qv hp hq) kind i j k s1 s2 s3 y”;

val _ = stmt "S007" “0 < D /\ st_wf n st /\ LENGTH (y:real list) = n /\ FST (add_kap D n 1096 rp rq kp kq st) ==> FST st /\ 0 < kp /\ st_wf n (add_kap D n 1096 rp rq kp kq st) /\ st_val ws (add_kap D n 1096 rp rq kp kq st) y = st_val ws st y - &D * qv kp kq * ((ldot ws y / 1096) * (qv rp rq - ldot ws y / 1096))”;

val _ = stmt "S008" “FST (add_form D n 1096 lp lq hp hq kind i j k s1 s2 s3 mp mq st) ==> FST st /\ 0 < mp /\ kind <= 14 /\ form_idx_ok n kind i j k /\ (kind = 14 ==> (s1 = 1 \/ s1 = -1) /\ (s2 = 1 \/ s2 = -1) /\ (s3 = 1 \/ s3 = -1) /\ s1 * s2 * s3 = 1)”;

val _ = stmt "S009" “0 < D /\ st_wf n st /\ LENGTH (y:real list) = n /\ kind = 14 /\ FST (add_form D n 1096 lp lq hp hq kind i j k s1 s2 s3 mp mq st) ==> st_wf n (add_form D n 1096 lp lq hp hq kind i j k s1 s2 s3 mp mq st) /\ st_val ws (add_form D n 1096 lp lq hp hq kind i j k s1 s2 s3 mp mq st) y = st_val ws st y - &D * qv mp mq * form_val m lo hi kind i k j s1 s2 s3 y”;

val _ = stmt "S010" “0 < D /\ st_wf n st /\ LENGTH (y:real list) = n /\ FST (add_lam D n lam st) ==> FST st /\ st_wf n (add_lam D n lam st) /\ st_val ws (add_lam D n lam st) y = st_val ws st y - &D * lam_val lam y /\ 0 <= lam_val lam y”;

val _ = stmt "S011" “FST (add_forms D n 1096 lp lq hp hq forms st) /\ in_box n y /\ lo <= m /\ m <= hi ==> 0 <= forms_val m lo hi forms y”;

val _ = stmt "S012" “0 < D /\ st_wf n st /\ LENGTH (y:real list) = n /\ FST (add_cut D n (1096 * 1096) zs st) ==> FST st /\ st_wf n (add_cut D n (1096 * 1096) zs st) /\ st_val ws (add_cut D n (1096 * 1096) zs st) y = st_val ws st y + &D * cut_val zs y /\ EVERY (\z. 0 <= FST (SND z) /\ FST (SND z) < &(SND (SND z))) zs”;

val _ = stmt "S013" “in_box (LENGTH grid - 1) y ==> 0 <= mval grid y”;

val _ = stmt "S014" “st_wf n st /\ LENGTH (ws:int list) = n /\ LENGTH (y:real list) = n ==> qform (slab_matrix D ep eq ws st) (1 :: y) (1 :: y) = 2 * st_val ws st y + 2 * real_of_int (sc D ep eq) * sumsq y”;

val _ = stmt "S015" “inner_check ab cuts full grid rp rq lam nu kp kq nn cc D T2 ds Lw ==> !y. in_box (LENGTH grid - 1) y /\ mval grid y <= qv rp rq ==> 0 < L0 ab cuts full y /\ (L0 ab cuts full y = 0 ==> EVERY (\x. x = 0) y)”;

val _ = stmt "S016" “st_wf n st /\ LENGTH (ws:int list) = n ==> LENGTH (slab_matrix D ep eq ws st) = n /\ EVERY (\r. LENGTH r = n + 1) (slab_matrix D ep eq ws st) /\ !i j. i < n + 1 /\ j < n + 1 ==> EL j (EL i (slab_matrix D ep eq ws st)) = EL i (EL j (slab_matrix D ep eq ws st))”;

val _ = stmt "S017" “0 < D /\ D MOD q = 0 ==> real_of_int (sc D p q) = &D * qv p q”;

val _ = stmt "S018" “0 < D /\ st_wf n st /\ LENGTH (y:real list) = n /\ FST (add_full D n (1096 * 1096) full st) ==> FST st /\ st_wf n (add_full D n (1096 * 1096) full st) /\ st_val ws (add_full D n (1096 * 1096) full st) y = st_val ws st y + &D * full_val full y”;

val _ = stmt "S019" “0 < D /\ LENGTH (y:real list) = n /\ FST (slab_poly D n ab cuts full Bp Bq lp lq hp hq theta forms) ==> st_wf n (slab_poly D n ab cuts full Bp Bq lp lq hp hq theta forms) /\ D MOD Bq = 0 /\ st_val ws (slab_poly D n ab cuts full Bp Bq lp lq hp hq theta forms) y = &D * (Ltheta ab cuts full theta y - qv Bp Bq - forms_val (ldot ws y / 1096) (qv lp lq) (qv hp hq) forms y)”;

val _ = stmt "S020" “0 < D /\ st_wf n st /\ LENGTH (y:real list) = n /\ FST (add_nu D n 1096 rp rq j nu st) ==> FST st /\ st_wf n (add_nu D n 1096 rp rq j nu st) /\ st_val ws (add_nu D n 1096 rp rq j nu st) y = st_val ws st y - &D * nu_val (ldot ws y / 1096) (qv rp rq) j nu y /\ (in_box n y ==> 0 <= nu_val m rin j nu y)”;

val _ = stmt "S021" “LENGTH (addm i j v Cm) = LENGTH Cm /\ (EVERY (\r. LENGTH r = n) Cm ==> EVERY (\r. LENGTH r = n) (addm i j v Cm)) /\ (i < LENGTH Cm /\ j < n /\ EVERY (\r. LENGTH r = n) Cm /\ LENGTH (u:real list) = LENGTH Cm /\ LENGTH (y:real list) = n ==> qform (addm i j v Cm) u y = qform Cm u y + real_of_int v * (EL i u * EL j y))”;

val _ = stmt "S022" “0 < D /\ st_wf n st /\ LENGTH (y:real list) = n /\ FST (add_full D n (1096 * 1096) full st) ==> FST st /\ st_wf n (add_full D n (1096 * 1096) full st) /\ st_val ws (add_full D n (1096 * 1096) full st) y = st_val ws st y + &D * full_val full y”;

val _ = stmt "S023" “0 < D /\ st_wf n st /\ LENGTH (y:real list) = n /\ FST (add_nn D n nn st) ==> FST st /\ st_wf n (add_nn D n nn st) /\ st_val ws (add_nn D n nn st) y = st_val ws st y - &D * (2 * nn_val nn y) /\ (in_box n y ==> 0 <= nn_val nn y)”;

val _ = stmt "S024" “0 < Bq /\ 0 < eq /\ (cp:int) * &(Bq:num) * &(eq:num) <= (Bp * &eq - ep * &(n + 1) * &Bq) * &(cq:num) ==> qv cp cq <= qv Bp Bq - qv ep eq * &(n + 1)”;

val _ = stmt "S025" “in_box n y ==> sumsq y < &n”;

val _ = stmt "S026" “0 < D /\ st_wf n st /\ LENGTH (y:real list) = n /\ FST (add_nn D n nn st) ==> FST st /\ st_wf n (add_nn D n nn st) /\ st_val ws (add_nn D n nn st) y = st_val ws st y - &D * nn_val nn y /\ (in_box n y ==> 0 <= nn_val nn y)”;

val _ = stmt "S027" “st_wf n st /\ LENGTH (ws:int list) = n ==> LENGTH (slab_matrix D ep eq ws st) = n + 1 /\ EVERY (\r. LENGTH r = n + 1) (slab_matrix D ep eq ws st) /\ !i j. i < n + 1 /\ j < n + 1 ==> EL j (EL i (slab_matrix D ep eq ws st)) = EL i (EL j (slab_matrix D ep eq ws st))”;

val _ = stmt "S028" “0 < D /\ LENGTH (y:real list) = n /\ FST (inner_poly D n ab cuts full rp rq lam nu kp kq nn cc) ==> st_wf n (inner_poly D n ab cuts full rp rq lam nu kp kq nn cc) /\ st_val ws (inner_poly D n ab cuts full rp rq lam nu kp kq nn cc) y = &D * (L0 ab cuts full y - mults_val (ldot ws y / 1096) (qv rp rq) lam nu (qv kp kq) nn cc y) /\ (in_box n y /\ 0 <= m /\ m <= rin ==> 0 <= mults_val m rin lam nu (qv kp kq) nn cc y)”;

val _ = stmt "S029" “0 < D /\ st_wf n st /\ LENGTH (y:real list) = n /\ FST (add_cut0 D n (1096 * 1096) cuts st) ==> FST st /\ st_wf n (add_cut0 D n (1096 * 1096) cuts st) /\ st_val ws (add_cut0 D n (1096 * 1096) cuts st) y = st_val ws st y + &D * cut0_val cuts y”;

val _ = stmt "S030" “0 < D /\ st_wf n st /\ LENGTH (y:real list) = n /\ FST (add_cc D n i cc st) ==> FST st /\ st_wf n (add_cc D n i cc st) /\ st_val ws (add_cc D n i cc st) y = st_val ws st y - &D * cc_val i cc y /\ (in_box n y ==> 0 <= cc_val i cc y)”;

val _ = stmt "S031" “0 < D /\ st_wf n st /\ LENGTH (y:real list) = n /\ FST (add_nn D n nn st) ==> FST st /\ st_wf n (add_nn D n nn st) /\ st_val ws (add_nn D n nn st) y = st_val ws st y - &D * nn_val nn y /\ (in_box n y ==> 0 <= nn_val nn y)”;

val _ = stmt "S032" “0 < D /\ st_wf n st /\ LENGTH (y:real list) = n /\ kind <= 7 /\ FST (add_form D n 1096 lp lq hp hq kind i j k s1 s2 s3 mp mq st) ==> st_wf n (add_form D n 1096 lp lq hp hq kind i j k s1 s2 s3 mp mq st) /\ st_val ws (add_form D n 1096 lp lq hp hq kind i j k s1 s2 s3 mp mq st) y = st_val ws st y - &D * qv mp mq * form_val m lo hi kind i j k s1 s2 s3 y”;

val _ = stmt "S033" “0 < D /\ st_wf n st /\ LENGTH (y:real list) = n /\ FST (add_cells D n i ab st) ==> FST st /\ st_wf n (add_cells D n i ab st) /\ st_val ws (add_cells D n i ab st) y = st_val ws st y + &D * cells_val (i + 1) ab y”;

val _ = stmt "S034" “dd_rows c1 c2 0 M Lw Lw ds ds /\ LENGTH Lw = LENGTH M /\ LENGTH ds = LENGTH M /\ EVERY (\r. LENGTH r = LENGTH M) M /\ (!i j. i < LENGTH M /\ j < LENGTH M ==> EL j (EL i M) = EL i (EL j M)) /\ 0 <= c2 ==> !v:real list. LENGTH v = LENGTH M ==> 0 <= qform M v v”;

val _ = stmt "S035" “0 < D /\ st_wf n st /\ LENGTH (y:real list) = n /\ FST (add_kap D n 1096 rp rq kp kq st) ==> FST st /\ 0 < kp /\ st_wf n (add_kap D n 1096 rp rq kp kq st) /\ st_val ws (add_kap D n 1096 rp rq kp kq st) y = st_val ws st y - &D * qv kp kq * ((ldot ws y / 1096) * (qv rp rq - ldot ws y / 1096))”;

val _ = stmt "S036" “0 < D /\ LENGTH (y:real list) = n /\ FST (inner_poly D n ab cuts full rp rq lam nu kp kq nn cc) ==> st_wf n (inner_poly D n ab cuts full rp rq lam nu kp kq nn cc) /\ st_val ws (inner_poly D n ab cuts full rp rq lam nu kp kq nn cc) y = &D * (L0 ab cuts full y + mults_val (ldot ws y / 1096) (qv rp rq) lam nu (qv kp kq) nn cc y) /\ (in_box n y /\ 0 <= m /\ m <= rin ==> 0 <= mults_val m rin lam nu (qv kp kq) nn cc y)”;

val _ = stmt "S037" “0 < D /\ st_wf n st /\ LENGTH (y:real list) = n /\ FST (add_forms D n 1096 lp lq hp hq forms st) ==> FST st /\ st_wf n (add_forms D n 1096 lp lq hp hq forms st) /\ st_val ws (add_forms D n 1096 lp lq hp hq forms st) y = st_val ws st y + &D * forms_val (ldot ws y / 1096) (qv lp lq) (qv hp hq) forms y”;

val _ = stmt "S038" “LENGTH (ws:int list) = LENGTH g ==> LENGTH (lin c ws g) = LENGTH g /\ !i. i < LENGTH g ==> EL i (lin c ws g) = EL i g + c * EL i ws”;

val _ = stmt "S039" “0 < D /\ LENGTH (y:real list) = n /\ FST (inner_poly D n ab cuts full rp rq lam nu kp kq nn cc) ==> st_wf n (inner_poly D n ab cuts full rp rq lam nu kp kq nn cc) /\ st_val ws (inner_poly D n ab cuts full rp rq lam nu kp kq nn cc) y = &D * (L0 ab cuts full y - mults_val (ldot ws y / 1096) (qv rp rq) lam nu (qv kp kq) nn cc y) /\ (in_box n y /\ 0 <= m /\ m <= rin ==> 0 <= mults_val m rin lam nu (qv kp kq) nn cc y)”;

val _ = stmt "S040" “dd_rows c1 c2 0 M Lw Lw ds ds /\ LENGTH Lw = LENGTH M /\ LENGTH ds = LENGTH M /\ EVERY (\r. LENGTH r = LENGTH M) M /\ (!i j. i < LENGTH M /\ j < LENGTH M ==> EL j (EL i M) = EL i (EL j M)) /\ 0 < c1 /\ 0 <= c2 ==> !v:real list. LENGTH v = LENGTH M ==> 0 <= qform M v v”;

val _ = stmt "S041" “LENGTH (addl n v l) = LENGTH l /\ (n < LENGTH l /\ LENGTH (y:real list) = LENGTH l ==> ldot (addl n v l) y = ldot l y + real_of_int v * EL n y)”;

val _ = stmt "S042" “0 < D /\ st_wf n st /\ LENGTH (y:real list) = n /\ FST (add_term D n tag i j p q st) ==> st_val ws (add_term D n tag i j p q st) y = st_val ws st y + &D * qv p q * mono ws tag i j y”;

val _ = stmt "S043" “0 < D /\ st_wf n st /\ LENGTH (y:real list) = n /\ FST (add_kap D n 1096 rp rq kp kq st) ==> FST st /\ 0 <= kp /\ st_wf n (add_kap D n 1096 rp rq kp kq st) /\ st_val ws (add_kap D n 1096 rp rq kp kq st) y = st_val ws st y - &D * qv kp kq * ((ldot ws y / 1096) * (qv rp rq - ldot ws y / 1096))”;

val _ = stmt "S044" “0 < D /\ st_wf n st /\ LENGTH (y:real list) = n /\ kind <= 7 /\ FST (add_form D n 1096 lp lq hp hq kind i j k s1 s2 s3 mp mq st) ==> st_wf n (add_form D n 1096 lp lq hp hq kind i j k s1 s2 s3 mp mq st) /\ st_val ws (add_form D n 1096 lp lq hp hq kind i j k s1 s2 s3 mp mq st) y = st_val ws st y - &D * qv mp mq * form_val m lo hi kind i j k s1 s2 s3 y”;

val _ = stmt "S045" “slab_check ab cuts full grid lp lq hp hq Bp Bq ep eq cp cq theta forms D T2 ds Lw ==> !y. in_box (LENGTH grid - 1) y /\ mval grid y <= qv hp hq ==> qv cp cq <= Ltheta ab cuts full theta y”;

val _ = stmt "S046" “sdd_rows c1 c2 0 M Lw Lw ds ds /\ LENGTH Lw = LENGTH M /\ LENGTH ds = LENGTH M /\ EVERY (\r. LENGTH r = LENGTH M) M /\ (!i j. i < LENGTH M /\ j < LENGTH M ==> EL j (EL i M) = EL i (EL j M)) /\ 0 < c1 /\ 0 <= c2 ==> !v:real list. LENGTH v = LENGTH M ==> 0 <= qform M v v /\ (EXISTS (\x. x <> 0) v ==> 0 < qform M v v)”;

val _ = stmt "S047" “0 < D /\ st_wf n st /\ LENGTH (y:real list) = n /\ FST (add_cc D n i cc st) ==> FST st /\ st_wf n (add_cc D n i cc st) /\ st_val ws (add_cc D n i cc st) y = st_val ws st y - &D * cc_val i cc y /\ (in_box n y ==> 0 <= cc_val i cc y)”;

val _ = stmt "S048" “0 < D /\ st_wf n st /\ LENGTH (y:real list) = n /\ FST (add_cut0 D n (1096 * 1096) cuts st) ==> FST st /\ st_wf n (add_cut0 D n (1096 * 1096) cuts st) /\ st_val ws (add_cut0 D n (1096 * 1096) cuts st) y = st_val ws st y + &D * cut0_val cuts y”;

val _ = stmt "S049" “inner_check ab cuts full grid rp rq lam nu kp kq nn cc D T2 ds Lw ==> !y. in_box (LENGTH grid - 1) y /\ mval grid y <= qv rp rq ==> 0 <= L0 ab cuts full y /\ (L0 ab cuts full y = 0 ==> EVERY (\x. x = 0) y)”;

val _ = stmt "S050" “st_wf n (ok,k,g,Cm,mL,mY,mM) /\ LENGTH (ws:int list) = n /\ LENGTH (y:real list) = n ==> LENGTH (inner_matrix ws (ok,k,g,Cm,mL,mY,mM)) = n /\ EVERY (\r. LENGTH r = n) (inner_matrix ws (ok,k,g,Cm,mL,mY,mM)) /\ (!i j. i < n /\ j < n ==> EL j (EL i (inner_matrix ws (ok,k,g,Cm,mL,mY,mM))) = EL i (EL j (inner_matrix ws (ok,k,g,Cm,mL,mY,mM)))) /\ qform (inner_matrix ws (ok,k,g,Cm,mL,mY,mM)) y y = (qform Cm y y + ldot mY y * ldot ws y + real_of_int mM * (ldot ws y * ldot ws y))”;

val _ = stmt "S051" “0 < D /\ st_wf n st /\ LENGTH (y:real list) = n /\ kind = 14 /\ FST (add_form D n 1096 lp lq hp hq kind i j k s1 s2 s3 mp mq st) ==> st_wf n (add_form D n 1096 lp lq hp hq kind i j k s1 s2 s3 mp mq st) /\ st_val ws (add_form D n 1096 lp lq hp hq kind i j k s1 s2 s3 mp mq st) y = st_val ws st y - &D * qv mp mq * form_val m lo hi kind i j k s1 s2 s3 y”;

val _ = stmt "S052" “EVERY (\r. LENGTH r = n) (Cm:int list list) ==> LENGTH (transp n Cm) = n /\ EVERY (\r. LENGTH r = LENGTH Cm) (transp n Cm) /\ !i j. i < n /\ j < LENGTH Cm ==> EL j (EL i (transp n Cm)) = EL i (EL j Cm)”;

val _ = stmt "S053" “cover ap aq ivs ==> !m:real. qv ap aq < m /\ m <= 1 / 2 ==> in_some m ivs”;

val _ = stmt "S054" “-1 <= a /\ a <= 1 /\ -1 <= b /\ b <= 1 /\ -1 <= c /\ c <= (1:real) /\ (s1 = 1 \/ s1 = -1) /\ (s2 = 1 \/ s2 = -1) /\ (s3 = 1 \/ s3 = -1) /\ s1 * s2 * s3 = (1:int) ==> 0 <= 1 + real_of_int s1 * (a * b) + real_of_int s2 * (b * c) + real_of_int s3 * (a * c)”;

val _ = stmt "S055" “0 < D /\ st_wf n st /\ LENGTH (y:real list) = n /\ FST (add_lam D n lam st) ==> FST st /\ st_wf n (add_lam D n lam st) /\ st_val ws (add_lam D n lam st) y = st_val ws st y - &D * lam_val lam y /\ (in_box n y ==> 0 <= lam_val lam y)”;

val _ = stmt "S056" “0 < D /\ st_wf n st /\ LENGTH (y:real list) = n /\ FST (add_lam D n lam st) ==> FST st /\ st_wf n (add_lam D n lam st) /\ st_val ws (add_lam D n lam st) y = st_val ws st y - &D * lam_val lam y /\ (in_box n y ==> 0 <= lam_val lam y)”;

val _ = stmt "S057" “st_wf n st /\ LENGTH (ws:int list) = n /\ LENGTH (y:real list) = n ==> qform (slab_matrix D ep eq ws st) (1 :: y) (1 :: y) = 2 * st_val ws st y + 2 * real_of_int (sc D ep eq) * (1 + sumsq y)”;

val _ = stmt "S058" “(LENGTH (ws:int list) = LENGTH g /\ LENGTH (y:real list) = LENGTH g ==> ldot (lin mL ws g) y = ldot g y + real_of_int mL * ldot ws y) /\ (all_zero l ==> ldot l y = 0)”;

val _ = stmt "S059" “0 < D /\ st_wf n st /\ LENGTH (y:real list) = n /\ FST (add_nu D n 1096 rp rq j nu st) ==> FST st /\ st_wf n (add_nu D n 1096 rp rq j nu st) /\ st_val ws (add_nu D n 1096 rp rq j nu st) y = st_val ws st y - &D * nu_val (ldot ws y / 1096) (qv rp rq) j nu y /\ (in_box n y /\ m <= rin ==> 0 <= nu_val m rin j nu y)”;

val _ = stmt "S060" “in_box (LENGTH grid - 1) y ==> 0 <= mval grid y”;

val _ = stmt "S061" “LENGTH (addl n v l) = LENGTH l /\ (n < LENGTH l /\ LENGTH (y:real list) = LENGTH l ==> ldot (addl n v l) y = ldot l y + 2 * real_of_int v * EL n y)”;

val _ = stmt "S062" “in_box n y /\ m <= hi /\ kind <= 13 /\ form_idx_ok n kind i j k ==> 0 <= form_val m lo hi kind i j k s1 s2 s3 y”;

val _ = stmt "S063" “slab_check ab cuts full grid lp lq hp hq Bp Bq ep eq cp cq theta forms D T2 ds Lw ==> !y. in_box (LENGTH grid - 1) y /\ mval grid y <= qv hp hq ==> qv cp cq <= Ltheta ab cuts full theta y”;

val _ = stmt "S064" “0 < D /\ st_wf n st /\ LENGTH (y:real list) = n /\ kind = 14 /\ FST (add_form D n 1096 lp lq hp hq kind i j k s1 s2 s3 mp mq st) ==> st_wf n (add_form D n 1096 lp lq hp hq kind i j k s1 s2 s3 mp mq st) /\ st_val ws (add_form D n 1096 lp lq hp hq kind i j k s1 s2 s3 mp mq st) y = st_val ws st y - &D * qv mp mq * form_val m lo hi kind i k j s1 s2 s3 y”;

val _ = stmt "S065" “(LENGTH (ws:int list) = LENGTH g /\ LENGTH (y:real list) = LENGTH g ==> ldot (lin mL ws g) y = ldot g y - real_of_int mL * ldot ws y) /\ (all_zero l ==> ldot l y = 0)”;

val _ = stmt "S066" “0 < D /\ st_wf n st /\ LENGTH (y:real list) = n /\ FST (add_cut0 D n (1096 * 1096) cuts st) ==> FST st /\ st_wf n (add_cut0 D n (1096 * 1096) cuts st) /\ st_val ws (add_cut0 D n (1096 * 1096) cuts st) y = st_val ws st y - &D * cut0_val cuts y”;

val _ = stmt "S067" “LENGTH (addm i j v Cm) = LENGTH Cm /\ (EVERY (\r. LENGTH r = n) Cm ==> EVERY (\r. LENGTH r = n) (addm i j v Cm)) /\ (i < LENGTH Cm /\ j < n /\ EVERY (\r. LENGTH r = n) Cm /\ LENGTH (u:real list) = LENGTH Cm /\ LENGTH (y:real list) = n ==> qform (addm i j v Cm) u y = qform Cm u y + real_of_int v * (EL i u * EL j y))”;

val _ = stmt "S068" “FST (add_forms D n 1096 lp lq hp hq forms st) /\ LENGTH (y:real list) = n /\ lo <= m /\ m <= hi ==> 0 <= forms_val m lo hi forms y”;

val _ = stmt "S069" “0 < D /\ st_wf n st /\ LENGTH (y:real list) = n /\ FST (add_nu D n 1096 rp rq j nu st) ==> FST st /\ st_wf n (add_nu D n 1096 rp rq j nu st) /\ st_val ws (add_nu D n 1096 rp rq j nu st) y = st_val ws st y - &D * nu_val (ldot ws y / 1096) (qv rp rq) j nu y /\ (in_box n y /\ m <= rin ==> 0 <= nu_val m rin j nu y)”;

val _ = stmt "S070" “st_wf n st /\ LENGTH (ws:int list) = n ==> LENGTH (slab_matrix D ep eq ws st) = n /\ EVERY (\r. LENGTH r = n + 1) (slab_matrix D ep eq ws st) /\ !i j. i < n + 1 /\ j < n + 1 ==> EL j (EL i (slab_matrix D ep eq ws st)) = EL i (EL j (slab_matrix D ep eq ws st))”;

val _ = stmt "S071" “0 < D /\ st_wf n st /\ LENGTH (y:real list) = n /\ FST (add_cut D n (1096 * 1096) zs st) ==> FST st /\ st_wf n (add_cut D n (1096 * 1096) zs st) /\ st_val ws (add_cut D n (1096 * 1096) zs st) y = st_val ws st y + &D * cut_val zs y /\ EVERY (\z. 0 <= FST (SND z) /\ FST (SND z) < &(SND (SND z))) zs”;

val _ = stmt "S072" “0 < D /\ st_wf n st /\ LENGTH (y:real list) = n /\ FST (add_term D n tag i j p q st) ==> st_val ws (add_term D n tag i j p q st) y = st_val ws st y + &D * qv p q * mono ws tag i j y”;

val _ = stmt "S073" “inner_check ab cuts full grid rp rq lam nu kp kq nn cc D T2 ds Lw ==> !y. in_box (LENGTH grid - 1) y /\ mval grid y <= qv rp rq ==> 0 <= L0 ab cuts full y /\ (L0 ab cuts full y = 0 ==> EVERY (\x. x = 0) y)”;

val _ = stmt "S074" “FST (add_forms D n 1096 lp lq hp hq forms st) /\ in_box n y /\ lo <= m /\ m <= hi ==> 0 <= forms_val m lo hi forms y”;

val _ = stmt "S075" “0 < D /\ st_wf n st /\ LENGTH (y:real list) = n /\ FST (add_cc D n i cc st) ==> FST st /\ st_wf n (add_cc D n i cc st) /\ st_val ws (add_cc D n i cc st) y = st_val ws st y - &D * cc_val (i + 1) cc y /\ (in_box n y ==> 0 <= cc_val i cc y)”;

val _ = stmt "S076" “0 < D /\ st_wf n st /\ LENGTH (y:real list) = n /\ FST (add_kap D n 1096 rp rq kp kq st) ==> FST st /\ 0 < kp /\ st_wf n (add_kap D n 1096 rp rq kp kq st) /\ st_val ws (add_kap D n 1096 rp rq kp kq st) y = st_val ws st y - &D * qv kp kq * ((ldot ws y / 1096) * (qv rp rq - ldot ws y / 1096))”;

val _ = stmt "S077" “0 < D /\ st_wf n st /\ LENGTH (y:real list) = n /\ FST (add_zz D n c q a b st) ==> FST st /\ st_wf n (add_zz D n c q a b st) /\ st_val ws (add_zz D n c q a b st) y = st_val ws st y - &D * qv c q * ((1 - 2 * EL a y) * (1 - 2 * EL b y))”;

val _ = stmt "S078" “LENGTH (widths grid) = LENGTH grid - 1”;

val _ = stmt "S079" “0 < D /\ st_wf n st /\ LENGTH (y:real list) = n /\ FST (add_zz D n c q a b st) ==> FST st /\ st_wf n (add_zz D n c q a b st) /\ st_val ws (add_zz D n c q a b st) y = st_val ws st y + &D * qv c q * ((1 - 2 * EL a y) * (1 - 2 * EL b y))”;

val _ = stmt "S080" “0 < D /\ st_wf n st /\ LENGTH (y:real list) = n /\ FST (add_full D n 1096 full st) ==> FST st /\ st_wf n (add_full D n 1096 full st) /\ st_val ws (add_full D n 1096 full st) y = st_val ws st y + &D * full_val full y”;

val _ = stmt "S081" “0 < D /\ st_wf n st /\ LENGTH (y:real list) = n /\ FST (add_kap D n 1096 rp rq kp kq st) ==> FST st /\ 0 <= kp /\ st_wf n (add_kap D n 1096 rp rq kp kq st) /\ st_val ws (add_kap D n 1096 rp rq kp kq st) y = st_val ws st y - &D * qv kp kq * ((ldot ws y / 1096) * (qv rp rq - ldot ws y / 1096))”;

val _ = stmt "S082" “0 < D /\ st_wf n st /\ LENGTH (y:real list) = n /\ FST (add_zz D n c q a b st) ==> FST st /\ st_wf n (add_zz D n c q a b st) /\ st_val ws (add_zz D n c q a b st) y = st_val ws st y + &D * qv c q * ((1 - 2 * EL a y) * (1 - 2 * EL b y))”;

val _ = stmt "S083" “(st_wf n st ==> st_wf n (add_term D n tag i j p q st)) /\ (FST (add_term D n tag i j p q st) ==> FST st /\ D MOD q = 0 /\ i < n /\ j < n /\ tag < 5)”;

val _ = stmt "S084" “0 < D /\ st_wf n st /\ LENGTH (y:real list) = n /\ kind <= 6 /\ FST (add_form D n 1096 lp lq hp hq kind i j k s1 s2 s3 mp mq st) ==> st_wf n (add_form D n 1096 lp lq hp hq kind i j k s1 s2 s3 mp mq st) /\ st_val ws (add_form D n 1096 lp lq hp hq kind i j k s1 s2 s3 mp mq st) y = st_val ws st y - &D * qv mp mq * form_val m lo hi kind i j k s1 s2 s3 y”;

val _ = stmt "S085" “0 < D /\ st_wf n st /\ LENGTH (y:real list) = n /\ FST (add_cells D n i ab st) ==> FST st /\ st_wf n (add_cells D n i ab st) /\ st_val ws (add_cells D n i ab st) y = st_val ws st y + &D * cells_val (i + 1) ab y”;

val _ = stmt "S086" “-1 <= a /\ a <= 1 /\ -1 <= b /\ b <= 1 /\ -1 <= c /\ c <= (1:real) /\ (s1 = 1 \/ s1 = -1) /\ (s2 = 1 \/ s2 = -1) /\ (s3 = 1 \/ s3 = -1) /\ s1 * s2 * s3 = (1:int) ==> 0 < 1 + real_of_int s1 * (a * b) + real_of_int s2 * (b * c) + real_of_int s3 * (a * c)”;

val _ = stmt "S087" “slab_check ab cuts full grid lp lq hp hq Bp Bq ep eq cp cq theta forms D T2 ds Lw ==> !y. in_box (LENGTH grid - 1) y /\ mval grid y <= qv hp hq ==> qv cp cq <= Ltheta ab cuts full theta y”;

val _ = stmt "S088" “LENGTH (ws:int list) = LENGTH g ==> LENGTH (lin c ws g) = LENGTH g /\ !i. i < LENGTH g ==> EL i (lin c ws g) = EL i g + EL i ws”;

val _ = stmt "S089" “0 < D /\ st_wf n st /\ LENGTH (y:real list) = n /\ kind = 14 /\ FST (add_form D n 1096 lp lq hp hq kind i j k s1 s2 s3 mp mq st) ==> st_wf n (add_form D n 1096 lp lq hp hq kind i j k s1 s2 s3 mp mq st) /\ st_val ws (add_form D n 1096 lp lq hp hq kind i j k s1 s2 s3 mp mq st) y = st_val ws st y - &D * qv mp mq * form_val m lo hi kind i j k s1 s2 s3 y”;

val _ = stmt "S090" “cover_all ivs ==> !m:real. 0 <= m /\ m <= 1 ==> in_some m ivs”;

val _ = stmt "S091" “0 < D /\ st_wf n st /\ LENGTH (y:real list) = n /\ FST (add_forms D n 1096 lp lq hp hq forms st) ==> FST st /\ st_wf n (add_forms D n 1096 lp lq hp hq forms st) /\ st_val ws (add_forms D n 1096 lp lq hp hq forms st) y = st_val ws st y + &D * forms_val (ldot ws y / 1096) (qv lp lq) (qv hp hq) forms y”;

val _ = stmt "S092" “0 < D /\ st_wf n st /\ LENGTH (y:real list) = n /\ FST (add_cells D n i ab st) ==> FST st /\ st_wf n (add_cells D n i ab st) /\ st_val ws (add_cells D n i ab st) y = st_val ws st y + &D * cells_val i ab y”;

val _ = stmt "S093" “inner_check ab cuts full grid rp rq lam nu kp kq nn cc D T2 ds Lw ==> !y. in_box (LENGTH grid - 1) y /\ mval grid y <= qv rp rq ==> 0 < L0 ab cuts full y /\ (L0 ab cuts full y = 0 ==> EVERY (\x. x = 0) y)”;

val _ = stmt "S094" “0 < D /\ st_wf n st /\ LENGTH (y:real list) = n /\ FST (add_cells D n i ab st) ==> FST st /\ st_wf n (add_cells D n i ab st) /\ st_val ws (add_cells D n i ab st) y = st_val ws st y + &D * cells_val i ab y”;

val _ = stmt "S095" “FST (add_form D n 1096 lp lq hp hq kind i j k s1 s2 s3 mp mq st) ==> FST st /\ 0 <= mp /\ kind <= 14 /\ form_idx_ok n kind i j k /\ (kind = 14 ==> (s1 = 1 \/ s1 = -1) /\ (s2 = 1 \/ s2 = -1) /\ (s3 = 1 \/ s3 = -1) /\ s1 * s2 * s3 = 1)”;

val _ = stmt "S096" “0 < D /\ st_wf n st /\ LENGTH (y:real list) = n /\ FST (add_lam D n lam st) ==> FST st /\ st_wf n (add_lam D n lam st) /\ st_val ws (add_lam D n lam st) y = st_val ws st y - &D * lam_val lam y /\ 0 <= lam_val lam y”;

val _ = stmt "S097" “0 < D /\ st_wf n st /\ LENGTH (y:real list) = n /\ FST (add_forms D n 1096 lp lq hp hq forms st) ==> FST st /\ st_wf n (add_forms D n 1096 lp lq hp hq forms st) /\ st_val ws (add_forms D n 1096 lp lq hp hq forms st) y = st_val ws st y - &D * forms_val (ldot ws y / 1096) (qv lp lq) (qv hp hq) forms y”;

val _ = stmt "S098" “0 < D /\ st_wf n st /\ LENGTH (y:real list) = n /\ 7 <= kind /\ kind <= 13 /\ FST (add_form D n 1096 lp lq hp hq kind i j k s1 s2 s3 mp mq st) ==> st_wf n (add_form D n 1096 lp lq hp hq kind i j k s1 s2 s3 mp mq st) /\ st_val ws (add_form D n 1096 lp lq hp hq kind i j k s1 s2 s3 mp mq st) y = st_val ws st y - &D * qv mp mq * form_val (ldot ws y / 1096) (qv lp lq) (qv hp hq) kind i j k s1 s2 s3 y”;

val _ = stmt "S099" “cover_all ivs ==> !m:real. 0 <= m /\ m <= 1 ==> in_some m ivs”;

val _ = stmt "S100" “0 < D /\ st_wf n st /\ LENGTH (y:real list) = n /\ FST (add_full D n (1096 * 1096) full st) ==> FST st /\ st_wf n (add_full D n (1096 * 1096) full st) /\ st_val ws (add_full D n (1096 * 1096) full st) y = st_val ws st y + &D * full_val full y”;

val _ = stmt "S101" “0 < D /\ st_wf n st /\ LENGTH (y:real list) = n /\ kind = 14 /\ FST (add_form D n 1096 lp lq hp hq kind i j k s1 s2 s3 mp mq st) ==> st_wf n (add_form D n 1096 lp lq hp hq kind i j k s1 s2 s3 mp mq st) /\ st_val ws (add_form D n 1096 lp lq hp hq kind i j k s1 s2 s3 mp mq st) y = st_val ws st y - &D * qv mp mq * form_val m lo hi kind i j k s1 s2 s3 y”;

val _ = stmt "S102" “cover ap aq ivs ==> !m:real. qv ap aq <= m /\ m <= 1 / 2 ==> in_some m ivs”;

val _ = stmt "S103" “st_wf n (ok,k,g,Cm,mL,mY,mM) /\ LENGTH (ws:int list) = n /\ LENGTH (y:real list) = n ==> LENGTH (inner_matrix ws (ok,k,g,Cm,mL,mY,mM)) = n /\ EVERY (\r. LENGTH r = n) (inner_matrix ws (ok,k,g,Cm,mL,mY,mM)) /\ (!i j. i < n /\ j < n ==> EL j (EL i (inner_matrix ws (ok,k,g,Cm,mL,mY,mM))) = EL i (EL j (inner_matrix ws (ok,k,g,Cm,mL,mY,mM)))) /\ qform (inner_matrix ws (ok,k,g,Cm,mL,mY,mM)) y y = (qform Cm y y + ldot mY y * ldot ws y + real_of_int mM * (ldot ws y * ldot ws y))”;

val _ = stmt "S104" “0 < D /\ st_wf n st /\ LENGTH (y:real list) = n /\ FST (add_cut D n (1096 * 1096) zs st) ==> FST st /\ st_wf n (add_cut D n (1096 * 1096) zs st) /\ st_val ws (add_cut D n (1096 * 1096) zs st) y = st_val ws st y + &D * cut_val zs y /\ EVERY (\z. 0 <= FST (SND z) /\ FST (SND z) < &(SND (SND z))) zs”;

val _ = stmt "S105" “0 < D /\ LENGTH (y:real list) = n /\ FST (inner_poly D n ab cuts full rp rq lam nu kp kq nn cc) ==> st_wf n (inner_poly D n ab cuts full rp rq lam nu kp kq nn cc) /\ st_val ws (inner_poly D n ab cuts full rp rq lam nu kp kq nn cc) y = &D * (L0 ab cuts full y - mults_val (ldot ws y / 1096) (qv rp rq) lam nu (qv kp kq) nn cc y) /\ (in_box n y /\ 0 <= m /\ m <= rin ==> 0 <= mults_val m rin lam nu (qv kp kq) nn cc y)”;

val _ = stmt "S106" “0 < D /\ st_wf n st /\ LENGTH (y:real list) = n /\ 7 <= kind /\ kind <= 13 /\ FST (add_form D n 1096 lp lq hp hq kind i j k s1 s2 s3 mp mq st) ==> st_wf n (add_form D n 1096 lp lq hp hq kind i j k s1 s2 s3 mp mq st) /\ st_val ws (add_form D n 1096 lp lq hp hq kind i j k s1 s2 s3 mp mq st) y = st_val ws st y - &D * qv mp mq * form_val (ldot ws y / 548) (qv lp lq) (qv hp hq) kind i j k s1 s2 s3 y”;

val _ = stmt "S107" “0 < D /\ st_wf n st /\ LENGTH (y:real list) = n /\ FST (add_forms D n 1096 lp lq hp hq forms st) ==> FST st /\ st_wf n (add_forms D n 1096 lp lq hp hq forms st) /\ st_val ws (add_forms D n 1096 lp lq hp hq forms st) y = st_val ws st y - &D * forms_val (ldot ws y / 1096) (qv lp lq) (qv hp hq) forms y”;

val _ = stmt "S108" “0 < Bq /\ 0 < eq /\ 0 < cq /\ (cp:int) * &(Bq:num) * &(eq:num) <= (Bp * &eq - ep * &(n + 1) * &Bq) * &(cq:num) ==> qv cp cq <= qv Bp Bq - qv ep eq * &(n + 1)”;

val _ = stmt "S109" “st_wf n (ok,k,g,Cm,mL,mY,mM) /\ LENGTH (ws:int list) = n /\ LENGTH (y:real list) = n ==> LENGTH (inner_matrix ws (ok,k,g,Cm,mL,mY,mM)) = n /\ EVERY (\r. LENGTH r = n) (inner_matrix ws (ok,k,g,Cm,mL,mY,mM)) /\ (!i j. i < n /\ j < n ==> EL j (EL i (inner_matrix ws (ok,k,g,Cm,mL,mY,mM))) = EL i (EL j (inner_matrix ws (ok,k,g,Cm,mL,mY,mM)))) /\ qform (inner_matrix ws (ok,k,g,Cm,mL,mY,mM)) y y = 2 * (qform Cm y y + ldot mY y * ldot ws y + real_of_int mM * (ldot ws y * ldot ws y))”;

val _ = stmt "S110" “(st_wf n st ==> st_wf n (add_term D n tag i j p q st)) /\ (FST (add_term D n tag i j p q st) ==> FST st /\ D MOD q = 0 /\ i < n /\ j < n /\ tag <= 5)”;

val _ = stmt "S111" “0 < D /\ LENGTH (y:real list) = n /\ FST (inner_poly D n ab cuts full rp rq lam nu kp kq nn cc) ==> st_wf n (inner_poly D n ab cuts full rp rq lam nu kp kq nn cc) /\ st_val ws (inner_poly D n ab cuts full rp rq lam nu kp kq nn cc) y = &D * (L0 ab cuts full y + mults_val (ldot ws y / 1096) (qv rp rq) lam nu (qv kp kq) nn cc y) /\ (in_box n y /\ 0 <= m /\ m <= rin ==> 0 <= mults_val m rin lam nu (qv kp kq) nn cc y)”;

val _ = stmt "S112" “0 < D /\ st_wf n st /\ LENGTH (y:real list) = n /\ 7 <= kind /\ kind <= 13 /\ FST (add_form D n 1096 lp lq hp hq kind i j k s1 s2 s3 mp mq st) ==> st_wf n (add_form D n 1096 lp lq hp hq kind i j k s1 s2 s3 mp mq st) /\ st_val ws (add_form D n 1096 lp lq hp hq kind i j k s1 s2 s3 mp mq st) y = st_val ws st y - &D * qv mp mq * form_val (ldot ws y / 1096) (qv lp lq) (qv hp hq) kind i j k s1 s2 s3 y”;

val _ = stmt "S113" “dd_rows c1 c2 0 M Lw Lw ds ds /\ LENGTH Lw = LENGTH M /\ LENGTH ds = LENGTH M /\ EVERY (\r. LENGTH r = LENGTH M) M /\ (!i j. i < LENGTH M /\ j < LENGTH M ==> EL j (EL i M) = EL i (EL j M)) /\ 0 < c1 /\ 0 <= c2 ==> !v:real list. LENGTH v = LENGTH M ==> 0 <= qform M v v /\ (EXISTS (\x. x <> 0) v ==> 0 < qform M v v)”;

val _ = stmt "S114" “cover_all ivs ==> !m:real. 0 <= m /\ m <= 1 / 2 ==> in_some m ivs”;

val _ = stmt "S115" “increasing grid /\ in_box (LENGTH grid - 1) y ==> 0 <= mval grid y”;

val _ = stmt "S116" “0 < D /\ LENGTH (y:real list) = n /\ FST (slab_poly D n ab cuts full Bp Bq lp lq hp hq theta forms) ==> st_wf n (slab_poly D n ab cuts full Bp Bq lp lq hp hq theta forms) /\ D MOD Bq = 0 /\ st_val ws (slab_poly D n ab cuts full Bp Bq lp lq hp hq theta forms) y = &D * (Ltheta ab cuts full theta y + qv Bp Bq - forms_val (ldot ws y / 1096) (qv lp lq) (qv hp hq) forms y)”;

val _ = stmt "S117" “0 < D /\ st_wf n st /\ LENGTH (y:real list) = n /\ FST (add_zz D n c q a b st) ==> FST st /\ st_wf n (add_zz D n c q a b st) /\ st_val ws (add_zz D n c q a b st) y = st_val ws st y - &D * qv c q * ((1 - 2 * EL a y) * (1 - 2 * EL b y))”;

val _ = stmt "S118" “FST (add_forms D n 1096 lp lq hp hq forms st) /\ LENGTH (y:real list) = n /\ lo <= m /\ m <= hi ==> 0 <= forms_val m lo hi forms y”;

val _ = stmt "S119" “0 < D /\ st_wf n st /\ LENGTH (y:real list) = n /\ FST (add_nu D n 1096 rp rq j nu st) ==> FST st /\ st_wf n (add_nu D n 1096 rp rq j nu st) /\ st_val ws (add_nu D n 1096 rp rq j nu st) y = st_val ws st y - &D * nu_val (ldot ws y / 1096) (qv rp rq) j nu y /\ (in_box n y /\ m <= rin ==> 0 <= nu_val m rin j nu y)”;

val _ = stmt "S120" “st_wf n st /\ LENGTH (ws:int list) = n /\ LENGTH (y:real list) = n ==> qform (slab_matrix D ep eq ws st) (1 :: y) (1 :: y) = 2 * st_val ws st y + 2 * real_of_int (sc D ep eq) * sumsq y”;

val _ = stmt "S121" “st_wf n (ok,k,g,Cm,mL,mY,mM) /\ LENGTH (ws:int list) = n /\ LENGTH (y:real list) = n ==> LENGTH (inner_matrix ws (ok,k,g,Cm,mL,mY,mM)) = n /\ EVERY (\r. LENGTH r = n) (inner_matrix ws (ok,k,g,Cm,mL,mY,mM)) /\ (!i j. i < n /\ j < n ==> EL j (EL i (inner_matrix ws (ok,k,g,Cm,mL,mY,mM))) = EL i (EL j (inner_matrix ws (ok,k,g,Cm,mL,mY,mM)))) /\ qform (inner_matrix ws (ok,k,g,Cm,mL,mY,mM)) y y = 2 * (qform Cm y y + ldot mY y * ldot ws y + real_of_int mM * (ldot ws y * ldot ws y))”;

val _ = stmt "S122" “LENGTH (addm i j v Cm) = LENGTH Cm /\ (EVERY (\r. LENGTH r = n) Cm ==> EVERY (\r. LENGTH r = n) (addm i j v Cm)) /\ (i < LENGTH Cm /\ j < n /\ EVERY (\r. LENGTH r = n) Cm /\ LENGTH (u:real list) = LENGTH Cm /\ LENGTH (y:real list) = n ==> qform (addm i j v Cm) u y = qform Cm u y + real_of_int v * (EL j u * EL i y))”;

val _ = stmt "S123" “in_box n y ==> sumsq y <= &n”;

val _ = stmt "S124" “st_wf n st /\ LENGTH (ws:int list) = n /\ LENGTH (y:real list) = n ==> qform (slab_matrix D ep eq ws st) (1 :: y) (1 :: y) = 2 * st_val ws st y + 2 * real_of_int (sc D ep eq) * sumsq y”;

val _ = stmt "S125" “st_wf n st /\ LENGTH (ws:int list) = n ==> LENGTH (slab_matrix D ep eq ws st) = n /\ EVERY (\r. LENGTH r = n + 1) (slab_matrix D ep eq ws st) /\ !i j. i < n + 1 /\ j < n + 1 ==> EL j (EL i (slab_matrix D ep eq ws st)) = EL i (EL j (slab_matrix D ep eq ws st))”;

val _ = stmt "S126" “slab_check ab cuts full grid lp lq hp hq Bp Bq ep eq cp cq theta forms D T2 ds Lw ==> !y. in_box (LENGTH grid - 1) y /\ mval grid y <= qv hp hq ==> qv cp cq <= Ltheta ab cuts full theta y”;

val _ = stmt "S127" “0 < D /\ LENGTH (y:real list) = n /\ FST (slab_poly D n ab cuts full Bp Bq lp lq hp hq theta forms) ==> st_wf n (slab_poly D n ab cuts full Bp Bq lp lq hp hq theta forms) /\ D MOD Bq = 0 /\ st_val ws (slab_poly D n ab cuts full Bp Bq lp lq hp hq theta forms) y = &D * (Ltheta ab cuts full theta y - qv Bp Bq - forms_val (ldot ws y / 1096) (qv lp lq) (qv hp hq) forms y)”;

val _ = stmt "S128" “0 < D /\ st_wf n st /\ LENGTH (y:real list) = n /\ FST (add_nu D n 1096 rp rq j nu st) ==> FST st /\ st_wf n (add_nu D n 1096 rp rq j nu st) /\ st_val ws (add_nu D n 1096 rp rq j nu st) y = st_val ws st y - &D * nu_val (ldot ws y / 1096) (qv rp rq) j nu y /\ (in_box n y ==> 0 <= nu_val m rin j nu y)”;

val _ = stmt "S129" “inner_check ab cuts full grid rp rq lam nu kp kq nn cc D T2 ds Lw ==> !y. in_box (LENGTH grid - 1) y /\ mval grid y <= qv rp rq ==> 0 < L0 ab cuts full y /\ (L0 ab cuts full y = 0 ==> EVERY (\x. x = 0) y)”;

val _ = stmt "S130" “0 < D /\ st_wf n st /\ LENGTH (y:real list) = n /\ FST (add_cells D n i ab st) ==> FST st /\ st_wf n (add_cells D n i ab st) /\ st_val ws (add_cells D n i ab st) y = st_val ws st y + &D * cells_val i ab y”;

val _ = stmt "S131" “0 < D ==> real_of_int (sc D p q) = &D * qv p q”;

val _ = stmt "S132" “0 < D /\ LENGTH (y:real list) = n /\ FST (slab_poly D n ab cuts full Bp Bq lp lq hp hq theta forms) ==> st_wf n (slab_poly D n ab cuts full Bp Bq lp lq hp hq theta forms) /\ D MOD Bq = 0 /\ st_val ws (slab_poly D n ab cuts full Bp Bq lp lq hp hq theta forms) y = &D * (Ltheta ab cuts full theta y - qv Bp Bq - forms_val (ldot ws y / 1096) (qv lp lq) (qv hp hq) forms y)”;

val _ = stmt "S133" “0 < D /\ LENGTH (y:real list) = n /\ FST (slab_poly D n ab cuts full Bp Bq lp lq hp hq theta forms) ==> st_wf n (slab_poly D n ab cuts full Bp Bq lp lq hp hq theta forms) /\ D MOD Bq = 0 /\ st_val ws (slab_poly D n ab cuts full Bp Bq lp lq hp hq theta forms) y = &D * (Ltheta ab cuts full theta y + qv Bp Bq - forms_val (ldot ws y / 1096) (qv lp lq) (qv hp hq) forms y)”;

val _ = stmt "S134" “st_wf n st /\ LENGTH (ws:int list) = n ==> LENGTH (slab_matrix D ep eq ws st) = n + 1 /\ EVERY (\r. LENGTH r = n + 1) (slab_matrix D ep eq ws st) /\ !i j. i < n + 1 /\ j < n + 1 ==> EL j (EL i (slab_matrix D ep eq ws st)) = EL i (EL j (slab_matrix D ep eq ws st))”;

val _ = stmt "S135" “(st_wf n st ==> st_wf n (add_term D n tag i j p q st)) /\ (FST (add_term D n tag i j p q st) ==> FST st /\ D MOD q = 0 /\ i < n /\ j < n /\ tag <= 5)”;

val _ = stmt "S136" “st_wf n st /\ LENGTH (ws:int list) = n /\ LENGTH (y:real list) = n ==> qform (slab_matrix D ep eq ws st) (1 :: y) (1 :: y) = 2 * st_val ws st y + 2 * real_of_int (sc D ep eq) * sumsq y”;

val _ = stmt "S137" “0 < D /\ st_wf n st /\ LENGTH (y:real list) = n ==> st_val ws (add_term D n tag i j p q st) y = st_val ws st y + &D * qv p q * mono ws tag i j y”;

val _ = stmt "S138" “0 < D /\ st_wf n st /\ LENGTH (y:real list) = n ==> st_val ws (add_term D n tag i j p q st) y = st_val ws st y + &D * qv p q * mono ws tag i j y”;

val _ = stmt "S139" “0 < D /\ st_wf n st /\ LENGTH (y:real list) = n /\ FST (add_nn D n nn st) ==> FST st /\ st_wf n (add_nn D n nn st) /\ st_val ws (add_nn D n nn st) y = st_val ws st y - &D * nn_val nn y /\ (in_box n y ==> 0 <= nn_val nn y)”;

val _ = stmt "S140" “0 < D /\ st_wf n st /\ LENGTH (y:real list) = n /\ FST (add_cc D n i cc st) ==> FST st /\ st_wf n (add_cc D n i cc st) /\ st_val ws (add_cc D n i cc st) y = st_val ws st y - &D * cc_val (i + 1) cc y /\ (in_box n y ==> 0 <= cc_val i cc y)”;

val _ = stmt "S141" “-1 <= a /\ a <= 1 /\ -1 <= b /\ b <= 1 /\ -1 <= c /\ c <= (1:real) /\ ((s1:int) = 1 \/ s1 = -1) /\ (s2 = 1 \/ s2 = -1) /\ (s3 = 1 \/ s3 = -1) ==> 0 <= 1 + real_of_int s1 * (a * b) + real_of_int s2 * (b * c) + real_of_int s3 * (a * c)”;

val _ = stmt "S142" “0 < D /\ st_wf n st /\ LENGTH (y:real list) = n /\ FST (add_cut0 D n (1096 * 1096) cuts st) ==> FST st /\ st_wf n (add_cut0 D n (1096 * 1096) cuts st) /\ st_val ws (add_cut0 D n (1096 * 1096) cuts st) y = st_val ws st y + &D * cut0_val cuts y”;

val _ = stmt "S143" “(LENGTH (ws:int list) = LENGTH g /\ LENGTH (y:real list) = LENGTH g ==> ldot (lin mL ws g) y = ldot g y - real_of_int mL * ldot ws y) /\ (all_zero l ==> ldot l y = 0)”;

val _ = stmt "S144" “0 < D /\ st_wf n st /\ LENGTH (y:real list) = n /\ FST (add_cut D n (1096 * 1096) zs st) ==> FST st /\ st_wf n (add_cut D n (1096 * 1096) zs st) /\ st_val ws (add_cut D n (1096 * 1096) zs st) y = st_val ws st y + &D * cut_val zs y /\ EVERY (\z. 0 <= FST (SND z) /\ FST (SND z) < &(SND (SND z))) zs”;

val _ = stmt "S145" “0 < D /\ st_wf n st /\ LENGTH (y:real list) = n ==> st_val ws (add_term D n tag i j p q st) y = st_val ws st y + &D * qv p q * mono ws tag i j y”;

val _ = stmt "S146" “0 < D /\ st_wf n st /\ LENGTH (y:real list) = n /\ FST (add_forms D n 1096 lp lq hp hq forms st) ==> FST st /\ st_wf n (add_forms D n 1096 lp lq hp hq forms st) /\ st_val ws (add_forms D n 1096 lp lq hp hq forms st) y = st_val ws st y - &D * forms_val (ldot ws y / 1096) (qv lp lq) (qv hp hq) forms y”;

val _ = stmt "S147" “0 < D /\ st_wf n st /\ LENGTH (y:real list) = n /\ FST (add_cut0 D n (1096 * 1096) cuts st) ==> FST st /\ st_wf n (add_cut0 D n (1096 * 1096) cuts st) /\ st_val ws (add_cut0 D n (1096 * 1096) cuts st) y = st_val ws st y - &D * cut0_val cuts y”;

val _ = stmt "S148" “0 < D /\ st_wf n st /\ LENGTH (y:real list) = n /\ 7 <= kind /\ kind <= 13 /\ FST (add_form D n 1096 lp lq hp hq kind i j k s1 s2 s3 mp mq st) ==> st_wf n (add_form D n 1096 lp lq hp hq kind i j k s1 s2 s3 mp mq st) /\ st_val ws (add_form D n 1096 lp lq hp hq kind i j k s1 s2 s3 mp mq st) y = st_val ws st y - &D * qv mp mq * form_val (ldot ws y / 548) (qv lp lq) (qv hp hq) kind i j k s1 s2 s3 y”;

val _ = stmt "S149" “slab_check ab cuts full grid lp lq hp hq Bp Bq ep eq cp cq theta forms D T2 ds Lw ==> !y. in_box (LENGTH grid - 1) y /\ qv lp lq <= mval grid y /\ mval grid y <= qv hp hq ==> qv cp cq <= Ltheta ab cuts full theta y”;

val _ = stmt "S150" “LENGTH (widths grid) = LENGTH grid”;

val _ = stmt "S151" “0 < D /\ st_wf n st /\ LENGTH (y:real list) = n /\ kind <= 6 /\ FST (add_form D n 1096 lp lq hp hq kind i j k s1 s2 s3 mp mq st) ==> st_wf n (add_form D n 1096 lp lq hp hq kind i j k s1 s2 s3 mp mq st) /\ st_val ws (add_form D n 1096 lp lq hp hq kind i j k s1 s2 s3 mp mq st) y = st_val ws st y - &D * qv mp mq * form_val m lo hi kind i j k s1 s2 s3 y”;

val _ = stmt "S152" “in_box n y /\ lo <= m /\ m <= hi /\ kind <= 13 /\ form_idx_ok n kind i j k ==> 0 <= form_val m lo hi kind i j k s1 s2 s3 y”;

val _ = stmt "S153" “st_wf n (st0 n) /\ FST (st0 n) /\ (LENGTH (y:real list) = n ==> st_val ws (st0 n) y = 1)”;

val _ = stmt "S154" “FST (add_forms D n 1096 lp lq hp hq forms st) /\ in_box n y /\ lo <= m /\ m <= hi ==> 0 <= forms_val m lo hi forms y”;

val _ = stmt "S155" “0 < D /\ st_wf n st /\ LENGTH (y:real list) = n /\ FST (add_zz D n c q a b st) ==> FST st /\ st_wf n (add_zz D n c q a b st) /\ st_val ws (add_zz D n c q a b st) y = st_val ws st y - &D * qv c q * ((1 - 2 * EL a y) * (1 - 2 * EL b y))”;

val _ = stmt "S156" “0 < D /\ st_wf n st /\ LENGTH (y:real list) = n /\ kind <= 7 /\ FST (add_form D n 1096 lp lq hp hq kind i j k s1 s2 s3 mp mq st) ==> st_wf n (add_form D n 1096 lp lq hp hq kind i j k s1 s2 s3 mp mq st) /\ st_val ws (add_form D n 1096 lp lq hp hq kind i j k s1 s2 s3 mp mq st) y = st_val ws st y - &D * qv mp mq * form_val m lo hi kind i j k s1 s2 s3 y”;

val _ = stmt "S157" “FST (add_form D n 1096 lp lq hp hq kind i j k s1 s2 s3 mp mq st) ==> FST st /\ 0 < mp /\ kind <= 14 /\ form_idx_ok n kind i j k /\ (kind = 14 ==> (s1 = 1 \/ s1 = -1) /\ (s2 = 1 \/ s2 = -1) /\ (s3 = 1 \/ s3 = -1) /\ s1 * s2 * s3 = 1)”;

val _ = stmt "S158" “0 < D /\ st_wf n st /\ LENGTH (y:real list) = n /\ FST (add_full D n 1096 full st) ==> FST st /\ st_wf n (add_full D n 1096 full st) /\ st_val ws (add_full D n 1096 full st) y = st_val ws st y + &D * full_val full y”;

val _ = stmt "S159" “EVERY (\r. LENGTH r = n) (Cm:int list list) ==> LENGTH (transp n Cm) = n /\ EVERY (\r. LENGTH r = LENGTH Cm) (transp n Cm) /\ !i j. i < n /\ j < LENGTH Cm ==> EL j (EL i (transp n Cm)) = EL j (EL i Cm)”;

val _ = stmt "S160" “sdd_rows c1 c2 0 M Lw Lw ds ds /\ LENGTH Lw = LENGTH M /\ LENGTH ds = LENGTH M /\ EVERY (\r. LENGTH r = LENGTH M) M /\ (!i j. i < LENGTH M /\ j < LENGTH M ==> EL j (EL i M) = EL i (EL j M)) /\ 0 < c1 /\ 0 <= c2 ==> !v:real list. LENGTH v = LENGTH M ==> 0 <= qform M v v /\ (EXISTS (\x. x <> 0) v ==> 0 < qform M v v)”;

val _ = stmt "S161" “(st_wf n st ==> st_wf n (add_term D n tag i j p q st)) /\ (FST (add_term D n tag i j p q st) ==> FST st /\ D MOD q = 0 /\ i < n /\ j < n /\ tag <= 5)”;

val _ = stmt "S162" “0 < D /\ st_wf n st /\ LENGTH (y:real list) = n /\ FST (add_nn D n nn st) ==> FST st /\ st_wf n (add_nn D n nn st) /\ st_val ws (add_nn D n nn st) y = st_val ws st y - &D * (2 * nn_val nn y) /\ (in_box n y ==> 0 <= nn_val nn y)”;

(* C01: the harness's own control statement (true, trivial); not a lemma *)
val _ = stmt "C01" “(n:num) + 0 = n”;

(* C02: the harness's refutation control (FALSE on purpose, public); not a lemma *)
val _ = stmt "C02" “(n:num) + 1 = n”;
