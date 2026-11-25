Theory attempt
Ancestors
  arithmetic list integer real intreal delta3_check delta3_check2 delta3_sem delta3_stmts
Libs
  intLib realLib RealField

fun instance def env =
  let val th = EQ_MP def (ASSUME (lhs (concl def)))
      val vs = fst (strip_forall (concl th))
      fun arg v = let val nm = fst (dest_var v) in
        case List.find (fn (k,_) => k = nm) env of
          SOME (_,q) => q | NONE => [QUOTE nm]
        end
  in Q.SPECL (map arg vs) th end;

Theorem shape_bad[local]:
  !st. st_wf n st ==> st_wf n (bad st)
Proof
  PairCases >> simp[st_wf_def,bad_def]
QED

val term_shape = GEN_ALL (CONJUNCT1 (SPEC_ALL (EQ_MP S110_def (ASSUME ``S110``))));

Theorem shape_cells[local]:
  S110 ==> !ab i st. st_wf n st ==> st_wf n (add_cells D n i ab st)
Proof
  disch_tac >> Induct >> simp[add_cells_def] >>
  PairCases >> rw[add_cells_def] >>
  metis_tac[term_shape,shape_bad]
QED

Theorem shape_full[local]:
  S110 ==> !full st. st_wf n st ==> st_wf n (add_full D n u full st)
Proof
  disch_tac >> Induct >> simp[add_full_def] >>
  PairCases >> rw[add_full_def] >>
  metis_tac[term_shape,shape_bad]
QED

Theorem shape_cut[local]:
  S110 ==> !zs st. st_wf n st ==> st_wf n (add_cut D n u zs st)
Proof
  disch_tac >> Induct >> simp[add_cut_def] >>
  PairCases >> rw[add_cut_def] >>
  metis_tac[term_shape,shape_bad]
QED

val seed = instance S005_def [];
val cells = instance S130_def [("i", `0`), ("st", `st0 n`)];
val fullth = instance S100_def [("st", `add_cells D n 0 ab (st0 n)`)];
val cutth = instance S001_def [("zs", `ZIP (cuts,theta)`), ("st", `add_full D n (1096 * 1096) full (add_cells D n 0 ab (st0 n))`)];
val termth = instance S110_def [("tag", `0`), ("i", `0`), ("j", `0`), ("p", `-Bp`), ("q", `Bq`), ("st", `add_cut D n (1096 * 1096) (ZIP (cuts,theta)) (add_full D n (1096 * 1096) full (add_cells D n 0 ab (st0 n)))`)];
val valterm = instance S042_def [("tag", `0`), ("i", `0`), ("j", `0`), ("p", `-Bp`), ("q", `Bq`), ("st", `add_cut D n (1096 * 1096) (ZIP (cuts,theta)) (add_full D n (1096 * 1096) full (add_cells D n 0 ab (st0 n)))`)];
val forms = instance S146_def [("st", `add_term D n 0 0 0 (-Bp) Bq (add_cut D n (1096 * 1096) (ZIP (cuts,theta)) (add_full D n (1096 * 1096) full (add_cells D n 0 ab (st0 n))))`)];
fun inputs th = strip_conj (fst (dest_imp (concl th)));
fun extend rule next prev =
  let val t = List.nth (inputs next,1)
      val r = PART_MATCH (snd o dest_imp) (UNDISCH rule) t
  in MP r prev end;
val w0 = CONJUNCT1 seed;
val w1 = extend shape_cells fullth w0;
val w2 = extend shape_full cutth w1;
val w3 = extend shape_cut valterm w2;
val w4 = MP (CONJUNCT1 termth) w3;
val common = inputs forms;
val positive = ASSUME (hd common);
val leny = ASSUME (List.nth(common,2));
val okend = ASSUME (List.nth(common,3));
fun step th w ok = MP th (LIST_CONJ [positive,w,leny,ok]);
val f5 = step forms w4 okend;
val tinfo = MP (CONJUNCT2 termth) (CONJUNCT1 f5);
val f3 = step cutth w2 (CONJUNCT1 tinfo);
val f2 = step fullth w1 (CONJUNCT1 f3);
val f1 = step cells w0 (CONJUNCT1 f2);
val vt = step valterm w3 (CONJUNCT1 f5);
val vz = MP (last (CONJUNCTS seed)) leny;
val values = [List.nth(CONJUNCTS f5,2),vt,List.nth(CONJUNCTS f3,2),
              List.nth(CONJUNCTS f2,2),List.nth(CONJUNCTS f1,2),vz];

Theorem qv_minus[local]:
  qv (-p) q = -qv p q
Proof
  rewrite_tac[qv_def,real_div,real_of_int_neg,REAL_NEG_LMUL]
QED

Theorem unit_monomial[local]:
  mono ws 0 0 0 y = 1
Proof
  simp[mono_def]
QED

Theorem collect_slab[local]:
  ((((0 + (d:real)*a) + d*f) + d*c) + d*(-b)*1) - d*t =
    d * (a + f + c - b - t)
Proof
  RealField.REAL_ARITH_TAC
QED

val expanded_value = foldl (fn (eq,th) => SUBS [eq] th) (hd values) (tl values);
val simple_value = CONV_RULE (RAND_CONV (PURE_REWRITE_CONV [qv_minus,unit_monomial])) expanded_value;
val final_value = TRANS simple_value (PART_MATCH lhs collect_slab (rhs (concl simple_value)));

Theorem S019_as_constants[local]:
  S110 /\ S042 /\ S005 /\ S130 /\ S100 /\ S001 /\ S146 ==> S019
Proof
  strip_tac >> rewrite_tac[S019_def] >> rpt gen_tac >>
  PURE_REWRITE_TAC[slab_poly_def,GSYM st0_def,Ltheta_def] >>
  disch_then strip_assume_tac >>
  conj_tac >- (ACCEPT_TAC (List.nth(CONJUNCTS f5,1))) >>
  conj_tac >- ACCEPT_TAC (List.nth(CONJUNCTS tinfo,1)) >>
  ACCEPT_TAC final_value
QED

Theorem S019 = CONV_RULE (RAND_CONV (REWR_CONV S019_def)) S019_as_constants
