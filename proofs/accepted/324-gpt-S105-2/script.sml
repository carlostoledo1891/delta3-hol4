Theory attempt
Ancestors
  arithmetic list integer real intreal delta3_check delta3_check2 delta3_sem delta3_stmts
Libs
  intLib realLib

Theorem bad_flag[local]:
  !st. FST (bad st) = F
Proof
  gen_tac >> PairCases_on `st` >> simp [bad_def]
QED

Theorem term_back[local]:
  !D n tag i j p q st. FST (add_term D n tag i j p q st) ==> FST st
Proof
  rpt gen_tac >> PairCases_on `st` >> rw [add_term_def]
QED
Theorem add_cells_back[local]:
  !xs i st. FST (add_cells D n i xs st) ==> FST st
Proof
  Induct >- simp [add_cells_def] >> rpt gen_tac >> PairCases_on `h` >>
  rewrite_tac [add_cells_def] >> rpt IF_CASES_TAC >>
  metis_tac [term_back,bad_flag]
QED

Theorem add_full_back[local]:
  !xs st. FST (add_full D n u xs st) ==> FST st
Proof
  Induct >- simp [add_full_def] >> rpt gen_tac >> PairCases_on `h` >>
  rewrite_tac [add_full_def] >> rpt IF_CASES_TAC >>
  metis_tac [term_back,bad_flag]
QED

Theorem add_cut0_back[local]:
  !xs st. FST (add_cut0 D n u xs st) ==> FST st
Proof
  Induct >- simp [add_cut0_def] >> rpt gen_tac >> PairCases_on `h` >>
  rewrite_tac [add_cut0_def] >> rpt IF_CASES_TAC >>
  metis_tac [term_back,bad_flag]
QED

Theorem add_lam_back[local]:
  !xs st. FST (add_lam D n xs st) ==> FST st
Proof
  Induct >- simp [add_lam_def] >> rpt gen_tac >> PairCases_on `h` >>
  rewrite_tac [add_lam_def] >> rpt IF_CASES_TAC >>
  metis_tac [term_back,bad_flag]
QED

Theorem add_nu_back[local]:
  !xs j st. FST (add_nu D n u rp rq j xs st) ==> FST st
Proof
  Induct >- simp [add_nu_def] >> rpt gen_tac >> PairCases_on `h` >>
  rewrite_tac [add_nu_def] >> rpt IF_CASES_TAC >>
  metis_tac [term_back,bad_flag]
QED

Theorem add_nn_back[local]:
  !xs st. FST (add_nn D n xs st) ==> FST st
Proof
  Induct >- simp [add_nn_def] >> rpt gen_tac >> PairCases_on `h` >>
  rewrite_tac [add_nn_def] >> rpt IF_CASES_TAC >>
  metis_tac [term_back,bad_flag]
QED

Theorem add_cc_back[local]:
  !xs i st. FST (add_cc D n i xs st) ==> FST st
Proof
  Induct >- simp [add_cc_def] >> rpt gen_tac >> PairCases_on `h` >>
  rewrite_tac [add_cc_def] >> rpt IF_CASES_TAC >>
  metis_tac [term_back,bad_flag]
QED

Theorem kap_back[local]:
  !D n u rp rq kp kq st. FST (add_kap D n u rp rq kp kq st) ==> FST st
Proof
  rpt gen_tac >> rewrite_tac [add_kap_def] >> IF_CASES_TAC >>
  metis_tac [bad_flag,term_back]
QED

Theorem qv_nonneg[local]:
  !p q. 0 <= p ==> 0 <= qv p q
Proof
  rpt gen_tac >> disch_then (mp_tac o REWRITE_RULE [GSYM real_of_int_le]) >>
  rewrite_tac [real_of_int_num,qv_def] >> strip_tac >>
  irule REAL_LE_DIV >> simp []
QED

fun prop d = UNDISCH (fst (EQ_IMP_RULE d))
val build_stages =
  [("add_cc",S047_def,add_cc_back),("add_nn",S139_def,add_nn_back),
   ("add_kap",S043_def,kap_back),("add_nu",S059_def,add_nu_back),
   ("add_lam",S002_def,add_lam_back),("add_cut0",S048_def,add_cut0_back),
   ("add_full",S100_def,add_full_back),("add_cells",S130_def,add_cells_back)]
fun propagate pos len ok =
  let val state = rand (concl ok)
      val name = fst (dest_const (fst (strip_comb state)))
      val _ = print ("deriving " ^ name ^ "\n")
  in
    if name = "st0" then
      let val seed = PART_MATCH (rand o hd o strip_conj) (prop S005_def) state
          val [wf,flag,zero] = CONJUNCTS seed
      in (wf,[wf,flag,MP zero len]) end
    else
      let val (_,d,back) = valOf (List.find (fn (s,_,_) => name=s) build_stages)
          val (priorwf,facts) = propagate pos len (MATCH_MP back ok)
          val rule = PART_MATCH (List.last o strip_conj o fst o dest_imp) (prop d) (concl ok)
          val req = LIST_CONJ [pos,priorwf,len,ok]
          val _ = if aconv (concl req) (fst (dest_imp (concl rule))) then ()
                  else print ("premise mismatch " ^ name ^ "\nexpected " ^
                    term_to_string (fst (dest_imp (concl rule))) ^ "\nsupplied " ^
                    term_to_string (concl req) ^ "\n")
          val out = CONJUNCTS (MP rule req)
          fun iswf t = fst (dest_const (fst (strip_comb (concl t)))) = "st_wf"
          val wf = valOf (List.find iswf out)
      in (wf,out @ facts) end
  end
fun chain_tac pos len ok =
  let val (wf,facts) = propagate pos len ok
  in MAP_EVERY ASSUME_TAC facts end
fun trace_goal label (g as (asl,w)) =
  (print (label ^ "\n" ^ String.concatWith "\n" (map term_to_string (rev asl)) ^
          "\n|- " ^ term_to_string w ^ "\n"); ALL_TAC g)
Theorem S105_as_constants[local]:
  S005 /\ S130 /\ S100 /\ S048 /\ S002 /\ S059 /\ S043 /\ S139 /\ S047 ==> S105
Proof
  strip_tac >> rewrite_tac [S105_def,inner_poly_def,GSYM st0_def] >>
  rpt gen_tac >> strip_tac >>
  qpat_assum `0 < D` (fn pos =>
    qpat_assum `LENGTH y = n` (fn len =>
      qpat_assum `FST (add_cc _ _ _ _ _)` (chain_tac pos len))) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac
  >- (asm_rewrite_tac [L0_def,mults_val_def] >> trace_goal "identity" >>
      CONV_TAC (BINOP_CONV RealField.REAL_POLY_CONV) >> REFL_TAC) >>
  strip_tac >>
  `0 <= rin - m` by (qpat_x_assum `m <= rin` mp_tac >> realLib.REAL_ARITH_TAC) >>
  `0 <= qv kp kq * (m * (rin - m))` by
    (irule REAL_LE_MUL >> conj_tac >- metis_tac [qv_nonneg] >>
     irule REAL_LE_MUL >> asm_rewrite_tac []) >>
  rewrite_tac [mults_val_def] >>
  rpt (irule REAL_LE_ADD >> conj_tac) >> asm_simp_tac bool_ss [] >>
  trace_goal "nonnegativity" >> metis_tac []
QED

Theorem S105 = CONV_RULE (RAND_CONV (REWR_CONV S105_def)) S105_as_constants
