Theory attempt
Ancestors
  arithmetic list integer real intreal delta3_check delta3_check2 delta3_sem delta3_stmts
Libs
  intLib realLib

open delta3_stmtsTheory delta3_checkTheory delta3_check2Theory delta3_semTheory
open realTheory intrealTheory integerTheory arithmeticTheory listTheory

Theorem bad_facts[local]:
  !st. ~FST (bad st) /\ (st_wf n (bad st) <=> st_wf n st)
Proof
  PairCases >> simp[bad_def,st_wf_def]
QED

val term_guards = SPEC_ALL (EQ_MP S110_def (ASSUME “S110”))
val step_wf = GEN_ALL (CONJUNCT1 term_guards)
val step_ok = GEN_ALL (CONJUNCT2 term_guards)
val step_val = EQ_MP S042_def (ASSUME “S042”)


fun headed name tm =
  case total dest_thy_const (fst (strip_comb tm)) of
    SOME data => #Name data = name
  | NONE => false

fun derive known tm =
  case List.find (fn th => aconv (concl th) tm) known of
    SOME th => th
  | NONE =>
    if is_conj tm then
      let val (a,b) = dest_conj tm in CONJ (derive known a) (derive known b) end
    else if headed "st_wf" tm andalso headed "bad" (rand tm) then
      let val eq = PURE_REWRITE_CONV [bad_facts] tm
      in EQ_MP (SYM eq) (derive known (rhs (concl eq))) end
    else if headed "st_wf" tm andalso headed "add_term" (rand tm) then
      let val rule = PART_MATCH (snd o dest_imp) step_wf tm
      in MP rule (derive known (fst (dest_imp (concl rule)))) end
    else raise Fail ("missing premise " ^ term_to_string tm)

fun carry foldname ih = ASSUM_LIST (fn known =>
  let val ok = valOf (List.find (fn th =>
        headed "FST" (concl th) andalso headed foldname (rand (concl th))) known)
      val updated = rand (rand (concl ok))
      val ih_now = SPEC updated ih
      val tail = CONJUNCTS (MP ih_now (derive known (fst (dest_imp (concl ih_now)))))
      val ok_now = hd tail
  in if headed "bad" updated then
       CONTR_TAC (REWRITE_RULE [bad_facts] ok_now)
     else
       let val eq = List.nth(tail,2)
           val (sv,args) = strip_comb (lhs (concl eq))
           fun terms accepted =
             let val state = rand (concl accepted)
             in if headed "add_term" state then
                  let val prev = CONJUNCTS (MATCH_MP step_ok accepted)
                      val target = list_mk_comb (sv,[hd args,state,List.last args])
                      val rule = PART_MATCH (lhs o snd o dest_imp) step_val target
                      val change = MP rule (derive (accepted::known) (fst (dest_imp (concl rule))))
                  in change :: (prev @ terms (hd prev)) end
                else [] end
           val facts = tail @ terms ok_now
       in map_every assume_tac facts >> PURE_REWRITE_TAC facts end
  end)

fun apply_tail name =
  FIRST [qpat_assum ‘FST (bad _)’ (CONTR_TAC o REWRITE_RULE [bad_facts]),
         qpat_x_assum ‘!st. _’ (carry name)]

Theorem S001_as_constants[local]:
  S110 /\ S042 ==> S001
Proof
  strip_tac >> PURE_REWRITE_TAC[S001_def] >> rpt gen_tac >>
  map_every qid_spec_tac [‘st’,‘zs’] >> INDUCT_THEN list_induction assume_tac
  >- (simp[add_cut_def,cut_val_def] >> metis_tac[]) >>
  rpt gen_tac >> PairCases_on ‘h’ >>
  PURE_REWRITE_TAC[add_cut_def,cut_val_def,LET_THM,EVERY_DEF,pairTheory.FST,pairTheory.SND] >>
  BETA_TAC >> rpt IF_CASES_TAC >> BETA_TAC >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  apply_tail "add_cut" >>
  simp_tac bool_ss [pairTheory.FST,pairTheory.SND,EVERY_DEF] >>
  ‘h6 <> 0’ by (strip_tac >> gvs[]) >>
  ‘(&h6:real) <> 0’ by simp[] >>
  ‘0 <= h5 /\ h5 <= &h6’ by
    (qpat_assum ‘~(_ \/ _)’ mp_tac >> intLib.ARITH_TAC) >>
  asm_rewrite_tac [] >>
  simp_tac (srw_ss()) [qv_def,mono_def] >>
  PURE_REWRITE_TAC [GSYM REAL_OF_NUM_MUL] >>
  qpat_assum ‘(&h6:real) <> 0’ mp_tac >>
  RealField.REAL_FIELD_TAC
QED

Theorem S001 = CONV_RULE (RAND_CONV (REWR_CONV S001_def)) S001_as_constants
