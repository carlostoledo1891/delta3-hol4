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

Theorem qv_nonneg[local]:
  !p q. 0 <= p ==> 0 <= qv p q
Proof
  rpt strip_tac >> rewrite_tac[qv_def] >> match_mp_tac REAL_LE_DIV >>
  conj_tac
  >- (qpat_assum ‘0 <= p’ (fn th =>
        let val lifted = PURE_REWRITE_RULE [GSYM real_of_int_le] th
        in FIRST_PROVE [
             ACCEPT_TAC (PURE_REWRITE_RULE [real_of_int_num] lifted),
             mp_tac lifted >> simp_tac bool_ss [real_of_int_num,REAL_0]]
        end)) >>
  simp[]
QED

Theorem lam_head_nonneg[local]:
  !n y i j p q. in_box n y /\ i < n /\ j < n /\ ~(p < 0) ==>
    0 <= qv p q * (EL i y * (1 - EL j y))
Proof
  rpt strip_tac >>
  ‘0 <= EL i y /\ EL j y <= 1’ by
    (qpat_assum ‘in_box n y’ mp_tac >>
     PURE_REWRITE_TAC[in_box_def,EVERY_EL] >> metis_tac[]) >>
  match_mp_tac REAL_LE_MUL >> conj_tac
  >- (match_mp_tac qv_nonneg >> metis_tac[INT_NOT_LT]) >>
  match_mp_tac REAL_LE_MUL >> asm_rewrite_tac[REAL_SUB_LE]
QED

Theorem S002_as_constants[local]:
  S110 /\ S042 ==> S002
Proof
  strip_tac >> PURE_REWRITE_TAC[S002_def] >> rpt gen_tac >>
  map_every qid_spec_tac [‘st’,‘lam’] >> INDUCT_THEN list_induction assume_tac
  >- (simp[add_lam_def,lam_val_def] >> metis_tac[]) >>
  rpt gen_tac >> PairCases_on ‘h’ >>
  PURE_REWRITE_TAC[add_lam_def,lam_val_def,LET_THM,EVERY_DEF,pairTheory.FST,pairTheory.SND] >>
  BETA_TAC >> rpt IF_CASES_TAC >> BETA_TAC >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  apply_tail "add_lam" >>
  simp_tac bool_ss [pairTheory.FST,pairTheory.SND,EVERY_DEF] >>
  rpt conj_tac >> FIRST_PROVE [
    simp_tac (srw_ss()) [qv_def,mono_def] >> PURE_REWRITE_TAC [real_div] >> RealField.REAL_FIELD_TAC,
    strip_tac >> match_mp_tac REAL_LE_ADD >> conj_tac >- metis_tac[lam_head_nonneg] >>
      metis_tac[],
    fs[]]
QED

Theorem S002 = CONV_RULE (RAND_CONV (REWR_CONV S002_def)) S002_as_constants
