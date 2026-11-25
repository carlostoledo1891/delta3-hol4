Theory attempt
Ancestors
  arithmetic list integer real intreal delta3_check delta3_check2 delta3_sem delta3_stmts
Libs
  intLib realLib

fun named_spec binds th =
  let
    fun get v = case List.find (fn (s,_) => s = fst (dest_var v)) binds of
          SOME (_,x) => x | NONE => raise Fail (fst (dest_var v))
  in SPECL (map get (fst (strip_forall (concl th)))) th end

Theorem zz_ok[local]:
  !D n c q a b st. FST (add_zz D n c q a b st) ==> FST st
Proof
  rpt gen_tac >> PairCases_on `st` >> simp [add_zz_def, add_term_def]
QED

fun step_facts guard_def sound_def (asl,g) =
  let
    fun body def = EQ_MP def (ASSUME (lhs (concl def)))
    val guard = body guard_def and sound = body sound_def
    val zz = body S117_def
    fun head t = total (fst o dest_const o fst o strip_comb) t
    fun is_update t = head t = SOME "add_term" orelse head t = SOME "add_zz"
    val ok = ASSUME (valOf (List.find (fn t => head t = SOME "FST" andalso is_update (rand t)) asl))
    val stv = find_term (fn t => head t = SOME "st_val" andalso length (snd (strip_comb t)) = 3) g
    val [ws,_,ys] = snd (strip_comb stv)
    val names = ["D","n","tag","i","j","p","q","st"]
    fun descend ok =
      let val t = rand (concl ok) in
        if not (is_update t) then
          (ok, ASSUME (valOf (List.find (fn h => head h = SOME "st_wf" andalso aconv (rand h) t) asl)), [])
        else let
          val args = snd (strip_comb t)
          val iszz = head t = SOME "add_zz"
          val keys = if iszz then ["D","n","c","q","a","b","st"] else names
          val binds = ListPair.zip (keys,args)
          val next_ok = if iszz then MATCH_MP zz_ok ok else
                   CONJUNCT1 (MATCH_MP (CONJUNCT2 (named_spec binds guard)) ok)
          val (baseok,prevwf,eqs) = descend next_ok
          
          val rule = named_spec (("ws",ws)::("y",ys)::binds) (if iszz then zz else sound)
          val (hyps,_) = dest_imp (concl rule)
          fun fact h = if aconv h (concl prevwf) then prevwf
                       else if aconv h (concl ok) then ok
                       else if List.exists (aconv h) asl then ASSUME h
                       else TAC_PROOF ((asl,h), simp [] >> decide_tac)
          val result = MP rule (LIST_CONJ (map fact (strip_conj hyps)))
          val (wf,eqn) = if iszz then CONJ_PAIR (CONJUNCT2 result)
               else (MATCH_MP (CONJUNCT1 (named_spec binds guard)) prevwf,result)
        in (baseok,wf,eqn::eqs) end
      end
    val (baseok,wf,eqs) = descend ok
  in (rewrite_tac (baseok::wf::eqs)) (asl,g) end
Theorem fst_bad[local]:
  !st. ~FST (bad st)
Proof
  gen_tac >> PairCases_on `st` >> simp [bad_def]
QED

Theorem S089_as_constants[local]:
  S110 /\ S042 /\ S117 ==> S089
Proof
  strip_tac >> rewrite_tac [S089_def] >> rpt gen_tac >>
  Cases_on `kind = 14` >| [
    pop_assum SUBST_ALL_TAC,
    asm_rewrite_tac []
  ] >>
  Cases_on `mp < 0` >> asm_simp_tac (srw_ss()) [add_form_def, fst_bad, form_val_def] >>
  IF_CASES_TAC >> asm_rewrite_tac [fst_bad] >> strip_tac >>
  step_facts S110_def S042_def >>
  simp [mono_def, qv_def, realTheory.real_div] >>
  W (fn (_,g) => ACCEPT_TAC (RealField.REAL_RING g))
QED

Theorem S089 = CONV_RULE (RAND_CONV (REWR_CONV S089_def)) S089_as_constants
