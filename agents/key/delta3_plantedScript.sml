(* delta3_planted — PRIVATE.  For every planted false statement: its counterexample instance must
   evaluate to F in the kernel; and the TRUE sibling must evaluate to T on the same instance.
   GENERATED (harness/gen-statements.py).  Results are written to planted-results.tsv. *)
Theory delta3_planted[no_sig_docs]
Ancestors
  arithmetic list integer real intreal delta3_check delta3_check2 delta3_sem delta3_stmts
Libs
  intLib realLib

val out = TextIO.openOut "planted-results.tsv";
fun body nm = let val th = DB.fetch "delta3_stmts" (nm ^ "_def") in snd (strip_forall (rhs (concl th))) end;
fun inst_all pairs tm =
  let
    fun look v = List.find (fn (s, _) => s = fst (dest_var v)) pairs
    fun sub tm = let val fvs = free_vars tm in
      subst (List.mapPartial (fn v => case look v of NONE => NONE
               | SOME (_, q) => SOME (v |-> Parse.typedTerm [QUOTE q] (type_of v))) fvs) tm end
    fun pos tm =
      if is_forall tm then
        let val (v, b) = dest_forall tm in
          case look v of NONE => mk_forall (v, pos b)
          | SOME (_, q) => pos (subst [v |-> Parse.typedTerm [QUOTE q] (type_of v)] b) end
      else if is_imp tm andalso not (is_neg tm) then let val (a, b) = dest_imp tm in mk_imp (a, pos b) end
      else if is_conj tm then let val (a, b) = dest_conj tm in mk_conj (pos a, pos b) end
      else tm
  in pos (sub tm) end;
val fallback = SIMP_CONV (srw_ss() ++ ARITH_ss ++ realSimps.REAL_ARITH_ss ++ intSimps.INT_ARITH_ss) [];
fun value tm =
  let val th = EVAL tm val r = rhs (concl th) in
    if aconv r T orelse aconv r F then r
    else (rhs (concl (fallback r)) handle _ => r) end handle _ => tm;
fun check nm truth sibling pairs =
  let
    val v = value (inst_all pairs (body nm))
    val s = value (inst_all pairs (body sibling))
    val ok = aconv v F andalso aconv s T
    val line = String.concatWith "\t" [nm, sibling, if ok then "OK" else "CHECK",
                 "planted=" ^ term_to_string v, "true_sibling=" ^ term_to_string s] ^ "\n"
  in TextIO.output (out, line) end;

val _ = check "S008" false "S095" [("D", "1"), ("n", "1"), ("lp", "0"), ("lq", "1"), ("hp", "1"), ("hq", "1"), ("kind", "5"), ("i", "0"), ("j", "0"), ("k", "0"), ("s1", "1"), ("s2", "1"), ("s3", "1"), ("mp", "0"), ("mq", "1"), ("st", "st0 1")];
val _ = check "S015" false "S049" [("ab", "[(0,1,1,1)]"), ("cuts", "[]"), ("full", "[]"), ("grid", "[0;1096]"), ("rp", "1"), ("rq", "1"), ("lam", "[]"), ("nu", "[(0,1)]"), ("kp", "0"), ("kq", "1"), ("nn", "[]"), ("cc", "[(0,1)]"), ("D", "1096 * 1096"), ("T2", "0"), ("ds", "[1]"), ("Lw", "[[]]"), ("y", "[0]")];
val _ = check "S020" false "S059" [("D", "1096"), ("n", "1"), ("rp", "1"), ("rq", "1"), ("j", "0"), ("nu", "[(1,1)]"), ("st", "st0 1"), ("y", "[1]"), ("ws", "[0]"), ("m", "2"), ("rin", "1")];
val _ = check "S024" false "S108" [("cp", "0"), ("Bq", "1"), ("eq", "1"), ("Bp", "-1"), ("ep", "0"), ("n", "0"), ("cq", "0")];
val _ = check "S025" false "S123" [("n", "1"), ("y", "[1]")];
val _ = check "S034" false "S040" [("c1", "0"), ("c2", "0"), ("M", "[[-1]]"), ("Lw", "[[]]"), ("ds", "[1]"), ("v", "[1]")];
val _ = check "S035" false "S043" [("D", "1096 * 1096"), ("n", "1"), ("rp", "1"), ("rq", "1"), ("kp", "0"), ("kq", "1"), ("st", "st0 1"), ("y", "[0]"), ("ws", "[0]")];
val _ = check "S036" false "S105" [("D", "1096 * 1096"), ("n", "1"), ("ab", "[]"), ("cuts", "[]"), ("full", "[]"), ("rp", "1"), ("rq", "1"), ("lam", "[]"), ("nu", "[]"), ("kp", "0"), ("kq", "1"), ("nn", "[]"), ("cc", "[(1,1)]"), ("y", "[1]"), ("ws", "[0]"), ("m", "0"), ("rin", "1")];
val _ = check "S044" false "S084" [("D", "1096"), ("n", "1"), ("lp", "0"), ("lq", "1"), ("hp", "1"), ("hq", "1"), ("kind", "7"), ("i", "0"), ("j", "0"), ("k", "0"), ("s1", "1"), ("s2", "1"), ("s3", "1"), ("mp", "1"), ("mq", "1"), ("st", "st0 1"), ("y", "[0]"), ("ws", "[0]"), ("m", "5"), ("lo", "0"), ("hi", "1")];
val _ = check "S060" false "S115" [("grid", "[1096;0]"), ("y", "[1]")];
val _ = check "S061" false "S041" [("n", "0"), ("v", "1"), ("l", "[0]"), ("y", "[1]")];
val _ = check "S062" false "S152" [("n", "0"), ("y", "[]"), ("m", "0"), ("lo", "1"), ("hi", "2"), ("kind", "7"), ("i", "0"), ("j", "0"), ("k", "0"), ("s1", "1"), ("s2", "1"), ("s3", "1")];
val _ = check "S064" false "S089" [("D", "1"), ("n", "3"), ("lp", "0"), ("lq", "1"), ("hp", "1"), ("hq", "1"), ("kind", "14"), ("i", "0"), ("j", "1"), ("k", "2"), ("s1", "1"), ("s2", "-1"), ("s3", "-1"), ("mp", "1"), ("mq", "1"), ("st", "st0 3"), ("y", "[0;0;1]"), ("ws", "[0;0;0]"), ("m", "0"), ("lo", "0"), ("hi", "1")];
val _ = check "S065" false "S058" [("ws", "[1]"), ("g", "[0]"), ("mL", "1"), ("y", "[1]"), ("l", "[]")];
val _ = check "S066" false "S048" [("D", "1096 * 1096"), ("n", "1"), ("cuts", "[(0,0,-1,1,0)]"), ("st", "st0 1"), ("y", "[1]"), ("ws", "[0]")];
val _ = check "S068" false "S154" [("D", "1"), ("n", "1"), ("lp", "0"), ("lq", "1"), ("hp", "1"), ("hq", "1"), ("forms", "[(5,0,0,0,1,1,1,1,1)]"), ("st", "st0 1"), ("y", "[-1]"), ("m", "0"), ("lo", "0"), ("hi", "0")];
val _ = check "S082" false "S117" [("D", "1"), ("n", "1"), ("c", "1"), ("q", "1"), ("a", "0"), ("b", "0"), ("st", "st0 1"), ("y", "[0]"), ("ws", "[0]")];
val _ = check "S083" false "S110" [("D", "1"), ("n", "1"), ("tag", "5"), ("i", "0"), ("j", "0"), ("p", "0"), ("q", "1"), ("st", "st0 1")];
val _ = check "S085" false "S130" [("D", "1"), ("n", "2"), ("i", "0"), ("ab", "[(1,1,0,1)]"), ("st", "st0 2"), ("y", "[1;0]"), ("ws", "[0;0]")];
val _ = check "S086" false "S054" [("a", "1"), ("b", "1"), ("c", "-1"), ("s1", "1"), ("s2", "1"), ("s3", "1")];
val _ = check "S087" false "S149" [("ab", "[(10,1,0,1)]"), ("cuts", "[]"), ("full", "[]"), ("grid", "[0;1096]"), ("lp", "1"), ("lq", "2"), ("hp", "1"), ("hq", "1"), ("Bp", "4"), ("Bq", "1"), ("ep", "0"), ("eq", "1"), ("cp", "4"), ("cq", "1"), ("theta", "[]"), ("forms", "[(7,0,0,0,1,1,1,10,1)]"), ("D", "1096"), ("T2", "0"), ("ds", "[1;1]"), ("Lw", "[[];[]]"), ("y", "[0]")];
val _ = check "S088" false "S038" [("ws", "[1]"), ("g", "[1]"), ("c", "2"), ("i", "0")];
val _ = check "S091" false "S146" [("D", "1"), ("n", "1"), ("lp", "0"), ("lq", "1"), ("hp", "1"), ("hq", "1"), ("forms", "[(5,0,0,0,1,1,1,1,1)]"), ("st", "st0 1"), ("y", "[1]"), ("ws", "[0]")];
val _ = check "S096" false "S002" [("D", "1"), ("n", "1"), ("lam", "[(0,0,1,1)]"), ("st", "st0 1"), ("y", "[2]"), ("ws", "[0]")];
val _ = check "S099" false "S114" [("ivs", "[(0,1,1,2)]"), ("m", "1")];
val _ = check "S102" false "S053" [("ap", "1"), ("aq", "2"), ("ivs", "[]"), ("m", "1 / 2")];
val _ = check "S103" false "S109" [("n", "1"), ("ok", "T"), ("k", "0"), ("g", "[0]"), ("Cm", "[[1]]"), ("mL", "0"), ("mY", "[0]"), ("mM", "0"), ("ws", "[0]"), ("y", "[1]")];
val _ = check "S106" false "S098" [("D", "1096"), ("n", "1"), ("lp", "0"), ("lq", "1"), ("hp", "1"), ("hq", "1"), ("kind", "7"), ("i", "0"), ("j", "0"), ("k", "0"), ("s1", "1"), ("s2", "1"), ("s3", "1"), ("mp", "1"), ("mq", "1"), ("st", "st0 1"), ("y", "[1]"), ("ws", "[1096]")];
val _ = check "S113" false "S046" [("c1", "1"), ("c2", "0"), ("M", "[[0]]"), ("Lw", "[[]]"), ("ds", "[1]"), ("v", "[1]")];
val _ = check "S122" false "S021" [("i", "0"), ("j", "1"), ("v", "1"), ("Cm", "[[0;0];[0;0]]"), ("n", "2"), ("u", "[1;0]"), ("y", "[0;1]")];
val _ = check "S125" false "S027" [("n", "0"), ("st", "st0 0"), ("ws", "[]"), ("D", "1"), ("ep", "0"), ("eq", "1")];
val _ = check "S131" false "S017" [("D", "1"), ("q", "2"), ("p", "1")];
val _ = check "S133" false "S019" [("D", "1"), ("n", "1"), ("ab", "[]"), ("cuts", "[]"), ("full", "[]"), ("Bp", "1"), ("Bq", "1"), ("lp", "0"), ("lq", "1"), ("hp", "1"), ("hq", "1"), ("theta", "[]"), ("forms", "[]"), ("y", "[0]"), ("ws", "[0]")];
val _ = check "S136" false "S057" [("n", "0"), ("st", "st0 0"), ("ws", "[]"), ("y", "[]"), ("D", "1"), ("ep", "1"), ("eq", "1")];
val _ = check "S137" false "S042" [("D", "1"), ("n", "1"), ("tag", "0"), ("i", "0"), ("j", "0"), ("p", "1"), ("q", "2"), ("st", "st0 1"), ("y", "[0]"), ("ws", "[0]")];
val _ = check "S140" false "S047" [("D", "1"), ("n", "2"), ("i", "0"), ("cc", "[(1,1)]"), ("st", "st0 2"), ("y", "[1;0]"), ("ws", "[0;0]")];
val _ = check "S141" false "S054" [("a", "1"), ("b", "1"), ("c", "1"), ("s1", "-1"), ("s2", "-1"), ("s3", "-1")];
val _ = check "S144" false "S001" [("D", "4 * (1096 * 1096)"), ("n", "1"), ("zs", "[((0,0,1,1,0),(1,1))]"), ("st", "st0 1"), ("y", "[0]"), ("ws", "[0]")];
val _ = check "S150" false "S078" [("grid", "[0]")];
val _ = check "S153" false "S005" [("n", "0"), ("y", "[]"), ("ws", "[]")];
val _ = check "S158" false "S100" [("D", "1096 * 1096"), ("n", "1"), ("full", "[(0,0,1)]"), ("st", "st0 1"), ("y", "[1]"), ("ws", "[0]")];
val _ = check "S159" false "S052" [("n", "2"), ("Cm", "[[1;2];[3;4]]"), ("i", "0"), ("j", "1")];
val _ = check "S162" false "S139" [("D", "1"), ("n", "1"), ("nn", "[(0,0,1,1)]"), ("st", "st0 1"), ("y", "[1]"), ("ws", "[0]")];
val _ = TextIO.closeOut out;
