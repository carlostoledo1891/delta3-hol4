(*
  delta3_cover_sound — the soundness theorem of cover_all, assembled from the proved lemmas.

  NON-BLIND.  Built by the builder agent AFTER the blind benchmark was scored and its key opened
  (hol4/delta3/assembly/, 2026-11-25), exactly as delta3_slab_sound: the lemma proofs are the run's accepted
  scripts (assembly/SOURCES.tsv says which, from whom, and why), each built unchanged except its first line
  (Theory attempt -> Theory acc_<id>).  For each statement of the chain below S114 (L42), in dependency
  order, the accepted theorem  |- S_d1 /\ ... /\ S_dk ==> <rhs of S_def>  is checked to be exactly that goal
  with no hypotheses, its "May use" constants are discharged by MP, and it is folded back into |- S.
  S114 unfolded is the theorem cover_all_sound below: no hypothesis is left.
*)
Theory delta3_cover_sound
Ancestors
  delta3_check delta3_check2 delta3_sem delta3_stmts
  acc_S053 acc_S114

(* (statement, its "May use" list from harness/lemmas.json, the accepted theorem), in dependency order *)
val accepted = [
  ("S053", [],
   acc_S053Theory.S053),
  ("S114", ["S053"],
   acc_S114Theory.S114)
];

fun stmt_def s = DB.fetch "delta3_stmts" (s ^ "_def");
fun stmt_const s = prim_mk_const {Thy = "delta3_stmts", Name = s};
fun lookup s proved =
  case List.find (fn (n, _) => n = s) proved of
    SOME (_, th) => th
  | NONE => raise Fail ("assembly: " ^ s ^ " is used before it is proved");

fun discharge ((s, deps, th), proved) =
  let
    val d = stmt_def s                                            (* |- S = rhs *)
    val goal = if null deps then rhs (concl d)
               else mk_imp (list_mk_conj (map stmt_const deps), rhs (concl d))
    val _ = if aconv (concl th) goal andalso null (hyp th) then ()
            else raise Fail ("assembly: the theorem of " ^ s ^ " is not its judged goal")
    val th_rhs = if null deps then th
                 else MP th (LIST_CONJ (map (fn n => lookup n proved) deps))
  in (s, EQ_MP (SYM d) th_rhs) :: proved end;

val proved = List.foldl discharge [] accepted;
val _ = List.app (fn (s, th) => ignore (save_thm (s ^ "_holds", th))) (List.rev proved);

Theorem cover_all_sound:
  !ivs. cover_all ivs ==> !m:real. 0 <= m /\ m <= 1 / 2 ==> in_some m ivs
Proof
  ACCEPT_TAC (EQ_MP (stmt_def "S114") (lookup "S114" proved))
QED
