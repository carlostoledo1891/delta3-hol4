(*
  delta3_inner_sound — the soundness theorem of inner_check, assembled from the proved lemmas.

  NON-BLIND.  Built by the builder agent AFTER the blind benchmark was scored and its key opened
  (hol4/delta3/assembly/, 2026-11-25), exactly as delta3_slab_sound: the lemma proofs are the run's accepted
  scripts (assembly/SOURCES.tsv says which, from whom, and why), each built unchanged except its first line
  (Theory attempt -> Theory acc_<id>).  For each statement of the chain below S049 (L40), in dependency
  order, the accepted theorem  |- S_d1 /\ ... /\ S_dk ==> <rhs of S_def>  is checked to be exactly that goal
  with no hypotheses, its "May use" constants are discharged by MP, and it is folded back into |- S.
  S049 unfolded is the theorem inner_check_sound below: no hypothesis is left.
  The strictness lemma L29 (S046, sdd_rows_pd) rests on L26 (S040, dd_rows_psd).
*)
Theory delta3_inner_sound
Ancestors
  delta3_check delta3_check2 delta3_sem delta3_stmts
  acc_S078 acc_S040 acc_S046 acc_S005 acc_S041 acc_S021 acc_S110 acc_S017 acc_S042 acc_S130 acc_S100 acc_S048 acc_S002 acc_S059 acc_S043 acc_S139 acc_S047 acc_S105 acc_S052 acc_S038 acc_S109 acc_S058 acc_S115 acc_S049

(* (statement, its "May use" list from harness/lemmas.json, the accepted theorem), in dependency order *)
val accepted = [
  ("S078", [],
   acc_S078Theory.S078),
  ("S040", [],
   acc_S040Theory.S040),
  ("S046", ["S040"],
   acc_S046Theory.S046),
  ("S005", [],
   acc_S005Theory.S005),
  ("S041", [],
   acc_S041Theory.S041),
  ("S021", ["S041"],
   acc_S021Theory.S021),
  ("S110", ["S041", "S021"],
   acc_S110Theory.S110),
  ("S017", [],
   acc_S017Theory.S017),
  ("S042", ["S017", "S041", "S021", "S110"],
   acc_S042Theory.S042),
  ("S130", ["S110", "S042"],
   acc_S130Theory.S130),
  ("S100", ["S110", "S042"],
   acc_S100Theory.S100),
  ("S048", ["S110", "S042"],
   acc_S048Theory.S048),
  ("S002", ["S110", "S042"],
   acc_S002Theory.S002),
  ("S059", ["S110", "S042"],
   acc_S059Theory.S059),
  ("S043", ["S110", "S042"],
   acc_S043Theory.S043),
  ("S139", ["S110", "S042"],
   acc_S139Theory.S139),
  ("S047", ["S110", "S042"],
   acc_S047Theory.S047),
  ("S105", ["S005", "S130", "S100", "S048", "S002", "S059", "S043", "S139", "S047"],
   acc_S105Theory.S105),
  ("S052", [],
   acc_S052Theory.S052),
  ("S038", [],
   acc_S038Theory.S038),
  ("S109", ["S052", "S038"],
   acc_S109Theory.S109),
  ("S058", ["S038"],
   acc_S058Theory.S058),
  ("S115", ["S078"],
   acc_S115Theory.S115),
  ("S049", ["S078", "S046", "S105", "S109", "S058", "S115"],
   acc_S049Theory.S049)
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

Theorem inner_check_sound:
  !ab cuts full grid rp rq lam nu kp kq nn cc D T2 ds Lw.
    inner_check ab cuts full grid rp rq lam nu kp kq nn cc D T2 ds Lw ==>
    !y. in_box (LENGTH grid - 1) y /\ mval grid y <= qv rp rq ==>
        0 <= L0 ab cuts full y /\ (L0 ab cuts full y = 0 ==> EVERY (\x. x = 0) y)
Proof
  ACCEPT_TAC (EQ_MP (stmt_def "S049") (lookup "S049" proved))
QED
