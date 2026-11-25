(*
  delta3_slab_sound — the soundness theorem of slab_check, assembled from the proved lemmas.

  NON-BLIND.  Built by the builder agent AFTER the blind benchmark was scored and its key opened
  (hol4/delta3/assembly/, 2026-11-25).  The lemma proofs are the run's accepted scripts (all but one blind;
  assembly/SOURCES.tsv says which, from whom, and why), each built here unchanged except for its first
  line (Theory attempt -> Theory acc_<id>); L28 (S149) is the builder's (claude-b9's script with one fix).

  What this file does, and nothing else: for each true slab statement of the chain (L01-L28 of
  key-revealed/LEMMAS.md), in dependency order, it takes the accepted theorem
        |- S_d1 /\ ... /\ S_dk ==> <rhs of S_def>          (the judge's goal; |- <rhs> when k = 0)
  checks that its conclusion is exactly that goal with no hypotheses, discharges the S_di (each already
  turned into |- S_di here) by MP, and folds the result back into |- S (EQ_MP with S_def).  The last one,
  S149 (L28), unfolded, is the theorem slab_check_sound below: no hypothesis is left.
*)
Theory delta3_slab_sound
Ancestors
  delta3_check delta3_sem delta3_stmts
  acc_S017 acc_S041 acc_S021 acc_S110 acc_S042 acc_S005 acc_S130 acc_S100 acc_S001 acc_S117 acc_S095 acc_S084 acc_S098 acc_S089 acc_S146 acc_S152 acc_S054 acc_S154 acc_S019 acc_S052 acc_S038 acc_S027 acc_S057 acc_S123 acc_S078 acc_S040 acc_S108 acc_S149

(* (statement, its "May use" list from harness/lemmas.json, the accepted theorem), in dependency order *)
val accepted = [
  ("S017", [],
   acc_S017Theory.S017),
  ("S041", [],
   acc_S041Theory.S041),
  ("S021", ["S041"],
   acc_S021Theory.S021),
  ("S110", ["S041", "S021"],
   acc_S110Theory.S110),
  ("S042", ["S017", "S041", "S021", "S110"],
   acc_S042Theory.S042),
  ("S005", [],
   acc_S005Theory.S005),
  ("S130", ["S110", "S042"],
   acc_S130Theory.S130),
  ("S100", ["S110", "S042"],
   acc_S100Theory.S100),
  ("S001", ["S110", "S042"],
   acc_S001Theory.S001),
  ("S117", ["S110", "S042"],
   acc_S117Theory.S117),
  ("S095", ["S110"],
   acc_S095Theory.S095),
  ("S084", ["S110", "S042"],
   acc_S084Theory.S084),
  ("S098", ["S110", "S042"],
   acc_S098Theory.S098),
  ("S089", ["S110", "S042", "S117"],
   acc_S089Theory.S089),
  ("S146", ["S095", "S084", "S098", "S089"],
   acc_S146Theory.S146),
  ("S152", [],
   acc_S152Theory.S152),
  ("S054", [],
   acc_S054Theory.S054),
  ("S154", ["S095", "S152", "S054"],
   acc_S154Theory.S154),
  ("S019", ["S110", "S042", "S005", "S130", "S100", "S001", "S146"],
   acc_S019Theory.S019),
  ("S052", [],
   acc_S052Theory.S052),
  ("S038", [],
   acc_S038Theory.S038),
  ("S027", ["S052", "S038"],
   acc_S027Theory.S027),
  ("S057", ["S052", "S038"],
   acc_S057Theory.S057),
  ("S123", [],
   acc_S123Theory.S123),
  ("S078", [],
   acc_S078Theory.S078),
  ("S040", [],
   acc_S040Theory.S040),
  ("S108", [],
   acc_S108Theory.S108),
  ("S149", ["S017", "S154", "S019", "S027", "S057", "S123", "S078", "S040", "S108"],
   acc_S149Theory.S149)
];

fun stmt_def s = DB.fetch "delta3_stmts" (s ^ "_def");
fun stmt_const s = prim_mk_const {Thy = "delta3_stmts", Name = s};
fun lookup s proved =
  case List.find (fn (n, _) => n = s) proved of
    SOME (_, th) => th
  | NONE => raise Fail ("delta3_slab_sound: " ^ s ^ " is used before it is proved");

fun discharge ((s, deps, th), proved) =
  let
    val d = stmt_def s                                            (* |- S = rhs *)
    val goal = if null deps then rhs (concl d)
               else mk_imp (list_mk_conj (map stmt_const deps), rhs (concl d))
    val _ = if aconv (concl th) goal andalso null (hyp th) then ()
            else raise Fail ("delta3_slab_sound: the theorem of " ^ s ^ " is not its judged goal")
    val th_rhs = if null deps then th
                 else MP th (LIST_CONJ (map (fn n => lookup n proved) deps))
  in (s, EQ_MP (SYM d) th_rhs) :: proved end;

val proved = List.foldl discharge [] accepted;

(* |- S for every statement of the chain, saved for the record *)
val _ = List.app (fn (s, th) => ignore (save_thm (s ^ "_holds", th))) (List.rev proved);

(* L28, the top of the slab chain, unfolded: an accepting slab_check bounds L_theta below by the claim
   on the whole region (the box [0,1]^n, with lo <= m <= hi). *)
Theorem slab_check_sound:
  !ab cuts full grid lp lq hp hq Bp Bq ep eq cp cq theta forms D T2 ds Lw.
    slab_check ab cuts full grid lp lq hp hq Bp Bq ep eq cp cq theta forms D T2 ds Lw ==>
    !y. in_box (LENGTH grid - 1) y /\ qv lp lq <= mval grid y /\ mval grid y <= qv hp hq ==>
        qv cp cq <= Ltheta ab cuts full theta y
Proof
  ACCEPT_TAC (EQ_MP (stmt_def "S149") (lookup "S149" proved))
QED
