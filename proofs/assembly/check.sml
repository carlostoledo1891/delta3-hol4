(* proofs/assembly/check.sml — read back what the assembly saved, in a fresh HOL process (like the judge does):
   each soundness theorem against its statement's text, hypotheses, tags; every axiom in the ancestry;
   the five certificate theorems, the cover, and the Layer-1 conjunction with their tags.
   Run by replay.sh from _replay/kernel:  hol < check.sml   (writes ../check.out) *)
loadPath := "../base/.hol/objs" :: "../base" :: "../proofs/.hol/objs" :: "../proofs" :: ".hol/objs" :: !loadPath;
load "delta3_layer1Theory";
val out = TextIO.openOut "../check.out";
fun say s = (TextIO.output (out, s ^ "\n"); TextIO.flushOut out);
fun tags th = let val (o1, a1) = Tag.dest_tag (Thm.tag th) in
  "oracles [" ^ String.concatWith "," o1 ^ "] axioms [" ^ String.concatWith "," a1 ^ "] hyps " ^
  Int.toString (length (hyp th)) end;
val _ = set_trace "Unicode" 0;
fun sound (thy, nm, s) =
  let val th = DB.fetch thy nm
      val txt = rhs (concl (DB.fetch "delta3_stmts" (s ^ "_def")))
  in say ("SOUND " ^ nm ^ " EXACT_" ^ s ^ " " ^ Bool.toString (aconv (concl th) txt) ^ " " ^ tags th);
     say (thm_to_string th) end;
val _ = List.app sound [("delta3_slab_sound", "slab_check_sound", "S149"),
                        ("delta3_inner_sound", "inner_check_sound", "S049"),
                        ("delta3_cover_sound", "cover_all_sound", "S114")];
val _ = List.app (fn thy =>
          List.app (fn (n, t) => say ("HOLDS " ^ thy ^ " " ^ n ^ " " ^ tags t))
            (List.filter (fn (n, _) => String.isSuffix "_holds" n) (DB.thms thy)))
          ["delta3_slab_sound", "delta3_inner_sound", "delta3_cover_sound"];
val anc = "delta3_layer1" :: ancestry "delta3_layer1";
val _ = List.app (fn thy => case DB.axioms thy of [] => ()
                     | axs => say ("AXIOMS_IN " ^ thy ^ " " ^ String.concatWith "," (map #1 axs))) anc;
val _ = say ("ANCESTRY_SIZE " ^ Int.toString (length anc));
val _ = List.app (fn (thy, x) =>
          let val t = DB.fetch thy x in say ("THM " ^ x ^ " " ^ tags t); say (thm_to_string t) end)
          [("delta3_slab_bounds", "slabA_bound_n"), ("delta3_slab_bounds", "slabB_bound_n"),
           ("delta3_slab_bounds", "slabC_bound_n"), ("delta3_slab_bounds", "slabD_bound_n"),
           ("delta3_layer1", "inner_bound_n"), ("delta3_layer1", "cover_bound_regions"),
           ("delta3_layer1", "delta3_layer1")];
val _ = List.app (fn (thy, x) =>
          let val t = DB.fetch thy x in
            say ("CHECK " ^ x ^ " " ^ tags t ^ " rhs " ^ term_to_string (rhs (concl t))) end)
          [("delta3_slabA", "slabA_check"), ("delta3_slabB", "slabB_check"), ("delta3_slabC", "slabC_check"),
           ("delta3_slabD", "slabD_check"), ("delta3_inner", "inner_check"), ("delta3_cover", "cover_check")];
val _ = TextIO.closeOut out;
