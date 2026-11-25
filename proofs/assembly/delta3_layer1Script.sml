(*
  delta3_layer1 — the five δ₃ certificates and the cover through the three soundness theorems.
  NON-BLIND assembly (hol4/delta3/assembly/, 2026-11-25).

  inputs, each a kernel theorem by cv_eval (Day 1 / Day 2 / CakeML-agent theory scripts, unchanged,
  rebuilt here against the same base as the proofs):
     delta3_slab{A,B,C,D}  |- slab_check <data> <=> T        (via delta3_slab_bounds)
     delta3_inner          |- inner_check <data> <=> T
     delta3_cover          |- cover_all <the five regions> <=> T
  and the soundness theorems slab_check_sound, inner_check_sound, cover_all_sound (theories/).
  MP of each pair gives a statement about L_theta / L0 on each region; delta3_layer1 is their conjunction
  with the cover written out.  The model constants (ab, cut, full) are data here, not derived.
*)
Theory delta3_layer1[no_sig_docs]
Ancestors
  delta3_sem delta3_slab_bounds delta3_inner_sound delta3_cover_sound delta3_inner delta3_cover

fun with_n grid_def th =
  let val grid = lhs (concl grid_def)
      val len = (REWRITE_CONV [grid_def] THENC EVAL)
                  (numSyntax.mk_minus (listSyntax.mk_length grid, numSyntax.term_of_int 1))
  in PURE_REWRITE_RULE [len] th end;

fun bound_inner check_th =
  let val args = snd (strip_comb (lhs (concl check_th)))      (* the sixteen arguments of inner_check *)
  in MP (SPECL args inner_check_sound) (EQT_ELIM check_th) end;

fun bound_cover check_th =
  MP (SPEC (rand (lhs (concl check_th))) cover_all_sound) (EQT_ELIM check_th);

Theorem inner_bound = bound_inner inner_check

Theorem inner_bound_n = with_n inner_grid_def inner_bound

Theorem cover_bound = bound_cover cover_check

(* the cover with in_some written out: the five regions, as the certificates state them *)
Theorem cover_bound_regions = REWRITE_RULE [in_some_def] cover_bound

Theorem delta3_layer1 =
  LIST_CONJ [cover_bound_regions, inner_bound_n,
             slabA_bound_n, slabB_bound_n, slabC_bound_n, slabD_bound_n]
