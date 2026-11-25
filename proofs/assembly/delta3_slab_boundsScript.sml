(*
  delta3_slab_bounds — the four slab certificates through the soundness theorem.  NON-BLIND assembly
  (hol4/delta3/assembly/, 2026-11-25).

  For each slab X: delta3_slabX (Day 1's generated theory, rebuilt here against the same base as the
  proof) holds  |- slab_check <the data of X> <=> T  by cv_eval; delta3_slab_sound holds slab_check_sound.
  MP of the two gives, on the region of X,
      |- !y. in_box n y /\ lo <= mval grid y /\ mval grid y <= hi ==> claim <= Ltheta ab cut full theta y
  and slabX_bound_n is the same theorem with LENGTH grid - 1 computed to the numeral n.
*)
Theory delta3_slab_bounds[no_sig_docs]
Ancestors
  delta3_slab_sound delta3_slabA delta3_slabB delta3_slabC delta3_slabD

fun bound check_th =
  let val args = snd (strip_comb (lhs (concl check_th)))      (* the twenty arguments of slab_check *)
  in MP (SPECL args slab_check_sound) (EQT_ELIM check_th) end;

fun with_n grid_def th =
  let val grid = lhs (concl grid_def)
      val len = (REWRITE_CONV [grid_def] THENC EVAL)
                  (numSyntax.mk_minus (listSyntax.mk_length grid, numSyntax.term_of_int 1))
  in PURE_REWRITE_RULE [len] th end;

Theorem slabA_bound = bound slabA_check
Theorem slabB_bound = bound slabB_check
Theorem slabC_bound = bound slabC_check
Theorem slabD_bound = bound slabD_check

Theorem slabA_bound_n = with_n slabA_grid_def slabA_bound
Theorem slabB_bound_n = with_n slabB_grid_def slabB_bound
Theorem slabC_bound_n = with_n slabC_grid_def slabC_bound
Theorem slabD_bound_n = with_n slabD_grid_def slabD_bound
