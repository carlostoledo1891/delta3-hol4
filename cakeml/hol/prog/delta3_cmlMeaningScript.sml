(*
  delta3_cmlMeaning — what the binary's one line means, in terms of the frozen checker.
  hol4/delta3/cakeml · cert-machine · 2026-11-25

  main_semantics (delta3_cmlMain) says the program prints  d3_main (implode text).
  d3_main_verdicts: an "ACCEPT slab_check" line means the text parses to sections secs with
  d3_slab secs = SOME T, a "REJECT slab_check" line SOME F; the same for inner_check and cover_all.
  d3_slab_SOME, d3_inner_SOME, d3_cover_SOME: d3_slab secs = SOME b means that the named sections
  read as these arguments and b IS the frozen slab_check on them (likewise for the other two).
  ("MALFORMED" says nothing about the checks.)
*)
Theory delta3_cmlMeaning
Ancestors
  delta3_cmlProg
Libs
  preamble

Theorem d3_main_verdicts:
  (d3_main s = strlit "ACCEPT slab_check\n" ==>
     ?secs. d3_parse s = SOME secs /\ d3_slab secs = SOME T) /\
  (d3_main s = strlit "REJECT slab_check\n" ==>
     ?secs. d3_parse s = SOME secs /\ d3_slab secs = SOME F) /\
  (d3_main s = strlit "ACCEPT inner_check\n" ==>
     ?secs. d3_parse s = SOME secs /\ d3_inner secs = SOME T) /\
  (d3_main s = strlit "REJECT inner_check\n" ==>
     ?secs. d3_parse s = SOME secs /\ d3_inner secs = SOME F) /\
  (d3_main s = strlit "ACCEPT cover_all\n" ==>
     ?secs. d3_parse s = SOME secs /\ d3_cover secs = SOME T) /\
  (d3_main s = strlit "REJECT cover_all\n" ==>
     ?secs. d3_parse s = SOME secs /\ d3_cover secs = SOME F)
Proof
  rw [delta3_cmlProgTheory.d3_main_def, delta3_cmlProgTheory.d3_verdict_def, AllCaseEqs ()]
  \\ gvs [AllCaseEqs ()]
QED

Theorem d3_slab_SOME:
  d3_slab secs = SOME b ==>
  ?g0 grid0 s0 lp0 lq0 hp0 hq0 bp0 bq0 ep0 eq0 cp0 cq0 theta0 forms0 ab0 cut0 full0
   w0 dd0 tt0 ds1 ds0 lw0.
    d3_one (strlit "grid") secs = SOME g0 /\ d3_nums g0 = SOME grid0 /\
    d3_one (strlit "scal") secs = SOME s0 /\
    r_scal10 s0 = SOME (lp0, lq0, hp0, hq0, bp0, bq0, ep0, eq0, cp0, cq0) /\
    d3_rows r_in (strlit "theta") secs = SOME theta0 /\
    d3_rows r_form (strlit "forms") secs = SOME forms0 /\
    d3_rows r_inin (strlit "ab") secs = SOME ab0 /\
    d3_rows r_nninn (strlit "cut") secs = SOME cut0 /\
    d3_rows r_nni (strlit "full") secs = SOME full0 /\
    d3_one (strlit "wit") secs = SOME w0 /\ r_wit w0 = SOME (dd0, tt0) /\
    d3_one (strlit "ds") secs = SOME ds1 /\ d3_nums ds1 = SOME ds0 /\
    d3_sec (strlit "L") secs = SOME lw0 /\
    b = slab_check ab0 cut0 full0 grid0 lp0 lq0 hp0 hq0 bp0 bq0 ep0 eq0 cp0 cq0
                   theta0 forms0 dd0 tt0 ds0 lw0
Proof
  rw [delta3_cmlProgTheory.d3_slab_def, AllCaseEqs ()] \\ gvs []
QED

Theorem d3_inner_SOME:
  d3_inner secs = SOME b ==>
  ?g0 grid0 s0 rp0 rq0 kp0 kq0 lam0 nu0 nn0 cc0 ab0 cut0 full0 w0 dd0 tt0 ds1 ds0 lw0.
    d3_one (strlit "grid") secs = SOME g0 /\ d3_nums g0 = SOME grid0 /\
    d3_one (strlit "scal") secs = SOME s0 /\ r_inin s0 = SOME (rp0, rq0, kp0, kq0) /\
    d3_rows r_nnin (strlit "lam") secs = SOME lam0 /\
    d3_rows r_in (strlit "nu") secs = SOME nu0 /\
    d3_rows r_nnin (strlit "nn") secs = SOME nn0 /\
    d3_rows r_in (strlit "cc") secs = SOME cc0 /\
    d3_rows r_inin (strlit "ab") secs = SOME ab0 /\
    d3_rows r_nninn (strlit "cut") secs = SOME cut0 /\
    d3_rows r_nni (strlit "full") secs = SOME full0 /\
    d3_one (strlit "wit") secs = SOME w0 /\ r_wit w0 = SOME (dd0, tt0) /\
    d3_one (strlit "ds") secs = SOME ds1 /\ d3_nums ds1 = SOME ds0 /\
    d3_sec (strlit "L") secs = SOME lw0 /\
    b = inner_check ab0 cut0 full0 grid0 rp0 rq0 lam0 nu0 kp0 kq0 nn0 cc0 dd0 tt0 ds0 lw0
Proof
  rw [delta3_cmlProgTheory.d3_inner_def, AllCaseEqs ()] \\ gvs []
QED

Theorem d3_cover_SOME:
  d3_cover secs = SOME b ==>
  ?ivs0. d3_rows r_inin (strlit "cover") secs = SOME ivs0 /\ b = cover_all ivs0
Proof
  rw [delta3_cmlProgTheory.d3_cover_def, AllCaseEqs ()] \\ gvs []
QED
