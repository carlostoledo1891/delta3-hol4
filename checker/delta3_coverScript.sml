(*
  delta3_cover — the cover check  cover_all  (delta3_check2Script.sml, as frozen in
  harness/base) run in the HOL4 kernel by cv_eval on the four cover inputs of ../d3/
  (the genuine cover of [0, 1/2] by the five regions, and battery.js's three cover forgeries).
  hol4/delta3/cakeml · cert-machine · 2026-11-25. Written by the CakeML agent so that the
  binary's cover verdicts have a kernel verdict to be compared with; no cover theorem existed.
  Each theorem saved here is  |- cover_all <regions> = T  or  = F  and nothing more.
*)
Theory delta3_cover[no_sig_docs]
Ancestors
  delta3_check delta3_check2
Libs
  cv_transLib delta3DataLib

fun one (nm, expect) =
  let
    val dat = read_dat ("../d3/" ^ nm ^ ".d3")
    val ivs = rows_tm "inin" (section dat "cover")
    val th = timed nm "cv_eval_cover_all" cv_eval (mk_comb (prim_mk_const {Thy = "delta3_check2", Name = "cover_all"}, ivs))
    val got = term_to_string (rhs (concl th))
    val (oracles, axioms) = Tag.dest_tag (Thm.tag th)
    val _ = print ("D3RESULT\t" ^ nm ^ "\t" ^ got ^ "\texpected " ^ expect ^
                   "\toracles [" ^ String.concatWith "," oracles ^ "]" ^
                   "\taxioms [" ^ String.concatWith "," axioms ^ "]" ^
                   "\thyps " ^ Int.toString (length (hyp th)) ^ "\n")
    val _ = if got = expect andalso null (hyp th) then ()
            else raise Fail ("delta3_cover: " ^ nm ^ " returned " ^ got ^ ", expected " ^ expect)
    val out = TextIO.openOut (nm ^ ".theorem.txt")
    val _ = TextIO.output (out, thm_to_string th ^ "\n")
    val _ = TextIO.closeOut out
  in th end;

val ths = map one [("cover", "T"), ("cover_red_gap", "F"),
                   ("cover_red_noinner", "F"), ("cover_red_short", "F")];

Theorem cover_check = el 1 ths
Theorem cover_red_gap_check = el 2 ths
Theorem cover_red_noinner_check = el 3 ths
Theorem cover_red_short_check = el 4 ths
