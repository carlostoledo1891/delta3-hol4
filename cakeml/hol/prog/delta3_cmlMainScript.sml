(*
  delta3_cmlMain — the main of the delta_3 checker binary, its specification in CakeML's
  characteristic-formula logic, the semantics theorem of the whole program, and the program
  written out as an S-expression (delta3.sexp) for the released CakeML compiler binary.
  hol4/delta3/cakeml · cert-machine · 2026-11-24/25

  main reads ALL of standard input and prints  d3_main <the input>  (delta3_cmlProgScript.sml):
  one line, "ACCEPT <check>", "REJECT <check>" or "MALFORMED".
*)
Theory delta3_cmlMain
Ancestors
  delta3_cmlProg cfApp basis_ffi
Libs
  preamble basis basisFunctionsLib astToSexprLib

val _ = translation_extends "delta3_cmlProg";
val _ = hide_environments true;

Quote add_cakeml:
  fun main u =
    case TextIO.inputAllFrom None of
      None => TextIO.print "MALFORMED\n"
    | Some s => TextIO.print (d3_main s)
End

val st = get_ml_prog_state ();

val d3_main_v_thm = fetch "delta3_cmlProg" "d3_main_v_thm";

Theorem main_spec:
  stdin_content fs = SOME text ==>
  app (p:'ffi ffi_proj) ^(fetch_v "main" st) [Conv NONE []]
    (STDIO fs)
    (POSTv uv. &UNIT_TYPE () uv *
               STDIO (add_stdout (fastForwardFD fs 0) (d3_main (implode text))))
Proof
  strip_tac
  \\ xcf "main" st
  \\ reverse (Cases_on `STD_streams fs`) >- (fs [STDIO_def] \\ xpull)
  \\ xlet `POSTv nv. &OPTION_TYPE FILENAME NONE nv * STDIO fs`
  >- (xcon \\ xsimpl \\ simp [std_preludeTheory.OPTION_TYPE_def])
  \\ xlet `POSTv sv. &OPTION_TYPE STRING_TYPE (SOME (implode text)) sv *
                     STDIO (fastForwardFD fs 0)`
  >- (xapp_spec inputAllFrom_NONE_spec \\ fs [std_preludeTheory.OPTION_TYPE_def])
  \\ gvs [std_preludeTheory.OPTION_TYPE_def]
  \\ xmatch
  \\ IF_CASES_TAC >- (pop_assum mp_tac \\ EVAL_TAC)
  \\ reverse conj_tac >- (EVAL_TAC \\ fs [])
  \\ assume_tac d3_main_v_thm
  \\ xlet_auto >- xsimpl
  \\ xapp_spec print_spec
  \\ xsimpl
QED

Theorem main_whole_prog_spec:
  stdin_content fs = SOME text ==>
  whole_prog_spec ^(fetch_v "main" st) cl fs NONE
    ((=) (add_stdout (fastForwardFD fs 0) (d3_main (implode text))))
Proof
  strip_tac
  \\ rw [whole_prog_spec_def]
  \\ qmatch_goalsub_abbrev_tac `fs1 = _ with numchars := _`
  \\ qexists_tac `fs1`
  \\ simp [Abbr `fs1`, GSYM add_stdo_with_numchars, with_same_numchars,
           GSYM fsFFIPropsTheory.fastForwardFD_with_numchars]
  \\ match_mp_tac (MP_CANON (MATCH_MP app_wgframe (UNDISCH main_spec)))
  \\ xsimpl
QED

Theorem main_semantics =
  prove_sem_thm "main" "delta3_prog" main_whole_prog_spec;

val _ = print ("D3SEM\t" ^ thm_to_string main_semantics ^ "\n");

val _ = write_program_def_to_file "delta3.sexp" (definition "delta3_prog_def");
