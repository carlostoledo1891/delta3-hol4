(*
  delta3_cmlSexp — the S-expression the cake binary reads, PRODUCED IN HOL and proved to read back
  to the program delta3_prog that main_semantics is about.
  hol4/delta3/cakeml · cert-machine · 2026-11-25

  CakeML v3671's compiler, given --sexp=true, parses its input with
      parse_sexp_input input = case mlsexp$parse input of
                                 INL (perr, _) => INL …
                               | INR (x, _) => case ast_sexp$to_dec_list x of
                                                 NONE => INL … | SOME x => INR x
  (compiler/compilerScript.sml, parse_sexp_input_def).  CakeML proves, in basis/pure:
      mlsexp$parse_sexp_to_string :
        (s <> "" ==> isSpace (HD s)) ==> parse (explode (sexp_to_string x) ++ s) = INR (x, s)
      ast_sexp$to_from_dec_list_ok :  to_dec_list (from_dec_list decs) = SOME decs
  Here: EVAL computes  sexp_to_string (from_dec_list delta3_prog)  to a string literal S
  (a theorem), the two facts above give  parse S = INR (from_dec_list delta3_prog, "")  and
  to_dec_list (from_dec_list delta3_prog) = SOME delta3_prog,  and S is written to
  delta3.proved.sexp.  build-binary.sh then checks that this file is byte-identical to the
  delta3.sexp that astToSexprLib (the unverified ML printer) wrote, and compiles it.
  What stays trusted for this step: that TextIO.output wrote the characters of S to the file.
*)
Theory delta3_cmlSexp[no_sig_docs]
Ancestors
  delta3_cmlMain ast_sexp mlsexp
Libs
  preamble

(* the printer, evaluated by EVAL (it is higher-order: from_option, MAP Atom, so not cv_trans'd here) *)
val prog_def = delta3_cmlMainTheory.delta3_prog_def;

val t0 = Time.now ();
val str_th =
  (RAND_CONV (RAND_CONV (REWR_CONV prog_def)) THENC EVAL)
    “sexp_to_string (from_dec_list delta3_prog)”;
val _ = print ("D3SEXP\tEVAL sexp_to_string (from_dec_list delta3_prog): " ^
               Time.toString (Time.- (Time.now (), t0)) ^ " s\n");
val _ = if mlstringSyntax.is_mlstring_literal (rhs (concl str_th)) then ()
        else raise Fail "delta3_cmlSexp: EVAL did not reach a string literal";

val S_tm = mlstringSyntax.dest_mlstring (rhs (concl str_th)) |> stringSyntax.fromMLstring;

val parse_th =
  mlsexpTheory.parse_sexp_to_string
  |> Q.SPECL [‘[]’, ‘from_dec_list delta3_prog’]
  |> SIMP_RULE std_ss [listTheory.APPEND_NIL]
  |> PURE_REWRITE_RULE [str_th, mlstringTheory.explode_thm];

val dec_th = ast_sexpTheory.to_from_dec_list_ok
             |> INST [mk_var ("decs", type_of (lhs (concl prog_def))) |-> lhs (concl prog_def)];

Theorem delta3_sexp_reads_back = CONJ parse_th dec_th;

val _ = let
          val out = TextIO.openOut "delta3.proved.sexp"
          val _ = TextIO.output (out, stringSyntax.fromHOLstring S_tm)
        in TextIO.closeOut out end;

val _ = print ("D3SEXP\tchars " ^ Int.toString (size (stringSyntax.fromHOLstring S_tm)) ^
               "\thyps " ^ Int.toString (length (hyp delta3_sexp_reads_back)) ^ "\n");
