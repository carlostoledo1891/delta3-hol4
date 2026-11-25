(* delta3DataLib — reads a .d3 data file (written by export.js) and builds HOL4 terms
   from it DIRECTLY with the syntax functions: no parser, no type inference.
   hol4/delta3 · cert-machine · Day 1 (2026-11-24)

   Why not a quotation: the smallest slab is about 0.46 MB of digits in ~26,000 rows.
   The term is built in ML by numSyntax.mk_numeral / intSyntax / pairSyntax /
   listSyntax, which is linear in the data and needs no inference; the script files
   stay small and the data stays a separate, hashable file. *)
structure delta3DataLib :> delta3DataLib =
struct

open HolKernel boolLib

type dat = (string * string list list) list

fun read_dat file =
  let
    val ins = TextIO.openIn file
    fun lines acc =
      case TextIO.inputLine ins of NONE => rev acc | SOME l => lines (l :: acc)
    val ls = lines []
    val _ = TextIO.closeIn ins
    fun toks l = String.tokens Char.isSpace l
    fun close NONE acc = acc
      | close (SOME (nm, rows)) acc = (nm, rev rows) :: acc
    fun go [] cur acc = rev (close cur acc)
      | go (l :: rest) cur acc =
          if String.isPrefix "@" l then
            go rest (SOME (String.extract (hd (toks l), 1, NONE), [])) (close cur acc)
          else
            (case cur of
               NONE => go rest cur acc
             | SOME (nm, rows) => go rest (SOME (nm, toks l :: rows)) acc)
  in
    go ls NONE []
  end

fun section (dat : dat) nm =
  case List.find (fn (n, _) => n = nm) dat of
    SOME (_, rows) => rows
  | NONE => raise Fail ("delta3DataLib: no section " ^ nm)

fun num_tm s = numSyntax.mk_numeral (Arbnum.fromString s)

fun int_tm s =
  if String.isPrefix "-" s then
    intSyntax.mk_negated (intSyntax.mk_injected (num_tm (String.extract (s, 1, NONE))))
  else intSyntax.mk_injected (num_tm s)

fun cell #"n" s = num_tm s
  | cell #"i" s = int_tm s
  | cell c _ = raise Fail ("delta3DataLib: bad column kind " ^ str c)

fun cell_ty #"n" = numSyntax.num
  | cell_ty #"i" = intSyntax.int_ty
  | cell_ty c = raise Fail ("delta3DataLib: bad column kind " ^ str c)

fun row_tm spec row =
  let val ks = String.explode spec in
    if length ks <> length row then
      raise Fail ("delta3DataLib: row of " ^ Int.toString (length row) ^ " for spec " ^ spec)
    else pairSyntax.list_mk_pair (ListPair.map (fn (k, s) => cell k s) (ks, row))
  end

fun rows_tm spec rows =
  let val ty = pairSyntax.list_mk_prod (map cell_ty (String.explode spec)) in
    listSyntax.mk_list (map (row_tm spec) rows, ty)
  end

fun nums_tm row = listSyntax.mk_list (map num_tm row, numSyntax.num)

fun intss_tm rows =
  listSyntax.mk_list
    (map (fn r => listSyntax.mk_list (map int_tm r, intSyntax.int_ty)) rows,
     listSyntax.mk_list_type intSyntax.int_ty)

fun define nm tm =
  new_definition (nm ^ "_def", mk_eq (mk_var (nm, type_of tm), tm))

(* from_list / from_pair / Num / from_int on literals, by call-by-value rewriting *)
val from_conv =
  let
    val cs = computeLib.add_thms
               [cv_typeTheory.from_list_def, cv_typeTheory.from_pair_def,
                delta3_checkTheory.from_int_pos, delta3_checkTheory.from_int_neg]
               (computeLib.copy reduceLib.num_compset)
  in
    computeLib.CBV_CONV cs
  end

fun timed thy label f x =
  let
    val rt = Timer.startRealTimer ()
    val ct = Timer.startCPUTimer ()
    val r = f x
    val wall = Time.toReal (Timer.checkRealTimer rt)
    val {usr, sys} = Timer.checkCPUTimer ct
    val gc = Timer.checkGCTime ct
    val line = String.concatWith "\t"
                 [thy, label, Real.fmt (StringCvt.FIX (SOME 3)) wall,
                  Real.fmt (StringCvt.FIX (SOME 3)) (Time.toReal usr + Time.toReal sys),
                  Real.fmt (StringCvt.FIX (SOME 3)) (Time.toReal gc)] ^ "\n"
    val out = TextIO.openAppend "timings.tsv"
    val _ = TextIO.output (out, line)
    val _ = TextIO.closeOut out
    val _ = print ("D3TIME\t" ^ line)
  in
    r
  end

end
