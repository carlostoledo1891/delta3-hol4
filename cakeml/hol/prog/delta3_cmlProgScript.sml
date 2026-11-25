(*
  delta3_cmlProg — the delta_3 = 117/2192 certificate checker of hol4/delta3 (the theories
  delta3_check and delta3_check2, built from whatever delta3_checkScript.sml / delta3_check2Script.sml
  build-binary.sh is given — on 2026-11-25 the FROZEN harness/base ones), translated to CakeML by CakeML's proof-producing translator;
  a reader for the .d3 data files written as HOL functions and translated the same way; a main
  that reads a .d3 file on standard input and prints one line; its whole-program specification
  (characteristic formulae) and the semantics theorem of the whole program; and the program
  written out as an S-expression for the released CakeML compiler binary (cake v3671).
  hol4/delta3/cakeml · cert-machine · 2026-11-24/25

  What is PROVED here (in HOL4 trindemossen-2-v10, with CakeML v3671's translator and basis):
   - for every translated function f, a certificate theorem  Eval env (Var f) (A f)  saying that
     the CakeML closure f_v implements the HOL function f, with no precondition left;
   - main_semantics: from any file system whose standard input holds text, the CakeML program
     delta3_prog (basis library + the translated checker + main) terminates and its standard
     output is  d3_main (implode text).
  What d3_main is: a HOL function defined below — parse the .d3 text, convert the sections to
  the argument types of slab_check / inner_check / cover_all, and return
  "ACCEPT <check>\n" when the check returns T, "REJECT <check>\n" when it returns F, and
  "MALFORMED\n" when the text does not parse into the arguments.
  What is NOT proved here: that slab_check / inner_check / cover_all mean the bound (no soundness
  theorem yet; that is the proof harness's work); anything about the machine code (see README.md).
*)
Theory delta3_cmlProg
Ancestors
  delta3_check delta3_check2 cfApp basis_ffi
Libs
  preamble basis basisFunctionsLib astToSexprLib

val _ = translation_extends "basisProg";
val _ = hide_environments true;

(* ------------------------------------------------------------------------------------------ *)
(* DIV and MOD by zero.  HOL4 has  k DIV 0 = 0  and  k MOD 0 = k  (arithmeticTheory.DIV_0,    *)
(* MOD_0); CakeML's div and mod raise an exception on 0, so the translator asks for a nonzero *)
(* divisor.  These two total versions are equal to DIV and MOD everywhere, so rewriting the    *)
(* frozen definitions with them changes nothing in HOL and removes the precondition.           *)
(* ------------------------------------------------------------------------------------------ *)

Definition tdiv_def:
  tdiv (a:num) (b:num) = if b = 0 then 0 else a DIV b
End

Definition tmod_def:
  tmod (a:num) (b:num) = if b = 0 then a else a MOD b
End

Theorem DIV_tdiv:
  a DIV b = tdiv a b
Proof
  rw [tdiv_def]
QED

Theorem MOD_tmod:
  a MOD b = tmod a b
Proof
  rw [tmod_def]
QED

(* and  n - 1  on num: CakeML's translation of  a - b  asks for  b <= a  unless the context gives
   it; at  LENGTH grid - 1  in slab_check and inner_check nothing does (it is 0 in HOL for an empty
   grid).  tsub1 a = a - 1 for every a (0 - 1 = 0 in num), proved, so the rewrite changes nothing. *)
Definition tsub1_def:
  tsub1 (a:num) = if a = 0 then 0 else a - 1
End

Theorem SUB1_tsub1:
  a - 1 = tsub1 a
Proof
  rw [tsub1_def]
QED

val r = translate tdiv_def;
val r = translate tmod_def;
val r = translate tsub1_def;
val r = translate rich_listTheory.REPLICATE;   (* used by slab_poly / inner_poly; not in the basis *)

(* ------------------------------------------------------------------------------------------ *)
(* The checker is an INPUT: every constant the theories delta3_check and delta3_check2 define *)
(* (except cv_trans's own cv_* constants) is translated from its <name>_def, dependencies     *)
(* first, so a reshaped checker is translated as it stands.  Non-recursive definitions are   *)
(* rewritten with the three equations above (each is an equality in HOL, so nothing changes  *)
(* in what is translated); recursive ones are translated as they are, so that their           *)
(* induction theorems still match.  Every certificate theorem is checked for a precondition  *)
(* at the end of this file.                                                                   *)
(* ------------------------------------------------------------------------------------------ *)

val checker_thys = ["delta3_check", "delta3_check2"];

val checker_consts =
  List.concat (map (fn thy => map (fn c => (thy, c)) (constants thy)) checker_thys)
  |> List.filter (fn (_, c) => not (String.isPrefix "cv_" (fst (dest_const c))));

fun def_of (thy, c) = DB.fetch thy (fst (dest_const c) ^ "_def");

fun rhs_consts th =
  List.concat (map (fn cj => find_terms is_const (rhs (snd (strip_forall cj))))
                   (strip_conj (concl th)));

fun deps (thy, c) =
  let val used = rhs_consts (def_of (thy, c)) in
    List.filter (fn (_, d) => not (same_const d c) andalso
                              List.exists (same_const d) used) checker_consts
  end;

fun is_recursive (thy, c) = List.exists (same_const c) (rhs_consts (def_of (thy, c)));

(* dependencies first; among the ready ones, alphabetical, so the order is reproducible *)
fun topo done [] = rev done
  | topo done todo =
      let
        fun ready x = List.all (fn (_, d) => List.exists (fn (_, e) => same_const d e) done) (deps x)
        val rs = List.filter ready todo
        val _ = if null rs then raise Fail "delta3_cmlProg: cyclic checker definitions" else ()
        val pick = hd (Listsort.sort (fn ((_, a), (_, b)) =>
                                         String.compare (fst (dest_const a), fst (dest_const b))) rs)
      in topo (pick :: done) (List.filter (fn (_, c) => not (same_const c (snd pick))) todo) end;

val checker_order = topo [] checker_consts;

fun translate_checker (thy, c) =
  let
    val nm = fst (dest_const c)
    val th = def_of (thy, c)
    val th' = if is_recursive (thy, c) then th
              else PURE_REWRITE_RULE [DIV_tdiv, MOD_tmod, SUB1_tsub1] th
    val _ = print ("D3TRANSLATE\t" ^ thy ^ "\t" ^ nm ^
                   (if is_recursive (thy, c) then "\trecursive" else "\tnon-recursive") ^
                   (if aconv (concl th) (concl th') then "" else "\trewritten") ^ "\n")
  in translate th' end;

val _ = List.app (ignore o translate_checker) checker_order;
val translated_checker_names = map (fst o dest_const o snd) checker_order;

(* ------------------------------------------------------------------------------------------ *)
(* Reading a .d3 file.  The format is the one export.js writes and delta3DataLib.read_dat     *)
(* reads: a line "@name count" opens a section, every other non-blank line is one row of      *)
(* whitespace-separated decimal integers (a leading '-' for a negative one).  The count after  *)
(* the name is ignored, as read_dat ignores it.  A section is looked up by name, first match.  *)
(* ------------------------------------------------------------------------------------------ *)

Definition d3_ints_def:
  d3_ints [] = SOME [] /\
  d3_ints (tok :: toks) =
    case mlint$fromString tok of
      NONE => NONE
    | SOME (iv:int) =>
        (case d3_ints toks of NONE => NONE | SOME ivs => SOME (iv :: ivs))
End

(* white space as SML's Char.isSpace has it (delta3DataLib.read_dat splits rows with it):
   the characters 9 to 13 and 32 *)
Definition d3_space_def:
  d3_space (c:char) = (ORD c = 32 \/ (9 <= ORD c /\ ORD c <= 13))
End

Definition d3_group_def:
  d3_group [] (nm:mlstring) (rows:int list list) acc =
    SOME (REVERSE ((nm, REVERSE rows) :: acc)) /\
  d3_group (ln :: lns) nm rows acc =
    case mlstring$tokens d3_space ln of
      [] => d3_group lns nm rows acc
    | (tok :: toks) =>
        if mlstring$isPrefix (strlit "@") tok then
          d3_group lns (mlstring$extract tok 1 NONE) [] ((nm, REVERSE rows) :: acc)
        else
          case d3_ints (tok :: toks) of
            NONE => NONE
          | SOME rw => d3_group lns nm (rw :: rows) acc
End

Definition d3_parse_def:
  d3_parse (s:mlstring) =
    d3_group (mlstring$tokens (\c. c = #"\n") s) (strlit "") [] []
End

Definition d3_sec_def:
  d3_sec (nm:mlstring) [] = (NONE : int list list option) /\
  d3_sec nm ((nm1, rows) :: rest) = if nm1 = nm then SOME rows else d3_sec nm rest
End

Definition d3_one_def:
  d3_one nm secs =
    case d3_sec nm secs of SOME [rw] => SOME rw | _ => (NONE : int list option)
End

Definition d3_has_def:
  d3_has nm secs = case d3_sec nm secs of NONE => F | SOME _ => T
End

Definition d3_num_def:
  d3_num (iv:int) = if iv < 0 then NONE else SOME (Num (ABS iv))
End

Definition d3_map_def:
  d3_map f [] = SOME [] /\
  d3_map f (x :: xs) =
    case f x of
      NONE => NONE
    | SOME y => (case d3_map f xs of NONE => NONE | SOME ys => SOME (y :: ys))
End

Definition d3_rows_def:
  d3_rows f nm secs =
    case d3_sec nm secs of NONE => NONE | SOME rows => d3_map f rows
End

(* one converter per row shape; the letters are delta3DataLib's: n = num, i = int *)
Definition r_in_def:
  r_in (rw:int list) =
    case rw of
      [a1; a2] => (case d3_num a2 of NONE => NONE | SOME n2 => SOME (a1, n2))
    | _ => NONE
End

Definition r_inin_def:
  r_inin (rw:int list) =
    case rw of
      [a1; a2; a3; a4] =>
        (case (d3_num a2, d3_num a4) of
           (SOME n2, SOME n4) => SOME (a1, n2, a3, n4)
         | _ => NONE)
    | _ => NONE
End

Definition r_nnin_def:
  r_nnin (rw:int list) =
    case rw of
      [a1; a2; a3; a4] =>
        (case (d3_num a1, d3_num a2, d3_num a4) of
           (SOME n1, SOME n2, SOME n4) => SOME (n1, n2, a3, n4)
         | _ => NONE)
    | _ => NONE
End

Definition r_nni_def:
  r_nni (rw:int list) =
    case rw of
      [a1; a2; a3] =>
        (case (d3_num a1, d3_num a2) of
           (SOME n1, SOME n2) => SOME (n1, n2, a3)
         | _ => NONE)
    | _ => NONE
End

Definition r_nninn_def:
  r_nninn (rw:int list) =
    case rw of
      [a1; a2; a3; a4; a5] =>
        (case (d3_num a1, d3_num a2, d3_num a4, d3_num a5) of
           (SOME n1, SOME n2, SOME n4, SOME n5) => SOME (n1, n2, a3, n4, n5)
         | _ => NONE)
    | _ => NONE
End

Definition r_form_def:
  r_form (rw:int list) =
    case rw of
      [a1; a2; a3; a4; a5; a6; a7; a8; a9] =>
        (case (d3_num a1, d3_num a2, d3_num a3, d3_num a4, d3_num a9) of
           (SOME n1, SOME n2, SOME n3, SOME n4, SOME n9) =>
             SOME (n1, n2, n3, n4, a5, a6, a7, a8, n9)
         | _ => NONE)
    | _ => NONE
End

(* the slab's ten scalars "ininininin": lo, hi, B, eps, claim, each as (p:int, q:num) *)
Definition r_scal10_def:
  r_scal10 (rw:int list) =
    case rw of
      [a1; a2; a3; a4; a5; a6; a7; a8; a9; a10] =>
        (case (d3_num a2, d3_num a4, d3_num a6, d3_num a8, d3_num a10) of
           (SOME n2, SOME n4, SOME n6, SOME n8, SOME n10) =>
             SOME (a1, n2, a3, n4, a5, n6, a7, n8, a9, n10)
         | _ => NONE)
    | _ => NONE
End

(* the witness line "D T" *)
Definition r_wit_def:
  r_wit (rw:int list) =
    case rw of
      [a1; a2] =>
        (case (d3_num a1, d3_num a2) of
           (SOME n1, SOME n2) => SOME (n1, n2)
         | _ => NONE)
    | _ => NONE
End

Definition d3_nums_def:
  d3_nums (rw:int list) = d3_map d3_num rw
End

(* the arguments of slab_check, in the order of slab.template's goal term *)
Definition d3_slab_def:
  d3_slab secs =
    case d3_one (strlit "grid") secs of NONE => NONE | SOME g0 =>
    case d3_nums g0 of NONE => NONE | SOME grid0 =>
    case d3_one (strlit "scal") secs of NONE => NONE | SOME s0 =>
    case r_scal10 s0 of NONE => NONE | SOME (lp0, lq0, hp0, hq0, bp0, bq0, ep0, eq0, cp0, cq0) =>
    case d3_rows r_in (strlit "theta") secs of NONE => NONE | SOME theta0 =>
    case d3_rows r_form (strlit "forms") secs of NONE => NONE | SOME forms0 =>
    case d3_rows r_inin (strlit "ab") secs of NONE => NONE | SOME ab0 =>
    case d3_rows r_nninn (strlit "cut") secs of NONE => NONE | SOME cut0 =>
    case d3_rows r_nni (strlit "full") secs of NONE => NONE | SOME full0 =>
    case d3_one (strlit "wit") secs of NONE => NONE | SOME w0 =>
    case r_wit w0 of NONE => NONE | SOME (dd0, tt0) =>
    case d3_one (strlit "ds") secs of NONE => NONE | SOME ds1 =>
    case d3_nums ds1 of NONE => NONE | SOME ds0 =>
    case d3_sec (strlit "L") secs of NONE => NONE | SOME lw0 =>
      SOME (slab_check ab0 cut0 full0 grid0 lp0 lq0 hp0 hq0 bp0 bq0 ep0 eq0 cp0 cq0
                       theta0 forms0 dd0 tt0 ds0 lw0)
End

(* the arguments of inner_check, in the order of inner.template's goal term *)
Definition d3_inner_def:
  d3_inner secs =
    case d3_one (strlit "grid") secs of NONE => NONE | SOME g0 =>
    case d3_nums g0 of NONE => NONE | SOME grid0 =>
    case d3_one (strlit "scal") secs of NONE => NONE | SOME s0 =>
    case r_inin s0 of NONE => NONE | SOME (rp0, rq0, kp0, kq0) =>
    case d3_rows r_nnin (strlit "lam") secs of NONE => NONE | SOME lam0 =>
    case d3_rows r_in (strlit "nu") secs of NONE => NONE | SOME nu0 =>
    case d3_rows r_nnin (strlit "nn") secs of NONE => NONE | SOME nn0 =>
    case d3_rows r_in (strlit "cc") secs of NONE => NONE | SOME cc0 =>
    case d3_rows r_inin (strlit "ab") secs of NONE => NONE | SOME ab0 =>
    case d3_rows r_nninn (strlit "cut") secs of NONE => NONE | SOME cut0 =>
    case d3_rows r_nni (strlit "full") secs of NONE => NONE | SOME full0 =>
    case d3_one (strlit "wit") secs of NONE => NONE | SOME w0 =>
    case r_wit w0 of NONE => NONE | SOME (dd0, tt0) =>
    case d3_one (strlit "ds") secs of NONE => NONE | SOME ds1 =>
    case d3_nums ds1 of NONE => NONE | SOME ds0 =>
    case d3_sec (strlit "L") secs of NONE => NONE | SOME lw0 =>
      SOME (inner_check ab0 cut0 full0 grid0 rp0 rq0 lam0 nu0 kp0 kq0 nn0 cc0
                        dd0 tt0 ds0 lw0)
End

(* the cover: one section "@cover", one row "lp lq hp hq" per region, in order *)
Definition d3_cover_def:
  d3_cover secs =
    case d3_rows r_inin (strlit "cover") secs of
      NONE => NONE
    | SOME ivs => SOME (cover_all ivs)
End

Definition d3_verdict_def:
  d3_verdict (acc:mlstring) (rej:mlstring) ob =
    case ob of
      NONE => strlit "MALFORMED\n"
    | SOME b => if b then acc else rej
End

Definition d3_main_def:
  d3_main (s:mlstring) =
    case d3_parse s of
      NONE => strlit "MALFORMED\n"
    | SOME secs =>
        if d3_has (strlit "forms") secs then
          d3_verdict (strlit "ACCEPT slab_check\n") (strlit "REJECT slab_check\n") (d3_slab secs)
        else if d3_has (strlit "lam") secs then
          d3_verdict (strlit "ACCEPT inner_check\n") (strlit "REJECT inner_check\n") (d3_inner secs)
        else if d3_has (strlit "cover") secs then
          d3_verdict (strlit "ACCEPT cover_all\n") (strlit "REJECT cover_all\n") (d3_cover secs)
        else strlit "MALFORMED\n"
End

val r = translate d3_ints_def;
val r = translate d3_space_def;
val r = translate d3_group_def;
val r = translate d3_parse_def;
val r = translate d3_sec_def;
val r = translate d3_one_def;
val r = translate d3_has_def;
val r = translate d3_num_def;
val r = translate d3_map_def;
val r = translate d3_rows_def;
val r = translate r_in_def;
val r = translate r_inin_def;
val r = translate r_nnin_def;
val r = translate r_nni_def;
val r = translate r_nninn_def;
val r = translate r_form_def;
val r = translate r_scal10_def;
val r = translate r_wit_def;
val r = translate d3_nums_def;
val r = translate d3_slab_def;
val r = translate d3_inner_def;
val r = translate d3_cover_def;
val r = translate d3_verdict_def;
val d3_main_v_thm = translate d3_main_def;

(* the certificate theorems as stored at the end (update_precondition replaces them there):
   none of the top-level ones may still carry a PRECONDITION *)
fun no_pre nm =
  let val th = fetch "-" (nm ^ "_v_thm")
      val _ = print ("D3CERT\t" ^ nm ^ "\t" ^ term_to_string (concl th) ^ "\n")
  in if can (find_term (fn t => is_const t andalso fst (dest_const t) = "PRECONDITION"))
            (concl th)
     then raise Fail ("delta3_cmlProg: " ^ nm ^ " still has a precondition")
     else ()
  end;
val _ = List.app no_pre (["tdiv", "tmod", "tsub1"] @ translated_checker_names @
  ["d3_ints", "d3_space", "d3_group", "d3_parse", "d3_sec", "d3_one", "d3_has", "d3_num",
   "d3_map", "d3_rows", "r_in", "r_inin", "r_nnin", "r_nni", "r_nninn", "r_form", "r_scal10",
   "r_wit", "d3_nums", "d3_slab", "d3_inner", "d3_cover", "d3_verdict", "d3_main"]);
val _ = print ("D3COUNT\tchecker functions translated: " ^
               Int.toString (length translated_checker_names) ^ "\n");
