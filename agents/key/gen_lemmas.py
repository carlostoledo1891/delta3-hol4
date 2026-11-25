#!/usr/bin/env python3
# gen_lemmas.py — PRIVATE. From lemma_source.py writes:
#   PUBLIC to the control room, NOT to proving agents:  hol4/delta3/LEMMAS.md (the true lemmas, L-ids)
#   AGENT-FACING (neutral ids, true and planted mixed):  hol4/delta3/delta3_stmtsScript.sml,
#       hol4/delta3/agents/STATEMENTS.md, hol4/delta3/harness/lemmas.json
#   PRIVATE (this folder):  key.json (neutral id -> truth), delta3_plantedScript.sml (kernel-checks every counterexample)
import json, random, os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import lemma_source as S
HERE = os.path.dirname(os.path.abspath(__file__))
D3 = os.path.abspath(os.path.join(HERE, '..', '..', '..', 'hol4', 'delta3'))
items = [('T', t) for t in S.T] + [('F', f) for f in S.F]
rng = random.Random(20261124); order = list(range(len(items))); rng.shuffle(order)
sid = {}
for pos, idx in enumerate(order): sid[idx] = 'S%02d' % (pos + 1)
L2S = {items[i][1]['id']: sid[i] for i in range(len(items)) if items[i][0] == 'T'}
Ldeps = {t['id']: t['deps'] for t in S.T}
Lpurp = {t['id']: t['purpose'] for t in S.T}
def group(lid):
    k = int(lid[1:])
    return 'SLAB' if k <= 28 else 'STRICT' if k == 29 else 'INNER' if k <= 40 else 'COVER'
rows = []
for i, (tf, it) in enumerate(items):
    lid = it['id'] if tf == 'T' else it['of']
    rows.append(dict(sid=sid[i], truth=(tf == 'T'), lemma=lid, group=group(lid), deps=[L2S[d] for d in Ldeps[lid]], purpose=Lpurp[lid],
                     stmt=it['stmt'], kind=it.get('kind'), why=it.get('why'), inst=it.get('inst')))
rows.sort(key=lambda r: r['sid'])
# 1. the statements theory
o = ['''(*
  delta3_stmts — the statements the proving agents are given, each as a boolean constant
  Snn defined to be its statement (universally closed).  GENERATED; do not edit.
  hol4/delta3 · cert-machine · Day 2 (2026-11-24)

  Some of these statements are FALSE on purpose.  Which ones is not recorded in this
  folder.  The harness accepts a proof of Snn only as the kernel theorem
      |- (deps) ==> <statement of Snn>
  where deps are the constants of the statements it may use (harness/lemmas.json).
  Nothing here is a theorem: these are definitions of propositions.
*)
Theory delta3_stmts
Ancestors
  arithmetic list integer real intreal delta3_check delta3_check2 delta3_sem
Libs
  intLib realLib

fun stmt nm tm =
  ignore (new_definition (nm ^ "_def",
            mk_eq (mk_var (nm, bool), list_mk_forall (free_vars_lr tm, tm))));
''']
for r in rows: o.append('val _ = stmt "%s" “%s”;\n' % (r['sid'], r['stmt']))
o.append("(* C01: the harness's own control statement (true, trivial); not a lemma *)\nval _ = stmt \"C01\" \u201c(n:num) + 0 = n\u201d;\n")
open(os.path.join(D3, 'delta3_stmtsScript.sml'), 'w').write('\n'.join(o))
# 2. agents
os.makedirs(os.path.join(D3, 'agents'), exist_ok=True); os.makedirs(os.path.join(D3, 'harness'), exist_ok=True)
a = ['# The statements\n', 'Each is a boolean constant `Snn` of `delta3_stmtsTheory` (`Snn_def` unfolds it). Free variables are universally closed.',
     'To submit `Snn`, prove the theorem named `Snn` whose conclusion is exactly `Sd1 /\\ ... /\\ Sdk ==> <statement>` for the listed "may use"',
     'constants in the listed order (just `<statement>` when the list is empty), then run `harness/attempt.sh Snn <script> <agent>`.',
     'Some statements are false. A false statement should be reported as refuted, with a counterexample; it cannot be proved.\n']
for r in rows:
    a.append('## %s  [%s]\n\nFor: %s.\n\nMay use: %s\n\n```\n%s\n```\n' % (r['sid'], r['group'], r['purpose'], ', '.join(r['deps']) or '(nothing)', r['stmt']))
open(os.path.join(D3, 'agents', 'STATEMENTS.md'), 'w').write('\n'.join(a))
lj = {r['sid']: {'deps': r['deps'], 'group': r['group']} for r in rows}; lj['C01'] = {'deps': [], 'group': 'CONTROL'}
json.dump(lj, open(os.path.join(D3, 'harness', 'lemmas.json'), 'w'), indent=1)
# 3. LEMMAS.md (true lemmas only)
m = ['# hol4/delta3 — the soundness lemmas (the true ones)\n',
     'NOT FOR THE PROVING AGENTS: this file lists only true statements, so reading it reveals which of the neutral',
     'statements `Snn` are planted. Agents get `agents/` and `harness/` only. The map L-id <-> S-id and the planted',
     'variants with their counterexamples are outside this folder (see README-DAY2.md).\n',
     'Generated from one private source. %d lemmas, in dependency order. Definitions: `delta3_checkScript.sml`,' % len(S.T),
     '`delta3_check2Script.sml` (the functions), `delta3_semScript.sml` (the real-valued meanings).\n',
     '| id | part | name | may use | what it is for |', '|---|---|---|---|---|']
for t in S.T: m.append('| %s | %s | `%s` | %s | %s |' % (t['id'], group(t['id']), t['name'], ' '.join(t['deps']) or '—', t['purpose']))
m.append('\n## Statements\n')
for t in S.T: m.append('### %s `%s`\n\n```\n%s\n```\n' % (t['id'], t['name'], t['stmt']))
open(os.path.join(D3, 'LEMMAS.md'), 'w').write('\n'.join(m))
# 4. key + the refutation theory
json.dump({r['sid']: {k: r[k] for k in ('truth', 'lemma', 'group', 'kind', 'why', 'inst', 'deps')} for r in rows},
          open(os.path.join(HERE, 'key.json'), 'w'), indent=1)
p = ['''(* delta3_planted — PRIVATE.  For every planted false statement: its counterexample instance must
   evaluate to F in the kernel; and the TRUE sibling must evaluate to T on the same instance.
   GENERATED.  Results are printed as D3PLANT lines and written to planted-results.tsv. *)
Theory delta3_planted[no_sig_docs]
Ancestors
  arithmetic list integer real intreal delta3_check delta3_check2 delta3_sem delta3_stmts
Libs
  intLib realLib

val out = TextIO.openOut "planted-results.tsv";
fun body nm = let val th = DB.fetch "delta3_stmts" (nm ^ "_def") in snd (strip_forall (rhs (concl th))) end;
fun inst_all pairs tm =
  let
    fun look v = List.find (fn (s, _) => s = fst (dest_var v)) pairs
    fun sub tm = let val fvs = free_vars tm in
      subst (List.mapPartial (fn v => case look v of NONE => NONE
               | SOME (_, q) => SOME (v |-> Parse.typedTerm [QUOTE q] (type_of v))) fvs) tm end
    fun pos tm =
      if is_forall tm then
        let val (v, b) = dest_forall tm in
          case look v of NONE => mk_forall (v, pos b)
          | SOME (_, q) => pos (subst [v |-> Parse.typedTerm [QUOTE q] (type_of v)] b) end
      else if is_imp tm andalso not (is_neg tm) then let val (a, b) = dest_imp tm in mk_imp (a, pos b) end
      else if is_conj tm then let val (a, b) = dest_conj tm in mk_conj (pos a, pos b) end
      else tm
  in pos (sub tm) end;
val fallback = SIMP_CONV (srw_ss() ++ ARITH_ss ++ realSimps.REAL_ARITH_ss ++ intSimps.INT_ARITH_ss) [];
fun value tm =
  let val th = EVAL tm val r = rhs (concl th) in
    if aconv r T orelse aconv r F then r
    else (rhs (concl (fallback r)) handle _ => r) end handle _ => tm;
fun check nm truth sibling pairs =
  let
    val v = value (inst_all pairs (body nm))
    val s = value (inst_all pairs (body sibling))
    val ok = aconv v F andalso aconv s T
    val line = String.concatWith "\\t" [nm, sibling, if ok then "OK" else "CHECK",
                 "planted=" ^ term_to_string v, "true_sibling=" ^ term_to_string s] ^ "\\n"
  in TextIO.output (out, line); print ("D3PLANT\\t" ^ line) end;
''']
for r in rows:
    if r['truth']: continue
    pairs = ', '.join('("%s", "%s")' % (k, v) for k, v in r['inst'].items())
    p.append('val _ = check "%s" false "%s" [%s];' % (r['sid'], L2S[r['lemma']], pairs))
p.append('val _ = TextIO.closeOut out;\n')
open(os.path.join(HERE, 'delta3_plantedScript.sml'), 'w').write('\n'.join(p))
print(len(rows), 'statements;', sum(r['truth'] for r in rows), 'true;', 'critical lemma L26 is', L2S['L26'])
