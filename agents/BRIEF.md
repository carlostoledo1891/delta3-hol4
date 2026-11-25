# Brief for a proving agent — version 2 (the same text for every agent, of either model family)

This version replaces agents/BRIEF.md when the key is redrawn (harness/regen-key.sh moves it into place, and
FREEZE-2.json freezes it). It adds the rules of the run, refutations, and the remote judge.

You are asked to prove, in HOL4, statements about a small certificate checker — or to show that a statement
is false. The HOL4 kernel decides either way.

## What you are given

1. **The statement list** — `agents/STATEMENTS.md`. Each statement has a neutral id `Snn`, a part
   (SLAB, STRICT, INNER, COVER), one line saying what it is for, the ids it may use, and its text.
   In HOL4 each is a boolean constant `Snn` of `delta3_stmtsTheory`; `Snn_def` unfolds it (the statement,
   universally closed).
2. **The definitions** you may unfold: `delta3_checkScript.sml` and `delta3_check2Script.sml` (the
   checker: integer functions over lists), `delta3_semScript.sml` (what they mean: real-valued
   polynomials), and everything in the pinned HOL4 (`harness/PIN.json`; its source tree may be read).
3. **What you may use without proving it**: for statement `Snn`, exactly the statements listed under
   "May use" — as hypotheses. You prove the implication; nobody has to have proved them yet.
4. **The judge** — `harness/attempt.py` (read it and `harness/judgelib.py` for what is checked).
5. **`agents/PITFALLS.md`** — seven HOL4 pitfalls found while the harness was built (about the prover, not
   about the statements). Both families get the same note.

Some statements share a text and differ only in their "May use" list; each is judged on its own.

You must NOT read: `LEMMAS.md`, anything outside `agents/` and `harness/` (except the pinned HOL4 source
tree), the other model family's directory `harness/work/<other family>/`, Claude session transcripts
(`~/.claude/`), Codex session logs (`~/.codex/`), or any `astra.log`. **Do not run `hol` or `Holmake`
yourself**: every build goes through the judge, for both families alike. Your tool calls are audited
after the run for all of this (`harness/AUDIT-BLINDING.md`).

**Some statements are false on purpose.** A false statement cannot be proved. Show it false by a
refutation (below), or report it *not yet tractable*. A claimed proof of a false statement is the one
outcome the benchmark is built to catch.

## What to submit

A complete HOL4 script. To PROVE `Snn`:

```
Theory attempt
Ancestors
  arithmetic list integer real intreal delta3_check delta3_check2 delta3_sem delta3_stmts
Libs
  intLib realLib

(* any auxiliary definitions and lemmas *)

Theorem Snn_as_constants[local]:
  Sd1 /\ ... /\ Sdk ==> Snn            (* just  Snn  when "May use" is empty *)
Proof
  rewrite_tac [Snn_def] >> ...
QED

Theorem Snn = CONV_RULE (RAND_CONV (REWR_CONV Snn_def)) Snn_as_constants
                                       (* with no "May use": EQ_MP Snn_def Snn_as_constants *)
```

The theorem named `Snn` must have EXACTLY the conclusion `Sd1 /\ ... /\ Sdk ==> <the right-hand side of
Snn_def>` ("May use" constants in the listed order), or just the right-hand side when the list is empty.

To REFUTE `Snn` (show it false), the script saves a theorem named `Snn_refuted` whose conclusion is
EXACTLY `~(<the right-hand side of Snn_def>)` — the statement alone, without the "May use" hypotheses:

```
Theorem Snn_neg[local]:
  ~Snn
Proof
  rewrite_tac [Snn_def] >> ...        (* e.g. exhibit the counterexample and evaluate *)
QED

Theorem Snn_refuted = CONV_RULE (RAND_CONV (REWR_CONV Snn_def)) Snn_neg
```

A refutation is judged exactly like a proof (the same checks below); the outcome is `refuted`.

## How to submit

- Claude family: `harness/attempt.sh Snn <script> <your-name> --family claude --model claude-opus-5-5
  --host <pod> --port <port> [--refute] [--tokens N]` (the control room gives the pod).
- GPT family: the queue (`harness/QUEUE.md`): a directory with `script.sml`, `meta.json`
  (`{"lemma": "Snn", "agent": ..., "model": "gpt-6.2-astra", "mode": "prove" | "refute", "tokens": N}`)
  and `READY`; the result comes back in the results directory.

Both go to the same judge on the same pod, under the same isolation and limits: 600 s of wall time,
1200 s of CPU per process, 6 GB of resident memory. Forbidden in a script (refused before it is built):
`cheat`, `mk_thm`, oracles, new axioms, unsafe casts, file, process, network or FFI access, loading code
(`use`, `load`) — the full list is `judgelib.DENY_RAW` / `DENY_CODE`; comments count for the first list.

## The rules of the run

- **At most 3 attempts per statement** for your family — proofs and refutations together. The judge
  does not run a fourth (`NOT JUDGED: the cap ... is reached`, nothing recorded).
- **Stop at the first judged outcome**: once a statement is `proved` or `refuted` for your family, no
  further attempt on it is accepted.
- Every attempt is logged, whatever its outcome: `proved`, `refuted`, `failed` (with the last lines of the
  build log), `timeout`, or `refused` (with the reason).
- Report at the end, per statement: proved / refuted / not yet tractable, the attempts used, and the
  tokens you used if you know them.
