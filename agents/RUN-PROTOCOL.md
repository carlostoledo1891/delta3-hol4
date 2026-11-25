# The run: two model families on the same statements

hol4/delta3/harness · written 2026-11-25 from the operator's decisions of 2026-11-24/25 (dialog): Claude family =
Opus 5.5 (`claude-opus-5-5`), GPT family = GPT-6.2 ("Astra", `gpt-6.2-astra`, through the Codex CLI); up to 3
attempts per statement per family, stopping early once a statement is judged. Nothing here has been run yet.

## Before the run (in this order)

1. The checker's formulation is final and the HOL pin is final (`PIN.json`; the control room decides
   -v9 or -v10 after the CakeML report). If the pin moves: rebuild HOL at it, `build-base.sh`, the Day-1
   kernel results again, the controls again.
2. `agents/BRIEF.next.md` is the brief of the run (rules below). The operator runs `bash regen-key.sh` in a
   Terminal outside any Claude/Codex session: fresh permutation from /dev/urandom, base rebuilt, every
   planted statement checked false in the kernel, the brief moved into place, the refutation control C02
   added, the truth encrypted with his passphrase, FREEZE-2.json written. Nothing is decided before this.
3. The pod: POD.md steps 1–4 (setup, `SELFTEST PASS`, runner started, `run-controls.py --host` 9/9).
   Plus the two refutation controls on the new base: `C02` refuted by a correct script → `refuted`;
   `C01` "refuted" by any script → not `refuted` (C01 is true).
4. `RUN.json` written by the control room at the start (copy `RUN.json.example`, set `start_utc` from
   `date -u`): from then on attempt.py enforces the cap for families `claude` and `gpt` on `Snn`.

## Starting the proving agents

| | Claude family | GPT family |
|---|---|---|
| model | claude-opus-5-5 | gpt-6.2-astra |
| started by | the control room (Agent tool), one agent per batch of statements | the control room, `notes/astra-cli/run-astra.sh <task-dir>` |
| gets | `agents/BRIEF.md` (v2), `agents/STATEMENTS.md`, the base scripts, read access to the pinned HOL tree | the same files, the same text |
| writes | its scripts under `harness/work/claude/<agent>/` | its task dir `work/` only (Codex `workspace-write`, no network) |
| submits | `attempt.sh … --family claude --host <pod>` | the queue (`judge-queue.py --host <pod>`, QUEUE.md) |
| may not | run `hol`/`Holmake` itself; read the forbidden paths (BRIEF) | the same (it cannot build HOL anyway) |
| judge | the same: `judgelib` on the pod, same limits (600 s wall, 1200 s CPU, 6 GB), same log | |

Both families get the statements in the same order, the same batches, and no hints beyond the brief. The
task text given to each agent is the brief plus one line naming its batch; it is saved beside the run
(`runs/<family>-<agent>-TASK.md`) and its sha256 noted in WORKLOG.md.

## The attempt cap and the early stop (enforced by attempt.py, from RUN.json)

- At most `cap` (= 3) attempts per statement per family, proofs and refutations together; a fourth is not
  run and not logged (`NOT JUDGED: the cap … is reached`).
- After `proved` or `refuted` for a family, no further attempt at that statement by that family is run.
- Controls (`C01`, `C02`) and the family `other` are exempt. Attempts before `start_utc` do not count.

## How "refuted" is checked

A refutation is a script that saves `Snn_refuted : ~(<right-hand side of Snn_def>)` — the statement
alone, closed — and is judged exactly like a proof: the text check, the isolated build, then the judge
process checks the conclusion is that negation (alpha-equal), no hypotheses, tags ⊆ {DISK_THM}, no axioms,
the base unchanged. A `refuted` on a TRUE statement would mean a kernel or judge fault: it stops the run.

## Tokens

- Claude: the Agent tool's own usage report per agent (input/output tokens), recorded by the control room
  in `runs/tokens.tsv` per agent; per attempt only if the agent passes `--tokens`.
- GPT: Codex's own count in `astra.log` ("tokens used") per session, recorded the same way; per attempt
  only if `meta.json` carries `tokens`.
Success rates are reported per statement; tokens per family as totals and per judged statement.

## What ends the run

Every statement is judged or has reached the cap for both families, or the operator stops it. Then:
1. stop the queue watcher and the runner (POD.md 6), pull the pod's log (7), delete the pod (8);
2. the blinding audit on every transcript and astra.log of the run (AUDIT-BLINDING.md);
3. the operator unlocks the key (`unlock-key.sh`), and the scoring reads attempts.jsonl against it:
   per family and part, success rates on true statements and refutation rates on planted ones with exact
   (Clopper–Pearson) 95 % intervals; **the gate: zero planted statements `proved`** — any one is reported
   first, with its script;
4. every `proved` script is read by a person (JUDGE.json `not_covered`: the token check is a filter).

## The statement list after the re-key: kernel-confirmed planted statements, and decoys

`regen-key.sh` runs `gen-statements.py` twice. Pass 1 writes every planted variant and the kernel checks each
(its counterexample instance evaluates to F and the true sibling's to T); pass 2 keeps ONLY the planted
statements the kernel confirmed (the rest are dropped; only the counts are printed — 43 of 44 in the dry runs),
draws a fresh permutation from /dev/urandom and adds DECOYS; the kernel then checks every kept planted
statement again and the re-key stops unless all are confirmed.

A decoy of lemma L has L's "For:" line, the text of one of L's originals (true or planted, drawn uniformly), and
a "May use" list with at least one PLANTED member of a dependency group (one slot is drawn among L's dependency
groups that have planted members and gets a planted member; the other slots are drawn so that, in expectation,
every member of each dependency group — true, planted or decoy — is named equally often). Lists obey:
- the true statement of L names only true statements: **the real slab/inner/cover chain never depends on a
  decoy** (nor on a planted statement);
- a planted statement names only true statements or decoys (never a planted one), so it stays false;
- a decoy names at least one planted statement, so it is TRUE (vacuously).
Every planted and decoy member of a dependency group is named at least once. At most 3 decoys per group
(`D3_DECOYS_PER_GROUP_MAX`); the dry runs gave 164 statements (42 true, 44 → 43 planted, about 78 decoys).

What the public files still give away, measured in the dry runs against the key (aggregate only,
`leak-check.py`): picking the most-named member of a group finds the true one about as often as chance
(10–15 of 39 groups, chance 11.7); "never named while its true sibling is named" now identifies 0 planted
statements (41 of 44 before decoys); the most repeated text is the true one in 22–23 of 42 groups (chance
20.7); the lists of true statements name members that are named somewhat less often than the others' lists do
(mean 10 against 11.5) — a weak signal, said with the results.

**How decoys are scored** — four classes, reported separately, each per family with exact (Clopper–Pearson)
95 % intervals:
- **T** true originals: success = `proved`. These are the benchmark's main numbers.
- **P** planted originals: success = `refuted`. **Gate: zero `proved`.** A `proved` here stops the run.
- **D-planted** decoys whose text is a planted statement's: TRUE, and provable only by deriving a contradiction
  from their planted hypotheses (the conclusion is false, the other hypotheses are true), i.e. at least as hard
  as refuting one planted statement. Success = `proved`; reported beside P as "refutation inside a proof".
- **D-true** decoys whose text is a true statement's: TRUE; provable by contradiction, or WITHOUT one when the
  planted hypothesis is stronger than the true one it replaces (some planted variants are strengthenings) or by
  proving the missing dependency inline. These can be easier than refuting: counted separately and never merged
  into T or P.
A `refuted` on a T or D statement is impossible unless the kernel or the judge is at fault: it stops the run.
Decoys are marked in the encrypted key (`role`, `text_of`, `planted_hyps`).

## Accepted proofs: a fresh rebuild and a reader (the judge gap)

An attempt judged `proved` or `refuted` COUNTS only after both:

1. **A fresh rebuild** in a new, separate process, from the submitted script alone, against the frozen base:
   ```
   cd ~/Projects/cert-machine/hol4/delta3/harness
   python3 rebuild-accepted.py --all          # or --seq <n> ...; one at a time on this Mac, under sandbox.sb
   ```
   It must print `REBUILT` (the same decision, the same script bytes); `MISMATCH` means the attempt does not count
   and is investigated. Result per attempt in `accepted/REBUILDS.tsv`.
2. **A person reads the script** (`accepted/<seq>-<family>-<id>-<n>/script.sml`) and ticks, in
   `accepted/<…>/READ.md`, name and date:
   - [ ] no deny-list hit, and no near-miss spelling of one (aliases, `open` of a structure, string building);
   - [ ] no ML outside the theorem/definition blocks and the tactics, except small helper functions over terms
         and tactics (no top-level `val _ = …` side effects, no references, no exceptions swallowed at top level);
   - [ ] no `mk_thm`, `mk_oracle_thm`, `disk_thm`, `Thm.` or `Tag.` internals, `Feedback`/`Globals` tricks, no use
         of the compute primitive beyond `EVAL`/`cv_eval` on the statement's own terms;
   - [ ] no `Theory` / `export_theory` / `adjoin_to_theory` / `new_theory` / `Ancestors` beyond the brief's /
         `loadPath` / `use` / `load` tricks; the `Theory attempt` header is the only theory;
   - [ ] the theorem named in INTERFACE.json is the one saved, with the conclusion the judge reports (judge.out);
   - [ ] nothing reads or writes files, the network or the environment;
   - [ ] the proof's idea makes sense for the statement (a proof that relies on something unexplained is flagged).
3. **The independent replay** (built by another agent, not here) reads the same folders. The interface, one
   folder per accepted attempt: `script.sml` (as submitted), `theory/attemptTheory.{sml,sig,dat,uo,ui}` (the
   fresh rebuild's theory), `INTERFACE.json` (statement id, theorem name `<id>` or `<id>_refuted`, theory name
   `attempt`, mode, dependency constants, the expected conclusion rule, the base folder and digest, the freeze
   digest, the HOL commit), `rebuild.json` (the judge's facts on the rebuild).

## Known limits of the comparison (said with the numbers)

- Before the decoys, 41 of the 44 planted statements could be identified from the public files alone
  (every "May use" list named the TRUE statement of its group). The decoys remove that signal; the residual
  signals measured in the dry runs are listed above and are reported with the results.
- The harness builders (Claude agents) have read LEMMAS.md; their transcripts are on this disk.

## Ruling of 2026-11-25 13:29 UTC (the operator, dialog), before the key is unlocked: refutations of D-planted decoys

A D-planted decoy's TEXT is a planted statement's text, so it is false and refutable (a refutation proves the negation of
the text alone, without the "May use" hypotheses), while the decoy itself is vacuously provable. So a `refuted` on a
D-planted decoy is CORRECT: it does not stop the run, and it is reported in its own column, "text refuted", beside
"proved" for that class (each with its Clopper–Pearson interval). The stop rule stays for T and D-true statements (a
`refuted` there still means a kernel or judge fault). The early stop is unchanged: a family that refutes such a decoy
first cannot then prove it, and the report says so. (The case that raised it is in hol4/delta3/WORKLOG.md, outside the agents’ tree.)

## Ruling of 2026-11-25 13:47 UTC (the operator, dialog): who reads the accepted scripts

Step 2 of "Accepted proofs" ("A person reads the script") is done by AGENTS ONLY: two independent readers, one Claude
(Opus 5.5) and one GPT-6.2 (Astra), each reads every accepted script against the seven-item checklist alone, without the
other's notes, and writes its ticks in accepted/<…>/READ-claude.md and READ-astra.md. A script counts when both readers
pass it; any flag is reported with the script. The report says plainly that no human read the scripts.

## Ruling of 2026-11-25 13:47 UTC (the operator, dialog), before the key is unlocked: the gate judges what the kernel judged

Found by claude-b2 (WORKLOG 13:41): a planted statement may name a D-planted decoy, whose constant is its (false) text,
so its judged goal "hypotheses ==> text" is vacuously TRUE and has a correct kernel proof. Scoring therefore classifies
every statement by the truth of what the kernel judges, computed from the key (each text's truth is known): the GOAL
"hypotheses ==> text" for a proof, the TEXT alone for a refutation. **The gate: zero `proved` on a statement whose goal
is false, and zero `refuted` on a statement whose text is true** — either one means a kernel or judge fault and is
reported first. Planted statements whose goal is vacuously true form their own class ("planted, vacuous goal"; proved =
correct, refuted = correct), reported beside P, D-planted and D-true, each with its exact interval. With the 13:29 ruling
this replaces the earlier wording "A `proved` here stops the run" and "a `refuted` on a T or D statement ... stops
the run".

## Ruling of 2026-11-25 16:19 UTC (the operator, dialog), before the key is unlocked: style-only reader flags

The two agent readers differ only on items 2 and 4 of the checklist (top-level `open` of theory structures and
top-level bindings of theorems, terms and tactics; two scripts adding the pinned theories real_sigma and pred_set to
Ancestors). Ruled: a flag on item 2 or 4 alone does NOT exclude an attempt when the other reader passed it and neither
reader flagged item 1, 3, 5, 6 or 7. The report lists every such script with both readers' reasons.
