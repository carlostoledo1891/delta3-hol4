# How the blinding rule is checked

hol4/delta3/harness · 2026-11-25. The rule (agents/BRIEF.md): a proving agent must not read `LEMMAS.md`, the
truth key or its sources, or the other model family's scripts. **The judge's sandbox does not enforce this.**
Reads are open in `sandbox.sb` and on the pod, and they have to be: the agents read the disk with their own
tools (Claude Code's Read/Grep/Bash; Codex's shell), outside any judge. A proof script that reads a file and
prints it into Holmake's output would also get it back through the results. So the rule is enforced in three
other ways, and checked at the end of the measurement by reading the agents' own tool logs.

## 1. Less to read

- The truth key, its sources, the planted-statement checks and LEMMAS.md are encrypted into one archive by
  `regen-key.sh` with a passphrase only the operator holds; the plaintexts are deleted (FREEZE-2.json pins
  the archive and the sha256 of every file inside). From then on there is no plaintext key on the disk.
- NOT closed by that: **Claude session transcripts on this disk** (`~/.claude/projects/…/*.jsonl`) contain the
  first key (printed by the earlier agent and the control room) and the full text of LEMMAS.md (read by the
  harness builders, including the author of this file). Because a fresh permutation does not change the
  statements' TEXTS, a reader of those transcripts can still tell true from planted by comparing texts. The
  transcripts therefore count as a forbidden path for the GPT family below. Codex session logs
  (`~/.codex/sessions/`) and `astra.log` files are forbidden for the Claude family in the same way.
- NOT closed by anything here: the public files themselves leak most of the key. Every statement named in some
  "May use" list is the TRUE one of its group (lemmas.json gives the dependencies by the true statements' ids).
  Counted on the current files: 39 of the 42 groups have a member named in some "May use" list, so 41 of the 44
  planted statements can be identified from `agents/STATEMENTS.md` and `harness/lemmas.json` alone, without
  any forbidden read. Only the three top statements' groups stay blind. The re-key now adds DECOYS
  (RUN-PROTOCOL.md) that name planted members as often as true ones in expectation; in the dry runs that
  signal identified 0 planted statements, and the residual signals (leak-check.py, aggregate only) are near
  chance; they are reported with the results.

## 2. What each family may run

- Claude agents: started by the control room with a brief that names the forbidden paths; their transcripts are
  kept by Claude Code (`~/.claude/projects/<project>/<session>.jsonl`, sub-agents in the same folder).
- GPT agents: `notes/astra-cli/run-astra.sh` — Codex `workspace-write` sandbox (writes only in its work folder,
  no network), the full event log in `<task>/astra.log`, the session id in `<task>/RUN.txt` (the session's
  rollout file is `~/.codex/sessions/YYYY/MM/DD/rollout-*-<session>.jsonl`).

## 3. The audit, at the end of the measurement (before any number is published)

```
cd ~/Projects/cert-machine/hol4/delta3/harness
# Claude family: every transcript of every session that took part (main and sub-agents)
python3 audit-blinding.py --family claude ~/.claude/projects/<project>/<session>.jsonl ...
# GPT family: each astra.log and the matching Codex rollout files
python3 audit-blinding.py --family gpt <task>/astra.log ~/.codex/sessions/2026/11/*/rollout-*-<session>.jsonl ...
```

`audit-blinding.py` reads only the TOOL CALLS in those logs (the prose cannot count: the brief itself names the
forbidden paths) and prints, per call:

- `VIOLATION` — the call names a forbidden path: `LEMMAS.md`, `hol4-lemmas`, `key.json`, `lemma_source.py`,
  `gen_lemmas.py`, `planted-results`, `delta3_plantedScript`, `README-DAY2.md`, `<private>`,
  `KEY-ARCHIVE`; and for the Claude family `harness/work/gpt`, `astra-prover/work`, `.codex/sessions`, `astra.log`;
  for the GPT family `harness/work/claude`, `.claude/`;
- `REVIEW` — a recursive read (grep -r, rg, find, ls -R, tar, cp -r, a Grep or Glob tool call) rooted at a folder
  that CONTAINS a forbidden path (the repository, hol4/delta3, the harness, notes/, the home folder, /), which
  may have read one without naming it. A person reads each REVIEW line and the call's output in the log.

Exit status 1 on any VIOLATION. A family with a violation is reported with it: its attempts on the affected
statements are marked, not silently dropped. The audit is a check on the logs we have: an agent that read a
file through a channel its log does not show (none is known) would not be caught.

Control (run-controls.py, control 9): a synthetic transcript with a Read of LEMMAS.md and an `ls harness/work/gpt`
is flagged with 2 violations; a clean one that only reads STATEMENTS.md and mentions LEMMAS.md in prose passes.
