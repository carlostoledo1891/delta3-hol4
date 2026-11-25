# hol4/delta3 — work log, Day 1 (environment and risk check)

All times UTC, read from `date -u` on the pod or the Mac at the moment of writing. The pod: a rented
container, 8 vCPU, 64 GB limit, Ubuntu 24.04.3, created 2026-11-24 20:06:32.

## 2026-11-24

- **20:08** Read the operator's plan in full. Pod reachable: 8 CPUs, cgroup `memory.max`
  64,000,000,000 bytes, 40 GB disk, `git gcc make curl` present, no Poly/ML.
- **20:08** Tags listed with `git ls-remote`: Poly/ML releases up to `v5.9.2` (commit 45575540…); HOL4
  `trindemossen-2-v4 … v9`; the newest, `trindemossen-2-v9`, is an annotated tag on commit 652d1f0a….
  Chosen: Poly/ML v5.9.2 from source, HOL4 `trindemossen-2-v9`.
- **20:09:07** `setup.sh` started on the pod (apt packages, Poly/ML configure/make/compiler/install, HOL
  smart-configure, `bin/build`), each step timed with GNU time into `logs/setup-times.tsv`.
- **20:12:29** Poly/ML built and installed (configure 14.7 s, make -j8 166.7 s, compiler 10.0 s).
- **20:12:43** HOL configure (31.5 s), then `bin/build` started.
- **20:12–20:20** While HOL built: read, in a separate read-only checkout of the same tag (`/root/hol-read`),
  `src/num/theories/cv_compute/README`, `Manual/Description/libraries.smd` (section "Computation with
  First-Order Terms — cv_computeLib and cv_transLib"), `help/Docfiles/cv_transLib.*.smd`,
  `src/num/theories/cv_compute/automation/{cv_typeScript,cv_primScript,cv_stdScript,cv_transLib}.sml`,
  `examples/cv_compute/cv_eval_exampleScript.sml`, `automation/selftest.sml`.
  Finding: `:rat` IS translated out of the box (`from_rat`, `cv_rat_add`, `cv_rat_mul`, `cv_rat_lt`, each
  add/mul normalising by `cv_gcd`); `:int` is translated; `:real` is not.
- **20:17** `export.js` written (the data file for one slab + a BigInt mirror of the HOL4 function). On the pod
  (node v18.19.1) the mirror accepts the genuine smallest slab and refuses the three forged copies, each by
  its intended rule (claim: the scalar test; negmu: the multiplier sign; bound: the dominance test).
- **20:19** `delta3_checkScript.sml`, `delta3DataLib.{sig,sml}`, `slab.template`, `gen.sh`, `Holmakefile` written.
- **20:25:44** The cv libraries appeared in HOL's `sigobj` (the parallel core of the build had finished);
  the rest of `bin/build` was still running. From here the check was built against `sigobj` while the build
  went on, so the first timings below were taken on a busy machine and are not the ones reported.
- **20:26** `delta3_check` first build: 25 of 26 `cv_trans` calls went through; `dd_rows` stopped with
  "failed to prove precondition" — it destructured the pair returned by `rowsum`. Folded the row sum and the
  diagonal entry into one integer (Σ_j d_j|G_ij| − 2 d_i G_ii ≤ 0). Rebuilt: all 26 translated, 15 s.
- **20:27:14** First try of the slab theory failed to compile: `reduceLib.num_compset` is a value, not a
  function. Looked it up (`src/num/reduce/src/reduceLib.sig`, `src/compute/src/computeLib.sig`) and used
  `computeLib.add_thms … (computeLib.copy reduceLib.num_compset)`.
- **20:29:10** **First kernel theorem: `slab_check … ⇔ T` on the smallest slab, `cv_eval` 1.146 s.** The
  whole Holmake build took 95 s and 1.88 GB: Holmake had written a 1.9 GB HTML page of the data constants
  (`.hol/docs/delta3_slabCTheory.html`). Found the switch in `Manual/Description/modern-syntax.smd`:
  `Theory name[no_sig_docs]`. With it the build takes 23 s.
- **20:29:07** `bin/build` finished: 951.56 s, "Hol built successfully".
- **20:33** Second run: the three forged copies each `⇔ F`. `delta3_breakdown` stopped: "Translation of
  mkrat needs $& : :num -> rat". Rewrote every rational literal as `rat_of_int <literal>`. The dominance
  test over `:rat` then ran: 22.1 s against 0.73 s in integers.
- **20:38:40** Third run (first complete one): the four slabs T (1.20, 1.33, 1.57, 1.17 s), the three forged
  copies F.
- **20:39** `delta3_bareiss` written. First result was F after 24.5 s: my function tested its fuel before the
  empty matrix, so it returned F after 147 good pivots. Corrected the order of the two tests: T in 25.2 s.
- **20:40** JavaScript baseline on the idle pod: the mirror in `export.js` 194, 175, 181, 176, 180 ms;
  `verify.js` alone on the smallest slab 1.0, 1.1, 1.0 s; all five certificates 3.7 s, THEOREM A VERIFIED.
- **20:41:20 → 20:46:30** **Final clean run of `run-day1.sh`** (it deletes `.hol` first): the numbers in
  `README.md` are from this run. Each theory also writes its theorem to `<name>.theorem.txt`.
- **20:46–20:51** Source searches recorded in `logs/hol-source-search.txt`; the three `diff`s of the forged
  data against the genuine in `logs/red-diffs.txt`.
- **20:46 → 21:01** `parse_bench.sml`, first run (10/20/40/80/147 rows of the witness matrix through
  HOL4's term parser): 0.222 s, 1.021 s, 16.891 s for 55, 210 and 820 integers; the 80-row case (3,240
  integers) had not finished when the 900 s timeout stopped it, at 6.9 GB resident. I had taken it for dead
  at 20:51 because `ps -C hol` printed nothing; it was running.
- **20:52 → 21:07** Second run at 10/20/40/80 rows, output to `logs/parse-bench.raw`: 0.129 s, 0.711 s,
  19.653 s; the 80-row case again unfinished at the timeout. Both runs shared the machine with each other
  and with the next measurement.
- **20:54 → 21:00** `eval_bench.sml`: one row of the dominance test by `cv_eval` (0.160 s) and by
  `computeLib.EVAL` (369.596 s), same value.
- **21:07:10** `collect.sh` on the pod: logs gathered, `SHA256SUMS` over 66 files. Bundle `d3-home.tgz`
  (sha256 72819aac…9b5e on both ends) copied home; all 66 hashes verified at home. The only script whose home
  copy differed was `parse_bench.sml` (its list of row counts was edited on the pod); the pod's version is
  the one kept. The certificates and the four JavaScript files on the pod have the same sha256 as the
  repository's, and the certificates the sha256 the ledger records.
- **21:07:40 → 21:12:20** Replay of the bundle in a fresh directory on the pod, generated files deleted
  first: same ten results; 36 of the 66 files regenerated byte-identical (every data file, generated script
  and theorem file); the four that differ are the timing files; the other 26 are logs that the replay did not
  produce (`logs/replay-check.txt`).
- **21:13** `examples/vector` (vector, matrix, determinant) builds at the pinned tag: 37.6 s
  (`logs/vector-build.txt`).
- **21:14** `README.md`, `PINS.json` and this log finished at home. Nothing committed, nothing sent.

# Day 2b — the judge in a sandbox, the queue, the re-key, the inner certificate, S33 (agent claude-opus-day2)

Times UTC from `date -u` on the Mac. Written by a Claude agent (model claude-opus-5-5) that continues the Day-2
agent's work. This agent built the harness and has READ LEMMAS.md: its own attempts at S33 are NOT a blind
measurement (said in every one of its log lines, field `notes`).

## 2026-11-24, before this agent (recorded now, as found)

- **22:03–22:21** The six harness controls (seq 1–6) and four attempts at S33 by "claude-fable-day2"
  (seq 7–10: two failed, two timed out at 600 s) ran **UNSANDBOXED**: no sandbox-exec, no memory limit, the
  Day-2 judge (text deny-list + kernel facts). They stay in attempts.jsonl as they are.
- Why they failed (read from harness/work/claude/S33-1..4): attempts 1–2 stopped on tactic failures in the
  finite-sum lemmas over realTheory's `sum (m,n)` (`sum_cmul_r`, `dsum_diag4`); attempts 3–4 hung until the
  600 s limit — attempt 4 at `dot_acc`, whose induction hypothesis `dot acc xs ys = acc + dot 0 xs ys` is a
  rewrite whose right side contains an instance of its left side: `simp`/`rw` use the assumptions, so they
  loop (0 + dot 0 xs ys → dot 0 xs ys → …); attempt 3 inside `wdd_core`.

## 2026-11-24/25, this agent

- **23:13** Read the plan (PLAN v3), README, WORKLOG, LEMMAS.md, agents/, harness/.
- **23:15–23:30** Sandbox by experiment (scratchpad builds of the correct control, `sandbox-exec`):
  a profile denying all writes except the build directory makes Holmake fail with EPERM; bisecting by
  directory found **/private/var/tmp**: Poly/ML's `OS.FileSys.tmpName` ignores TMPDIR on macOS and creates
  `/var/tmp/MLTEMPxxxxxx` (string in libpolyml), and HOL's `tautLib` (HolSatLib) writes its DIMACS file and the
  solver's answer next to it with a suffix; without them `TAUT_PROVE` fails while loading intLib. Allowed:
  that exact name pattern, nothing else in /var/tmp. Network denial alone: no effect on HOL. Then
  `process-exec` restricted to HOLDIR, the Poly/ML prefix, the build directory and /usr/bin/nice; signals only
  within the sandbox; `mach-lookup` and POSIX shared memory denied — the correct control still builds.
  Profile: harness/sandbox.sb (each allowance commented).
- **23:28–23:30** Task 3 (inner certificate) in `inner-check2/` (see below).
- **23:36–23:38** First run of the ten controls under the sandbox (seq 11–19). **Mistake:** another session's
  Holmake (the Astra H1 job) was running at the same time — two Holmake runs at once on the Mac, against the
  rule. After this, attempt.py itself waits until no other HOL build runs on the Mac and holds a lock for its
  own (field `waited_for_mac_s`). Control 7 was miscounted by the runner (it read each log twice: 10 DENIED
  for 5); corrected and re-run at 23:42 (seq 20): PASS. The judge's code was still being written during these
  runs (field `judge_code` differs); all controls are re-run on the final code (below).
- **23:43–23:46** regen-key.sh dry run on a throwaway copy (below).
- **23:54 → 00:30** S33 attempts 5–… by claude-opus-day2 (below).
- **00:13–00:15** Queue test (below).

### Task 3 — the inner certificate through check2 (inner-check2/, 2026-11-24 23:28–23:30)

The four theories generated from `inner.template` (Day 2) against `harness/base` (delta3_check2Script.sml as
frozen), data `day2/*.d3` copied unchanged (sha256 a9c327f6… inner, ff616e4b… red_c0, d289013e… red_kap,
65c412df… red_radius); `inner-check2/run.sh`, one Holmake each at nice 10, `/usr/bin/time -l`:

| theory | kernel theorem | cv_eval s | build s | peak resident |
|---|---|---|---|---|
| delta3_inner | `inner_check … ⇔ T` | 1.528 | 35.30 | 1.22 GB |
| delta3_inner_red_c0 (c[0] := −(c[0]+1)) | `⇔ F` | 1.155 | 39.34 | 1.20 GB |
| delta3_inner_red_kap (κ := −2⁻¹⁰⁰) | `⇔ F` | 1.067 | 29.52 | 1.23 GB |
| delta3_inner_red_radius (r_in := 2/5) | `⇔ F` | 0.973 | 21.35 | 1.32 GB |

Each theorem: oracles [DISK_THM], no axioms, no hypotheses (`inner-check2/results.tsv`, `*.theorem.txt`).
The other session's independent inner check (astra-hol4-inner) was not read.

### The judge (task 1, and decision (A))

- Final judge code digest `judge_code` in JUDGE.json; JUDGE.json lists what changed after the freeze (the
  freeze covers statements, lemmas.json, base scripts and BRIEF; the judge's code is not frozen) and what the
  isolation does NOT cover (an attempt's ML runs inside the processes that write the theory file and the
  judge's answer; HOL trusts its disk format; deliberate forgery is stopped only by the identifier deny-list
  and by reading proved scripts; the fix would be replaying a proof trace — the pinned tree has a draft PFT
  format, src/postkernel/prooftrace).
- 00:35–00:37: all controls on judge code 6b38e264…: 9/9 + memory limit control PASS; queue test PASS.
- 00:38–00:42, decisions (B)/(4) of the control room: refute mode (`--refute`, theorem `<id>_refuted` =
  `~statement`, outcome `refuted`), the run cap from RUN.json (≤ 3 attempts per statement per family, none
  after proved/refuted), the pin in ONE file (PIN.json: attempt.py refuses another local HOL commit, the pod
  client refuses a pod at another commit, setup-pod.sh builds the pod at it, regen-key.sh rebuilds the base
  only at it). The audit also lists (REVIEW) tool calls naming Holmake/bin/hol outside the judge.
- The pod path (runner.py, jail.c, client.py, setup-pod.sh, push.sh, POD.md) is written and syntax-checked,
  NOT run: no host was given. jail.c has not been compiled (Linux only).

### Re-key (decision (B)): regen-key.sh and unlock-key.sh

- 23:43–23:46 first dry run on a throwaway copy (scratchpad, deleted after): fresh permutation, base rebuilt,
  planted checks **43/44 OK — the same 43/44 as the first freeze**: one planted statement's counterexample is
  not settled by the kernel evaluation (its line reads CHECK, in the first freeze's planted-results.tsv too; which
  one was not looked at). The script requires at least the first freeze's count; that one needs a check by hand
  after unlock. Encryption, in-memory verification 8/8, FREEZE-2.json, deletion; unlock-key.sh decrypts and
  checks every sha256; a one-byte change to the archive is refused.
- 00:43–00:46 second dry run on a fresh copy with the run's additions: BRIEF.next.md moved into place, the
  refutation control C02 added; then in that copy: C01 proved under FREEZE-2.json, "refuting" C01 → failed,
  refuting C02 → refuted; the cap: three attempts at S01 by family gpt logged, the fourth NOT JUDGED.
  Copy deleted, no staging directory left in $TMPDIR. Nothing printed which statements are planted.
- The generator has one planted variant per lemma (two for two lemmas), all used: no choice to draw.
- **The first freeze (22:03:28Z) is superseded for the measurement**: its key was printed into Claude session
  transcripts on this disk. Moreover LEMMAS.md (the true statements' texts) is in this agent's transcript and the
  earlier agents', and a permutation does not change texts: blinding against a reader of the transcripts rests on
  the audit (AUDIT-BLINDING.md), not on the encryption.
- **Structural leak, found from public files only**: every "May use" list names the TRUE statement of its group,
  so 41 of the 44 planted statements are identifiable from agents/STATEMENTS.md and harness/lemmas.json without any
  forbidden read (39 of 42 groups have a member named in some May-use list; only the three top statements' groups
  stay blind). A re-key keeps this. Proposal for the control room: list dependencies by GROUP rather than by id —
  e.g. give each statement's hypotheses as "the true member of group g", realised by adding, for every planted
  sibling P of a used lemma, a decoy consumer statement that lists P under "May use" (P false makes it vacuously
  true and provable only by refuting P), so that being named in a May-use list no longer marks a statement true.
  Not done: it changes the benchmark and is the operator's decision.

### S33 (task 4) — agent claude-opus-day2, model claude-opus-5-5, NOT blind

| attempt | seq | outcome | what stopped it |
|---|---|---|---|
| 5 | 21 | failed (15.5 s) | `dsum_sub`: `irule SUM_SUB'` — the higher-order match returns the η-short `f i`, the goal has `\j. f i j` |
| 6 | 22 | timeout (300 s, 3.7 GB) | `dd_core`: REAL_ARITH eliminates `abs` inside a sum's lambda and does not come back |
| 7 | 24 | failed (16.2 s) | `gram_nonneg`: the variable `K` parses as the K combinator in tactic quotations |
| 8 | 25 | failed (17.3 s) | `roi_abs`: an assumption order slip |
| 9 | 26 | **proved** (13.9 s, 13.3 s CPU, 0.53 GB) | — judge: EXACT true, HYPS 0, ORACLES DISK_THM, no axioms |

Between attempts 6 and 9 the agent used scratch builds of script prefixes and an interactive HOL session to
locate failures (said in each log line's `notes`); every full S33 build is a judged attempt. The proof
(`harness/work/claude/S33-opus-src/S33.sml`, sha256 28f4da8a…, 500 lines) goes lists → index functions over
`count n` (real_sigma's sum), proves the unweighted core (Σ_j |H i j| ≤ 2 H i i ⇒ zᵀHz ≥ 0, by the AM-GM
pointwise bound and symmetry), the weighted form with H = dGd, z = x/d, and the Gram part as a sum of squares.
**The list/int formulation did not have to change**: what resisted were tactic pitfalls, which also explain the
four earlier attempts: (1) simp/rw use the assumptions, and an accumulator lemma's induction hypothesis
(`dot acc xs ys = acc + dot 0 xs ys`) loops; (2) REAL_ARITH on goals with `abs` under a binder hangs — every sum
must be generalised to a variable first; (3) rewrite_tac matches first-order: linearity over lambdas needs simp
or explicit instantiation; (4) `K` (and other constant names) as variables break quotations; (5) rewriting with
EQ_SYM_EQ loops; (6) some library theorems (real_of_int_le, real_of_int_num) are stored with free variables and
cannot be Q.SPECL'd; (7) real_sigma's `sum` is the constant `Sum`. Suggestion, not a change made: a brief for the
proving agents that names such pitfalls would help both families equally; whether to give it is the operator's
call (it changes what is measured). The reshape allowed by decision 1 is not needed for S33.

### The upstream lemma (task 5): upstream/

`upstream/diagdomScript.sml` (theory `diagdom`, only arithmetic/pred_set/real/real_sigma): DIAGONALLY_DOMINANT_PSD
and DIAGONALLY_DOMINANT_PD (weighted, textbook row condition Σ_{j≠i} d_j|A_ij| ≤ (<) d_i A_ii), PROVED, built in
7.8 s; upstream/README.md has the statements and where in the tree they would belong. The matrix (`real['N]['N]`)
corollary for examples/vector is a plan, not written.
- **00:46–00:49** Final control run on the final judge code (JUDGE.json `judge_code` 38db38e6…): 9/9 counted
  PASS, memory limit control PASS, refutation control 11 (refuting the true C01 fails) PASS; queue test (seq 47)
  proved. Control 12 (refuting C02) needs the re-keyed base: it passed in the second dry run. JUDGE.json rewritten
  with the final hashes.
- Not done here (on purpose, decisions (2)/(3)): regen-key.sh for real (the operator's, LAST, after the
  formulation and the pin are final); any HOL rebuild at -v10; any pod run. RUN.json is not written (the control
  room writes it at the start of the run).

## 2026-11-25, the control room's four further decisions (01:00–01:20 UTC)

1. **Decoys** (`harness/gen-statements.py`, public code; run by regen-key.sh). Each lemma's group gets up to 3
   decoys (`D3_DECOYS_PER_GROUP_MAX`): the "For:" line of the lemma, the text of one of its originals (uniform),
   a "May use" list with one slot forced to a planted member and the others drawn so that every member of each
   dependency group is named equally often in expectation; every planted and decoy member of a dependency group
   named at least once. True statements name only true ones (the real chain never touches a decoy); planted ones
   name only true ones or decoys (they stay false); every decoy is true (a false hypothesis). Exact balance was
   tried first (quotas, then exact expectations without a cap) and is not possible here: leaf groups cannot have
   decoys, and balancing them exactly needed 9,261 decoys; the cap keeps the list at ~160 statements and leaves
   4–5 groups only approximately balanced. Scoring classes T / P / D-planted / D-true (RUN-PROTOCOL.md).
   (b) holds for D-planted decoys (conclusion false ⇒ only a contradiction from the planted hypotheses proves it);
   NOT for D-true decoys (provable without refuting when the planted hypothesis is a strengthening, or by proving
   the dependency inline) — counted separately.
2. **Only kernel-confirmed planted statements**: two generator passes; pass 1's kernel check confirms 43 of 44;
   pass 2 keeps those 43, and the re-key refuses unless all kept ones check again.
3. **The judge gap**: `harness/rebuild-accepted.py` rebuilds every accepted attempt in a fresh process from its
   script alone against the frozen base and judges it again (tested 01:09: S33 seq 26 and control seq 1 →
   REBUILT); the reader's checklist and the replay interface (one folder per accepted attempt:
   `accepted/<seq>-<family>-<id>-<n>/{script.sml, theory/, INTERFACE.json, rebuild.json}`) are in RUN-PROTOCOL.md.
   The independent OpenTheory replay is another agent's; not built here.
4. **agents/PITFALLS.md**: the seven HOL pitfalls, one example each, nothing about which statements are true;
   referenced from agents/BRIEF.next.md; frozen with FREEZE-2 (freeze.PUBLIC2 adds it and gen-statements.py).

**Dry run 3** (01:13–01:18, throwaway copy, deleted; passphrase a throwaway; printed counts only):
pass 1: 164 statements, kernel confirms 43 of 44 planted, 1 dropped; pass 2: **162 statements (42 true, 43
planted, 77 decoys: 41 with a planted text, 36 with a true text)**, 43/43 planted confirmed, archive of 11 files
verified, FREEZE-2.json written; then in the copy C01 proved, "refuting" C01 failed, refuting C02 refuted, the
freeze held. leak-check (aggregate, against the key): most-named member is true in 9.9 of 39 groups (chance
11.9); "never named while the true sibling is named" identifies 0 planted (41 before); the most repeated text is
true in 18.8 of 42 groups (chance 20.8); true statements' lists name members named 10.6 times on average against
11.5 for the others (weak). Decoy members are named less (2.2 against ~3.1), so a decoy can be told from an
original somewhat more often than chance; that does not tell true from planted.
- **01:18–01:23** Controls on the final judge code 865705a7…: 1–6 PASS (seq 48–53), 9 PASS; 7, 8 and the extras
  were interrupted (another session's HOL build, hol4/delta3/replay, took the Mac and attempt.py waits; I
  stopped my waiting run). judgelib.py and sandbox.sb have not changed since the full 9/9 run at 00:46–00:49.
  JUDGE.json rewritten. regen-key.sh NOT run for real; no pod run; nothing sent.

## 2026-11-25, the judge pod (d3jbvgoxmzuvs2, <judge-pod>; 16 vCPU / 128 GB, Ubuntu 24.04.3, kernel 6.8.0-147)

- **01:31** Reachable; Python 3.12.3, gcc, unshare, setpriv present. **01:32** first setup start died at once: Day 1's
  setup.sh times every step with /usr/bin/time, absent on this image (setup-pod.sh now installs `time` first).
- **01:34:06 → 01:55:41** setup-pod.sh at the pin (-v9, 652d1f0a…): apt 10.7 s, Poly/ML configure 12.3 s, make 155.5 s,
  compiler 9.7 s, install 0.6 s, HOL configure 32.6 s, **HOL bin/build 952.4 s** (peak 1.81 GB), base, jail compiled,
  16 slot users judge0–judge15; selftest PASS (connect EACCES, three writes EACCES, listener saw 0); probe:
  **Landlock ABI 4 on; no network namespace** (the container refuses unshare -n), so seccomp is the network barrier.
- **-v10 built beside it**: tag `trindemossen-2-v10`, commit **9783a49979c94c401ff8c0e51b2eefae7ea95ae3** (annotated tag
  object 45e470aa…, from `git ls-remote` on the pod), in /root/work-trindemossen-2-v10/HOL with the same Poly/ML
  (pod/build-hol-alt.sh): configure 33.1 s, **bin/build 852.5 s** (peak 1.27 GB), done 01:52:45 (times.tsv there).
  Not used: PIN.json still says -v9. Tag -v11 also exists.
- **01:56:20** runner started, 16 slots. **01:56–01:59** first control run through the pod (seq 54–63): every build failed
  in 0 s — Holmake tried to write `.hol/make-deps/delta3_checkTheory.sml.d` in the base, which the slot user may not.
  The Mac's base had those files from the unsandboxed Day-2 controls. Fix: a warm-up build against the base as root
  right after the base build (setup-pod.sh and build-base.sh); done on the pod at 02:00.
- **02:00:47 → 02:07:11** controls through the pod (seq 64–73), judge code 61bbe80e…: **9/9 counted PASS** — 7: five
  routes DENIED (EACCES from Landlock, the shell's redirect fails), no file on the pod; 8: connect EACCES, the pod's
  listener saw only the positive control — plus memory limit (1.13 GB, killed) PASS and refuting C01 PASS. C02 needs
  the re-keyed base.
- **02:08–02:09** rebuild-accepted.py --host: seq 1 (C01) and seq 26 (S33) **REBUILT** on the pod (13.6 s for S33);
  the theory files come back (`accepted/*/theory/`) for the replay interface.
- **02:09:18** queue watcher started against the pod (pid in notes/…/astra-prover/work/watcher.pid, 8 in parallel);
  **02:09:29 → 02:10:20** submission queue-test-pod-c01 → seq 74 proved, host <judge-pod>.
- Left RUNNING: the runner on the pod and the watcher on the Mac (the benchmark uses them).

## 2026-11-25, the package moved to HOL trindemossen-2-v10 (operator's decision; 02:13 UTC →)

- **PIN.json** → `trindemossen-2-v10`, commit 9783a49979c94c401ff8c0e51b2eefae7ea95ae3, with `hol_dir_mac`
  (~/Projects/hol4-toolchain/HOL-v10) and `hol_dir_pod` (/root/work-trindemossen-2-v10/HOL); the -v9 pin kept under
  `previous` with the reason. Every consumer reads it: attempt.py (HOLDIR default; a pod attempt needs no HOL on the
  Mac), pod/client.py (commit), pod/runner.py (HOL dir), setup-pod.sh/push.sh (build or reuse HOL there; PIN.json
  copied to the pod), build-base.sh (pinned HOL, clean rebuild, commit checked), regen-key.sh (HOLDIR defaults to
  the pinned Mac folder, any other commit refused).
- **02:14–02:16:41** pod: runner stopped, push.sh: base rebuilt clean against -v10 + warm-up (13 make-deps files),
  selftest PASS, info: HOL 9783a499…; **02:17:10** runner restarted, 16 slots, HOL from PIN.json.
- **02:17:23–02:24:52** through the pod at -v10, judge code 21f9db83…: controls **9/9 PASS** + memory limit PASS +
  refuting C01 PASS (seq 75–84); rebuild-accepted seq 1 and 26 on the pod: **REBUILT, REBUILT** (S33 13.3 s).
- **Mac -v10 HOL** (harness/install-mac-hol.sh → ~/Projects/hol4-toolchain/HOL-v10, shallow clone at the tag,
  Homebrew Poly/ML 5.9.2, -v9 folder untouched): the first two starts stopped in configure (state T: a background
  poly touched the terminal — SIGTTIN/SIGTTOU), with or without stdin from /dev/null; started a third time in its own
  session (no controlling terminal) at ~02:27; bin/build running at nice 10 under caffeinate.
- **02:45:27** Mac -v10 HOL built (bin/build 1142 s, configure 18 s). **02:46:11–02:49:09** full re-key dry run at
  -v10 on a throwaway copy: pass 1 confirms 43 of 44 planted, pass 2 162 statements (42/43/77), 43/43 confirmed,
  archive 11/11 verified, FREEZE-2 written; then C01 proved and C02 refuted under it; freeze held. Copy deleted.
- **02:49–02:50 FREEZE** (the operator's word): watcher stopped (queue/STOP), pod runner stopped, pod records pulled
  (pod-records-2026-11-25/, sha256 4762356321ce2d75… on both ends), no process of this agent left. FROZEN-2026-11-25.md.

## 2026-11-25, resumed after the freeze: the no-passphrase work (Claude agent, 10:06 UTC →)

Scope: (1) rebuild at -v10 on the Mac the two pieces still built at -v9; (2) the upstream lemma as a ready-to-open
HOL4 PR (not opened); (3) the public repository's draft (not created). regen-key.sh not run, the passphrase not asked
for; harness/base, PIN.json, the queue and the pod untouched; nothing committed, pushed or sent.

- **10:10:03** no Holmake/hol/buildheap and no `bash … regen-key.sh` running (two Astra R(3,10) sessions running,
  load ~5 on 8 cores; battery 62%, discharging). HOL-v10 at 9783a499… (= PIN.json), tree clean.
- **rebuild-v10/** (new; inner-check2/ and upstream/ left as the -v9 records): copies of the sources byte for byte;
  inner-check2 builds against a private `rebuild-v10/base` (delta3_check + delta3_check2 only, cmp-checked equal to
  harness/base's scripts), so harness/base, which regen-key.sh rebuilds at the pin, is never touched. `run.sh`: clean
  builds, one Holmake at a time, nice 10, /usr/bin/time -l; refuses to start a step while any HOL process runs and
  YIELDS to the re-key (a running step is killed if a `bash … regen-key.sh` process appears, then waits and restarts).
  `upstream-show/` prints the two theorems with their tags.
- **10:10:08–10:12:30** all seven steps exit 0, no yield: base 17.5 s (0.36 GB); delta3_inner 35.0 s (1.20 GB,
  cv_eval 1.290 s) **⇔ T**; red_c0 28.4 s **⇔ F**; red_kap 24.2 s **⇔ F**; red_radius 21.1 s **⇔ F** (cv_eval
  0.903–1.031 s, peak ≤ 1.47 GB); all four `oracles [DISK_THM] axioms [] hyps 0`. diagdom 4.0 s (0.25 GB; HOL's
  theory time 0.525 s): **DIAGONALLY_DOMINANT_PSD, DIAGONALLY_DOMINANT_PD**, `oracles [DISK_THM] axioms [] hyps 0`.
- **Against -v9**: the four inner `*.theorem.txt` byte-identical; the four build logs identical apart from the
  D3TIME timing lines; the two upstream statements identical to the -v9 text in upstream/README.md, the generated
  theory doc body identical, the build log identical apart from the time line. Times: -v9 inner 35.3 / 39.3 / 29.5 /
  21.4 s (cv_eval 1.528 / 1.155 / 1.067 / 0.973 s), -v10 35.0 / 28.4 / 24.2 / 21.1 s (1.290 / 1.031 / 0.903 /
  0.925 s); same order of magnitude, both on a loaded Mac. Table: rebuild-v10/compare.tsv; times rebuild-v10/times.tsv.
- **10:23:4x — RULE BROKEN, by this agent, for about 4 s.** The upstream PR file's second check build at -v10
  (`upstream/pr/check-v10`, 3.6 s, its own directory) was started in the same command as a process check that
  PRINTED `Holmake`, `hol` and `bash regen-key.sh`, without gating on it: the operator had started regen-key.sh at
  ~10:23:47 and its build-base.sh (Holmake delta3_stmtsTheory.uo, pid 66912) was running. So two HOL builds ran at
  once for ~4 s. My build wrote only into upstream/pr/check-v10/.hol; harness/ was not touched. Known risk at -v10:
  HOL's SML-inspection scratch files are shared per user (~/.cache/hol4/scratch; fixed on develop after -v10, see its
  next-release.md: "two HOL builds run at once … one could fail with OpenStruct while building the documentation"),
  so the re-key's base build could in principle have been disturbed. From 10:24:15 no HOL command is run here until
  the re-key has finished; every later check gates (exits) instead of printing.
- **10:24:15–10:26:00** waited without running any HOL: the operator's regen-key.sh (started ~10:23:47) finished;
  FREEZE-2.json says frozen_utc 10:25:58Z, KEY-ARCHIVE-2.tar.enc exists, harness/base's four theories exported
  (logs 10:24). Read here: only those file names/times and FREEZE-2's top-level field names; no key content. No sign
  that the 4-s overlap disturbed it (the re-key writes FREEZE-2 only after its own checks pass).
- **Upstream PR package (upstream/pr/), 10:13–10:33.** Read HOL's conventions read-only: its CLAUDE.md (PRs target
  `develop`, branch from origin/develop; no TABs, no trailing whitespace, < 80 columns), Manual/Developers/
  developers.md, holproject.toml (h4pedant in `src/`: linelen 80, Unicode allowed), src/real/Holmakefile (every
  *Script.sml is a default target), release-notes/next-release.md ("New theories"); `gh api` only: default branch
  develop, no CONTRIBUTING/PR template, CI `docker-ci-for-pr.yml` on pull_request, no fork carlostoledo1891/HOL;
  GitHub code search on develop: 0 hits for semidefinite / Gershgorin / "diagonally dominant" / "positive definite".
  Target path **src/real/diagdomScript.sml** (theory `diagdom`, ancestors pred_set real real_sigma). The file was
  rewritten for HOL's style: lines ≤ 79, the exported constant `dsum` removed (helpers state explicit double sums;
  `irule` is first-order, so the two double-sum rules are applied with HO_MATCH_MP_TAC — the first build failed on
  exactly that, at dd_lower), the two cores share one lower-bound lemma, unused helpers dropped; the theory exports
  only DIAGONALLY_DOMINANT_PSD and _PD, statements text-identical to the -v9/-v10 originals. Final build at -v10
  (check-v10/check.sh, gated): 10:33:05Z, 3.80 s, 0.25 GB, both `oracles [DISK_THM] axioms [] hyps 0`; sha256
  e72d2b6b…; h4pedant's src/ rules: 0 violations. NOT built on develop's tip (RealArith.sml changed there since -v10).
  Also: release-notes.patch (applies cleanly to develop's next-release.md), COMMIT-MESSAGE.txt, PR-TITLE.txt,
  PR-BODY.md (first person, AI help disclosed, says where the lemma came from), STEPS.txt (the operator's commands).
  Nothing forked, pushed or opened.
- **Repository draft (repo-draft/), 10:28–10:33.** README.md (what is proved, what is not, one-command replay, pins;
  a DRAFT comment at the top lists what must happen before publishing), LAYOUT.txt (the tree it will have and the
  source of every part; replay.sh still to be assembled), LICENSE-QUESTION.txt (MIT vs BSD-3-Clause, the facts, a
  recommendation). No GitHub repository created.

## 2026-11-25 10:27–11:03 UTC, after the operator's re-key (FREEZE-2 of 10:25:58Z)

- FREEZE-2 holds on the Mac; the Mac base's tree digest is FREEZE-2's base_digest (335920fd…). PIN.json `hol_dir_pod`
  → /root/work/HOL (judge code 4b421d34…).
- New judge pod 3ozt1qbwggn6un (<judge-pod>, cpu3m 16 vCPU / 128 GB): push.sh 10:27:36; setup-pod done
  10:50:04 (Poly/ML make 183.4 s, HOL -v10 configure 35.7 s, bin/build 970.3 s), selftest PASS, Landlock ABI 4, no netns.
- **The pod's base against FREEZE-2.** The harness's tree digest cannot agree across machines: the pod's is d6b11efa…,
  the Mac's 335920fd…; the four .sig files are byte-identical, the four .dat files differ only by what they embed
  (absolute source paths — "Users"/"carlostoledo"/… against "root"/"judge"/"base" — and the parent theories'
  hashes that follow from those). Checked semantically: the Mac's frozen base copied to the pod at its own path and
  the pod's base each loaded in a fresh HOL process, every theorem, definition and axiom (with hypotheses, types and
  tags) and every constant of the four theories printed and sorted: **identical, 4451 lines, sha256 237f0700… for both.**
  (The 4-second overlap of another HOL build with the re-key at ~10:23:47 left no trace in them.)
- 10:53:28 runner started (16 slots). **10:53:31–11:00:38 controls under FREEZE-2 (seq 85–95): 9/9 PASS, memory limit
  PASS, "refuting" C01 fails (PASS), refuting C02 refuted (PASS, seq 95).**
- rebuild-accepted on the pod: seq 1 (C01) REBUILT; seq 26 (S33 of the FIRST freeze) MISMATCH, as it must: under
  FREEZE-2 the constant S33 does not exist ("S33_def has not been declared"); the ids are now S001–S162. Rebuilding it
  would need the first freeze's base (harness/freeze-1/), not built on this pod.
- 11:02:27 watcher started against the pod (8 in parallel); 11:02:30 RUN.json written (start_utc 2026-11-25T11:02:30Z,
  cap 3). No proving agent started.

## 2026-11-25 11:05–11:08 UTC, the blind run starts (wave 1 of 3)

- **Batches** (the same for both families, the list's order): nine batches of 18, b1 = S001–S018, b2 = S019–S036,
  b3 = S037–S054, b4 = S055–S072, b5 = S073–S090, b6 = S091–S108, b7 = S109–S126, b8 = S127–S144, b9 = S145–S162.
  At most three batches per family in flight; a family's next batch starts when one of its batches ends, in order.
- **Task texts** = agents/BRIEF.md (v2, FREEZE-2) + one line naming the batch, the agent's name, the paths and how
  it submits (Claude: attempt.sh to the judge pod <judge-pod>; GPT: its own queue). Saved in harness/runs/:
  a41c36b773a5ee50364ecdca78318618e753221007f31e13a550fb057650d6fc  claude-claude-b1-TASK.md
  d66778d7e74f5c7c6bd6f2d16ce20ad3495991bcd831c0b65c97c3c6d4388881  claude-claude-b2-TASK.md
  127d683516e5ad98b6f3db68a42168644e24f3aee62a4be8ae8359d6fdcdef3d  claude-claude-b3-TASK.md
  d53251e4e03b63cec907e67dc6938aa3a18da2d87279ec2cd427f6b0fda14753  claude-claude-b4-TASK.md
  8a0d243ce2b8dcf5bc847135deb6abb59f7bd071765dfdecc7279175e5fcf49c  claude-claude-b5-TASK.md
  f38420b2f0e4f0c2fed8325ae4f12164c14045c7656827c2bc95d83411c10d21  claude-claude-b6-TASK.md
  d35cacff39ef207fc05561425e174f00ca99a86e9268bbc96cd5c04bf6113bfa  claude-claude-b7-TASK.md
  acef642587171024533af6085002b589b8dc42c5808d16be827e65b7aa341676  claude-claude-b8-TASK.md
  7b8849482615a5bfb9318a42cdcce977a43f320c7b08734f6fce856fd7b74262  claude-claude-b9-TASK.md
  38cb31087ed836e93bc9ddfdb76a925858570c71e85f54097983ce5ebcf31456  gpt-astra-b1-TASK.md
  bd971139e6eeb337fba1f831ef6c5afb4c5aa6cd8ea017900759df3e5dd12299  gpt-astra-b2-TASK.md
  aec7dcd7590df97f2cd69cfb55a5226b03c869f4775196879fec4b64398be9da  gpt-astra-b3-TASK.md
  0fa830bd704918e1a11c3d2c78652c78ed750a4e55266a7f77d2c2c051f56f79  gpt-astra-b4-TASK.md
  60329d9af7fd5bdca2fe1529ed6deb85551cf007981a9ac47db3c181a37b72fb  gpt-astra-b5-TASK.md
  85a07951059e407dab571a8b2f4fdd31ff5de7c088561f51f27a4cd203688128  gpt-astra-b6-TASK.md
  bcbf015f871ca5063fa722fc76f785aa78d8be0fba766b03d4237d929279b4dd  gpt-astra-b7-TASK.md
  6f351f50e65ac8d2b0b3df964bc422ae1ca81758a588a3428fb06621f308ab09  gpt-astra-b8-TASK.md
  add766200a9203fb2c47bfdb7f373c42e742ea39752232922f0efa1e85661aa9  gpt-astra-b9-TASK.md
- **GPT family**: one task folder per batch, <private-notes>/astra-prover/work/b<k>/ (TASK.md = the
  saved text; work/ its only writable folder, holding work/queue and work/results; under astra-prover/work so the
  blinding audit's forbidden-path list for Claude covers it). One watcher per batch, 11:07:13:
  `judge-queue.py --host <judge-pod> --port 47903 --queue <b>/work/queue --results <b>/work/results --parallel 3`
  (b1 pid 29183, b2 29186, b3 29189). The old watcher on the default queue (pid 22684) idles; stopped at the end.
  Astra sessions started 11:08:06 by run-astra.sh: b1 <session>,
  b2 <session>, b3 <session> (RUN.txt in each folder).
- **Claude family**: three Opus 5.5 agents (general-purpose subagents of the control-room session
  <session>), prompt = the saved text verbatim, started 11:07–11:08: claude-b1, claude-b2,
  claude-b3. Their transcripts are this session's subagent files (for the blinding audit).
- Tokens: harness/runs/tokens.tsv, filled from each agent's usage report and each astra.log at its end.
- 11:24:07 astra-b1 ended (exit 0, 16 min, 100,094 tokens by Codex's count): every statement of b1 judged. 11:26:10
  watcher b4 (pid 63298) and astra-b4 started (the GPT family's next batch, in order). 11:2x the first Claude attempt
  (seq 175, S013, claude-b1).
- **11:38–11:39 UTC, PAUSE (the operator commutes; "when safe, make a pause"; the pod keeps running).** The three
  Claude agents were told to finish the attempt in flight, submit nothing new and end their turn (they resume with
  "continue", context intact; told not to report anything not tractable because of the pause). The GPT sessions
  astra-b2, -b3, -b4 were SIGSTOPped whole (process trees, state kept) at 11:39:10; their watchers keep running, so an
  attempt already queued is judged and its result waits in results/. No new batch starts during the pause. The remote
  judge client tolerates a sleeping Mac (it re-polls the pod for up to 6 h). claude-b3 paused at 11:39 with no
  attempt yet (S037–S054 analysed, no script written; next S038).
  claude-b2 paused 11:41 with no attempt yet (S019–S036 analysed; next S019). claude-b1 pauses when its attempt in flight returns.
  claude-b1 paused 11:41 after its in-flight attempt: 17 of 18 judged, each at its first attempt (16 proved,
  1 refuted); S001 not attempted (0 of 3), next on resume. All three Claude agents are paused; nothing is in flight.
- **A finding about the scoring rules (RUN-PROTOCOL.md, "How decoys are scored"), written before the key is opened.**
  The protocol says a `refuted` on a T or D statement "is impossible unless the kernel or the judge is at fault: it
  stops the run". That holds for T and D-true, NOT for D-planted: a refutation proves the negation of the TEXT alone
  (the right-hand side of Snn_def, without the "May use" hypotheses), and a D-planted decoy's text is a planted
  statement's text, so it is false and refutable, while the decoy itself (hypotheses ==> text) is vacuously provable.
  Seen already: S003 refuted by the GPT family (seq 129) and proved by the Claude family (vacuously, via a refuted
  "May use" member) — both kernel-correct if S003 is a D-planted decoy. At scoring: a `refuted` on a D-planted decoy
  does NOT stop the run; it is reported in its own column ("text refuted") beside "proved", and the early stop means
  a family that refutes such a decoy first can no longer prove it. The stop rule stays for T and D-true. For the
  operator's ruling before the key is unlocked.
- **13:13:11 UTC, RESUME** (the operator is back): every paused process SIGCONTed (116 pids); the three Claude agents told "continue". The pause lasted 1 h 34 min; no attempt was in flight for the Claude family. Mac on battery (78 %), the guards armed.
- 13:14:34 astra-b2 ended (exit 0, 127,213 tokens; 16 judged, S027 and S029 not yet tractable at the cap). 13:15 watcher b5 (pid 94820) and astra-b5 started.
- 13:16 astra-b4 ended (2026-11-25T13:16:08Z, 188894 tokens). Watcher b6 (pid 97054) and astra-b6 started.
- 13:17 astra-b3 ended (2026-11-25T13:16:51Z, 169787 tokens, 15 of 18 judged; not yet tractable: S040 S046 S049 ). Watcher b7 (pid 98237) and astra-b7 started.
- 13:24 claude-b1 ended: 18 of 18 judged at the first attempt (17 proved, 1 refuted); 481,370 tokens by the Agent tool's report. claude-b4 started (the Claude family's next batch, in order).
- 13:29 RULING (operator, dialog): a refuted D-planted decoy counts as correct, in its own 'text refuted' column; no stop (RUN-PROTOCOL.md, ruling appended). Also: the Claude family may run up to 6 batches at once (pace); claude-b5 and claude-b6 started.
- 13:32 astra-b6 ended (2026-11-25T13:32:03Z, 95837 tokens, 18 of 18 judged; not yet tractable: ). Watcher b8 (pid 22299) and astra-b8 started.
- 13:33 astra-b5 ended (2026-11-25T13:32:52Z, 102693 tokens, 14 of 18 judged; not yet tractable: S073 S074 S081 S084 ). Watcher b9 (pid 24101) and astra-b9 started (the GPT family's last batch).
- 13:41 astra-b8 ended (2026-11-25T13:40:56Z, 73986 tokens, 18 of 18 judged; not yet tractable: ). The GPT family has b7 and b9 running; no batch left to start.
- 13:41 astra-b7 ended (2026-11-25T13:41:28Z, 140689 tokens, 16 of 18 judged; not yet tractable: S109 S112 ). claude-b2 ended: 18 of 18 judged
  (12 proved, 6 refuted, 19 attempts); 544,030 tokens.
- **Two findings from claude-b2's report (13:41), both before the key is unlocked.**
  1. **A planted statement can be provable.** Its "May use" list never names a planted statement, but it may name a
     D-planted DECOY, whose constant is its text alone — false. Then "hypotheses ==> planted text" is vacuously true
     and has a kernel proof (claude-b2 names S020, S035, S036 by the public lists; it refuted them instead). So
     RUN-PROTOCOL's "a planted statement ... stays false" fails for those, and the gate "zero planted proved" would
     misfire on a correct vacuous proof. PROPOSED scoring rule (for the operator, consistent with the 13:29 ruling):
     classify each statement by the truth of what the kernel judges — the GOAL "hypotheses ==> text" for a proof, the
     TEXT for a refutation — computed from the key (every text's truth is known). The gate becomes: zero `proved` on
     a statement whose GOAL is false; zero `refuted` on a statement whose TEXT is true. A planted statement whose goal
     is vacuously true is scored in its own class ("planted, vacuous goal"), proved there = correct.
  2. **Cross-family leak through harness/attempts.jsonl.** The log holds every attempt of both families; the brief
     forbids harness/work/<other family>/ but not the log. claude-b2 read it (it cites claude-b3's seq 244), and the GPT
     family ran ahead, so a Claude agent reading it could see GPT outcomes. 13:42: every running Claude agent
     (b3, b4, b5, b6) told not to read attempts.jsonl or other agents' results, and to report whether it had and for
     which statements; new Claude agents get the same message at their start. The blinding audit counts every read of
     attempts.jsonl per agent and statement; scoring reports the Claude family with and without the statements an
     agent could have seen in the log first.
- 13:47 RULING (operator, dialog): the accepted scripts are read by agents only — one Claude and one Astra reader, independently, every script; the report says no human read them (RUN-PROTOCOL.md, ruling appended).
- 13:47 RULING (operator, dialog): the gate judges what the kernel judged — zero 'proved' on a false GOAL, zero 'refuted' on a true TEXT; planted statements with a vacuous goal in their own class (RUN-PROTOCOL.md, ruling appended).
- **13:51 CONTAMINATION found (claude-b3's report): non-blind pre-run material was readable by the blind Claude
  family.** harness/work/claude/ still held the Day-2 S33 attempts (S33-1..9) and sources (S33-opus-src, S33-src) written
  by claude-opus-day2, a harness builder that had READ LEMMAS.md. The brief allows reading harness/, so a Claude agent
  could read a proof written with the key's plaintext in view. claude-b3 used S33-9's proof for S040 (renamed) and as
  the base of S046. Actions: those eleven folders moved out of harness/ to hol4/delta3/day2-prerun-work/claude/
  (forbidden by the brief; MOVED-PRERUN.txt left in their place); the running Claude agents were already told at 13:42
  not to read other agents' material. Scoring: S040 and S046 for the Claude family are marked CONTAMINATED (non-blind
  source) and the family is reported with and without them; the blinding audit lists every read of the S33 folders by
  any agent. claude-b3 also read claude-b1's scripts S015, S008, S005, S017 (same family; S050 and S051 named as
  possibly influenced, S039's vacuous route) — same-family reuse is allowed by the brief and is reported, not excluded.
  claude-b3 ended: 17 of 18 judged (13 proved, 4 refuted), S054 at the cap; 714,365 tokens.
- **13:51 Two more pre-run leaks closed** (found while checking claude-b3's): harness/freeze-1/ (the FIRST freeze's
  STATEMENTS.md, whose lists — before decoys — identify 41 of 44 planted texts; the texts are unchanged under FREEZE-2,
  only renumbered, so an agent could map them) and harness/accepted/26-claude-S33-9/ (the non-blind S33 proof) moved to
  hol4/delta3/day2-prerun-work/ (harness/MOVED-PRERUN.txt says where). The blinding audit lists every read of
  freeze-1/, accepted/26-*, and work/claude/S33-* by any agent of either family, with the time; any statement an agent
  decided after such a read is reported separately.
- 13:54 astra-b9 ended (2026-11-25T13:54:03Z, 101016 tokens, 16 of 18 judged; not yet tractable: S149 S159 ). THE GPT FAMILY IS DONE (all nine batches). Its nine queue watchers told to stop (STOP files; each finishes what runs, then exits).
- 14:06 claude-b5 ended: 18 of 18 judged at the first attempt (7 proved, 11 refuted); 387,526 tokens. DISCLOSED: it
  read harness/attempts.jsonl once before the 13:42 message, filtered to S073–S090, which printed the GPT family's outcomes
  for that batch; it says S087 changed because of it (it had planned a vacuous proof, re-read the text after seeing GPT's
  refutation, then built its own counterexample). Scoring: S087 for the Claude family is CONTAMINATED; S073–S090's other
  17 are reported as "GPT outcomes visible" (its own classification predates the read, it says). No pre-run material read.
- 14:06 A leak of my own, closed: the 13:29 ruling appended to harness/RUN-PROTOCOL.md (readable by agents)
  named S003 and both families' outcomes on it. Both families had already judged S003, so no attempt on S003 could change;
  the text could still hint at the role of statements sharing S003's text. The id and outcomes are removed from
  RUN-PROTOCOL.md (the case stays here, outside the agents' tree); the blinding audit lists reads of RUN-PROTOCOL.md after
  13:29 by agents still proving.
- 14:24 claude-b7 ended: 18 of 18 judged at the first attempt (15 proved, 3 refuted); clean disclosure (no attempts.jsonl, no other agent's results, no pre-run material; only directory listings showed their names). Tokens: from its usage report when the notification lands.
- 14:29 claude-b6 ended: 18 of 18 judged (10 proved, 8 refuted; 20 attempts). DISCLOSED: read attempts.jsonl once before 13:42 through a filter that printed Claude-family lines only (none for S091–S108), so no GPT outcome seen; read the first 150 lines of the NON-BLIND accepted/26-claude-S33-9/script.sml (for syntax, it says), before it was moved — it names S093 as the one statement it could touch (its refutation uses nothing from it). Scoring: S093 for the Claude family marked 'pre-run material read' (reported, not excluded: a refutation by a concrete counterexample). Tokens: from its usage report.
- 14:31 claude-b4 ended: 18 of 18 judged (8 proved, 10 refuted; S057 at its 3rd attempt). DISCLOSED: before 13:42 it read attempts.jsonl (a Claude-family view for b1–b3 plus the last 5 raw lines, which showed GPT outcomes for S074, S104, S116, S105, S084); S104 shares S071's text and was shown refuted — S071 for the Claude family is marked 'GPT outcome visible' (it says it refuted from its own analysis). It read same-family scripts (allowed; reported). No pre-run material. Its 'flaw' note (a false text recorded as proved through a refuted dependency, e.g. S014) is the case the 13:47 gate ruling already scores by the goal.
- 15:02 claude-b9 ended: 16 of 18 judged (6 proved, 10 refuted; 20 attempts); S149 at the cap, S160 not attempted (its only 'May use' member is false, so the goal is vacuously provable; it chose not to submit that, and a direct proof was out of reach). Clean disclosure (directory names only). Only claude-b8 is still running.
- 15:09 claude-b8 ended: 17 of 18 judged (6 proved, 11 refuted; 22 attempts); S134 at the cap (an unjudged corrected script is
  on disk, not submitted); clean disclosure (names in listings only); 715,414 tokens.
- **15:09 the run ended**: every batch of both families is finished (the GPT family at 13:54, the Claude family now). No
  proving agent is running. Next, in order: fresh rebuild of every accepted attempt on the judge pod (307 accepted
  attempts), stop the runner, pull the pod's log, delete the pod; the blinding audit; two agent readers of every accepted
  script; the operator unlocks the key; scoring.
- **15:29 BLINDING AUDIT done** (a Claude agent; harness/audit/AUDIT.md, reads.tsv, sets.json, the tool's outputs).
  All nine GPT sessions clean; six Claude agents not clean (b1–b6). Nobody read the key, LEMMAS.md, the other family's
  folder or logs, or ran HOL outside the judge; the tool's 9 VIOLATION lines are false positives (prose mentions; an rg
  exclusion glob). Undisclosed by the agents and found here: claude-b1 and claude-b2 read the whole non-blind S33-9 script
  at 11:08–11:09 (b2 then refuted S034, the sibling text); claude-b3 also read freeze-1 (texts only) and S33-9's logs.
  Sets for scoring (Claude family; GPT none): CONTAMINATED 5 (S040, S046, S087 used; S034, S045 read before deciding);
  OTHER-FAMILY-VISIBLE 18 (S071, S073–S090 except S087); SAME-FAMILY-REUSE 13 (informational). 135 of the Claude family's
  158 judged statements are blind by this audit. The auditor is a Claude agent of the control-room session: a GPT
  re-reading of the same files is the independent check.
- 15:56 Astra's independent re-audit of the blinding started (<private-notes>/audit-astra/, without the first audit until its own is written). The readers' brief written (harness/readers/READER-BRIEF.md); both readers start when the rebuilds end.
- **16:04 REBUILDS DONE: 307 of 307 accepted attempts REBUILT** (a fresh process per attempt on the judge pod, the
  same decision, the same script bytes; accepted/REBUILDS.tsv). 20 were first cut off by dropped connections ("Connection
  closed" while the Mac was away) and rebuilt again at 16:00–16:03, all REBUILT. Then: the runner stopped (16:03:41), its
  log pulled to harness/logs/pod-final/, every queue watcher stopped, and the judge pod 3ozt1qbwggn6un DELETED (opened
  10:26:49 UTC, about 5 h 37 min at US$0.88/h, about US$4.95).
- **16:08 Astra's independent re-audit** (<private-notes>/audit-astra/, 15:55–16:08, 176,669 tokens;
  work/AUDIT.md, sets.json, DIFF.md): agrees on every agent and every read that matters; the tool outputs match byte for
  byte; zero cross-family reads and zero prover-run HOL builds in both. Differences: it keeps S045 (exposure real, no sign
  it changed the decision) — CONTAMINATED 4 against 5; it counts S087 in both sets (OTHER-FAMILY-VISIBLE 19 against 18);
  SAME-FAMILY-REUSE 19 against 13 (b4's ten refutations reuse a helper byte-identical to b3's S045 script). Its caveat:
  the WORKLOG it had to read already carried the first audit's headline, which limits independence.
  SCORING USES THE UNION (the stricter of the two): CONTAMINATED {S034, S040, S045, S046, S087}; OTHER-FAMILY-VISIBLE
  {S071, S073–S090}; 23 distinct Claude statements reported separately, 135 of 158 blind; GPT none excluded. Both
  audits' counts are reported side by side.
- **16:16 Astra reader done** (<private-notes>/readers/astra/work/READ.tsv, READ.md; 16:04–16:16; 252,659
  tokens): 250 of 307 pass all seven items; 57 flagged — item 2 (top-level ML) 55: mostly top-level `open` of the theory
  structures (delta3_stmtsTheory, realTheory, …) and top-level bindings that specialise a "May use" hypothesis with
  ASSUME; item 4 (ancestors) 2: seq 245 and 422 add real_sigma and pred_set. Items 1, 3, 5, 6, 7: 0 flags; every saved
  theorem matches the judge's conclusion; 90 proofs vacuous via a refuted "May use" member, each checked. By family: GPT 48
  flagged, Claude 9. The flags are about the checklist's style rules, not soundness (every judge log: EXACT true, HYPS 0,
  no axioms). Whether such flags exclude an attempt is put to the operator before the key is opened.
- **16:19 Claude reader done** (harness/readers/claude/READ.tsv, READ.md): 307 of 307 pass all seven items, 0 flags.
  It names the same three ambiguous readings Astra flagged and passed them: extra pinned ancestors (seq 245, 422:
  real_sigma, pred_set; PITFALLS #7 anticipates real_sigma), top-level `val` bindings of theorems/terms/tactics and
  top-level `open` of theory structures (pure values; HYPS 0 in all 307 shows no ASSUME leaked), and `handle` only inside
  helpers. It also notes 245 and 422 say in their headers they are the Day-2 S33 proof (already CONTAMINATED: S040, S046).
  The two readers differ ONLY on the reading of items 2 and 4 (57 scripts: GPT 48, Claude 9); no reader found a
  soundness problem. Put to the operator.
- 16:19 RULING (operator, dialog): style-only reader flags (items 2 and 4 alone, the other reader passing, no flag on 1/3/5/6/7) do not exclude an attempt; all 57 are listed in the report. With it, every one of the 307 accepted attempts COUNTS (subject to the blinding sets for the Claude family). The run is ready for the key.
- 16:36 SCORING PROGRAM FROZEN before the key: harness/score.py sha256 4439dd44a5509b009878a4fb8a1fb93f3e74dc7b4c593c2f1226d8303c00f64a (132/132 tests on synthetic keys, harness/score-test/). Its inputs (score.py, the tests, RUN-PROTOCOL.md with the four rulings, both audits' sets, both readers' tables, REBUILDS.tsv, attempts.jsonl) hashed in harness/score/SEAL-PRE-KEY.sha256 and stamped with OpenTimestamps. Waiting for the operator to unlock the key.
- **16:45 KEY UNLOCKED by the operator (unlock-key.sh, checked against FREEZE-2) and SCORED** with the frozen
  harness/score.py (4439dd44…), 16:45:04 UTC, exit 0: **GATE HELD** — no `proved` on a false goal, no `refuted` on a true
  text, in either family. 307 judged, all counted; 0 anomalies. Classes from the key: T 42, P 28, P-vac 15, D-planted 39,
  D-true 38. Success (exact 95 % intervals in harness/score/SCORE.md):
  T proved: Claude 40/42 (blind 35/37), GPT 35/42. P refuted: Claude 28/28 (blind 24/24), GPT 27/28 (1 not judged).
  D-true proved: Claude 36/38, GPT 33/38. P-vac and D-planted: every judged outcome correct in both families (proved or
  text refuted). Tokens: Claude 5,043,536 (31,921 per judged statement), GPT 1,100,209 (7,384) — different counters.
  The decrypted key copied to hol4/delta3/key-revealed/ (with SHA256SUMS) for publication at the operator's word (his
  decision of 11-25: publish the key at scoring with the attempt logs); the temporary folder is his to delete.
- **17:10 NON-BLIND BUILDER (hol4/delta3/assembly/, 16:46–17:10):** S149 PROVED (the last step's irule
  re-generalised free variables; all ten instantiated; judged by a byte-identical copy of the run's judge, 8.0 s, EXACT
  true, HYPS 0, DISK_THM only). **The slab soundness theorem delta3_slab_sound.slab_check_sound is assembled with no
  hypothesis** (L01–L28 discharged in dependency order; only bool's four standard axioms in its ancestry; oracle tag
  DISK_THM only) and the four slab certificates run through it: A ≈ 2.7849e-4, B ≈ 3.0355e-4, C ≈ 2.7471e-4,
  D ≈ 4.6383e-4 as exact rationals (lower bounds on Ltheta on each slab), no cv_compute tag; the three forgeries give F.
  Sources: 24 GPT blind, 1 Claude blind, 1 Claude other-family-visible (S084), 1 Claude CONTAMINATED (S040 = L26
  dd_rows_psd: its only accepted proof derives from the non-blind Day-2 S33 proof), 1 builder (S149). Still missing for
  Layer 1: inner (L40) and cover (L42) soundness assembled the same way (every true statement there has an accepted proof),
  the forgery recount, replay.sh, the repo README.
- **17:53 LAYER 1 HOLDS** (assembly/, 17:11–17:46): inner_check_sound (= S049), cover_all_sound (= S114) and
  slab_check_sound (= S149) assembled; delta3_layer1 joins them with the kernel runs of the five certificates (cover of
  [0, 1/2], inner L0 >= 0 with equality only at 0, the four slab bounds); DISK_THM only; only bool's four axioms in 159
  theories. Forgeries: 40 of 40 refused (39 in the kernel, 1 by the loader); the plan's 41st (PSD-not-PD) was never run
  on the frozen checker. Staged repository replay.sh from a fresh copy: exit 0 in 1148.3 s. Sources (42 lemmas): 35 GPT
  blind, 3 Claude blind, 1 Claude other-family-visible, 2 Claude CONTAMINATED (S040 = L26, S046 = L29, each the only
  accepted proof), 1 builder (S149).
- 17:53 The operator's answers: a CLEAN-ROOM proof of S040 and S046 by a fresh agent that never sees their
  earlier proofs (hol4/delta3/cleanroom/, its own judge copy; started now); the README may open with FACTS-CHECK §5's
  "to our knowledge … the first HOL4 work on Erdős #1186" line. The builder stages the repository (README edits,
  redaction of host addresses with the originals' sha256, the key with its hashes, the CI workflow).
- **18:38 CLEAN-ROOM proofs** (hol4/delta3/cleanroom/, a fresh Claude agent that saw only the public brief, the
  definitions, the judge code and the HOL4 sources): S040 PROVED (18:36:14Z, 14.7 s) and S046 PROVED (18:36:50Z, 14.0 s,
  without using its S040 hypothesis), each at its first judged attempt, by a copy of the frozen judge (EXACT true, HYPS 0,
  DISK_THM only, no axioms). Proof idea (S040): weighted diagonal dominance through the pairing C_ij + C_ji >= 0 and the
  Gram form of Lw·Lwᵀ; S046 the strict version. Audit of its tool calls (control room): no read of any earlier proof,
  the key, LEMMAS.md, the builder's folder or transcripts; it saw other HOL targets' NAMES in ps output only.
  With these, NO lemma on the Layer-1 chain needs a contaminated proof.
