# hol4/delta3/cakeml — the δ₃ checker, translated to CakeML and compiled by the verified compiler

The δ₃ = 117/2192 certificate checker of `hol4/delta3` — the HOL4 functions `slab_check`, `inner_check`
and `cover_all` with their 36 helpers, as frozen in `hol4/delta3/harness/base/` — turned into a CakeML
program by CakeML's proof-producing translator, given a `main` that reads a `.d3` data file and prints one
line, compiled by the released CakeML compiler binary to an x64 executable, and run on the five
certificates and every forgery that exists in `.d3` form. Built and run on 2026-11-24/25 on a rented
8-vCPU / 64 GB machine (Ubuntu 24.04.3); `WORKLOG.md` has the order of events.

## The answer

| | |
|---|---|
| the binary | `pod-run/out/delta3`, x86-64 ELF, 304,944 bytes, sha256 `991fe191…cbae98` |
| built by | the released CakeML compiler v3671 (`cake`, unmodified) from the S-expression in 2.24 s; gcc link 0.20 s |
| five certificates (slabA–D, inner) + the cover | **6 of 6 ACCEPT**, as the kernel (`⇔ T`) |
| forgeries in `.d3` form | **45 of 45 REJECT**, as the kernel (`⇔ F`): the 6 of Day 1/Day 2, the 3 cover forgeries, 36 of the 37 battery forgeries |
| the malformed battery input (r24, B = "2.7e-4") | `MALFORMED`; the kernel's loader refuses it too |
| disagreements with the kernel | **none, on 52 of 52 inputs** |
| time per certificate, whole run (read + parse + check) | 0.28–0.32 s (medians of 5: slabA 0.309, slabB 0.317, slabC 0.283, slabD 0.299, inner 0.309) |
| the same check in the kernel, same pod, -v10 (`cv_eval` alone; loading the data into the kernel, ~10 s more, not counted) | slabA 1.72, slabB 1.46, slabC 1.19, slabD 1.24, inner 2.08 s (`kernel-v10/timings.tsv`; the machine was also building CakeML's basis then). Day 1 pod: 1.15–1.36 s for the slabs |
| theorems | 66 certificate theorems with no precondition; `main_spec`; `main_whole_prog_spec`; `main_semantics`; `d3_main_verdicts` and `d3_slab_SOME`/`d3_inner_SOME`/`d3_cover_SOME` (what a line means); `delta3_sexp_reads_back` (the file `cake` read is, by theorem, `delta3_prog`) (`theorems.txt`) |

`main_semantics`, as HOL4 printed it:

```
⊢ stdin_content fs = SOME text ∧ wfcl cl ∧ wfFS fs ∧ STD_streams fs ⇒
  sem_satisfies
    (semantics_dec_list (init_state (basis_ffi ext cl fs)) init_env delta3_prog)
    (λbehavior.
       ∃io_events.
         behavior = Terminate Success io_events ∧
         extract_fs ext (cl,fs) io_events =
         SOME (add_stdout (fastForwardFD fs 0) (d3_main (implode text))))
```

and `⊢ (STRING_TYPE --> STRING_TYPE) d3_main d3_main_v`, where `d3_main` is the HOL function that parses
the text and calls the frozen `slab_check`, `inner_check` or `cover_all`.

The binary reads the `.d3` files THEMSELVES — the same bytes the kernel runs read (sha256 in
`kernel-verdicts.tsv`) — not a converted copy. Only the cover inputs (`d3/cover*.d3`, from `make-cover.py`)
and the 37 whole battery files (from `make-battery.py`, applied to Astra's partial files exactly as Astra's
`generate.py` applies them) are written here, by converters that are untrusted and say so; the kernel and
the binary then decide those same files.

## Replay

```
bash replay.sh <cert-machine repository root>     # fresh Ubuntu 24.04 x86_64, 8 vCPU / 64 GB
```

Replayed once from scratch on the same pod in a fresh prefix, then STOPPED by the freeze of 2026-11-25
02:48 UTC (`FROZEN-2026-11-25.md`): toolchain rebuilt (HOL -v10 `bin/build` 898.0 s; the release `cake`
binary byte-identical), CakeML's basis (first attempt failed at `basis-heap` with Poly/ML "Run out of
store" under `-j8`; resumed, done), then checker, translation (39 functions, 66 certificate theorems, no
precondition), `main_semantics`, the meaning theorems — all as in the first build — and the in-HOL
S-expression step interrupted after about 3 of its 8 minutes. The compile, link and the 52 runs were not
replayed. `replay/` holds its logs.

## The kernel side it is compared with

Every kernel verdict is a theorem of the frozen checker (`harness/base`, sha256 `785e8c08…`, `42a7aad2…`):

| inputs | -v9 kernel (Day 1, Day 2, the Mac) | -v10 kernel (this pod) | binary |
|---|---|---|---|
| slabA, slabB, slabC, slabD | `⇔ T` (`hol4/delta3/*.theorem.txt`) | `⇔ T` | ACCEPT |
| inner | `⇔ T` (`inner-check2/`) | `⇔ T` | ACCEPT |
| slabC_red_bound, _claim, _negmu | `⇔ F` | `⇔ F` | REJECT |
| inner_red_c0, _kap, _radius | `⇔ F` | `⇔ F` | REJECT |
| cover | `⇔ T` (`kernel-cover/`, run here: none existed) | `⇔ T` | ACCEPT |
| cover_red_gap, _noinner, _short | `⇔ F` (`kernel-cover/`) | `⇔ F` | REJECT |
| battery r01–r23, r25–r37 (36) | `⇔ F` (`kernel-battery/`, run here) | `⇔ F` | REJECT |
| battery r24 | loader: `Fail "String not DEC"` | the same | MALFORMED |

The battery run is the frozen checker's (the FIRST implementation's) red battery; Astra's H1 run decided the
same forgeries with its own checker (36 F, the loader refusal, 3 cover F, all in the kernel). The two
agree.

## What the binary's correctness rests on

The route is the standard light one: **CakeML's proof-producing translator + the released, verified CakeML
compiler binary `cake`**. It is not CakeML's in-logic compilation (below, "Not done").

**Proved here, in HOL4 trindemossen-2-v10 with CakeML v3671's translator, CF library and basis**
(`hol/prog/delta3_cmlProgScript.sml`, `hol/prog/delta3_cmlMainScript.sml`):

1. *The translation.* For each of the 39 functions the theories `delta3_check` and `delta3_check2` define,
   for the 24 reader functions defined here and for `tdiv`, `tmod`, `tsub1` (66 in all, `theorems.txt`;
   `REPLICATE` is translated too), a certificate theorem
   `⊢ (A₁ --> … --> B) f f_v` in the translator's `Eval` form: the CakeML closure `f_v`, applied to CakeML
   values that represent HOL arguments (refinement invariants `NUM`, `INT`, `BOOL`, `LIST_TYPE`,
   `PAIR_TYPE`, `STRING_TYPE`), evaluates under CakeML's semantics to a value representing `f` of those
   arguments. **No precondition remains on any of them** (checked by the script: it refuses to finish if
   one does). The functions are translated FROM THE FROZEN DEFINITIONS THEMSELVES; four non-recursive
   ones (`sc`, `add_term`, `slab_check`, `inner_check`) are first rewritten with three HOL equations,
   `⊢ a DIV b = tdiv a b`, `⊢ a MOD b = tmod a b`, `⊢ a − 1 = tsub1 a`, where `tdiv`, `tmod`, `tsub1`
   are the total versions (`if b = 0 then 0 else a DIV b`, …). They are equalities in HOL (HOL has
   `k DIV 0 = 0`, `k MOD 0 = k`, `0 − 1 = 0`), so the certificate theorems are about the frozen constants,
   unchanged; the rewrite only lets the translator see that CakeML's `div`, `mod` and `−` (which raise or
   ask for `b ≤ a`) are never reached with a bad argument.
2. *The reader.* `d3_main : mlstring -> mlstring` is a HOL function (defined in
   `delta3_cmlProgScript.sml`): it splits the text into lines, reads `@name count` section heads and rows
   of decimal integers (`mlint$fromString`), converts the sections to the argument types of
   `slab_check` / `inner_check` / `cover_all` exactly as `slab.template` / `inner.template` order them, and
   returns `"ACCEPT <check>\n"` if the check is `T`, `"REJECT <check>\n"` if it is `F`, `"MALFORMED\n"` if
   the text does not give the arguments. Which check: a file with a section `forms` goes to `slab_check`,
   one with `lam` to `inner_check`, one with `cover` to `cover_all`.
3. *The main.* `main_spec` (characteristic formulae): for every file system `fs` whose standard input
   holds `text` (`stdin_content fs = SOME text`), `main ()` prints `d3_main (implode text)` on standard output and nothing else
   (`STDIO (add_stdout (fastForwardFD fs 0) …)`). `main_whole_prog_spec`, and `main_semantics` by
   `prove_sem_thm`: the CakeML program `delta3_prog` (the basis library + the translated checker + main)
   terminates successfully under CakeML's source semantics with the basis FFI model, and the file system it
   leaves has `d3_main (implode text)` added to standard output.
4. *What the line means.* `delta3_cmlMeaning`: `d3_main_verdicts` — an `ACCEPT slab_check` line means the
   text parses to sections `secs` with `d3_slab secs = SOME T`, a `REJECT slab_check` line `SOME F`, and
   the same for `inner_check` and `cover_all`; `d3_slab_SOME` (and `d3_inner_SOME`, `d3_cover_SOME`) —
   `d3_slab secs = SOME b` means the sections `grid`, `scal`, `theta`, `forms`, `ab`, `cut`, `full`, `wit`,
   `ds`, `L` read as particular arguments and `b` IS the frozen `slab_check` on them.
5. *The file the compiler reads.* `delta3_sexp_reads_back` (`hol/prog/delta3_cmlSexpScript.sml`):
   `⊢ parse S = INR (from_dec_list delta3_prog, "") ∧ to_dec_list (from_dec_list delta3_prog) = SOME delta3_prog`,
   S a string literal of 655,069 characters computed in HOL by `EVAL` of
   `sexp_to_string (from_dec_list delta3_prog)` (455 s, 7.1 GB), from CakeML's own theorems
   `mlsexp$parse_sexp_to_string` and `ast_sexp$to_from_dec_list_ok`. `mlsexp$parse` then
   `ast_sexp$to_dec_list` is exactly what `cake --sexp=true` does with its input (`parse_sexp_input_def` in
   CakeML's `compiler/compilerScript.sml`). So the program the verified compiler reads is, by theorem, the
   program `main_semantics` is about. S is byte-identical to the file CakeML's unverified ML printer
   (`astToSexprLib`) wrote, and `build-binary.sh` refuses to go on otherwise.

**Trusted, not proved here:**

- *Writing one string to a file.* The S-expression `cake` compiled is the literal S of
  `delta3_sexp_reads_back` (item 5), written to `delta3.proved.sexp` by `TextIO.output` in the theory script;
  that the file holds exactly S is trusted (it is also byte-identical to what the ML printer wrote).
- *The compiler binary's provenance.* `cake` is the release v3671 asset `cake-x64-64.tar.gz`, checked
  against GitHub's sha256 digest. The compiler correctness theorem of CakeML is about the machine code
  that CakeML's in-logic bootstrap produced; that the `cake.S` in the release IS that code is trusted
  (not rebuilt here: the bootstrap is CakeML's regression's largest job). `cake --version` reports CakeML
  16bdb1aa, HOL 9783a499 (trindemossen-2-v10), Poly/ML 5.9.
- *What the compiler theorem itself assumes.* An x64 machine that behaves as CakeML's x64 model; the C
  file `basis_ffi.c` (from the same release, unverified) implementing the FFI calls as the basis FFI
  model says (here: reading standard input, writing standard output, exit); the assembler and linker
  (gcc 13.3.0) and the operating system loading the program as the startup code expects. The theorem
  allows the machine code to stop early when it runs out of heap or stack; a run that does so does not
  print a verdict (every run below printed one line and exited 0).
- *The reading of the same bytes by two loaders.* The kernel's runs read each `.d3` file with
  `delta3DataLib.read_dat` (ML, unverified); the binary reads the same file with `d3_main` (HOL, translated,
  proved). That the two parse a file to the same arguments is not proved; on the 52 inputs they agree in
  outcome (both accept, both reject, or both refuse the malformed one).
- *The shell.* `run-binary.sh` feeds each file on standard input and reads the one line back.

**Not established at all here:**

- That `slab_check … = T` (or `inner_check`, `cover_all`) implies the bound: no soundness theorem; that is
  the proof harness's work in `hol4/delta3/harness/`. The binary decides the same HOL functions the kernel
  evaluates, nothing more.
- The model constants (cells, cut pairs, full pairs) are data in the `.d3` files, exported from the
  JavaScript verifier, as on Day 1.
- An end-to-end theorem about the machine code inside HOL (in-logic compilation): not done, see below.
- A REJECT is the check failing on this witness, not a proof that no witness exists (as Day 1 says of F).

## Not done: in-logic compilation

CakeML can also compile a program inside HOL (`eval_cake_compile_x64`, by cv_compute) and combine the
result with the compiler's correctness theorem into one theorem about the machine code
(`examples/compilation/x64/` and its `proofs/`). That removes the release binary's provenance and the
compiler binary itself from the trusted base (the printer is out of it already, item 5), leaving the x64
model, the FFI C code and the loader. It needs the compiler backend's correctness proofs (`compiler/backend/proofs`, the x64 target
proofs) and the cv translation of the compiler built first. CakeML's own regression job 3724 (CakeML
8785d4c, HOL 1c803b0, machine "fairybread", page `cakeml.org/regression.cgi/job/3724`, read 2026-11-24)
ran from Nov 23 13:01:41 to Nov 24 13:51:32, about 24 h 50 min, with single steps up to 110 GB
(`compiler/bootstrap/compilation/x64/proofs`, 6 h 15 min) and 143 GB (ag32). This pod has 64 GB and a
7.5-hour cap, so it was not attempted. That figure is CakeML's whole regression, not a measurement of the
part an in-logic compile of this program would need; that part was not measured.

## HOL version: the package is on trindemossen-2-v10

Day 1 pinned HOL4 `trindemossen-2-v9` (commit `652d1f0aad5cd537ed1e5d470ba3444e70ba470e`). CakeML's
releases each name the HOL commit they were built with (`gh api repos/CakeML/cakeml/releases`); none names
-v9. Release **v3671** (commit `16bdb1aaaab64a6ac66504ad2e9f0ed6146060e9`, 2026-11-07) names
**`trindemossen-2-v10`, commit `9783a49979c94c401ff8c0e51b2eefae7ea95ae3`**, the tag right after -v9, and its
compiler binary reports that HOL itself (`cake --version`). The only CakeML revision recorded with -v9 is
`239aca184c1321d6f5fcfb8b923b91af20558d2f` on the unreleased branch `version-string` (an example
`cake --version` output in `developers/changes-since-release.md`, commit `67faf9d8`); it has no released
compiler binary, and making one means CakeML's compiler bootstrap, far beyond this machine. So the
operator's decision (2026-11-25, relayed by the control room): **the package moves to -v10**, with the
frozen checker's -v10 kernel verdicts as the baseline.

The evidence that nothing the checker depends on changed:

| | -v9 (Day 1, Day 2; the Mac for the battery and the cover) | -v10 (this pod) |
|---|---|---|
| the frozen checker builds, all 39 `cv_trans` calls | yes | yes (`pod-run/logs/checker-build.log`, 65 s; again in `build-checker.log`, 31.8 s) |
| slabA, slabB, slabC, slabD, inner | `⇔ T` | `⇔ T` |
| slabC_red_{bound,claim,negmu}, inner_red_{c0,kap,radius} | `⇔ F` | `⇔ F` |
| cover; cover_red_{gap,noinner,short} | `⇔ T`; `⇔ F` | `⇔ T`; `⇔ F` |
| the 37 battery forgeries | 36 `⇔ F`, r24 refused by the loader | 36 `⇔ F`, r24 refused by the loader |
| the 51 theorem statements, as printed | — | **51 of 51 byte-identical to -v9's** |

Between the two tags (96 commits, `kernel-v10/hol-v9-v10-diff.txt`) the logical kernel and the compute
primitive did not change: no file in `src/0`, `src/thm` (with `Compute.sml`), `src/prekernel`,
`src/experimental-kernel`. What changed nearby: the datatype package, TFL / `TotalDefn` (termination of
mutual recursion, over-applied calls), `listScript.sml` (how `list` is declared; `MAP` and `LIST_TO_SET_DEF`
restated as theorems), `cv_typeLib.sml` (an error message when a representation cannot be built). The
checker's definitions elaborate to the same theorems on both (the 51 identical statements).

## Files

| | |
|---|---|
| `setup-cakeml.sh` | the toolchain from nothing: Poly/ML 5.9.2, HOL -v10, CakeML v3671 + its basis, the released `cake` (each pinned by commit or sha256) |
| `build-binary.sh` | checker (an INPUT: the directory holding its two script files) → translation → main + proofs → `delta3.sexp` → `cake` → `gcc` |
| `run-binary.sh` | the binary on a list of inputs, compared with the kernel's verdicts; nonzero exit on any disagreement |
| `replay.sh` | all of it in one command on a fresh Ubuntu 24.04 x86_64 machine: `bash replay.sh <repository root>` |
| `hol/prog/delta3_cmlProgScript.sml` | the translation (generic over the checker theories), the `.d3` reader, `d3_main` |
| `hol/prog/delta3_cmlMainScript.sml` | `main`, `main_spec`, `main_whole_prog_spec`, `main_semantics`, the S-expression (ML printer) |
| `hol/prog/delta3_cmlMeaningScript.sml` | `d3_main_verdicts`, `d3_slab_SOME`, `d3_inner_SOME`, `d3_cover_SOME` |
| `hol/prog/delta3_cmlSexpScript.sml` | the S-expression computed in HOL, `delta3_sexp_reads_back`, `delta3.proved.sexp` |
| `hol/checker/Holmakefile`, `hol/prog/Holmakefile` | the build directories (the scripts are built inside the CakeML checkout) |
| `make-cover.py`, `make-battery.py` | UNTRUSTED converters: the cover inputs; the 37 whole battery files |
| `d3/cover*.d3` | the genuine cover and the three cover forgeries |
| `inputs-pod.tsv`, `kernel-verdicts.tsv` | the 52 inputs with their kernel verdicts; the 15 non-battery ones with sha256 of input and theorem file |
| `kernel-cover/` | `cover_all` in the -v9 kernel (Mac, Day-1 pins): script, results |
| `kernel-battery/` | the frozen checker in the -v9 kernel on the 37 battery files: templates (Day 1's, recording instead of failing), runner, results |
| `kernel-v10/` | the -v10 baseline: the 15 Day-1/Day-2/cover theories and the 37 battery theories on the pod, theorem files, logs; `hol-v9-v10-diff.txt` |
| `pod-run/out/` | `delta3.sexp`, `delta3.S`, the binary `delta3`, the runs (`runs/binary-runs.tsv`, each stdout), the timing repeats |
| `pod-run/logs/` | every setup and build step's log and time; the theory logs (with every certificate theorem printed); `checker-input/` (the two checker files as used, sha256); the smoke test and the CF debugging session; `versions.txt` |
| `pod-run/cake-release/` | the release's `basis_ffi.c` and `Makefile`, sha256 of the release tarball, `cake`, `cake.S` |
| `theorems.txt` | the 66 certificate theorems and `main_semantics`, as printed |
| `PINS-cakeml.json`, `SHA256SUMS` | versions, commits, build times, the sha256 of every file here |
| `replay/` | the from-scratch replay's logs, up to the freeze |
| `FROZEN-2026-11-25.md` | the state at the freeze and how to resume |
| `WORKLOG.md` | the night in order |

Code here is MIT, like the rest of cert-machine.
