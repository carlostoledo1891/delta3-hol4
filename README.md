# δ₃ = 117/2192: a certificate checker in HOL4, proved sound

[![replay](https://github.com/carlostoledo1891/delta3-hol4/actions/workflows/replay.yml/badge.svg)](https://github.com/carlostoledo1891/delta3-hol4/actions/workflows/replay.yml)

To my knowledge (from a search on 25 November 2026), this is the first HOL4 work on Erdős problem #1186: a
certificate checker proved sound in HOL4 and run in the HOL4 kernel on the five certificates behind δ₃ = 117/2192.
The full statement is formalised in Lean by Snively (v1.0.0, see "Related work").

δ₃ is the k = 3 case of Erdős #1186, the Parrilo–Robertson–Saracino conjecture. Its value rests on five exact
certificates: one for the inner region and four "slabs". This repository holds a small checker for them, written in
HOL4. The checker runs inside the HOL4 kernel, and it is proved correct: when it accepts a certificate, the polynomial
bound the certificate claims really holds on its whole region. The same checker is also compiled by CakeML's verified compiler into a
program that decides the certificates outside HOL4.

I built this with AI agents, and part of the proof was a measured experiment. Two model families tried to prove the
soundness lemmas blind to each other, with planted false lemmas among the true ones. That run is logged here in
full. Three lemmas were finished after scoring, once the answer key was open, and I say below exactly which ones.

## What is proved

Everything here is a HOL4 theorem at `trindemossen-2-v10`. Each one carries no tag but `DISK_THM` (the mark of a
theorem read back from a theory file), no axiom tag and no hypothesis. In the whole ancestry of the final theorem (159 theories) the only axioms are
HOL's four standard ones (`BOOL_CASES_AX`, `ETA_AX`, `SELECT_AX`, `INFINITY_AX`).

**The three soundness theorems.** If `slab_check` accepts, the slab polynomial L_θ is at least the claimed bound on
the whole region. If `inner_check` accepts, L₀ ≥ 0 on its region, with equality only at y = 0. If `cover_all`
accepts, the regions cover every m in [0, 1/2].

```
slab_check_sound   ⊢ ∀… slab_check ab cuts full grid lp lq hp hq Bp Bq ep eq cp cq theta forms D T2 ds Lw ⇒
                       ∀y. in_box (LENGTH grid − 1) y ∧ qv lp lq ≤ mval grid y ∧ mval grid y ≤ qv hp hq ⇒
                           qv cp cq ≤ Ltheta ab cuts full theta y
inner_check_sound  ⊢ ∀… inner_check ab cuts full grid rp rq lam nu kp kq nn cc D T2 ds Lw ⇒
                       ∀y. in_box (LENGTH grid − 1) y ∧ mval grid y ≤ qv rp rq ⇒
                           0 ≤ L0 ab cuts full y ∧ (L0 ab cuts full y = 0 ⇒ EVERY (λx. x = 0) y)
cover_all_sound    ⊢ ∀ivs. cover_all ivs ⇒ ∀m. 0 ≤ m ∧ m ≤ 1/2 ⇒ in_some m ivs
```

**The five certificates, through them.** The kernel runs each check on its certificate and gets T. Putting that
together with the soundness theorems gives one theorem, `delta3_layer1` (`proofs/assembly/delta3_layer1Script.sml`).
In words:

- every m in [0, 1/2] lies in one of [0, 1/5], [1/5, 3/10], [3/10, 2/5], [2/5, 9/20] and [9/20, 1/2];
- on [0, 1/5] (130 cells), L₀(y) ≥ 0 for every y in the box, and L₀(y) = 0 only at y = 0;
- on the four slabs, L_θ(y) is at least an exact rational for every y in the box: about 2.7849·10⁻⁴ on
  [1/5, 3/10], 3.0355·10⁻⁴ on [3/10, 2/5], 2.7471·10⁻⁴ on [2/5, 9/20] and 4.6383·10⁻⁴ on [9/20, 1/2].

| what | theorem | where |
|---|---|---|
| the four slab certificates | `⊢ slab_check <data> ⇔ T`, then the slab's bound | `checker/`, `proofs/assembly/delta3_slab_boundsScript.sml` |
| the inner certificate, 22,808 forms | `⊢ inner_check <data> ⇔ T`, then L₀ ≥ 0 | `proofs/assembly/delta3_layer1Script.sml` |
| the cover of [0, 1/2] by the five regions | `⊢ cover_all <regions> ⇔ T`, then the cover | the same |
| the three soundness theorems | `slab_check_sound`, `inner_check_sound`, `cover_all_sound` | `proofs/assembly/` |
| the 42 lemmas behind them | one proof each, every one accepted by the same judge (see "How the proof was made") | `proofs/accepted/`, `proofs/cleanroom/`, `proofs/builder/` |
| the 40 planted forgeries of the battery | all 40 refused: 39 give `⇔ F` in the kernel, and the loader refuses the malformed one before the kernel | `data/`, `kernel/expected/` |
| weighted diagonal dominance, in index form | `DIAGONALLY_DOMINANT_PSD` and `DIAGONALLY_DOMINANT_PD` | `lemmas/diagdomScript.sml` (also offered to HOL4 as a pull request) |
| the CakeML program | `main_semantics`: the compiled program prints `d3_main` of its standard input. `delta3_sexp_reads_back`: the file the compiler read is, by theorem, the translated program | `cakeml/theorems.txt` |

**About the forgeries.** The battery comes from the first verifier (`instruments/delta3/battery.js` in cert-machine).
It has 37 forged certificates and 3 forged covers. Six more forged files in `data/` (`slabC_red_*`, `inner_red_*`) are
copies of battery forgeries, kept because the first kernel runs used them: five are byte-identical to r14, r15, r26,
r28 and r36, and `slabC_red_bound` is r01 with one fraction left unreduced. So there are 40 different forgeries, not
46. The plan I started from also asked for a 41st control, a matrix that is positive semidefinite but not definite.
That control was run only on a second, independent implementation of the checker, where the strict test refused it.
It has not been run on this checker.

**Times.** On an 8-vCPU x86 machine (-v9), `cv_eval` decides a slab in 1.15–1.36 s. On an Apple-silicon laptop
(-v10) it takes 0.96–1.26 s for a slab and 1.05 s for the inner certificate. The whole replay takes 19 minutes on that
laptop when HOL4 is already built.

**The binary.** It is an x86-64 file of 304,944 bytes (sha256 `991fe191…cbae98`). It prints ACCEPT on the 6 genuine
inputs (four slabs, inner, cover), REJECT on the 45 forged data files, and MALFORMED on the malformed one: 52 of 52
agreements with the kernel, at 0.28–0.32 s per certificate. The binary itself is not in this repository;
`cakeml/` builds it.

**-v9 against -v10.** The kernel runs at -v9 and at -v10 give byte-identical theorem statements on all 51 inputs that
reach the kernel.

## How the proof was made, and how blind it was

The soundness proof was split into 42 true lemmas. They were mixed with 43 planted false lemmas and 77 decoys into 162
numbered statements, so that a prover could not tell which were which. Claude Opus 5.5 and GPT-6.2 each tried all
162, each family blind to the other's scripts. A judge on a throwaway machine built every attempt against the frozen
statements, with no network and with time and memory limits. The answer key was encrypted until scoring. No person
read the accepted scripts; two agent readers did, one from each family.

The run went from 11:02 to 15:09 UTC on 25 November 2026, and it was scored at 16:45. The gate held in both
families: the kernel accepted no proof of a false goal and no refutation of a true statement. On the 42 true lemmas:

| | proved |
|---|---|
| Claude, all 42 | 40 (95.2 %, exact 95 % interval 83.8–99.5) |
| Claude, the 37 left after the blinding audit | 35 (94.6 %, 81.8–99.4) |
| GPT, all 42 | 35 (83.3 %, 68.6–93.1) |

Of the 28 planted lemmas whose goal is false, Claude refuted all 28 and GPT refuted 27 (one never reached a verdict).
The other 15 planted lemmas could be proved only vacuously, and both families answered all of them correctly. Two audits of the agents'
tool calls found that some Claude agents had seen material they should not have seen, so 23 of Claude's statements
are left out of its blind score. All of it is in `agents/`: `SCORE.md`, `AUDIT-BLINDING.md` and `attempts.jsonl`.

**Then I assembled the proof**, one proof per lemma, and no lemma on the chain rests on a contaminated proof.
`proofs/SOURCES.tsv` lists every lemma with its source. In plain terms:

| how the proof was made | lemmas | which |
|---|---|---|
| blind, by GPT | 35 | all but the seven below |
| blind, by Claude | 3 | L22, L37, L40 |
| by Claude, after that agent had seen GPT's three failed attempts at the same lemma (not contaminated, but not counted as blind) | 1 | L12 |
| clean-room, after scoring, by a fresh Claude agent that never saw any earlier proof of them | 2 | L26 (diagonal dominance), L29 (strictness) |
| by the Claude agent that had read the key, after scoring | 1 | L28 (S149, the top slab lemma) |

Where both families had a blind proof, I took the one judged first. L26 and L29 had only one accepted proof in the
run, and both of those were built on an earlier proof written by an agent that had read the answer key. So after
scoring I had a separate agent prove them again without seeing any earlier proof, and its proofs are the ones on the
chain. The two contaminated proofs stay in `proofs/accepted/` as the run's record. Neither family proved L28; the
agent that had read the key finished it with a one-step fix to Claude's third attempt. Every one of the 42 proofs,
the three after scoring included, was accepted by the same judge code under the same frozen statements.

None of this changes the scores, which count only blind attempts.

## What is not proved

- **The model constants are data.** These are the areas and bathtub constants of the extremal colouring φ\* that
  L_θ and L₀ are built from. The JavaScript verifier computes them and HOL4 loads them as data. Deriving them inside
  HOL4 is not done. So the theorems above are about L_θ and L₀ as built from that data, not yet about E(σ).
- **The analytic reduction is not in HOL4.** That is the step from E(σ) ≥ L(y) and the five statements to
  δ₃ = 117/2192. The uniqueness of the extremal colouring is not in HOL4 either.
- **Each certificate lives on its own grid** (130 cells for the inner certificate and the first two slabs, 146 for
  the other two). No theorem here joins them over one y; that happens in the analysis, outside HOL4.
- **The witness is untrusted.** The Gram factor, the weights and the scale are hints that an exporter writes in
  floating point. A wrong hint can only turn T into F. So `⇔ F` on a forgery says that the check fails with that
  witness. It does not say that no witness exists.
- **Strictness is tested differently from the JavaScript verifier.** HOL4 tests strict weighted diagonal dominance of
  the remainder matrix, and that test is now proved sufficient for positive definiteness (lemma L29). It is not a
  necessary condition. The JavaScript verifier tests leading minors, which is exact. Both accept all five
  certificates.
- **The trusted base.** It is HOL4's kernel, including its compute primitive. That primitive is a port of the compute
  facility proved sound for Candle (O. Abrahamsson, M. O. Myreen, M. Norrish, H. Kanabar, J. Åman Pohjola,
  *J. Automated Reasoning* 69(1):7, 2025). The port itself is not proved inside HOL4. The binary adds CakeML's
  released compiler binary, the C FFI stubs of its basis library and the gcc link step.

## Replay

```
./replay.sh            # Poly/ML and HOL4 at the pins, the checker, every kernel run, every proof, the Layer-1 theorem
./replay.sh --cakeml   # also CakeML's basis, the translation, the compile and the 52 binary runs (x86-64 Linux)
```

`replay.sh` exits nonzero unless all of this holds: every file matches `SHA256SUMS`; every genuine input gives T and
every forgery gives F; every theorem file equals its record in `kernel/expected/`; every proof builds; and the three
soundness theorems read back exactly as stated, with no hypothesis and no tag but `DISK_THM`. If `HOLDIR` points to
HOL4 built at the pin, the toolchain step is skipped. HOL4's own build takes 15–20 minutes on 8 cores. The replay
writes everything under `_replay/`. A GitHub Actions workflow (`.github/workflows/replay.yml`) runs it on every push.
`--cakeml` runs in CI by hand or weekly. CakeML job green on CI (82 min): run
[45687039594](https://github.com/carlostoledo1891/delta3-hol4/actions/runs/45687039594), 25 Nov 2026, at commit
`a0973f6`, on GitHub's runner from nothing — CakeML's basis, the translation, the compile and the 52 binary runs. It
was first run on a machine with 8 vCPU and 64 GB, from cert-machine's layout.

**Data and the exporter.** The kernel and the binary read the `.d3` files in `data/`, and those bytes are checked
against `SHA256SUMS`. They were exported from the certificate JSONs in `certs/` by `export/export.js` and
`export/export_inner.js`. Those two exporters need cert-machine's verifier modules (`instruments/`), so they do not run
from this repository alone, and the replay does not run them. They are untrusted anyway: they compute the floating-
point witness, and a wrong witness can only make the check fail.

## Pins

| | version | commit or sha256 |
|---|---|---|
| Poly/ML | 5.9.2 (`--with-gmp`) | `4557554077078decce4ce5f90da00a713cfc32e4` |
| HOL4 | `trindemossen-2-v10` | `9783a49979c94c401ff8c0e51b2eefae7ea95ae3` |
| CakeML | release v3671 | `16bdb1aaaab64a6ac66504ad2e9f0ed6146060e9`; `cake-x64-64.tar.gz` sha256 `e3edd113497bf7fce443e69c70f09c3df1942849251c86ce8e44e6327ade0d3d` |
| certificates | [cert-machine](https://github.com/carlostoledo1891/cert-machine) `certs/delta3/`, archived at doi:10.5281/zenodo.23171167 | `slab-1_5-3_10` `f8c569e4…`, `slab-3_10-4_10` `d9b37a69…`, `slab-2_5-9_20` `bc23d33c…`, `slab-9_20-1_2` `b3f8615a…`, `inner-r20` `2edd2285…` |

`PINS.json` has the full hashes, and `SHA256SUMS` has the sha256 of every file.

## The answer key, and what was redacted

The decrypted answer key is in `agents/key/`. `python3 tools/check-key.py` checks it against `judge/FREEZE-2.json`,
which recorded its hashes before the run began (`agents/key/README.md` says how).

A few records came from my private working copy, so before publishing them I removed host addresses (the judge
machine's IP), private paths and session ids. `tools/redact.py` does this, the same way every time, and each
redacted file has the original's sha256 beside it (`*.original.sha256`), so anyone who holds an original can check
it. `REDACTIONS.tsv` lists the files and how much was removed from each. Nothing else was changed.

## Related work

- **Lean.** Snively formalised the full statement in Lean:
  [dreadpiratechan/erdos-1186](https://github.com/dreadpiratechan/erdos-1186), v1.0.0 (26 October 2026). It
  states five departures from the claim. One of them: the five finite statements are proved in the weaker form
  L ≥ 0, so the equality case is not formalised.
- **The value.** Star Fleet Math stated δ₃ = 117/2192, with an exact rational sum-of-squares certificate, by
  15 July 2026 (Internet Archive capture 20260715002525).
- **The certificates and their first verifier.** These are in cert-machine, under `certs/delta3/` and
  `instruments/delta3/`. That JavaScript verifier was written under a clean-room rule, and it refuses the same 40
  forgeries.

## Licence

MIT (`LICENSE`). The certificates are cert-machine's, also MIT. A binary built by `cakeml/` links CakeML's basis
library and carries its BSD-3-Clause notice.
