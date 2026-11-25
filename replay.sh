#!/usr/bin/env bash
# replay.sh — δ₃ = 117/2192 in HOL4, from this repository and the pinned toolchain, in one command.
#
#   ./replay.sh             the toolchain (skipped when HOLDIR points to HOL4 built at PINS.json's commit),
#                           the checker, every kernel run (four slabs, the inner certificate, the cover, and
#                           every forgery), every proof, the three soundness theorems and the Layer-1 theorem
#   ./replay.sh --cakeml    also the CakeML binary (cakeml/replay.sh; x86-64 Linux, CakeML's released compiler;
#                           PREFIX=<dir> for its toolchain, CAKEML_SETUP_DONE=1 when it is already built there)
#
# Exit status 0 only if ALL of these hold:
#   - every file matches SHA256SUMS, and the checker, meanings and statements are the frozen ones (judge/FREEZE-2.json);
#   - every genuine input gives T, every forgery gives F, and the malformed battery input r24 is refused by the loader;
#   - every theorem file is byte-identical to its record in kernel/expected/;
#   - every proof builds (the 42 lemma proofs, the three soundness theorems, the Layer-1 theorem, lemmas/diagdom);
#   - the read-back finds the three soundness theorems exactly as stated (S149, S049, S114 of the statements),
#     with no hypothesis, no axiom tag and no oracle but DISK_THM, and no axiom in the ancestry but bool's four.
# Everything is built under _replay/ (deleted first), one HOL process at a time, at nice 10. A forgery's theory files
# are deleted once its verdict and theorem file are recorded (KEEP_ALL=1 keeps them).
set -euo pipefail
R="$(cd "$(dirname "$0")" && pwd)"
W="$R/_replay"; rm -rf "$W"; mkdir -p "$W"
LOG="$W/replay.log"; TIMES="$W/times.tsv"; T0=$(date +%s)
printf 'step\twall_s\tmax_rss_kb\texit\n' > "$TIMES"
say()  { echo "$(date -u +%FT%TZ) $*" | tee -a "$LOG"; }
fail() { say "FAIL: $*"; say "replay: FAILED after $(( $(date +%s) - T0 )) s"; exit 1; }
pin()  { python3 -I -c 'import json,sys; print(json.load(open(sys.argv[1]))[sys.argv[2]])' "$R/PINS.json" "$1"; }
sha()  { if command -v sha256sum >/dev/null 2>&1; then sha256sum "$@"; else shasum -a 256 "$@"; fi; }
timed() { python3 -I "$R/tools/timed.py" "$TIMES" "$@"; }       # timed <label> <log> <cmd...>
CAKEML=0
for a in "$@"; do case "$a" in --cakeml) CAKEML=1 ;; *) echo "usage: replay.sh [--cakeml]"; exit 2 ;; esac; done
say "replay: start; repository $R"

# ---- 0. the files --------------------------------------------------------------------------------------------
( cd "$R" && sha -c SHA256SUMS > "$W/sha256-check.txt" 2>&1 ) || fail "a file differs from SHA256SUMS ($W/sha256-check.txt)"
say "files: $(wc -l < "$R/SHA256SUMS" | tr -d ' ') match SHA256SUMS"
python3 -I - "$R" <<'PY' || fail "the checker, the meanings or the statements differ from judge/FREEZE-2.json"
import hashlib, json, os, sys
r = sys.argv[1]; fr = json.load(open(os.path.join(r, 'judge', 'FREEZE-2.json')))['public']
where = {'base/delta3_checkScript.sml': 'checker', 'base/delta3_check2Script.sml': 'checker',
         'base/delta3_semScript.sml': 'semantics', 'base/delta3_stmtsScript.sml': 'semantics'}
for k, d in where.items():
    p = os.path.join(r, d, os.path.basename(k))
    assert hashlib.sha256(open(p, 'rb').read()).hexdigest() == fr[k], p
print('the four base scripts = FREEZE-2')
PY

# ---- 1. the toolchain ----------------------------------------------------------------------------------------
if [ -z "${HOLDIR:-}" ]; then
  say "toolchain: Poly/ML $(pin poly_tag) and HOL4 $(pin hol_tag) from source (toolchain/setup.sh, Ubuntu 24.04 x86_64)"
  PREFIX="$R/_toolchain" bash "$R/toolchain/setup.sh"
  HOLDIR="$R/_toolchain/HOL"
  export PATH="$R/_toolchain/polyml-install/bin:$PATH"
fi
[ "$(git -C "$HOLDIR" rev-parse HEAD)" = "$(pin hol_commit)" ] || fail "HOL at $HOLDIR is not at $(pin hol_commit)"
export PATH="$HOLDIR/bin:$PATH"
poly -v 2>/dev/null | head -1 | grep -q "$(pin poly_version)" || fail "poly on PATH is not Poly/ML $(pin poly_version)"
say "toolchain: HOL $(pin hol_tag) $(pin hol_commit); $(poly -v 2>/dev/null | head -1)"

# ---- 2. the base: the checker, its meanings, the statements ----------------------------------------------------
B="$W/base"; mkdir -p "$B"
cp "$R"/checker/delta3_checkScript.sml "$R"/checker/delta3_check2Script.sml "$R"/semantics/delta3_semScript.sml \
   "$R"/semantics/delta3_stmtsScript.sml "$B/"
( cd "$B" && timed base "$B/holmake.log" Holmake delta3_stmtsTheory.uo ) || fail "the base theories ($B/holmake.log)"
say "base: delta3_check, delta3_check2, delta3_sem, delta3_stmts built"

# ---- 3. the inputs ---------------------------------------------------------------------------------------------
D="$W/d3"; mkdir -p "$D" "$W/battery-src"
cp "$R"/data/*.d3 "$D/"
cp "$R"/export/battery-parts/* "$W/battery-src/"
cp "$R"/data/slabA.d3 "$R"/data/slabB.d3 "$R"/data/slabC.d3 "$R"/data/slabD.d3 "$R"/data/inner.d3 "$W/battery-src/"
python3 -I "$R/export/make-battery.py" "$W/battery-src" "$D" > "$W/make-battery.log"
( cd "$D" && sha r*.d3 ) | awk '{print $1"  "$2}' | diff - "$R/data/battery.sha256" > "$W/battery-diff.txt" \
  || fail "the regenerated battery files differ from data/battery.sha256 ($W/battery-diff.txt)"
say "inputs: $(ls "$D"/*.d3 | wc -l | tr -d ' ') data files; the 37 battery files regenerated, byte-identical to data/battery.sha256"

# ---- 4. the proofs ---------------------------------------------------------------------------------------------
P="$W/proofs"; mkdir -p "$P"
python3 -I "$R/tools/acc_rename.py" "$R/proofs/SOURCES.tsv" "$R" "$P" >> "$LOG"
cp "$R"/proofs/assembly/delta3_slab_soundScript.sml "$R"/proofs/assembly/delta3_inner_soundScript.sml \
   "$R"/proofs/assembly/delta3_cover_soundScript.sml "$P/"
printf 'INCLUDES = %s\n' "$B" > "$P/Holmakefile"
( cd "$P" && timed proofs "$P/holmake.log" Holmake -j 1 delta3_slab_soundTheory.uo delta3_inner_soundTheory.uo \
    delta3_cover_soundTheory.uo ) || fail "the proofs ($P/holmake.log)"
say "proofs: 42 lemma theories and delta3_slab_sound, delta3_inner_sound, delta3_cover_sound built"
L="$W/lemmas"; mkdir -p "$L"; cp "$R/lemmas/diagdomScript.sml" "$L/"
( cd "$L" && timed lemma-diagdom "$L/holmake.log" Holmake diagdomTheory.uo ) || fail "lemmas/diagdom ($L/holmake.log)"
say "lemmas: diagdom built"

# ---- 5. the kernel runs ----------------------------------------------------------------------------------------
K="$W/kernel"; mkdir -p "$K"
cp "$R"/checker/delta3DataLib.sig "$R"/checker/delta3DataLib.sml "$R"/checker/delta3_coverScript.sml "$K/"
cp "$R"/proofs/assembly/delta3_slab_boundsScript.sml "$R"/proofs/assembly/delta3_layer1Script.sml "$R/proofs/assembly/check.sml" "$K/"
printf 'INCLUDES = %s %s\n' "$B" "$P" > "$K/Holmakefile"
printf 'delta3_coverTheory.sml: ../d3/cover.d3 ../d3/cover_red_gap.d3 ../d3/cover_red_noinner.d3 ../d3/cover_red_short.d3\n' >> "$K/Holmakefile"
printf 'input\tkind\texpected\tkernel\tdetail\ttheorem_file\n' > "$W/verdicts.tsv"
BAD=0
tail -n +2 "$R/kernel/expected/verdicts.tsv" | grep -v '^cover' > "$W/inputs.tsv"
while IFS=$'\t' read -r nm kind expect; do
  cp "$D/$nm.d3" "$K/"
  e="$expect"; [ "$expect" = LOADER ] && e=F
  sed -e "s/@NAME@/$nm/g" -e "s/@EXPECT@/$e/g" "$R/checker/$kind.template" > "$K/delta3_${nm}Script.sml"
  printf 'delta3_%sTheory.sml: %s.d3\n' "$nm" "$nm" >> "$K/Holmakefile"
  set +e; ( cd "$K" && timed "kernel-$nm" "$K/holmake.$nm.log" Holmake "delta3_${nm}Theory.uo" ); rc=$?; set -e
  got=$(grep -ah '^D3RESULT' "$K/.hol/logs/delta3_${nm}Theory" 2>/dev/null | cut -f3 || true)
  if [ "$expect" = LOADER ]; then
    if [ $rc -ne 0 ] && [ -z "$got" ] && grep -aq 'String not DEC' "$K/.hol/logs/delta3_${nm}Theory" 2>/dev/null; then
      printf '%s\t%s\tLOADER\tLOADER\trefused by the loader: String not DEC\t-\n' "$nm" "$kind" >> "$W/verdicts.tsv"
    else
      printf '%s\t%s\tLOADER\t%s\tNOT REFUSED BY THE LOADER\t-\n' "$nm" "$kind" "${got:-none}" >> "$W/verdicts.tsv"; BAD=1
    fi
    continue
  fi
  same=differs; cmp -s "$K/$nm.theorem.txt" "$R/kernel/expected/$nm.theorem.txt" && same=identical
  printf '%s\t%s\t%s\t%s\t%s\t%s\n' "$nm" "$kind" "$expect" "${got:-none}" \
    "$(grep -ah '^D3RESULT' "$K/.hol/logs/delta3_${nm}Theory" 2>/dev/null | cut -f5-7 | tr '\t' ' ')" "$same" >> "$W/verdicts.tsv"
  { [ $rc -eq 0 ] && [ "$got" = "$expect" ] && [ "$same" = identical ]; } || BAD=1
  # a forgery's theory is not needed after its verdict: its objects go (about 10 MB each), unless KEEP_ALL=1
  if [ "$expect" = F ] && [ "${KEEP_ALL:-0}" != 1 ]; then rm -f "$K"/.hol/objs/delta3_"${nm}"Theory.* "$K/$nm.d3"; fi
done < "$W/inputs.tsv"
set +e; ( cd "$K" && timed kernel-cover "$K/holmake.cover.log" Holmake delta3_coverTheory.uo ); rc=$?; set -e
for nm in cover cover_red_gap cover_red_noinner cover_red_short; do
  expect=$(awk -F'\t' -v n="$nm" '$1 == n {print $3}' "$R/kernel/expected/verdicts.tsv")
  got=$(grep -ah "^D3RESULT	$nm	" "$K/.hol/logs/delta3_coverTheory" 2>/dev/null | cut -f3 || true)
  same=differs; cmp -s "$K/$nm.theorem.txt" "$R/kernel/expected/$nm.theorem.txt" && same=identical
  printf '%s\tcover\t%s\t%s\t%s\t%s\n' "$nm" "$expect" "${got:-none}" \
    "$(grep -ah "^D3RESULT	$nm	" "$K/.hol/logs/delta3_coverTheory" 2>/dev/null | cut -f5-7 | tr '\t' ' ')" "$same" >> "$W/verdicts.tsv"
  { [ $rc -eq 0 ] && [ "$got" = "$expect" ] && [ "$same" = identical ]; } || BAD=1
done
[ $BAD -eq 0 ] || { cat "$W/verdicts.tsv" | tee -a "$LOG"; fail "a kernel verdict or a theorem file differs from its record"; }
say "kernel: $(awk -F'\t' 'NR>1 && $4=="T"' "$W/verdicts.tsv" | wc -l | tr -d ' ') genuine inputs T, $(awk -F'\t' 'NR>1 && $4=="F"' "$W/verdicts.tsv" | wc -l | tr -d ' ') forgeries F, $(awk -F'\t' 'NR>1 && $4=="LOADER"' "$W/verdicts.tsv" | wc -l | tr -d ' ') refused by the loader; every theorem file identical to its record"

# ---- 6. the Layer-1 theorem and the read-back ------------------------------------------------------------------
( cd "$K" && timed layer1 "$K/holmake.layer1.log" Holmake delta3_layer1Theory.uo ) || fail "delta3_layer1 ($K/holmake.layer1.log)"
( cd "$K" && timed read-back "$W/check.log" hol < "$K/check.sml" ) || fail "the read-back ($W/check.log)"
[ "$(grep -c '^SOUND .* true oracles \[DISK_THM\] axioms \[\] hyps 0$' "$W/check.out")" = 3 ] \
  || fail "a soundness theorem is not exactly its statement, or carries a hypothesis, an axiom or another oracle"
grep -q '^THM delta3_layer1 oracles \[DISK_THM\] axioms \[\] hyps 0$' "$W/check.out" || fail "delta3_layer1's tags"
[ "$(grep -c '^AXIOMS_IN' "$W/check.out")" = 1 ] && grep -q '^AXIOMS_IN bool SELECT_AX,INFINITY_AX,ETA_AX,BOOL_CASES_AX$' "$W/check.out" \
  || fail "an axiom outside bool's four in the ancestry"
say "read-back: slab_check_sound, inner_check_sound, cover_all_sound exactly as stated; delta3_layer1; only DISK_THM, no axiom tag, no hypothesis"

# ---- 7. CakeML (optional) --------------------------------------------------------------------------------------
if [ $CAKEML -eq 1 ]; then
  PREFIX="${PREFIX:-$W/cm}" bash "$R/cakeml/replay.sh" "$R" 2>&1 | tee "$W/cakeml.log" || fail "cakeml/replay.sh ($W/cakeml.log)"
  say "cakeml: the binary agrees with the kernel on every input"
fi

say "replay: PASSED in $(( $(date +%s) - T0 )) s"
cat "$TIMES" | tee -a "$LOG"
