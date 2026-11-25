#!/usr/bin/env bash
# build-binary.sh — after setup-cakeml.sh: the HOL side (frozen checker → CakeML translation →
# main + CF proofs → delta3.sexp; the same S-expression computed in HOL with its read-back theorem,
# delta3.proved.sexp, checked equal), then the released cake binary compiles it to x64
# assembly, and gcc links it with the release's basis_ffi.c.
# Usage: bash build-binary.sh <this folder> <checker source dir> [PREFIX=/root/cm]
#   <checker source dir> holds delta3_checkScript.sml and delta3_check2Script.sml — the checker is an
#   INPUT, read from there at build time (on 2026-11-25: hol4/delta3/harness/base, the frozen ones);
#   the translation (hol/prog/delta3_cmlProgScript.sml) translates whatever those two theories define.
# Writes: $PREFIX/out/{delta3.sexp, delta3.S, delta3}, $PREFIX/logs/build-*.{log,time},
#   $PREFIX/logs/checker-input/ (the two files as used, with their sha256)
set -euo pipefail
HERE="$(cd "$1" && pwd)"
CHK="$(cd "$2" && pwd)"
PREFIX="${PREFIX:-/root/cm}"
export PATH="$PREFIX/polyml-install/bin:$PREFIX/HOL/bin:$PATH"
export LD_LIBRARY_PATH="$PREFIX/polyml-install/lib:${LD_LIBRARY_PATH:-}"
export CAKEMLDIR="$PREFIX/cakeml"
LOGS="$PREFIX/logs"; OUT="$PREFIX/out"; mkdir -p "$LOGS" "$OUT"
TIMES="$LOGS/build-times.tsv"
[ -f "$TIMES" ] || printf 'step\tstart_utc\twall_s\tmax_rss_kb\n' > "$TIMES"
step() {
  local name="$1"; shift
  local t0; t0=$(date -u +%Y-%m-%dT%H:%M:%SZ)
  /usr/bin/time -f '%e %M' -o "$LOGS/$name.time" "$@" > "$LOGS/$name.log" 2>&1
  read -r wall rss < "$LOGS/$name.time"
  printf '%s\t%s\t%s\t%s\n' "$name" "$t0" "$wall" "$rss" >> "$TIMES"
}
# the HOL scripts go inside the CakeML checkout, where CakeML's holproject.toml resolves its directories
D="$CAKEMLDIR/examples/delta3_cakeml"
mkdir -p "$D"; cp -r "$HERE/hol/checker" "$HERE/hol/prog" "$D/"
cp "$CHK/delta3_checkScript.sml" "$CHK/delta3_check2Script.sml" "$D/checker/"
mkdir -p "$LOGS/checker-input"
cp "$CHK/delta3_checkScript.sml" "$CHK/delta3_check2Script.sml" "$LOGS/checker-input/"
( cd "$LOGS/checker-input" && sha256sum delta3_checkScript.sml delta3_check2Script.sml > SHA256 && cat SHA256 )
cd "$D/checker"; step build-checker Holmake
cd "$D/prog";    step build-translation Holmake delta3_cmlProgTheory.uo
cd "$D/prog";    step build-main Holmake delta3_cmlMainTheory.uo
cd "$D/prog";    step build-meaning Holmake delta3_cmlMeaningTheory.uo
# the S-expression again, computed IN HOL with a theorem that it reads back to delta3_prog
# (delta3_cmlSexpScript.sml; about 8 min and 7 GB); it must equal the ML printer's byte for byte
cd "$D/prog";    step build-sexp Holmake delta3_cmlSexpTheory.uo
cp "$D/prog/delta3.sexp" "$OUT/delta3.sexp"
cp "$D/prog/delta3.proved.sexp" "$OUT/delta3.proved.sexp"
if cmp "$OUT/delta3.proved.sexp" "$OUT/delta3.sexp"; then
  echo "delta3.proved.sexp (HOL) and delta3.sexp (astToSexprLib) are byte-identical" | tee "$LOGS/sexp-compare.txt"
else
  echo "delta3.proved.sexp and delta3.sexp DIFFER" | tee "$LOGS/sexp-compare.txt"; exit 1
fi
# compile with the RELEASED verified compiler binary (no --skip_type_inference: type inference runs)
REL="$PREFIX/cake-release/cake-x64-64"
step cake-compile bash -c "'$REL/cake' --sexp=true --exclude_prelude=true < '$OUT/delta3.proved.sexp' > '$OUT/delta3.S'"
step gcc-link gcc "$OUT/delta3.S" "$REL/basis_ffi.c" -lm -o "$OUT/delta3"
sha256sum "$OUT/delta3.sexp" "$OUT/delta3.proved.sexp" "$OUT/delta3.S" "$OUT/delta3" | tee "$LOGS/binary-sha256.txt"
cat "$TIMES"
