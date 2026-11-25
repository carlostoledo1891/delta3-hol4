#!/usr/bin/env bash
# run-binary.sh — the CakeML binary on every input, each run timed; its verdict compared with the
# kernel's. Exits nonzero on ANY disagreement or on any run that does not print a verdict line.
# Usage: bash run-binary.sh <binary> <inputs.tsv> <out dir>
#   inputs.tsv: input path <TAB> kernel verdict (T, F, or LOADER for an input the kernel's loader refuses)
# Writes <out>/binary-runs.tsv (input, sha256, kernel, binary stdout, exit code, wall s, max RSS kB,
# agreement) and <out>/stdout/<name>.txt.
set -uo pipefail
BIN="$1"; LIST="$2"; OUT="$3"
mkdir -p "$OUT/stdout"
T="$OUT/binary-runs.tsv"
printf 'input\tinput_sha256\tkernel\tbinary_stdout\texit\twall_s\tmax_rss_kb\tagree\n' > "$T"
bad=0
while IFS=$'\t' read -r inp kern; do
  [ -z "$inp" ] && continue
  case "$inp" in \#*) continue;; esac
  nm=$(basename "$inp" .d3)
  sha=$(sha256sum "$inp" | cut -d' ' -f1)
  /usr/bin/time -f '%e %M' -o "$OUT/stdout/$nm.time" "$BIN" < "$inp" > "$OUT/stdout/$nm.txt" 2> "$OUT/stdout/$nm.err"
  code=$?
  read -r wall rss < "$OUT/stdout/$nm.time"
  got=$(tr -d '\n' < "$OUT/stdout/$nm.txt")
  case "$kern:$got" in
    T:"ACCEPT "*) ok=yes;;
    F:"REJECT "*) ok=yes;;
    LOADER:MALFORMED) ok=yes;;
    *) ok=NO; bad=1;;
  esac
  [ "$code" = 0 ] || { ok=NO; bad=1; }
  printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n' "$inp" "$sha" "$kern" "$got" "$code" "$wall" "$rss" "$ok" >> "$T"
done < "$LIST"
cat "$T"
if [ "$bad" = 0 ]; then echo "ALL AGREE"; else echo "DISAGREEMENT OR FAILED RUN — see $T"; exit 1; fi
