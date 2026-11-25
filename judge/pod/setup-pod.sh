#!/usr/bin/env bash
# setup-pod.sh — makes a fresh Ubuntu 24.04 pod (root) into the benchmark's remote judge.
# hol4/delta3/harness/pod · 2026-11-25. Run ON THE POD, from the folder push.sh copied:
#     bash /root/judge-src/setup-pod.sh
# 1. the toolchain: Day 1's setup.sh, unchanged (Poly/ML v5.9.2 + HOL4 trindemossen-2-v9 at 652d1f0a…, ≈ 20 min on 8 vCPU)
#    into /root/work (polyml-install/, HOL/);
# 2. SLOTS (default 16) unprivileged slot users judge0.. (no home, no shell, no sudo) — one per concurrent attempt;
# 3. /root/judge: judgelib.py + runner.py (byte copies from the Mac), jail (compiled from jail.c here),
#    base/ built from the four frozen scripts with Holmake, the queue folders;
# 4. permissions: slot users may read HOL, Poly/ML and base, write nothing but their own run directory;
# 5. the selftest (no network, no writes outside the run directory, as a slot user, without HOL).
# It does not start the runner: `python3 /root/judge/runner.py serve --slots 8` (POD.md).
set -euo pipefail
SRC="$(cd "$(dirname "$0")" && pwd)"
J=/root/judge
export PREFIX=/root/work
# 1 — Day 1's setup.sh with the tags and commits of PIN.json (the one pin) written into a copy
PIN() { python3 -c "import json,sys; print(json.load(open('$SRC/PIN.json'))[sys.argv[1]])" "$1"; }
sed -e "s/^POLY_TAG=.*/POLY_TAG=\"$(PIN poly_tag)\"/" -e "s/^POLY_COMMIT=.*/POLY_COMMIT=\"$(PIN poly_commit)\"/" \
    -e "s/^HOL_TAG=.*/HOL_TAG=\"$(PIN hol_tag)\"/" -e "s/^HOL_COMMIT=.*/HOL_COMMIT=\"$(PIN hol_commit)\"/" \
    "$SRC/setup.sh" > "$SRC/setup-pinned.sh"
export DEBIAN_FRONTEND=noninteractive
[ -x /usr/bin/time ] || { apt-get update -qq && apt-get install -y -qq time; }   # Day 1's setup.sh times every step with it
HOLD="$(PIN hol_dir_pod)"           # where the pinned HOL lives on the pod (PIN.json)
if [ ! -x "$HOLD/bin/Holmake" ]; then
  if [ "$HOLD" = "$PREFIX/HOL" ]; then bash "$SRC/setup-pinned.sh"
  else
    [ -x "$PREFIX/polyml-install/bin/poly" ] || bash "$SRC/setup-pinned.sh"    # Poly/ML first (it also builds a HOL in $PREFIX)
    bash "$SRC/build-hol-alt.sh" "$(PIN hol_tag)" "$(PIN hol_commit)"            # HOL at the pin in /root/work-<tag>/HOL
  fi
fi
export PATH="$HOLD/bin:$PREFIX/polyml-install/bin:$PATH"
export LD_LIBRARY_PATH="$PREFIX/polyml-install/lib:${LD_LIBRARY_PATH:-}"
test "$(git -C "$HOLD" rev-parse HEAD)" = "$(PIN hol_commit)" || { echo "HOL on the pod is not at the pin"; exit 1; }
# 2
SLOTS="${SLOTS:-16}"     # one unprivileged user per concurrent attempt (16 on the 16-vCPU / 128 GB judge pod)
for k in $(seq 0 $((SLOTS - 1))); do
  id "judge$k" >/dev/null 2>&1 || useradd --system --no-create-home --shell /usr/sbin/nologin "judge$k"
done
# 3
mkdir -p "$J"/{inbox,running,outbox,runs,base}
cp "$SRC/judgelib.py" "$SRC/runner.py" "$SRC/jail.c" "$SRC/PIN.json" "$J/"
gcc -O2 -Wall -o "$J/jail" "$J/jail.c"
cp "$SRC"/base/delta3_checkScript.sml "$SRC"/base/delta3_check2Script.sml "$SRC"/base/delta3_semScript.sml \
   "$SRC"/base/delta3_stmtsScript.sml "$J/base/"
rm -rf "$J/base/.hol"                                                     # a clean base at the pinned HOL
( cd "$J/base" && nice -n 10 Holmake delta3_stmtsTheory.uo ) > "$J/base-build.log" 2>&1
# warm-up: one build against the base, outside any sandbox, so that Holmake writes the base's remaining
# dependency files (.hol/make-deps/*Theory.{sml,sig}.d) now; a sandboxed attempt may not write into the base,
# and on Linux Holmake would otherwise try to (found on the judge pod, 2026-11-25)
W="$(mktemp -d)"; printf 'Theory attempt\nAncestors\n  arithmetic delta3_stmts\n\nTheorem C01:\n  !n:num. n + 0 = n\nProof\n  simp[]\nQED\n' > "$W/attemptScript.sml"
printf 'INCLUDES = %s\n' "$J/base" > "$W/Holmakefile"; ( cd "$W" && nice -n 10 Holmake attemptTheory.uo > /dev/null ); rm -rf "$W"

# 4
chmod 711 /root "$J" "$J/runs"
chmod 700 "$J/inbox" "$J/running" "$J/outbox"
chmod -R a+rX "$HOLD" "$PREFIX/polyml-install" "$J/base"
chmod 755 "$J/jail"; chmod 644 "$J/judgelib.py" "$J/runner.py" "$J/jail.c" "$J/PIN.json"
# 5
cd "$J" && python3 runner.py selftest
python3 runner.py info > "$J/info.json"; cat "$J/info.json"
echo "setup-pod: done $(date -u +%Y-%m-%dT%H:%M:%SZ)"
