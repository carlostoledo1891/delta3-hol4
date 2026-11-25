#!/usr/bin/env bash
# toolchain/setup.sh — Poly/ML and HOL4 from source at the commits in PINS.json, on Ubuntu 24.04 x86_64.
# Day 1's setup.sh (the pod of 2026-11-24), moved to the PINS.json tags and made re-runnable for CI.
#
#   PREFIX=<dir> bash toolchain/setup.sh     installs under <dir> (default: <repository>/_toolchain)
#   SKIP_APT=1                               do not install the system packages (CI installs them first)
#
# A step whose result is already there at the right commit is skipped, so a restored cache costs nothing.
# Writes $PREFIX/logs/*.log and $PREFIX/logs/setup-times.tsv (wall seconds, peak resident kB).
set -euo pipefail
R="$(cd "$(dirname "$0")/.." && pwd)"
pin() { python3 -I -c 'import json,sys; print(json.load(open(sys.argv[1]))[sys.argv[2]])' "$R/PINS.json" "$1"; }
PREFIX="${PREFIX:-$R/_toolchain}"
POLY_TAG=$(pin poly_tag); POLY_COMMIT=$(pin poly_commit)
HOL_TAG=$(pin hol_tag);   HOL_COMMIT=$(pin hol_commit)
SUDO=""; [ "$(id -u)" = 0 ] || SUDO=sudo
mkdir -p "$PREFIX/logs"; LOGS="$PREFIX/logs"; TIMES="$LOGS/setup-times.tsv"
[ -f "$TIMES" ] || printf 'step\tstart_utc\twall_s\tmax_rss_kb\n' > "$TIMES"

# 0. system packages (GNU time first: step() needs it)
if [ "${SKIP_APT:-0}" != 1 ]; then
  export DEBIAN_FRONTEND=noninteractive
  $SUDO apt-get update -qq
  $SUDO apt-get install -y -qq build-essential git curl ca-certificates libgmp-dev time python3 pkg-config
fi
step() {  # step <name> <command...>
  local name="$1"; shift
  local t0; t0=$(date -u +%Y-%m-%dT%H:%M:%SZ)
  /usr/bin/time -f '%e %M' -o "$LOGS/$name.time" "$@" > "$LOGS/$name.log" 2>&1 || { tail -40 "$LOGS/$name.log"; exit 1; }
  read -r wall rss < "$LOGS/$name.time"
  printf '%s\t%s\t%s\t%s\n' "$name" "$t0" "$wall" "$rss" >> "$TIMES"
}

# 1. Poly/ML, from source, at the release tag
export PATH="$PREFIX/polyml-install/bin:$PATH"
export LD_LIBRARY_PATH="$PREFIX/polyml-install/lib:${LD_LIBRARY_PATH:-}"
if [ -f "$PREFIX/polyml-install/.built-$POLY_COMMIT" ]; then
  echo "Poly/ML $POLY_TAG: already built"
else
  cd "$PREFIX"; [ -d polyml ] || git clone -q https://github.com/polyml/polyml.git
  cd polyml; git checkout -q "$POLY_TAG"
  test "$(git rev-parse HEAD)" = "$POLY_COMMIT" || { echo "Poly/ML commit mismatch: $(git rev-parse HEAD)"; exit 1; }
  step polyml-configure ./configure --prefix="$PREFIX/polyml-install" --with-gmp
  step polyml-make make -j"$(nproc)"
  step polyml-compiler make compiler
  step polyml-install make install
  touch "$PREFIX/polyml-install/.built-$POLY_COMMIT"
fi
poly -v | tee "$LOGS/poly-version.txt"

# 2. HOL4, at the release tag
if [ -f "$PREFIX/HOL/.built-$HOL_COMMIT" ] && [ "$(git -C "$PREFIX/HOL" rev-parse HEAD)" = "$HOL_COMMIT" ]; then
  echo "HOL4 $HOL_TAG: already built"
else
  cd "$PREFIX"; [ -d HOL ] || git clone -q https://github.com/HOL-Theorem-Prover/HOL.git
  cd HOL; git checkout -q "$HOL_TAG"
  test "$(git rev-parse HEAD)" = "$HOL_COMMIT" || { echo "HOL commit mismatch: $(git rev-parse HEAD)"; exit 1; }
  step hol-configure bash -c 'poly < tools/smart-configure.sml'
  step hol-build bin/build
  touch "$PREFIX/HOL/.built-$HOL_COMMIT"
fi
echo "HOL built: $(git -C "$PREFIX/HOL" rev-parse HEAD)" | tee "$LOGS/hol-version.txt"
cat "$TIMES"
