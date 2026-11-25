#!/usr/bin/env bash
# setup-cakeml.sh — the toolchain for hol4/delta3/cakeml, from nothing, on Ubuntu 24.04 (x86_64).
#   Poly/ML v5.9.2 (from source), HOL4 trindemossen-2-v10, CakeML release v3671 (source, for the
#   translator and the basis library), and the released CakeML compiler binary of v3671 (cake-x64-64).
# Every revision is pinned by commit hash or sha256; a mismatch stops the script.
# Usage:  bash setup-cakeml.sh                 (installs under $PREFIX, default /root/cm)
#         STEPS="cake hol" bash setup-cakeml.sh  (only some steps; default: all, in order)
# Writes: $PREFIX/logs/<step>.log and $PREFIX/logs/setup-times.tsv (wall s, peak RSS kB, cgroup peak)
#
# Why HOL trindemossen-2-v10 and not -v9 (the Day-1 pin): CakeML's release v3671 says
# "Corresponding HOL commit: trindemossen-2-v10 (9783a499…)", and no CakeML release names -v9.
# The only CakeML revision documented with -v9 is 239aca18 on the unreleased branch
# `version-string` (developers/changes-since-release.md at 67faf9d8), which has no released
# compiler binary. See PINS-cakeml.json.
set -euo pipefail

PREFIX="${PREFIX:-/root/cm}"
STEPS="${STEPS:-apt poly hol cakeml cake basis}"
POLY_TAG="v5.9.2";            POLY_COMMIT="4557554077078decce4ce5f90da00a713cfc32e4"
HOL_TAG="trindemossen-2-v10"; HOL_COMMIT="9783a49979c94c401ff8c0e51b2eefae7ea95ae3"
CML_TAG="v3671";              CML_COMMIT="16bdb1aaaab64a6ac66504ad2e9f0ed6146060e9"
CAKE_URL="https://github.com/CakeML/cakeml/releases/download/v3671/cake-x64-64.tar.gz"
CAKE_SHA256="e3edd113497bf7fce443e69c70f09c3df1942849251c86ce8e44e6327ade0d3d"  # GitHub's asset digest

mkdir -p "$PREFIX/logs"; LOGS="$PREFIX/logs"; TIMES="$LOGS/setup-times.tsv"
[ -f "$TIMES" ] || printf 'step\tstart_utc\twall_s\tmax_rss_kb\tcgroup_peak_bytes\n' > "$TIMES"
cgpeak() { cat /sys/fs/cgroup/memory.peak 2>/dev/null || echo NA; }
step() {   # returns the command's own exit status (so that "step a || step b" works under set -e)
  local name="$1"; shift
  local t0; t0=$(date -u +%Y-%m-%dT%H:%M:%SZ)
  local rc=0
  /usr/bin/time -f '%e %M' -o "$LOGS/$name.time" "$@" > "$LOGS/$name.log" 2>&1 || rc=$?
  read -r wall rss < <(tail -n 1 "$LOGS/$name.time")
  printf '%s\t%s\t%s\t%s\t%s\n' "$name" "$t0" "$wall" "$rss" "$(cgpeak)" >> "$TIMES"
  return $rc
}
want() { case " $STEPS " in *" $1 "*) return 0;; *) return 1;; esac; }
export PATH="$PREFIX/polyml-install/bin:$PREFIX/HOL/bin:$PATH"
export LD_LIBRARY_PATH="$PREFIX/polyml-install/lib:${LD_LIBRARY_PATH:-}"
export CAKEMLDIR="$PREFIX/cakeml"

if want apt; then
  export DEBIAN_FRONTEND=noninteractive
  # GNU time first: step() needs it
  [ -x /usr/bin/time ] || { apt-get update -qq && apt-get install -y -qq time; }
  step apt bash -c 'apt-get update -qq && apt-get install -y -qq build-essential git curl ca-certificates libgmp-dev time python3 nodejs jq xz-utils pkg-config autoconf libtool'
fi

if want poly; then
  cd "$PREFIX"; [ -d polyml ] || git clone -q https://github.com/polyml/polyml.git
  cd polyml; git checkout -q "$POLY_TAG"
  test "$(git rev-parse HEAD)" = "$POLY_COMMIT" || { echo "Poly/ML commit mismatch"; exit 1; }
  step polyml-configure ./configure --prefix="$PREFIX/polyml-install" --with-gmp
  step polyml-make make -j"$(nproc)"
  step polyml-compiler make compiler
  step polyml-install make install
  poly -v | tee "$LOGS/poly-version.txt"
fi

if want hol; then
  cd "$PREFIX"; [ -d HOL ] || git clone -q https://github.com/HOL-Theorem-Prover/HOL.git
  cd HOL; git checkout -q "$HOL_TAG"
  test "$(git rev-parse HEAD)" = "$HOL_COMMIT" || { echo "HOL commit mismatch"; exit 1; }
  step hol-configure bash -c 'poly < tools/smart-configure.sml'
  step hol-build bin/build
  echo "HOL built: $(git rev-parse HEAD)" | tee "$LOGS/hol-version.txt"
fi

if want cakeml; then
  cd "$PREFIX"; [ -d cakeml ] || git clone -q https://github.com/CakeML/cakeml.git
  cd cakeml; git checkout -q "$CML_TAG"
  test "$(git rev-parse HEAD)" = "$CML_COMMIT" || { echo "CakeML commit mismatch"; exit 1; }
  echo "CakeML checked out: $(git rev-parse HEAD)" | tee "$LOGS/cakeml-version.txt"
fi

if want cake; then
  mkdir -p "$PREFIX/cake-release"; cd "$PREFIX/cake-release"
  [ -f cake-x64-64.tar.gz ] || curl -sSL -o cake-x64-64.tar.gz "$CAKE_URL"
  echo "$CAKE_SHA256  cake-x64-64.tar.gz" | sha256sum -c -
  rm -rf cake-x64-64; tar xzf cake-x64-64.tar.gz
  cd cake-x64-64; step cake-make make cake
  ./cake --version > "$LOGS/cake-version.txt" 2>&1 || true
  sha256sum cake cake.S basis_ffi.c Makefile | tee "$LOGS/cake-sha256.txt"
fi

if want basis; then
  # the translator, CF and the basis library (not the compiler proofs, not the bootstrap)
  cd "$PREFIX/cakeml/basis"
  # Holmake resumes where it stopped; one retry on one core, because on 2026-11-25 the replay's first
  # attempt stopped in basis-heap with Poly/ML's "Run out of store" while two other theories built beside it
  step cakeml-basis Holmake -j"$(nproc)" || step cakeml-basis-retry Holmake -j1
fi

cat "$TIMES"
