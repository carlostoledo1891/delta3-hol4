#!/usr/bin/env bash
# gen.sh <NAME> <T|F> — writes delta3_<NAME>Script.sml from slab.template
set -euo pipefail
sed -e "s/@NAME@/$1/g" -e "s/@EXPECT@/$2/g" slab.template > "delta3_$1Script.sml"
