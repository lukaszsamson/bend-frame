#!/usr/bin/env bash
# W2.1 / W2.2 native differential matrix (bench/w2/w2diff.bend): every shape, sizes 0 .. 20000,
# including the wide shape the interpreter tests cannot build. Exit 1 on any BAD line.
#   bench/w2/diff.sh            (build + run, about a minute)
#   make w2-diff
set -euo pipefail
cd "$(dirname "$0")/../.."
BEND=${BEND:-$HOME/.bend/bin/bend}
mkdir -p build/w2
"$BEND" bench/w2/w2diff.bend -o build/w2/w2diff
bad=0
count=0
for shape in distinct prefix longprefix skew equal low uni empty nul aligned wide; do
  for n in 0 1 2 3 7 8 9 33 129 1000 5000 20000; do
    out=$(build/w2/w2diff "$shape" "$n")
    count=$((count + 3))
    if printf '%s\n' "$out" | grep -q BAD; then
      printf '%s\n' "$out" | grep BAD
      bad=1
    fi
  done
done
if [ "$bad" -ne 0 ]; then
  echo "w2 differential: FAILED"
  exit 1
fi
echo "w2 differential: $count checks ok"
