#!/usr/bin/env bash
# W2.3 wiring differential (bench/w2/wire.bend): group_by / unique / sort / n_unique / min / max /
# comparisons over Raw and Dictionary string columns at frame level, every shape x size x null
# pattern, against the v0.1 output recorded in bench/w2/results/wire_v01.txt. That file was produced
# by this same script with WIRE_BIN = wire.bend built at the pre-W2.3 tree (commit c79d5f5, the Map
# coder): WIRE_OUT=bench/w2/results/wire_v01.txt WIRE_BIN=<that binary> bench/w2/wire.sh record
#   bench/w2/wire.sh            build the current tree's probe, run the matrix, compare (exit 1 on any diff)
#   WIRE_JOBS=4                 parallel processes (default 4)
#   WIRE_BIG=0                  skip the 300k / 1M cells (minutes each on v0.1, seconds now)
set -euo pipefail
cd "$(dirname "$0")/../.."
BEND=${BEND:-$HOME/.bend/bin/bend}
JOBS=${WIRE_JOBS:-4}
BIG=${WIRE_BIG:-1}
mode=${1:-check}
mkdir -p build/w2
if [ -z "${WIRE_BIN:-}" ]; then
  "$BEND" bench/w2/wire.bend -o build/w2/wire
  WIRE_BIN=build/w2/wire
fi
cells() {
  for shape in distinct prefix longprefix skew equal low uni empty nul aligned wide; do
    for n in 0 1 2 7 33 1000 4097 30000 100000; do
      for nulls in none some heavy; do echo "$shape $n $nulls"; done
    done
    for n in 1 33 4097; do echo "$shape $n all"; done
  done
  if [ "$BIG" -ne 0 ]; then
    for shape in distinct skew longprefix; do
      echo "$shape 300000 none"
      echo "$shape 300000 heavy"
    done
    echo "distinct 1000000 some"
  fi
}
out=$(mktemp)
cells | xargs -P "$JOBS" -L 1 "$WIRE_BIN" > "$out"
LC_ALL=C sort "$out" -o "$out"
if [ "$mode" = record ]; then
  mv "$out" "${WIRE_OUT:?WIRE_OUT names the file to record}"
  echo "recorded $(wc -l < "$WIRE_OUT") lines in $WIRE_OUT"
  exit 0
fi
ref=bench/w2/results/wire_v01.txt
if [ "$BIG" -eq 0 ]; then
  grep -v -E ' (300000|1000000) ' "$ref" > "$out.ref"
else
  cp "$ref" "$out.ref"
fi
if diff "$out.ref" "$out" > "$out.diff"; then
  echo "wire differential: $(wc -l < "$out") lines equal to v0.1"
  rm -f "$out" "$out.ref" "$out.diff"
else
  cat "$out.diff"
  echo "wire differential: FAILED"
  exit 1
fi
