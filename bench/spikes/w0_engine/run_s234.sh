#!/bin/sh
# S2 / S3 / S4 sweep: N fresh processes per cell, interleaved, load recorded. Raw samples append to
# results/s2.jsonl, results/s3.jsonl, results/s4.jsonl.
#   sh bench/spikes/w0_engine/run_s234.sh [N=5] [REPS=10]
set -e
cd "$(dirname "$0")/../../.."
BEND=${BEND:-$HOME/.bend/bin/bend}
N=${1:-5}
REPS=${2:-10}
R=bench/spikes/w0_engine/results
mkdir -p build "$R"
$BEND bench/spikes/w0_engine/s2_align.bend -o build/s2
$BEND bench/spikes/w0_engine/s3_reduce.bend -o build/s3
$BEND bench/spikes/w0_engine/s4_owner.bend -o build/s4
COMMIT=$(git rev-parse --short HEAD 2>/dev/null || echo unknown)
load() { sysctl -n vm.loadavg | awk '{print $2}'; }
# bin spike threads mode grain reps out : one process; every output line becomes a record
cell() {
  l=$(load)
  "build/$1" --threads "$3" "$4" "$5" "$6" | while IFS= read -r line; do
    printf '{"spike":"%s","threads":%s,"round":%s,"load1":%s,"commit":"%s",%s\n' "$2" "$3" "$round" "$l" "$COMMIT" "${line#\{}" >> "$7"
  done
}
cell4() {
  l=$(load)
  line=$(build/s4 --threads 1 "$1" "$REPS")
  printf '{"spike":"s4","threads":1,"round":%s,"load1":%s,"commit":"%s",%s\n' "$round" "$l" "$COMMIT" "${line#\{}" >> "$R/s4.jsonl"
}
for f in s2 s3 s4; do echo "# start $(date) load=$(load)" >> "$R/$f.jsonl"; done
round=0
while [ "$round" -lt "$N" ]; do
  for t in 1 4 12; do
    for m in ragged concat rechunk; do cell s2 s2 "$t" "$m" 14 "$REPS" "$R/s2.jsonl"; done
    cell s2 s2 "$t" misaligned 14 1 "$R/s2.jsonl"
    for m in usum fsum aggs gathers; do cell s3 s3 "$t" "$m" 14 "$REPS" "$R/s3.jsonl"; done
  done
  for m in colclone colmove mapfresh mapinplace nsboxed nsflat; do cell4 "$m"; done
  round=$((round + 1))
done
for f in s2 s3 s4; do echo "# end $(date) load=$(load)" >> "$R/$f.jsonl"; done
