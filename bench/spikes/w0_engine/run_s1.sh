#!/bin/sh
# S1 sweep: grains 2^13..2^16 x threads 1/4/12 for the chunked modes, the flat modes at 1 thread,
# the build cost per grain; N fresh processes per cell, interleaved (every cell once per round), the
# 1-minute load average recorded with every sample. Raw samples: results/s1.jsonl (append).
#   sh bench/spikes/w0_engine/run_s1.sh [N=5] [REPS=10]
# Summarise: python3 bench/spikes/w0_engine/summarize.py bench/spikes/w0_engine/results/s1.jsonl
set -e
cd "$(dirname "$0")/../../.."
BEND=${BEND:-$HOME/.bend/bin/bend}
N=${1:-5}
REPS=${2:-10}
OUT=bench/spikes/w0_engine/results/s1.jsonl
mkdir -p build bench/spikes/w0_engine/results
$BEND bench/spikes/w0_engine/s1_chunks.bend -o build/s1
load() { sysctl -n vm.loadavg | awk '{print $2}'; }
cell() { # threads mode grain
  l=$(load)
  line=$(build/s1 --threads "$1" "$2" "$3" "$REPS")
  printf '{"spike":"s1","threads":%s,"round":%s,"load1":%s,"commit":"%s",%s\n' "$1" "$round" "$l" "$COMMIT" "${line#\{}" >> "$OUT"
}
COMMIT=$(git rev-parse --short HEAD 2>/dev/null || echo unknown)
echo "# start $(date) load=$(load)" >> "$OUT"
round=0
while [ "$round" -lt "$N" ]; do
  for m in q1today q1today3 q1fused q2today q2fused; do cell 1 "$m" 20; done
  for g in 13 14 15 16; do
    cell 1 build "$g"
    for t in 1 4 12; do
      cell "$t" q1chunk "$g"
      cell "$t" q2chunk "$g"
    done
  done
  round=$((round + 1))
done
echo "# end $(date) load=$(load)" >> "$OUT"
