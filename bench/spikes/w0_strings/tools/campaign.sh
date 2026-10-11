#!/usr/bin/env bash
# The W0 strings/reader measurement campaign (PROVISIONAL numbers on a shared machine).
# Run from bench/spikes/w0_strings after tools/build.sh; every command runs >= 5 times as a fresh
# process, interleaved, with the load recorded (tools/run.py). Raw samples: results/*.jsonl.
#   tools/campaign.sh [t1 t2 t3 t5 t6 t4]   (default: all)
set -uo pipefail
cd "$(dirname "$0")/.."
R="python3 tools/run.py"
want=" ${*:-t1 t2 t3 t4 t5 t6} "

if [[ $want == *" t1 "* ]]; then
  c=()
  for n in 100000 300000 1000000; do for s in distinct prefix skew equal low uni; do
    c+=("./build/coder --threads 1 $s $n new" "./build/coder --threads 1 $s $n old")
  done; done
  $R results/t1_coder.jsonl 5 "${c[@]}" > results/t1_coder.log 2>&1
fi

if [[ $want == *" t2 "* ]]; then
  c=()
  for n in 100000 300000 1000000; do for s in distinct prefix skew low uni; do
    c+=("./build/coder --threads 1 $s $n rrad" "./build/coder --threads 1 $s $n rnew" "./build/coder --threads 1 $s $n rmap")
  done; done
  for s in distinct prefix skew low uni; do c+=("./build/coder --threads 1 $s 100000 rold"); done
  c+=("./build/coder --threads 1 distinct 1000000 rold")
  $R results/t2_ranks.jsonl 5 "${c[@]}" > results/t2_ranks.log 2>&1
fi

if [[ $want == *" t3 "* ]]; then
  c=()
  for s in distinct prefix skew equal; do
    c+=("./build/probe --threads 1 $s 1000000 seq" "./build/probe --threads 1 $s 1000000 part 0"
        "./build/probe --threads 1 $s 1000000 part 4" "./build/probe --threads 4 $s 1000000 part 4"
        "./build/probe --threads 12 $s 1000000 part 4" "./build/probe --threads 12 $s 1000000 part 6")
  done
  $R results/t3_probe.jsonl 5 "${c[@]}" > results/t3_probe.log 2>&1
fi

if [[ $want == *" t6 "* ]]; then
  c=()
  for n in 100000 1000000; do for s in distinct prefix low uni; do c+=("./build/coder --threads 1 $s $n t6"); done; done
  $R results/t6_flat.jsonl 5 "${c[@]}" > results/t6_flat.log 2>&1
fi

if [[ $want == *" t4 "* ]]; then
  ( cd ../../.. && python3 bench/spikes/w0_strings/tools/run.py bench/spikes/w0_strings/results/t4_hot.jsonl 5 \
    "bench/spikes/w0_strings/build/hs_solo --threads 1" \
    "bench/spikes/w0_strings/build/rd_frame --threads 1 bench/data/sales_1000000.csv 0 hstep" \
    "bench/spikes/w0_strings/build/pk_cold --threads 1" \
    "bench/spikes/w0_strings/build/rd_frame --threads 1 bench/data/sales_1000000.csv 1048576 pack" \
    "bench/spikes/w0_strings/build/cnt_cold" "bench/spikes/w0_strings/build/cnt_hot" \
    > bench/spikes/w0_strings/results/t4_hot.log 2>&1 )
fi

if [[ $want == *" t5 "* ]]; then
  ( cd ../../.. && B=bench/spikes/w0_strings/build F=bench/data/sales_1000000.csv && \
    python3 bench/spikes/w0_strings/tools/run.py bench/spikes/w0_strings/results/t5_scale.jsonl 5 \
    "$B/rd_frame --threads 1 $F 1048576 spike" "$B/rd_frame --threads 4 $F 1048576 spike" \
    "$B/rd_frame --threads 12 $F 1048576 spike" "$B/rd_frame --threads 12 $F 262144 spike" \
    "$B/rd_frame --threads 12 $F 4194304 spike" "$B/rd_frame --threads 1 $F 4194304 spike" \
    "$B/rd_solo --threads 1 $F 1048576 spike" "$B/rd_solo --threads 12 $F 1048576 spike" \
    "$B/rd_frame --threads 1 $F 1048576 ref" "$B/rd_frame --threads 12 $F 1048576 ref" \
    "$B/rd_frame --threads 1 $F 1048576 hstep" \
    "$B/rd_frame --threads 1 $F 1048576 spike SSSUFFB" "$B/rd_frame --threads 12 $F 1048576 spike SSSUFFB" \
    "$B/rd_frame --threads 1 $F 1048576 ref SSSUFFB" \
    > bench/spikes/w0_strings/results/t5_scale.log 2>&1 )
  # phase decomposition: column letters U S F B, any other letter skips that column's loop
  ( cd ../../.. && B=bench/spikes/w0_strings/build F=bench/data/sales_1000000.csv && \
    python3 bench/spikes/w0_strings/tools/run.py bench/spikes/w0_strings/results/t5_phases.jsonl 5 \
    "$B/rd_frame --threads 1 $F 1048576 spike -------" "$B/rd_frame --threads 1 $F 1048576 spike U------" \
    "$B/rd_frame --threads 1 $F 1048576 spike ----F--" "$B/rd_frame --threads 1 $F 1048576 spike -S-----" \
    "$B/rd_frame --threads 1 $F 1048576 spike --S----" "$B/rd_frame --threads 1 $F 1048576 spike ------B" \
    "$B/rd_frame --threads 1 $F 1048576 spike USSUFFB" "$B/rd_frame --threads 1 $F 1048576 pack" \
    > bench/spikes/w0_strings/results/t5_phases.log 2>&1 )
fi
echo "campaign done: $want"
