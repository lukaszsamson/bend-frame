#!/usr/bin/env bash
# Benchmark driver: Polars reference side, then the Bend side, then a merged table.
#   scripts/bench.sh                  everything (Polars ~1 min, Bend ~10 min)
#   SKIP_POLARS=1 scripts/bench.sh    reuse bench/results/polars.json
#   SIZES="1000" QUERIES="q1 q3" scripts/bench.sh   a subset of the Bend runs (bend.json holds only those)
#   SKIP_CHECK=1                      skip the correctness diffs vs Polars goldens
#   CHECK_MAX=1000000                 also diff the 1M results (slow: renders big CSVs)
set -euo pipefail
cd "$(dirname "$0")/.."
ROOT=$PWD

BEND=${BEND:-$HOME/.bend/bin/bend}
SIZES=${SIZES:-"1000 100000 1000000"}
QUERIES=${QUERIES:-"q1 q2 q3 q4 q5 q6"}
PY="uv run --project $ROOT/bench python"

if ! ls bench/data/sales_*.csv >/dev/null 2>&1; then
  uv run --project bench python bench/gen.py
fi

if [ -z "${SKIP_POLARS:-}" ]; then
  uv run --project bench python bench/run_polars.py
fi

# ---- Bend side ----------------------------------------------------------------------------
mkdir -p build
"$BEND" bench/main.bend -o build/bench

# build/bench [--threads N] sales.csv query repeats batch label [out.csv] -> one JSON line.
# ONE measurement per process, `procs_for` processes per cell, best kept (compare.py takes the min):
# parsing again inside a process slows down (heap growth: 100k rows go from ~0.5 s to ~3 s per parse
# after a few), and so does the collect itself. IO.now has 1 ms resolution, so tiny queries run
# `batch` collects (each over its own freshly parsed inputs) in one timed window and report the mean.
# Batches distort larger queries (more live heap: q5 at 100k doubles with batch 3), so batch only
# where the window would otherwise be a few ms.
procs_for() { case "$1" in 1000|100000) echo 5;; *) echo 3;; esac; }
batch_for() { # n query
  case "$1" in
    1000) if [ "$2" = q1 ] || [ "$2" = q2 ]; then echo 500; else echo 40; fi;;
    100000) if [ "$2" = q2 ]; then echo 8; else echo 1; fi;;
    *) if [ "$2" = q2 ]; then echo 3; else echo 1; fi;;
  esac
}

# ---- correctness: Bend's rendered results (4 decimals) vs Polars on the same CSV ------------
if [ -z "${SKIP_CHECK:-}" ]; then
  echo "== correctness vs Polars (build/q<k>_<n>.csv vs golden) =="
  # group_by's f32 sums are plain sequential adds (Polars sums with far less error): ~1e-5 rel at 1M rows
  for n in $(echo "$SIZES" | tr ' ' '\n' | awk -v m="${CHECK_MAX:-100000}" '$1 <= m'); do
    if [ "$n" = 1000 ]; then gold=bench/golden/n$n; else gold=build/golden_$n; fi
    (cd bench && $PY golden.py --input data/sales_$n.csv --out "$ROOT/$gold" >/dev/null)
    for q in $QUERIES; do
      out=build/${q}_$n.csv
      rm -f "$out"
      line=$(./build/bench bench/data/sales_$n.csv $q 1 1 default "$out" | tail -1) || true
      if [ -f "$out" ]; then
        printf '%s n=%s: ' "$q" "$n"; $PY bench/check.py "$out" "$gold/$q.csv" --rtol "$([ "$n" -gt 100000 ] && echo 5e-5 || echo 1e-5)" || true
      else
        printf '%s n=%s: no output (%s)\n' "$q" "$n" "$line"
      fi
    done
  done
fi

# ---- timing -----------------------------------------------------------------------------------
: > build/bend.jsonl
for n in $SIZES; do
  for q in $QUERIES; do
    for t in 1 default; do
      flags=(); if [ "$t" = 1 ]; then flags=(--threads 1); fi
      for _ in $(seq "$(procs_for $n)"); do
        line=$(./build/bench ${flags[@]+"${flags[@]}"} bench/data/sales_$n.csv $q 1 "$(batch_for $n $q)" $t | tail -1) || true
        echo "$line"
        case "$line" in "{"*) echo "$line" >> build/bend.jsonl;; esac
      done
    done
  done
done

echo
$PY bench/compare.py --jsonl build/bend.jsonl | tee build/bench_table.md
