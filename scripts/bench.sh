#!/usr/bin/env bash
# Benchmark driver: generate data if missing, then run the Polars reference side.
set -euo pipefail
cd "$(dirname "$0")/.."

if ! ls bench/data/sales_*.csv >/dev/null 2>&1; then
  uv run --project bench python bench/gen.py
fi

uv run --project bench python bench/run_polars.py

# TODO bend side
# Run the Bend implementation of q1..q6 on the same bench/data/*.csv, write
# bench/results/bend.json ({query, n, seconds}), and diff against bench/golden/.
