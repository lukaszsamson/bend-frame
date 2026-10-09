#!/usr/bin/env bash
# M4 string experiment: build the measurement binaries.
#   build/bench          bench/main.bend (q1..q6; BF_STR=raw|dict|auto picks the reader's Str storage)
#   build/strbench       bench/strbench.bend (one string operation per process)
#   build/scanbench_<e>  bench/scanbench.bend (scan_csv + collect) with Csv.enc_default = Enc<e>
#                        (src/csv.bend is edited for the build and restored afterwards)
# Then: uv run --project bench python bench/strbench.py {q|ops|scan|table} ... (see its docstring)
set -euo pipefail
cd "$(dirname "$0")/.."
BEND=${BEND:-$HOME/.bend/bin/bend}
mkdir -p build
"$BEND" bench/main.bend -o build/bench
"$BEND" bench/strbench.bend -o build/strbench
cp src/csv.bend build/csv.bend.m4keep
trap 'cp build/csv.bend.m4keep src/csv.bend' EXIT
for e in Raw Dict Auto; do
  perl -0pi -e "s/(def Csv\\.enc_default\\(\\) -> ST\\.StrEnc:\\n  )ST\\.Enc\\w+\\{\\}/\${1}ST.Enc$e\\{\\}/" src/csv.bend
  grep -A1 "def Csv.enc_default" src/csv.bend | tail -1
  lc=$(echo "$e" | tr 'A-Z' 'a-z')
  "$BEND" bench/scanbench.bend -o "build/scanbench_$lc"
done
