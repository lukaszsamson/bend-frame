#!/usr/bin/env bash
# W2.1 / W2.2 measurement campaign (1 thread, fresh processes, old vs new interleaved, load recorded
# by bench/w2/run.py). PROVISIONAL on a shared machine (plans/M_02.txt section 5); gate numbers are
# the orchestrator's (bench/m2/, quiet machine).
#   bench/w2/campaign.sh [OUT.jsonl]        (about 20 minutes: the v0.1 coders are slow at 1M rows)
#   python3 bench/w2/tables.py OUT.jsonl
set -euo pipefail
cd "$(dirname "$0")/../.."
BEND=${BEND:-$HOME/.bend/bin/bend}
OUT=${1:-bench/w2/results/w2_$(date +%Y%m%d-%H%M%S).jsonl}
mkdir -p build/w2 bench/w2/results
"$BEND" bench/w2/w2.bend -o build/w2/w2
BIN="build/w2/w2 --threads 1"
echo "uptime before: $(uptime)"
cell() { # reps shape n modes...
  local reps=$1 shape=$2 n=$3
  shift 3
  local cmds=()
  for m in "$@"; do cmds+=("$BIN $shape $n $m"); done
  python3 bench/w2/run.py "$OUT" "$reps" "${cmds[@]}"
}
for shape in distinct prefix skew equal low uni; do
  for n in 100000 300000 1000000; do
    case "$shape:$n" in
      prefix:1000000) cell 1 "$shape" "$n" old; cell 5 "$shape" "$n" new ;;
      prefix:300000) cell 3 "$shape" "$n" old new ;;
      *:1000000|*:300000) cell 3 "$shape" "$n" old new; cell 5 "$shape" "$n" new newh ;;
      *) cell 5 "$shape" "$n" old new newh ;;
    esac
  done
done
for shape in distinct prefix skew equal low uni; do
  for n in 100000 300000 1000000; do
    case "$shape:$n" in
      prefix:1000000) cell 1 "$shape" "$n" rold; cell 5 "$shape" "$n" rnew rstage ;;
      *:1000000|*:300000) cell 3 "$shape" "$n" rold; cell 5 "$shape" "$n" rnew rstage ;;
      *) cell 5 "$shape" "$n" rold rnew rstage ;;
    esac
  done
done
for n in 100000 300000 1000000; do
  case "$n" in
    1000000) cell 3 distinct "$n" dold dnew ;;
    *) cell 5 distinct "$n" dold dnew ;;
  esac
done
echo "uptime after: $(uptime)"
echo "results: $OUT"
