#!/usr/bin/env bash
# bench/coverage/check.sh <name>: diff Polars's text for tests/coverage/<name>.bend (bench/coverage/<name>.py)
# against what Bend prints. Exit 0 when equal; stderr lists which invalid cases Polars refuses itself.
set -u
cd "$(dirname "$0")/../.."
n=$1
bend=${BEND:-$HOME/.bend/bin/bend}
exp=$(mktemp)
act=$(mktemp)
(cd bench && uv run python coverage/$n.py) > "$exp"
"$bend" tests/coverage/$n.bend </dev/null > "$act" 2>&1
perl -0777 -pe 's/[ \t]+$//mg; s/\A\s+//; s/\s+\z//' -i "$exp" "$act"
if diff -u --label polars --label bend "$exp" "$act"; then
  echo "$n: bend == polars"
else
  echo "$n: DIFFERS"
  exit 1
fi
