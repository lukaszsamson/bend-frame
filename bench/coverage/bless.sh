#!/usr/bin/env bash
# bench/coverage/bless.sh <name>: after `check.sh <name>` printed "bend == polars" (or every difference
# is a documented departure applied in bench/coverage/<name>.py), write the test's `#|` expectation
# lines from Bend's output. Refuses when Polars's text and Bend's differ.
set -eu
cd "$(dirname "$0")/../.."
n=$1
bend=${BEND:-$HOME/.bend/bin/bend}
"$(dirname "$0")/check.sh" "$n" >/dev/null 2>&1 || { echo "bless: $n differs from the Polars text; not writing"; exit 1; }
f=tests/coverage/$n.bend
act=$(mktemp)
"$bend" "$f" </dev/null > "$act" 2>&1
perl -ni -e 'print unless /^#\|/' "$f"
perl -pe 's/[ \t]+$//; $_ = "#|$_"' "$act" >> "$f"
echo "bless: $n: $(grep -c '^#|' "$f") expectation lines"
