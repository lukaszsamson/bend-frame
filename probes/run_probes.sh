#!/bin/sh
# Runs every probe that carries `#|` expectation lines and compares the
# program's stdout to them (the Bend repo's tests convention, see
# bend/gates/test.ts: expected = lines starting with `#|`, prefix stripped).
# Probes without `#|` lines (benchmarks, negative probes) are only checked.
#   sh probes/run_probes.sh
BEND="${BEND:-$HOME/.bend/bin/bend}"
cd "$(dirname "$0")" || exit 1
pass=0; fail=0
for f in p*.bend p08_laws/PROOF.bend p19_modules/main.bend p20_type_law/PROOF.bend; do
  case "$f" in
    p02b_*) # negative probe: must be refused with this exact message
      out=$("$BEND" "$f" 2>&1)
      if [ "$out" = "Error: an open Array element type" ]; then pass=$((pass+1)); else fail=$((fail+1)); echo "FAIL $f"; echo "$out" | head -5; fi
      continue;;
    p13_*|p21_*) # open laws (signature stubs): the checker reports them as TODOs and exits 1
      out=$("$BEND" "$f" --check-only 2>&1)
      case "$out" in *"TODOs found"*) pass=$((pass+1));; *) fail=$((fail+1)); echo "FAIL $f"; echo "$out" | head -5;; esac
      continue;;
    p07_*|p15_*|p15b_*|p15c_*|p16_*) # benchmarks: check only
      if "$BEND" "$f" --check-only >/dev/null 2>&1; then pass=$((pass+1)); else fail=$((fail+1)); echo "FAIL (check) $f"; fi
      continue;;
  esac
  want=$(grep '^#|' "$f" | sed 's/^#|//')
  if [ -z "$want" ]; then
    if "$BEND" "$f" --check-only >/dev/null 2>&1; then pass=$((pass+1)); else fail=$((fail+1)); echo "FAIL (check) $f"; fi
    continue
  fi
  got=$("$BEND" "$f" 2>&1)
  if [ "$got" = "$want" ]; then pass=$((pass+1)); else fail=$((fail+1)); echo "FAIL $f"; echo "--- want"; echo "$want"; echo "--- got"; echo "$got" | head -20; fi
done
echo "PASS: $pass / $((pass+fail))"
[ "$fail" -eq 0 ]
