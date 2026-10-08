#!/usr/bin/env bash
# Self-test of scripts/test.sh (review of M0): runs it over throwaway fixtures with a fake `bend`
# (prints the file's `#>` lines, exits with its `#>exit N`, sleeps `#>sleep N`), and checks the
# verdicts, the summary, the exit status and the report order under TEST_JOBS. Takes ~3 s.
set -uo pipefail
cd "$(dirname "$0")/.." || exit 1

d=$(mktemp -d) || exit 1
trap 'rm -rf "$d"' EXIT
mkdir -p "$d/t"
cat > "$d/bend" <<'SH'
#!/bin/sh
rc=0
while IFS= read -r l; do
  case "$l" in
    '#>exit '*) rc=${l#\#>exit } ;;
    '#>sleep '*) sleep "${l#\#>sleep }" ;;
    '#> '*) printf '%s\n' "${l#\#> }" ;;
  esac
done < "$1"
exit "$rc"
SH
chmod +x "$d/bend"

fix() { printf '%s\n' "$2" > "$d/t/$1.bend"; }
fix a_pass       $'#>sleep 1\n#> hello\n#| hello'
fix b_fail       $'#> got\n#| want'
fix c_xfail      $'#! xfail B99\n#> got\n#| want'
fix d_xpass      $'#! xfail B98\n#> want\n#| want'
fix e_empty      $'#|\n#|'
fix f_timeout    $'#>sleep 5\n#| never'
fix g_noexp_rc   $'#> boom\n#>exit 3'
fix h_errexp     $'#> SOME PROOFS FAIL\n#>exit 1\n#| SOME PROOFS FAIL'
fix i_xfail_rc   $'#! xfail B97\n#>exit 2\n#| want'

fail=0
expect() { # label pattern text
  if ! printf '%s\n' "$3" | grep -q -- "$2"; then echo "runner check FAILED: $1 (no line matching '$2')"; fail=1; fi
}

for jobs in 1 4; do
  t0=$SECONDS
  out=$(BEND="$d/bend" TEST_DIR="$d/t" TEST_TIMEOUT=2 TEST_JOBS=$jobs scripts/test.sh 2>&1)
  rc=$?
  # the timeout kills f_timeout's `sleep 5` child too (it used to hold the pipe open for 5 s)
  if [ "$jobs" -eq 4 ] && [ $((SECONDS - t0)) -ge 5 ]; then
    echo "runner check FAILED: the 2 s timeout took $((SECONDS - t0)) s"; fail=1
  fi
  [ "$rc" -eq 1 ] || { echo "runner check FAILED: jobs=$jobs exit $rc, want 1"; fail=1; }
  expect "pass"            "^PASS .*a_pass.bend$" "$out"
  expect "fail"            "^FAIL .*b_fail.bend$" "$out"
  expect "xfail"           "^XFAIL .*c_xfail.bend (B99)$" "$out"
  expect "xpass"           "^XPASS .*d_xpass.bend (B98)$" "$out"
  expect "empty expect"    "^FAIL .*e_empty.bend (empty expectation" "$out"
  expect "timeout"         "^FAIL .*f_timeout.bend (timeout)$" "$out"
  expect "no-expect exit"  "^FAIL .*g_noexp_rc.bend (exit 3)$" "$out"
  expect "error expected"  "^PASS .*h_errexp.bend$" "$out"
  expect "xfail crash"     "^XFAIL .*i_xfail_rc.bend (B97) (exit 2)$" "$out"
  # 9 files: 2 xfail; 7 counted, of which a_pass and h_errexp pass
  expect "summary"         "^PASS: 2 / 7, XFAIL: 2$" "$out"
  order=$(printf '%s\n' "$out" | sed -n 's/^[A-Z]* .*\/\([a-z]\)_[a-z_]*\.bend.*/\1/p' | tr -d '\n')
  [ "$order" = abcdefghi ] || { echo "runner check FAILED: jobs=$jobs report order $order"; fail=1; }
done

# green iff every counted test passes: pass + xfail only exits 0
rm "$d/t/b_fail.bend" "$d/t/d_xpass.bend" "$d/t/e_empty.bend" "$d/t/f_timeout.bend" "$d/t/g_noexp_rc.bend"
out=$(BEND="$d/bend" TEST_DIR="$d/t" TEST_JOBS=2 scripts/test.sh 2>&1)
rc=$?
[ "$rc" -eq 0 ] || { echo "runner check FAILED: pass+xfail run exit $rc, want 0"; printf '%s\n' "$out"; fail=1; }
expect "green summary" "^PASS: 2 / 2, XFAIL: 2$" "$out"

if [ "$fail" -ne 0 ]; then exit 1; fi
echo "runner check: ok"
