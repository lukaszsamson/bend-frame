#!/usr/bin/env bash
# Runs every tests/**/*.bend (sorted, recursive: tests/regress/, tests/diff/ too) and checks its
# output against its `#|` lines.
#
# Usage: scripts/test.sh [filter ...]    a file runs if its path contains any filter
#        BEND=/path/to/bend scripts/test.sh
#        TEST_JOBS=8 scripts/test.sh     run files in parallel (default 1); output stays in file order
#        TEST_DIR=dir TEST_TIMEOUT=s      another test tree / per-file limit (scripts/test_runner_check.sh)
#
# Native tests: a file with a line `#! native` is built with `bend FILE -o BIN` and the binary is run (the build
# counts against the same time limit; binaries go to build/test_native/). Used for the CSV lane tests, which the interpreter runs 3-7x slower and with
# ~10x the memory since Bend 2.0.37 (bendlang/bend#1983); one small interpreter CSV test (csv_v02_chunks) stays.
#
# Expected failures: a test with a line `#! xfail <ID>` (e.g. `#! xfail B01`) pins a known defect.
#  - it must FAIL its check: reported as `XFAIL <file> (<ID>)` and not counted as a failure;
#  - if it passes, it is reported as `XPASS <file> (<ID>)` and counted as a failure, so the marker
#    is removed when the defect is fixed.
#
# Summary: `PASS: p / total, XFAIL: x`, where total counts the tests not marked xfail (so the run
# is green iff p == total). Exit status is 1 when any test fails or XPASSes.
#
# Convention, matched to bend/gates/test.ts (where it differs, this is noted):
#  - expected output = every line starting with `#|`, with the `#|` removed and
#    nothing else stripped. gates keeps the space after `#|`, so `#| a` expects " a";
#    the whole-text trim below still makes a one-line `#| a` match. Write `#|a` when
#    a multi-line expectation needs no leading space. (Differs from the spec, which
#    strips one following space: gates does not, and its corpus relies on it.)
#    gates takes all `#|` lines; the spec says the trailing ones. They coincide here:
#    no test has non-`#|` text after its first `#|` line.
#  - stdout and stderr are merged (gates runs with 2>&1). The spec said stdout only.
#  - both sides: trailing whitespace trimmed per line, then leading and trailing
#    whitespace of the whole text trimmed (gates' tidy()). Trailing empty lines ignored.
#  - a run that exits non-zero fails, with "exit N" (or "timeout" for 142) appended to
#    its output, as gates does. Exception: a test expecting "SOME PROOFS FAIL" or
#    "Error:" (gates' failing-test form) ignores the exit code, since bend exits 1 there.
#    The spec did not mention this exception.
#  - a file with no `#|` lines must exit 0 (PASS (no expect)); `#|` lines that are all blank are a
#    FAIL (empty expectation), since they would accept a program that prints nothing.
#  - stdin is /dev/null, so a stray read cannot hang the run (gates has no stdin
#    handling; this is added).
#  - 300 s per file by default (TEST_TIMEOUT; the spec value is 120 s; gates uses 5 s per program on its cluster).
set -uo pipefail

cd "$(dirname "$0")/.." || exit 1

BEND_BIN="${BEND:-$HOME/.bend/bin/bend}"
LIMIT="${TEST_TIMEOUT:-300}"
TEST_DIR="${TEST_DIR:-tests}"
JOBS="${TEST_JOBS:-1}"
case "$JOBS" in
  ''|*[!0-9]*|0) echo "TEST_JOBS must be a positive integer, got: $JOBS" >&2; exit 2 ;;
esac

# gates' tidy(): strip trailing whitespace per line, then trim the whole text
norm() { perl -0777 -pe 's/[ \t]+$//mg; s/\A\s+//; s/\s+\z//'; }

# limited SECS CMD...: runs CMD in its own process group; after SECS the whole group is killed and
# the status is 142 (what a bare SIGALRM gives). A plain `alarm; exec` killed only CMD itself: a
# child it spawned kept the output pipe open and the $(...) around it waited for that child.
limited() {
  perl -e '
    my $t = shift;
    my $pid = fork; defined $pid or die "fork: $!";
    if (!$pid) { setpgrp(0, 0); exec @ARGV or exit 127 }
    setpgrp($pid, $pid);
    $SIG{ALRM} = sub { kill "KILL", -$pid; waitpid($pid, 0); exit 142 };
    alarm $t;
    waitpid($pid, 0);
    exit($? & 127 ? 128 + ($? & 127) : $? >> 8);
  ' "$@"
}

# xfail_id FILE: the ID of the file's `#! xfail <ID>` line, or nothing
xfail_id() { perl -ne 'if (/^#! xfail\s+(\S+)/) { print $1; last }' "$1"; }

# is_native FILE: the file asks to run as a native binary
is_native() { grep -q '^#! native' "$1"; }

# run_test FILE OUT: the test's merged output; status as limited's (142 = timeout). A native test is built to
# OUT.bin first; a failed build is reported with the compiler's output.
run_test() {
  local f=$1 out=$2
  if is_native "$f"; then
    # bend picks the output kind by extension, and mktemp's directory has a dot in it: build under build/
    local bin
    bin="build/test_native/$(printf '%s' "$f" | tr '/.' '__')"
    mkdir -p build/test_native
    limited "$LIMIT" "$BEND_BIN" "$f" -o "$bin" </dev/null > "$out.build" 2>&1 || { cat "$out.build"; return 3; }
    limited "$LIMIT" "./$bin" </dev/null 2>&1
  else
    limited "$LIMIT" "$BEND_BIN" "$f" </dev/null 2>&1
  fi
}

# check_one FILE OUT: runs one test. Its report goes to stdout; its verdict (PASS, FAIL, XFAIL or
# XPASS) goes to OUT.status. Temporary files use the OUT prefix, so parallel workers do not collide.
check_one() {
  local f=$1 out=$2 id run rc exp act errexp=0 ok=0 suffix="" body="" status
  id=$(xfail_id "$f")
  if ! grep -q '^#|' "$f"; then
    run=$(run_test "$f" "$out")
    rc=$?
    if [ "$rc" -eq 0 ]; then
      ok=1
      suffix=" (no expect)"
    else
      if [ "$rc" -eq 142 ]; then suffix=" (timeout)"; else suffix=" (exit $rc)"; fi
      body=$run
    fi
  else
    exp=$(perl -ne 'print substr($_, 2) if /^#\|/' "$f" | norm)
    case "$exp" in
      "SOME PROOFS FAIL"*|"Error:"*) errexp=1 ;;
    esac
    run=$(run_test "$f" "$out")
    rc=$?
    if [ "$rc" -eq 142 ]; then
      run="$run"$'\n'"timeout"
      suffix=" (timeout)"
    elif [ "$rc" -ne 0 ] && [ "$errexp" -eq 0 ]; then
      run="$run"$'\n'"exit $rc"
      suffix=" (exit $rc)"
    fi
    act=$(printf '%s\n' "$run" | norm)
    if [ -z "$exp" ]; then
      # `#|` lines that are all blank would accept a program that prints nothing
      suffix=" (empty expectation: blank \`#|\` lines)"
    elif [ "$exp" = "$act" ]; then
      ok=1
    else
      printf '%s\n' "$exp" > "$out.expected"
      printf '%s\n' "$act" > "$out.actual"
      body=$(diff -u --label expected --label actual "$out.expected" "$out.actual")
    fi
  fi

  if [ -n "$id" ]; then
    if [ "$ok" -eq 1 ]; then
      status=XPASS
      printf 'XPASS %s (%s)\n  the defect is fixed: delete its `#! xfail` line\n' "$f" "$id"
    else
      status=XFAIL
      printf 'XFAIL %s (%s)%s\n' "$f" "$id" "$suffix"
    fi
  elif [ "$ok" -eq 1 ]; then
    status=PASS
    printf 'PASS %s%s\n' "$f" "$suffix"
  else
    status=FAIL
    printf 'FAIL %s%s\n' "$f" "$suffix"
    [ -n "$body" ] && printf '%s\n' "$body"
  fi
  printf '%s\n' "$status" > "$out.status"
}

tmp=$(mktemp -d) || exit 1
trap 'rm -rf "$tmp"' EXIT

# Select the files: NUL-separated (index, path) pairs, so the report can follow file order.
list="$tmp/list"
: > "$list"
n=0
while IFS= read -r f; do
  [ -n "$f" ] || continue
  if [ "$#" -gt 0 ]; then
    keep=0
    for pat in "$@"; do
      case "$f" in *"$pat"*) keep=1 ;; esac
    done
    [ "$keep" -eq 1 ] || continue
  fi
  printf '%s\0%s\0' "$n" "$f" >> "$list"
  n=$((n + 1))
done <<< "$(find "$TEST_DIR" -name '*.bend' -type f -not -path '*/lib/*' | LC_ALL=C sort)"

if [ "$n" -eq 0 ]; then
  echo "no tests matched: $*" >&2
  exit 1
fi

# Run them (JOBS at a time). Each worker writes its report to $tmp/r<i>.log and its verdict to
# $tmp/r<i>.status; the report below reads them back in file order.
export -f norm xfail_id limited is_native run_test check_one
export BEND_BIN LIMIT tmp
xargs -0 -n 2 -P "$JOBS" bash -c 'check_one "$1" "$tmp/r$0" > "$tmp/r$0.log"' < "$list" || true

pass=0
total=0
xfail=0
while IFS= read -r -d '' i; do
  IFS= read -r -d '' f
  st=$(cat "$tmp/r$i.status" 2>/dev/null)
  if [ -z "$st" ]; then
    echo "FAIL $f (no result: the runner died)"
    st=FAIL
  else
    cat "$tmp/r$i.log"
  fi
  case "$st" in
    PASS) pass=$((pass + 1)); total=$((total + 1)) ;;
    XFAIL) xfail=$((xfail + 1)) ;;
    *) total=$((total + 1)) ;;
  esac
done < "$list"

echo "PASS: $pass / $total, XFAIL: $xfail"
if [ "$pass" -ne "$total" ]; then
  exit 1
fi
