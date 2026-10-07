#!/usr/bin/env bash
# Runs every tests/**/*.bend (sorted) and checks its output against its `#|` lines.
#
# Usage: scripts/test.sh [filter ...]    a file runs if its path contains any filter
#        BEND=/path/to/bend scripts/test.sh
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
#  - a file with no `#|` lines must exit 0 (PASS (no expect)).
#  - stdin is /dev/null, so a stray read cannot hang the run (gates has no stdin
#    handling; this is added).
#  - 120 s per file (the spec value; gates uses 5 s per program on its cluster).
set -uo pipefail

cd "$(dirname "$0")/.." || exit 1

BEND_BIN="${BEND:-$HOME/.bend/bin/bend}"
LIMIT=120

# gates' tidy(): strip trailing whitespace per line, then trim the whole text
norm() { perl -0777 -pe 's/[ \t]+$//mg; s/\A\s+//; s/\s+\z//'; }

tmp=$(mktemp -d) || exit 1
trap 'rm -rf "$tmp"' EXIT

# run_one FILE: prints PASS/FAIL (and a diff on failure); returns 0 on pass
run_one() {
  local f=$1 out rc exp act errexp=0
  if ! grep -q '^#|' "$f"; then
    out=$(perl -e 'alarm shift; exec @ARGV' "$LIMIT" "$BEND_BIN" "$f" </dev/null 2>&1)
    rc=$?
    if [ "$rc" -eq 0 ]; then
      echo "PASS $f (no expect)"
      return 0
    fi
    if [ "$rc" -eq 142 ]; then
      echo "FAIL $f (timeout)"
    else
      echo "FAIL $f (exit $rc)"
    fi
    printf '%s\n' "$out"
    return 1
  fi

  exp=$(perl -ne 'print substr($_, 2) if /^#\|/' "$f" | norm)
  case "$exp" in
    "SOME PROOFS FAIL"*|"Error:"*) errexp=1 ;;
  esac

  out=$(perl -e 'alarm shift; exec @ARGV' "$LIMIT" "$BEND_BIN" "$f" </dev/null 2>&1)
  rc=$?
  if [ "$rc" -eq 142 ]; then
    out="$out"$'\n'"timeout"
  elif [ "$rc" -ne 0 ] && [ "$errexp" -eq 0 ]; then
    out="$out"$'\n'"exit $rc"
  fi
  act=$(printf '%s\n' "$out" | norm)

  if [ "$exp" = "$act" ]; then
    echo "PASS $f"
    return 0
  fi
  echo "FAIL $f"
  printf '%s\n' "$exp" > "$tmp/expected"
  printf '%s\n' "$act" > "$tmp/actual"
  diff -u --label expected --label actual "$tmp/expected" "$tmp/actual"
  return 1
}

pass=0
total=0
while IFS= read -r f; do
  [ -n "$f" ] || continue
  if [ "$#" -gt 0 ]; then
    keep=0
    for pat in "$@"; do
      case "$f" in *"$pat"*) keep=1 ;; esac
    done
    [ "$keep" -eq 1 ] || continue
  fi
  total=$((total + 1))
  if run_one "$f"; then
    pass=$((pass + 1))
  fi
done <<< "$(find tests -name '*.bend' -type f | LC_ALL=C sort)"

if [ "$total" -eq 0 ]; then
  echo "no tests matched: $*" >&2
  exit 1
fi
echo "PASS: $pass / $total"
if [ "$pass" -ne "$total" ]; then
  exit 1
fi
