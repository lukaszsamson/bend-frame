#!/usr/bin/env bash
# Clean-consumer check (plans/M_01.txt section 7 M6; STATUS decision 2026-10-09: no throwaway hub
# publish). Clones the repo (HEAD) from the local path into a temp dir, then:
#   1. bend <clone>/frame.bend --check-only
#   2. builds and runs <clone>/examples/quickstart.bend natively (cwd = the clone, as documented)
#      and compares its output with a pinned expectation
#   3. creates a separate consumer directory that imports ../<clone>/frame.bend (relative) and,
#      in a second program, the same file by absolute path; checks, builds natively, runs, and
#      verifies the output
# It never publishes. `bend --publish` has no dry-run mode (bend 2.0.36 `bend --help`), so none is run.
# Uncommitted changes are NOT in the clone: commit first, or CONSUMER_SRC=<dir> to clone another repo.
#
# Usage: scripts/consumer_check.sh          BEND=/path/to/bend  KEEP=1 (keep the temp dir)
set -uo pipefail
cd "$(dirname "$0")/.." || exit 1
SRC="${CONSUMER_SRC:-$PWD}"
BEND_BIN="${BEND:-$HOME/.bend/bin/bend}"
TMP="$(mktemp -d "${CONSUMER_TMP:-/tmp}/bend-frame-consumer-XXXXXX")" && TMP="$(cd "$TMP" && pwd -P)"  # normalised and dot-free: import paths take plain names only, and macOS $TMPDIR paths (/var/folders/5t/..) were rejected, hence /tmp
[ "${KEEP:-0}" = 1 ] || trap 'rm -rf "$TMP"' EXIT
fail=0
ok()  { echo "ok     $*"; }
bad() { echo "FAIL   $*"; fail=1; }

if [ -n "$(git -C "$SRC" status --porcelain 2>/dev/null)" ]; then
  echo "note: $SRC has uncommitted changes; the clone below is HEAD only"
fi
git clone --quiet "$SRC" "$TMP/clone" || { echo "FAIL clone"; exit 1; }
HEADREV="$(git -C "$TMP/clone" rev-parse --short HEAD)"
echo "clone of $SRC at $HEADREV in $TMP"
CLONE="$TMP/clone"

# 1. the library itself, checked from the clone
if "$BEND_BIN" "$CLONE/frame.bend" --check-only >"$TMP/check.out" 2>&1; then ok "bend frame.bend --check-only"
else bad "bend frame.bend --check-only"; cat "$TMP/check.out"; fi

# expect_eq NAME EXPECTED_FILE ACTUAL_FILE
expect_eq() {
  if diff -u "$2" "$3" >"$TMP/diff.out"; then ok "$1 output"; else bad "$1 output differs"; cat "$TMP/diff.out"; fi
}

# 2. the quickstart, in the clone (it reads bench/fixtures/tiny.csv relative to the cwd)
cat >"$TMP/quickstart.expected" <<'EOT'
shape: (4, 8)
+-----+---------+---------+-----+--------+----------+------+-----------+
| id  | region  | product | qty | price  | discount | ok   | revenue   |
| --- | ---     | ---     | --- | ---    | ---      | ---  | ---       |
| u32 | str     | str     | u32 | f32    | f32      | bool | f32       |
+=====+=========+=========+=====+========+==========+======+===========+
| 1   | inland  | prod_61 | 78  | 333.37 |          | true | 26002.86  |
| 10  | coastal | prod_24 | 55  | 197.43 | 0.17     | true | 9012.679  |
| 11  | island  | prod_04 | 55  | 407.87 | 0.28     | true | 16151.652 |
| 18  | coastal | prod_33 | 88  | 190.93 | 0.14     | true | 14449.582 |
+-----+---------+---------+-----+--------+----------+------+-----------+
EOT
if (cd "$CLONE" && "$BEND_BIN" examples/quickstart.bend -o "$TMP/quickstart" >"$TMP/qs_build.out" 2>&1); then
  ok "quickstart native build"
  (cd "$CLONE" && "$TMP/quickstart") >"$TMP/quickstart.actual" 2>&1
  expect_eq "quickstart (native)" "$TMP/quickstart.expected" "$TMP/quickstart.actual"
else bad "quickstart native build"; cat "$TMP/qs_build.out"; fi

# 3. a consumer directory beside the clone
CONS="$TMP/consumer"; mkdir -p "$CONS"
printf 'city,amount\na,10\nb,5\na,7\nb,1\nc,3\n' >"$CONS/data.csv"
body() { cat <<'EOT'

def plan(p: DF.Plan()) -> DF.Plan():
  DF.lazy_sort(DF.lazy_group_by(p, [DF.col("city")], [DF.alias(DF.sum(DF.col("amount")), "total"), DF.alias(DF.len(), "n")]), [DF.asc("city")])

def run(s: DF.Res(DF.Plan())) -> IO(Unit):
  match s:
    case Fail{e}:
      IO.print("scan error: " ++ DF.err_show(e))
    case Done{p}:
      do IO<Unit>:
        r : DF.ResT(DF.Frame()) <- DF.collect(plan(p), DF.empty_env())
        IO.print(DF.show(r))

def main() -> IO(Unit):
  do IO<Unit>:
    s : DF.Res(DF.Plan()) <- DF.scan_csv("data.csv")
    run(s)
EOT
}
{ echo "import ../clone/frame.bend as DF"; body; } >"$CONS/rel.bend"
{ echo "import $CLONE/frame.bend as DF"; body; } >"$CONS/abs.bend"
# sums: a 10+7, b 5+1, c 3 (checked by hand); counts 2, 2, 1
cat >"$TMP/consumer.expected" <<'EOT'
shape: (3, 3)
+------+-------+-----+
| city | total | n   |
| ---  | ---   | --- |
| str  | u32   | u32 |
+======+=======+=====+
| a    | 17    | 2   |
| b    | 6     | 2   |
| c    | 3     | 1   |
+------+-------+-----+
EOT
for v in rel abs; do
  if (cd "$CONS" && "$BEND_BIN" $v.bend --check-only >"$TMP/c_$v.out" 2>&1); then ok "consumer ($v import) --check-only"
  else bad "consumer ($v import) --check-only"; cat "$TMP/c_$v.out"; continue; fi
  if (cd "$CONS" && "$BEND_BIN" $v.bend -o "$TMP/consumer_$v" >"$TMP/c_$v.build" 2>&1); then ok "consumer ($v import) native build"
  else bad "consumer ($v import) native build"; cat "$TMP/c_$v.build"; continue; fi
  (cd "$CONS" && "$TMP/consumer_$v") >"$TMP/consumer_$v.actual" 2>&1
  expect_eq "consumer ($v import, native)" "$TMP/consumer.expected" "$TMP/consumer_$v.actual"
done

# the interpreter agrees with the native binary on the consumer program
(cd "$CONS" && "$BEND_BIN" rel.bend) >"$TMP/consumer_interp.actual" 2>&1
expect_eq "consumer (rel import, interpreter)" "$TMP/consumer.expected" "$TMP/consumer_interp.actual"

if [ "$fail" -ne 0 ]; then echo "consumer_check: FAILED"; [ "${KEEP:-0}" = 1 ] && echo "kept $TMP"; exit 1; fi
echo "consumer_check: ok (clone $HEADREV; no publish; bend --publish has no dry-run mode)"
