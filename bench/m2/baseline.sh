#!/usr/bin/env bash
# W0: build the measurement driver (bench/m2/driver.bend) for the pinned BASELINE commit and for the
# CANDIDATE checkout, side by side, so both can be built and run forever after.
#
#   bench/m2/baseline.sh               materialise commit 3612482 into build/m2/baseline-src (git archive: sources
#                                      only, no .git, no worktree registration) and build
#                                      build/m2/baseline/driver from it with the SAME driver.bend as the candidate
#   bench/m2/baseline.sh --candidate   build build/m2/candidate/driver from the current checkout
#   --force                            rebuild even when build/m2/<which>/BUILD.json says it is up to date
#   BASELINE=<rev> BEND=<path>         override the pinned revision / the bend binary
#
# Each build writes build/m2/<which>/BUILD.json: commit, src hash (frame.bend + src/**/*.bend), driver hash,
# bend version, built_at, and for the candidate the number of changed lines in frame.bend (the facade) vs
# the baseline. The runner (run.py) refuses a stale candidate binary.
set -euo pipefail
cd "$(dirname "$0")/../.."
ROOT=$PWD
BASELINE=${BASELINE:-3612482}
BEND=${BEND:-$HOME/.bend/bin/bend}
which=baseline
force=0
for arg in "$@"; do
  case "$arg" in
    --candidate) which=candidate ;;
    --force) force=1 ;;
    *) echo "usage: $0 [--candidate] [--force]" >&2; exit 2 ;;
  esac
done

out=build/m2/$which
mkdir -p "$out"

if [ "$which" = baseline ]; then
  full=$(git rev-parse --verify "$BASELINE^{commit}")
  src=build/m2/baseline-src
  if [ ! -f "$src/.m2-commit" ] || [ "$(cat "$src/.m2-commit")" != "$full" ]; then
    rm -rf "$src"
    mkdir -p "$src"
    git archive "$full" | tar -x -C "$src"
    echo "$full" > "$src/.m2-commit"
    force=1
  fi
  mkdir -p "$src/bench/m2"
  cp bench/m2/driver.bend "$src/bench/m2/driver.bend"
  root=$src
  commit=$full
else
  root=$ROOT
  commit=$(git rev-parse HEAD)
fi

# the facade must be the same at both ends (the driver only uses it and a few src/ names)
srchash() { python3 - "$1" <<'EOF'
import hashlib, pathlib, sys
root = pathlib.Path(sys.argv[1])
h = hashlib.sha256()
files = [root / "frame.bend"] + sorted((root / "src").rglob("*.bend"))
for f in files:
    h.update(str(f.relative_to(root)).encode() + b"\0" + hashlib.sha256(f.read_bytes()).hexdigest().encode() + b"\n")
print(h.hexdigest())
EOF
}
sh=$(srchash "$root")
dh=$(shasum -a 256 "$root/bench/m2/driver.bend" | cut -d' ' -f1)

if [ "$force" = 0 ] && [ -x "$out/driver" ] && [ -f "$out/BUILD.json" ] \
   && grep -q "\"src_hash\": \"$sh\"" "$out/BUILD.json" && grep -q "\"driver_hash\": \"$dh\"" "$out/BUILD.json"; then
  echo "m2: $which driver is up to date ($out/driver, src $sh)"
  exit 0
fi

echo "m2: building $which driver from $root (commit ${commit:0:10}, src ${sh:0:12})"
"$BEND" "$root/bench/m2/driver.bend" -o "$out/driver"

facade_diff=null
if [ "$which" = candidate ]; then
  facade_diff=$(git diff --numstat "$BASELINE" -- frame.bend | awk '{print $1+$2}' | head -1)
  facade_diff=${facade_diff:-0}
fi
dirty=false
if [ "$which" = candidate ] && [ -n "$(git status --porcelain -- src frame.bend bench/m2/driver.bend)" ]; then dirty=true; fi
cat > "$out/BUILD.json" <<EOF
{
  "which": "$which",
  "commit": "$commit",
  "dirty_src": $dirty,
  "src_hash": "$sh",
  "driver_hash": "$dh",
  "bend_version": "$("$BEND" version 2>/dev/null | tr -d '\n')",
  "built_at": "$(date -u +%Y-%m-%dT%H:%M:%SZ)",
  "facade_changed_lines_vs_baseline": $facade_diff,
  "binary_sha256": "$(shasum -a 256 "$out/driver" | cut -d' ' -f1)"
}
EOF
echo "m2: $out/driver built"
