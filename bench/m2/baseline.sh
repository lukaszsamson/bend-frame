#!/usr/bin/env bash
# W0: build the measurement driver (bench/m2/driver.bend) for the pinned BASELINE commit and for the
# CANDIDATE checkout, side by side, so both can be built and run forever after.
#
#   bench/m2/baseline.sh               materialise commit 3612482 into build/m2/baseline-src (git archive: sources
#                                      only, no .git, no worktree registration) and build
#                                      build/m2/baseline/driver from it with the SAME driver.bend as the candidate
#   bench/m2/baseline.sh --candidate   build build/m2/candidate/driver from the current checkout
#   --force                            rebuild even when build/m2/<which>/BUILD.json says it is up to date
#   --instrument                       G6: build the INSTRUMENTED variant into build/m2/<which>-g6/driver: the emitted C
#                                      (`bend driver.bend -o x.c`) patched by bench/m2/instrument.py (copy / allocation
#                                      counters printed at every IO.now), compiled with bend's own flags. Its timings are
#                                      never valid; BUILD.json says "instrument": true. Combine with --candidate.
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
instrument=0
for arg in "$@"; do
  case "$arg" in
    --candidate) which=candidate ;;
    --force) force=1 ;;
    --instrument) instrument=1 ;;
    *) echo "usage: $0 [--candidate] [--force] [--instrument]" >&2; exit 2 ;;
  esac
done

out=build/m2/$which
suffix=
if [ "$instrument" = 1 ]; then suffix=-g6; out=build/m2/$which-g6; fi
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
  # the pinned facade has no v0.2 reader: the baseline's CSV shim reads with v0.1 (W6.3)
  cp bench/m2/engine_v01.bend "$src/bench/m2/engine.bend"
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
# the driver and its CSV reader shim (engine.bend; the baseline's is engine_v01.bend copied in)
dh=$(cat "$root/bench/m2/driver.bend" "$root/bench/m2/engine.bend" | shasum -a 256 | cut -d' ' -f1)
ih=null
if [ "$instrument" = 1 ]; then ih="\"$(shasum -a 256 "$ROOT/bench/m2/instrument.py" | cut -d' ' -f1)\""; fi

if [ "$force" = 0 ] && [ -x "$out/driver" ] && [ -f "$out/BUILD.json" ] \
   && grep -q "\"src_hash\": \"$sh\"" "$out/BUILD.json" && grep -q "\"driver_hash\": \"$dh\"" "$out/BUILD.json" \
   && { [ "$instrument" = 0 ] || grep -q "\"instrument_hash\": $ih," "$out/BUILD.json"; }; then
  echo "m2: $which driver is up to date ($out/driver, src $sh)"
  exit 0
fi

echo "m2: building $which$suffix driver from $root (commit ${commit:0:10}, src ${sh:0:12})"
if [ "$instrument" = 1 ]; then
  # emit the C, patch the runtime with the G6 counters (fails loudly if the runtime text is not what the patch
  # expects), compile with bend's own flags (instrument.py build)
  BEND="$BEND" python3 -I "$ROOT/bench/m2/instrument.py" build "$root/bench/m2/driver.bend" "$out"
else
  "$BEND" "$root/bench/m2/driver.bend" -o "$out/driver"
fi

facade_diff=null
if [ "$which" = candidate ]; then
  facade_diff=$(git diff --numstat "$BASELINE" -- frame.bend | awk '{print $1+$2}' | head -1)
  facade_diff=${facade_diff:-0}
fi
dirty=false
if [ "$which" = candidate ] && [ -n "$(git status --porcelain -- src frame.bend bench/m2/driver.bend bench/m2/engine.bend)" ]; then dirty=true; fi
cat > "$out/BUILD.json" <<EOF
{
  "which": "$which",
  "instrument": $([ "$instrument" = 1 ] && echo true || echo false),
  "instrument_hash": $ih,
  "timing_valid": $([ "$instrument" = 1 ] && echo false || echo true),
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
