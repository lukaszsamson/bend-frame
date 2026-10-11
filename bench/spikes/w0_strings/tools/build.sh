#!/usr/bin/env bash
# Build the W0 strings/reader spike binaries (and their emitted C, for tools/hot.py and reading)
# into bench/spikes/w0_strings/build/. Usage: tools/build.sh [name ...] (default: all)
set -euo pipefail
cd "$(dirname "$0")/.."
BEND=${BEND:-$HOME/.bend/bin/bend}
mkdir -p build
all="coder probe rd_solo rd_frame pk_cold cnt_cold cnt_hot hs_solo"
for p in ${@:-$all}; do
  echo "== $p"
  "$BEND" "$p.bend" -o "build/$p.c"
  "$BEND" "$p.bend" -o "build/$p"
done
# the adversarial test binary (tools/adv.py) is rd_frame under another name, so a running
# campaign never sees its binary replaced
case " ${*:-$all} " in *" rd_frame "*) cp build/rd_frame build/rd_adv ;; esac
