BEND ?= $(HOME)/.bend/bin/bend
SOURCES := $(shell find src tests -name '*.bend' -type f 2>/dev/null | LC_ALL=C sort)
EXAMPLES := frame.bend $(wildcard examples/*.bend) $(wildcard bench/*.bend)

.PHONY: ci test runner-check check proofs verdict bench bench-check toolchain-check clean mutation-check consumer-check diff-driver-check diff-smoke

# The full gate, in CI order. Needs the pinned toolchain (TOOLCHAIN): `make toolchain-check` first.
# Beyond the unit gates: the differential drivers' exit-status regression, a bounded strict
# differential smoke (Raw and Dictionary strings, then the F32 reduction check), the proof mutation
# check and the clean-consumer check (needs the work committed: it clones HEAD). Larger differential
# runs (make diff N=..., make diff-reduce REDUCE_N=...) are the scheduled/release gate.
ci: toolchain-check check runner-check diff-driver-check test proofs verdict mutation-check bench-check diff-smoke consumer-check
	@echo "ci: all gates passed"

test:
	scripts/test.sh

# scripts/test.sh itself, over throwaway fixtures with a fake bend (xfail/XPASS/timeouts/order)
runner-check:
	@scripts/test_runner_check.sh

# A file whose expectation is a failure (first `#|` text starts with "SOME PROOFS FAIL" or "Error:",
# scripts/test.sh's rule; e.g. tests/proof_negative/) cannot pass --check-only: test.sh runs it.
check:
	@for f in $(SOURCES) $(EXAMPLES); do \
	  case "$$(sed -n 's/^#|[[:space:]]*//p' "$$f" | sed -n '/./{p;q;}')" in \
	    "SOME PROOFS FAIL"*|"Error:"*) echo "skip $$f (expects a failure; scripts/test.sh checks it)"; continue ;; \
	  esac; \
	  $(BEND) "$$f" --check-only || exit 1; \
	done

proofs:
	@if [ -f PROOF.bend ]; then $(BEND) PROOF.bend; else echo "no PROOF.bend"; fi

verdict:
	$(BEND) PROOF.bend --verdict

# Mutates the PRODUCTION functions in a temp copy and requires `bend PROOF.bend` to fail for each
# (scripts/mutation_check.sh); the unmutated copy must pass. Complements tests/proof_negative/.
mutation-check:
	@scripts/mutation_check.sh

# Clean clone of HEAD: check, build and run the quickstart and a relative/absolute-import consumer.
consumer-check:
	@scripts/consumer_check.sh

# Correctness only, at 1k and 100k rows (scripts/bench.sh, BENCH_MODE=check).
bench-check:
	@BENCH_MODE=check scripts/bench.sh

# Fails when an installed tool differs from TOOLCHAIN (see the file for the pins).
toolchain-check:
	@. ./TOOLCHAIN; fail=0; \
	chk() { if [ "$$2" = "$$3" ]; then echo "ok     $$1 $$2"; else echo "DRIFT  $$1: installed '$$2', TOOLCHAIN '$$3'"; fail=1; fi; }; \
	chk bend "$$($(BEND) version 2>/dev/null | awk '{print $$2}')" "$$BEND_VERSION"; \
	chk lean "$$(lean --version 2>/dev/null | sed -n 's/^Lean (version \([^,]*\),.*/\1/p')" "$$LEAN_VERSION"; \
	chk uv "$$(uv --version 2>/dev/null | awk '{print $$2}')" "$$UV_VERSION"; \
	set -- $$(cd bench && uv run --quiet python -c 'import sys, polars, numpy; print(polars.__version__, numpy.__version__, "%d.%d.%d" % sys.version_info[:3])' 2>/dev/null); \
	chk polars "$${1:-}" "$$POLARS_VERSION"; chk numpy "$${2:-}" "$$NUMPY_VERSION"; chk python "$${3:-}" "$$PYTHON_VERSION"; \
	if [ "$$fail" -ne 0 ]; then echo "toolchain-check: FAILED (install the TOOLCHAIN versions)"; exit 1; fi; \
	echo "toolchain-check: ok"

bench:
	@if [ -f scripts/bench.sh ]; then scripts/bench.sh; else echo "no scripts/bench.sh"; fi

clean:
	rm -rf build

# ---- differential generator (bench/diff, plans/M_01.txt T2/T3) ----------------------------
# make diff [SEED=1] [N=1000] [DIFF_ARGS="--backend both --features noreductions,noselfjoin"]
# Runs N seeded cases: eager vs raw-lazy vs optimised-lazy (T2.1) and vs the Polars-based oracle
# (T2.2); failures are shrunk, classified against DESIGN.md 15.10 and written to
# build/diff/seed<SEED>/failures.json. Exits 1 on any failure (a mismatch, a crash
# or an oracle error), whether or not a known-defect rule labels it (classification never excuses a
# failure; --strict is a no-op kept for old command lines). See bench/diff/README.md.
.PHONY: diff diff-lib
SEED ?= 1
N ?= 1000
diff:
	cd bench && uv run python diff/run.py --seed $(SEED) --n $(N) $(DIFF_ARGS)

# regenerate the helper module tests/diff/lib/dx.bend after frame.bend gained verbs
diff-lib:
	cd bench && uv run python diff/gen.py --lib

# ---- T2.3: F32 reductions vs an exact reference (bench/diff/reduce.py, plans/M_01.txt T2.3) -----
# make diff-reduce [SEED=1] [REDUCE_N=2000] [REDUCE_ARGS="--shrink --classes cancel,special"]
# Sum/mean (eager, grouped, lazy) and describe (mean/std/quantiles) of generated F32 vectors against
# the exactly rounded value, the contract's step model and the derived error bound; reports how
# often Bend equals the correctly rounded f32. Exits 1 on a numerical defect (a bound or IEEE-special
# violation, a null where none is due, lazy != eager, a wrong group order); any finding fails, there
# is no allowlist. `make diff-reduce-selftest`
# checks the reference itself and that weaker summations (naive, Kahan, no guard) are flagged.
.PHONY: diff-reduce diff-reduce-selftest
REDUCE_N ?= 2000
diff-reduce:
	cd bench && uv run python diff/reduce.py --seed $(SEED) --n $(REDUCE_N) $(REDUCE_ARGS)

diff-reduce-selftest:
	cd bench && uv run python diff/reduce.py --selftest

# ---- the differential drivers inside `make ci` (bounded; larger runs: make diff / diff-reduce) ----
# diff-driver-check: bench/diff/tests/test_exit.py drives the real run.py and reduce.py with a mocked
# Bend and injects a mismatch (classified as a known defect or not), a crash and an oracle error: each
# must exit 1, a clean run 0. diff-smoke: fixed seeds, Raw then Dictionary (--dict) strings, then the
# F32 reduction check. DIFF_SMOKE_N / DIFF_SMOKE_REDUCE_N size it.
DIFF_SMOKE_N ?= 200
DIFF_SMOKE_REDUCE_N ?= 200
diff-driver-check:
	cd bench && uv run python diff/tests/test_exit.py

diff-smoke:
	cd bench && uv run python diff/run.py --seed 20261001 --n $(DIFF_SMOKE_N) --strict
	cd bench && uv run python diff/run.py --seed 20261002 --n $(DIFF_SMOKE_N) --strict --dict
	cd bench && uv run python diff/reduce.py --seed 20261003 --n $(DIFF_SMOKE_REDUCE_N)
