BEND ?= $(HOME)/.bend/bin/bend
SOURCES := $(shell find src tests -name '*.bend' -type f 2>/dev/null | LC_ALL=C sort)
EXAMPLES := frame.bend $(wildcard examples/*.bend) $(wildcard bench/*.bend)

.PHONY: ci test runner-check check proofs verdict bench bench-check toolchain-check clean

# The full gate, in CI order. Needs the pinned toolchain (TOOLCHAIN): `make toolchain-check` first.
ci: toolchain-check check runner-check test proofs verdict bench-check
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
# build/diff/seed<SEED>/failures.json. Exits 1 on a failure no known defect explains (NEW), a crash
# or an oracle error; DIFF_ARGS=--strict also fails on known defects. See bench/diff/README.md.
.PHONY: diff diff-lib
SEED ?= 1
N ?= 1000
diff:
	cd bench && uv run python diff/run.py --seed $(SEED) --n $(N) $(DIFF_ARGS)

# regenerate the helper module tests/diff/lib/dx.bend after frame.bend gained verbs
diff-lib:
	cd bench && uv run python diff/gen.py --lib
