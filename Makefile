BEND ?= $(HOME)/.bend/bin/bend
SOURCES := $(shell find src tests -name '*.bend' -type f 2>/dev/null | LC_ALL=C sort)
EXAMPLES := frame.bend $(wildcard examples/*.bend) $(wildcard bench/*.bend)

.PHONY: ci test runner-check check proofs verdict verdict-probe test-mutation-check bench bench-check toolchain-check clean mutation-check consumer-check diff-driver-check diff-smoke

# The full gate, in CI order. Needs the pinned toolchain (TOOLCHAIN): `make toolchain-check` first.
# Beyond the unit gates: the differential drivers' exit-status regression, a bounded strict
# differential smoke (Raw and Dictionary strings, then the F32 reduction check), the proof mutation
# check and the clean-consumer check (needs the work committed: it clones HEAD). Larger differential
# runs (make diff N=..., make diff-reduce REDUCE_N=...) are the scheduled/release gate.
ci: toolchain-check check runner-check diff-driver-check test proofs verdict mutation-check test-mutation-check bench-check diff-smoke csv-fuzz-smoke fork-audit radix-check tpch-check consumer-check
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

# the cheap half of verdict: only the BendTT translation (no Lean run); it fails the way --verdict
# did on Bend 2.0.38+ before the FZW Sigma was inlined (bendlang/bend#1984). Use after toolchain bumps.
# the tested-only fast paths guarded by their tests: each mutation (the v0.3 review's) must fail them
test-mutation-check:
	scripts/test_mutation_check.sh

verdict-probe:
	@mkdir -p build
	$(BEND) PROOF.bend -o build/PROOF.bendtt
	@echo "verdict-probe: BendTT translation ok ($$(wc -c < build/PROOF.bendtt | tr -d ' ') bytes)"

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
	chkw() { if [ "$$2" = "$$3" ]; then echo "ok     $$1 $$2"; else echo "warn   $$1: installed '$$2', TOOLCHAIN '$$3' (not a gate: uv sync --locked pins the Python side)"; fi; }; \
	chkw uv "$$(uv --version 2>/dev/null | awk '{print $$2}')" "$$UV_VERSION"; \
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
# F32 reduction check; the two program runs include G1 (--chunked: the chunked engine at grains 2^0, 2^2,
# 2^4 and 2^14 against the reference, exactly). DIFF_SMOKE_N / DIFF_SMOKE_REDUCE_N size it.
DIFF_SMOKE_N ?= 200
DIFF_SMOKE_REDUCE_N ?= 200
diff-driver-check:
	cd bench && uv run python diff/tests/test_exit.py

diff-smoke:
	cd bench && uv run python diff/run.py --seed 20261001 --n $(DIFF_SMOKE_N) --strict --chunked
	cd bench && uv run python diff/run.py --seed 20261002 --n $(DIFF_SMOKE_N) --strict --dict --chunked
	cd bench && uv run python diff/reduce.py --seed 20261003 --n $(DIFF_SMOKE_REDUCE_N)

# ---- G1 (v0.2 T5.3): the chunked engine against the reference engine (bench/diff run.py --chunked) ----
# make diff-chunked [SEED=1] [G1_N=2000]: G1_N generated cases in Raw and G1_N in Dictionary mode, plus
# G1_N/4 of each with --features deep (frames up to 300 rows, plans up to 6 verbs); every case runs the
# reference (eager, raw, collect, full) and the chunked engine at grains 2^0 / 2^2 / 2^4 (raw plan) and 2^14
# (collect), compared exactly (bench/check.py compare_dumps). Exits 1 on any failure.
G1_N ?= 2000
.PHONY: diff-chunked
diff-chunked:
	cd bench && uv run python diff/run.py --seed $(SEED) --n $(G1_N) --chunked
	cd bench && uv run python diff/run.py --seed $(shell expr $(SEED) + 1) --n $(G1_N) --chunked --dict
	cd bench && uv run python diff/run.py --seed $(shell expr $(SEED) + 2) --n $(shell expr $(G1_N) / 4) --chunked --features deep
	cd bench && uv run python diff/run.py --seed $(shell expr $(SEED) + 3) --n $(shell expr $(G1_N) / 4) --chunked --dict --features deep

# ---- T6: public-API coverage matrix (scripts/coverage_matrix.py, plans/M_01.txt T6) ----------
# make coverage: regenerates docs/COVERAGE.md (the matrix and the def-call report over src/) and exits 1
# when a released operation lacks a kind (success, null, empty, invalid, eager, lazy) or an annotation is
# invalid. `make coverage` is part of `make ci` (the extra prerequisite below).
.PHONY: coverage
coverage:
	python3 scripts/coverage_matrix.py

# ci's form: regenerate, then fail if the committed docs/COVERAGE.md is stale (v0.3 W2: it used to dirty the
# tree silently); commit the regenerated file to fix
coverage-check: coverage
	@git diff --quiet HEAD -- docs/COVERAGE.md || { git --no-pager diff --stat HEAD -- docs/COVERAGE.md; echo "coverage-check: docs/COVERAGE.md is stale: commit the regenerated file"; exit 1; }
	@echo "coverage-check: docs/COVERAGE.md up to date"

ci: coverage-check

# ---- W0 measurement harness (bench/m2/README.md, plans/M_02.txt W0, G2-G6) ---------------------
# make m2-baseline            materialise commit 3612482 into build/m2/baseline-src (git archive) and build its
#                             native driver; build/m2/baseline/driver and build/m2/candidate/driver coexist
# make m2-candidate           build the driver from the current checkout (run.py refuses a stale one)
# make m2-data                generate bench/data (sales, hc, nunique, long-prefix keys) and check the frozen sha256
# make m2-smoke               1 process per cell, 1k/100k rows only, threads 1 and 12, both binaries (sanity check)
# make m2-bench LABEL=x       the FULL gate run: every frozen workload, threads 1/4/12, 5 fresh interleaved
#                             processes per cell, results in bench/m2/results/x.jsonl. Needs a quiet machine
#                             (load < M2_QUIET at the start); on a shared machine add M2_ARGS="--provisional"
# make m2-summary LABEL=x     medians, ranges, ratios candidate/baseline, 12-vs-1 scaling, RSS, stage table
# make m2-freeze              re-freeze bench/m2/expected.json from the BASELINE binary (deliberate act)
# make m2-micro LABEL=x       the preserved review probes (bench/micro) under the interleaved runner
# make m2-g6-build            build the INSTRUMENTED drivers (build/m2/{baseline,candidate}-g6: the emitted C patched
#                             with copy / allocation counters by bench/m2/instrument.py; timings never valid)
# make m2-g6 LABEL=x          G6: q1-q6 + parse + the string cells once per engine combination (reference; v02 reader;
#                             v02,chunked) at 1 thread for the baseline and the candidate, instrumented; writes
#                             bench/m2/results/g6-x.jsonl and g6-x.md (copied / allocated bytes per phase, copy sources,
#                             chunk conversions). Counts are deterministic, so load does not matter. Options via
#                             M2_G6_ARGS, e.g. --smoke (100k rows), --procs 2 (determinism check), --only GLOB, --no-cstats
# The driver and the probes are also compiled by `make check` (EXAMPLES below).
EXAMPLES += $(wildcard bench/m2/*.bend) $(wildcard bench/micro/*.bend)
.PHONY: m2-baseline m2-candidate m2-data m2-smoke m2-bench m2-summary m2-freeze m2-micro m2-g6 m2-g6-build
LABEL ?= $(shell date +%Y%m%d-%H%M%S)
M2_QUIET ?= 2
M2_ARGS ?=
M2_G6_ARGS ?=
m2-baseline:
	bench/m2/baseline.sh

m2-candidate:
	bench/m2/baseline.sh --candidate

m2-data:
	uv run --project bench python bench/m2/gen.py

m2-smoke: m2-baseline m2-candidate
	uv run --project bench python bench/m2/run.py run --label smoke-$(LABEL) --smoke $(M2_ARGS)

m2-bench: m2-baseline m2-candidate
	uv run --project bench python bench/m2/run.py run --label $(LABEL) --require-quiet $(M2_QUIET) $(M2_ARGS)

m2-summary:
	uv run --project bench python bench/m2/run.py summary bench/m2/results/$(LABEL).jsonl --raw

m2-freeze: m2-baseline
	uv run --project bench python bench/m2/run.py freeze

m2-micro:
	uv run --project bench python bench/m2/run.py micro --label $(LABEL)

m2-g6-build:
	bench/m2/baseline.sh --instrument
	bench/m2/baseline.sh --candidate --instrument

m2-g6: m2-g6-build
	uv run --project bench python bench/m2/run.py g6 --label $(LABEL) --no-build $(M2_G6_ARGS)

# ---- W2.1 / W2.2: the flat string coder (src/hcode.bend) and the rank stage (src/ranks.bend) ------
# make w2-diff     native differential vs v0.1 (bench/w2/diff.sh): every shape up to 20000 rows, including
#                  the code points above U+10FFFF that the interpreter refuses (tests/ cannot build them)
# make w2-mutation the mutation controls of the tests (bench/w2/mutation.py; each mutant must be killed
#                  except the documented equivalent ones)
# bench/w2/campaign.sh + tables.py: the provisional measurements (not part of ci)
# The probes are also compiled by `make check` (EXAMPLES below).
EXAMPLES += $(wildcard bench/w2/*.bend)
.PHONY: w2-diff w2-mutation
w2-diff:
	bench/w2/diff.sh

w2-mutation:
	python3 bench/w2/mutation.py

# ---- PDS-H-style workload (bench/tpch/README.md) ----------------------------------------------------
# make tpch [TPCH_SF=0.2]  generate TPC-H-shaped tables if missing, build bench/tpch/run.bend, run the nine
#                          queries at one thread (5 collects each, ms per collect) and check every result
#                          against Polars (bench/tpch/run_polars.py check); not part of ci
EXAMPLES += $(wildcard bench/tpch/*.bend)
# bench/mem/probe.bend: peak-memory probes (arrays, lists, a CSV read), run under /usr/bin/time -l
EXAMPLES += $(wildcard bench/mem/*.bend)
TPCH_SF ?= 0.2
.PHONY: tpch
tpch:
	@test -f bench/data/tpch/sf$(TPCH_SF)/lineitem.csv || uv run --project bench python bench/tpch/gen.py $(TPCH_SF)
	$(BEND) bench/tpch/run.bend -o build/tpch
	@mkdir -p build/tpch_out
	./build/tpch +RTS --threads 1 -RTS bench/data/tpch/sf$(TPCH_SF) all 5 build/tpch_out
	uv run --project bench python bench/tpch/run_polars.py check bench/data/tpch/sf$(TPCH_SF) build/tpch_out

# make tpch-check: the comparator's self-test, then the nine queries at sf 0.01 (tables generated on demand),
# one collect each, every result checked against Polars; in make ci (v0.3 W2)
.PHONY: tpch-check
tpch-check:
	uv run --project bench python bench/tpch/run_polars.py selftest
	@test -f bench/data/tpch/sf0.01/lineitem.csv || uv run --project bench python bench/tpch/gen.py 0.01
	$(BEND) bench/tpch/run.bend -o build/tpch
	@mkdir -p build/tpch_check
	./build/tpch +RTS --threads 1 -RTS bench/data/tpch/sf0.01 all 1 build/tpch_check > /dev/null
	uv run --project bench python bench/tpch/run_polars.py check bench/data/tpch/sf0.01 build/tpch_check

# ---- W6.4: CSV fuzz harness of the reader (bench/diff/csvfuzz.py) -----------------------------------------
# The reference is the reader at 1 MiB pieces; the smoke seeds also check bench/diff/golden/seed<S>.json, the
# reference texts' hashes frozen from the removed v0.1 reader (DESIGN.md 14 "Pre-release").
# make csv-fuzz SEED=1 N=10000 [CSV_FUZZ_ARGS="--jobs 8 --shrink-secs 300"]
#     N random files + read specs (bench/diff/csvgen.py), each read by the reader at piece sizes 1, 2, 3, 7,
#     64, 4096 and the default, compared exactly (DF.dump + Str storage). Native runner build/csvfuzz/runner
#     (built on demand, ~7 s). Failures are shrunk and written to build/csvfuzz/seed<SEED>/failures.json;
#     exit 1 on any failure. ~30 s per 2000 cases on an 8-job run. `--show c000017` prints one case's texts.
# make csv-fuzz-check   the harness's own regression (generator coverage floor, fake runner: difference /
#                       crash -> exit 1, shrinking), no Bend needed
# make csv-fuzz-smoke   csv-fuzz-check, then two fixed seeds x CSV_SMOKE_N cases, deterministic (not in `ci:`
#                       yet; the orchestrator decides)
# make csv-fuzz-mutants detection power: mutants of the reader (bench/w6/mut63.py's list, applied to a
#                       COPY of src/) must make the fuzz run fail; ~10 min, not part of ci
CSV_SMOKE_N ?= 1500
CSV_FUZZ_ARGS ?=
EXAMPLES += bench/diff/csvfuzz.bend
.PHONY: csv-fuzz csv-fuzz-check csv-fuzz-smoke csv-fuzz-mutants
csv-fuzz:
	cd bench && BEND=$(BEND) uv run python diff/csvfuzz.py --seed $(SEED) --n $(N) $(CSV_FUZZ_ARGS)

csv-fuzz-check:
	cd bench && uv run python diff/tests/test_csvfuzz.py

csv-fuzz-smoke: csv-fuzz-check
	cd bench && BEND=$(BEND) uv run python diff/csvfuzz.py --seed 20261004 --n $(CSV_SMOKE_N) --strict --golden diff/golden/seed20261004.json
	cd bench && BEND=$(BEND) uv run python diff/csvfuzz.py --seed 20261005 --n $(CSV_SMOKE_N) --strict --golden diff/golden/seed20261005.json

csv-fuzz-mutants:
	cd bench && BEND=$(BEND) uv run python diff/csvfuzz_mut.py $(CSV_FUZZ_ARGS)

# ---- fork-audit: the Bend 2.0.36 scheduler's fork-shape rule (DESIGN.md 16.10, bench/w5/scale/forkaudit.py) ----
# A def with a parallel let does nothing but match (and call FLAT helpers) before the fork; a non-flat fork-free
# call in a branch argument or before the fork becomes a task the grow pass does not run, and the subtree below
# runs on one thread (the ~2x ceiling). Two parts, both static and deterministic (no timing, no data):
#   1. the source lint over src/*.bend and frame.bend: every parallel let (67 today, the generated src/ckernels.bend
#      wrappers included: no program reaches them all) has no non-primitive call in a branch argument or in a
#      statement before it; any finding fails (there is no allowlist for this part);
#   2. the emitted C of the audited programs (bench/m2/driver.bend: the v0.2 CSV reader, the chunked engine, the
#      describe fork; tests/ckernels_sizes.bend: the chunked kernel wrappers): every call task inside a forking def
#      must be an entry of bench/w5/scale/forkaudit.allow (leaf / root / join, with its one-line reason); a new
#      pair fails, and so does an entry that no longer matches anything (stale).
# Cost: two `bend -o x.c` compiles (~15 s each on a quiet machine) + two python passes; add a program to
# FORK_AUDIT_PROGS to cover a new fork tree no audited program reaches.
FORK_AUDIT_PROGS := bench/m2/driver.bend tests/ckernels_sizes.bend
.PHONY: fork-audit
fork-audit:
	@python3 -I bench/w5/scale/forkaudit.py --src src/*.bend frame.bend
	@mkdir -p build/fork-audit
	@for p in $(FORK_AUDIT_PROGS); do $(BEND) $$p -o build/fork-audit/$$(basename $$p .bend).c > /dev/null || exit 1; done
	@python3 -I bench/w5/scale/forkaudit.py --check bench/w5/scale/forkaudit.allow $(foreach p,$(FORK_AUDIT_PROGS),build/fork-audit/$(basename $(notdir $(p))).c)

# Radix.sort's 8-bit (depth <= 14) and 16-bit paths give the same stable order, 9 shapes x 10 sizes
# incl. the dispatch boundary 16383 / 16384 / 16385 / 32768 and n = 0 (native: the JS interpreter
# cannot build the 2^15-slot arrays the 16-bit side needs in reasonable time)
radix-check:
	@mkdir -p build
	@$(BEND) bench/checks/radix_paths.bend -o build/radix_paths > /dev/null
	@./build/radix_paths > build/radix_paths.out
	@n=$$(grep -c 'eq=1 sorted=1 stable=1$$' build/radix_paths.out); t=$$(wc -l < build/radix_paths.out | tr -d ' '); \
	  if [ "$$n" = 90 ] && [ "$$t" = 90 ]; then echo "radix-check: ok, 90 cases"; else echo "radix-check: FAIL ($$n of $$t ok)"; cat build/radix_paths.out; exit 1; fi
