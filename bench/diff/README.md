# bench/diff: the seeded differential generator (plans/M_01.txt T2/T3)

`make diff SEED=1 N=1000` generates N typed programs from a seed, runs each of them three ways in
Bend (eager, raw lazy `DF.collect_raw`, default-optimised `DF.collect`, fully optimised `DF.collect_full`), and compares the dumps (`DF.dump`, DESIGN.md 15.1) with
each other (T2.1) and with an oracle (T2.2). Failures are shrunk, classified against the defect
table (DESIGN.md 15.10) and written to `build/diff/seed<SEED>/failures.json`.

```
cd bench
uv run python diff/run.py --seed 1 --n 1000              # interpreter only: ~10 s (+ shrinking, ~10-30 s)
uv run python diff/run.py --seed 1 --n 1000 --backend both   # + native compile (5 programs, ~3 min), T2.4 interp vs native
uv run python diff/run.py --seed 7 --n 10000 --features deep # up to 300 rows, plans up to 6 verbs
uv run python diff/run.py --features noreductions,noselfjoin # mask B04-a / B04-b (see below)
uv run python diff/gen.py --seed 1 --n 5 --show          # look at generated cases
uv run python diff/gen.py --seed 1 --n 20 --out /tmp/c   # write dNNNN.bend files + cases.json
uv run python diff/shrink.py FAILURES.json d0010 --write # minimise one failure, write tests/diff/dNNNN.bend
uv run python diff/gen.py --lib                          # regenerate tests/diff/lib/dx.bend (after frame.bend grew)
```

## What is compared

| id | comparison | tolerance |
|----|------------|-----------|
| T2.1 | eager vs raw lazy (`DF.collect_raw`); raw vs `DF.collect`; raw vs `DF.collect_full` | none: `bench/check.py` `compare_dumps`; only the contract's NaN-payload rule (15.1 rule 3). Errors and row order count. |
| T2.2 | eager dump vs `oracle.py` | same |
| T2.4 | interpreter vs natively compiled program (`--backend both`) | same |

A symptom is reported once: a lazy result equal to the eager one is not reported against the
oracle again (same defect). Classes: `T2.2 eager`, `T2.1 eager!=raw`, `T2.1 raw!=opt`, `T2.1 raw!=full`,
`T2.2 lazy ..` (only where the oracle says eager and lazy may differ), `T2.4 ..`, `crash`,
`oracle error`.

**Inadmissible programs.** DESIGN.md 15.7 types the whole plan before running it (`collect`), but
eager verbs run one by one: a runtime error (a failing `cast`) in an inner verb is reported
before a static error (unknown column) in an outer one, while lazy reports the static one.
The oracle computes both answers; where they differ the program is "inadmissible" for the
eager-vs-lazy comparison and is counted apart (`inadmissible_for_T2.1`). This is a hole in the
contract's G2, not a defect of the code.

## Files

| file | job |
|------|-----|
| `model.py` | dtypes, frames, expression/plan trees, the contract's typing (15.3) and static errors, **the two tables `EXPRS` and `VERBS`**, case JSON |
| `gen.py` | the seeded generator (frames, expression trees, plans, invalid programs), CLI |
| `emit.py` | Bend emission: input frames from literals, `eager()`, `plan()`, the `DX.three` step; batch programs |
| `dxlib.py` | writes `tests/diff/lib/dx.bend` (static helpers + one eager wrapper per available verb + shims) |
| `oracle.py` | the expected dump: Polars 2.0.0 plus the contract's departures, each a named function |
| `bendrun.py` | batching, running (interpreted or native), output parsing, crash isolation by bisection |
| `evalcase.py` | comparison of one case against the oracle and across the three runs |
| `classify.py` | rules mapping a minimised failure to a 15.10 defect ID; unmatched = NEW |
| `shrink.py` | the minimiser and the writer of permanent `tests/diff/dNNNN.bend` regressions |
| `run.py` | the driver (`make diff`) |

## The grammar is table driven

`model.EXPRS` has one row per expression operator: name, arity, a typing function (the contract's
exact `TypeMismatch` texts), the argument-type signatures it can produce a result type from (used to
generate well-typed trees), and `needs`: the facade defs it requires. `model.VERBS` has one row per
plan verb with its static schema rule. The generator reads `frame.bend` and uses only rows whose
`needs` are all defined there (`--all` forces every row on, for exercising the oracle early). So:

* a verb or builder that lands in the facade (floor_div, try_cast, when, is_in, clip, drop, rename,
  slice, tail, unique, semi/anti join, concat_vertical, std/var/median, ...) starts being generated
  as soon as `frame.bend` has the def; run `make diff-lib` to regenerate `tests/diff/lib/dx.bend`
  (its `e_<verb>` wrappers follow `emit.VERB_DECLS`);
* to add a row: one `reg(...)`/`vreg(...)` line in `model.py` (plus, for a verb, its parameter
  printing in `emit.VERB_PARAMS`/`VERB_DECLS`, a generator in `gen.Gen.verb_params`, and one function
  in `oracle.py` (`IMPL` for expressions, `UNARY`/`JOINS` for verbs)).

Verb names follow the contract: eager `DF.<verb>`, lazy `DF.lazy_<verb>`. The wrappers for
`concat_vertical` (variadic) and the guessed signatures of not-yet-landed verbs are untested until
the facade has them.

## Generator

Seed and index fix a case (`random.Random(f"{seed}:{index}")`). Input frames `t` and `u` have 0..64
rows biased to 0, 1, 2^k-1, 2^k, 2^k+1; columns of the five dtypes; null rates 0/10/50/100 %;
small value domains (duplicate keys); NaN, +-inf, -0.0 and the cast edge values (2^32, -2^31,
4294967040, ...); empty strings, tabs, quotes, non-ASCII. Expressions are well typed by
construction (depth <= 3: arithmetic, comparisons, Kleene logic, fill_null, cast, reductions at any
depth, ...); plans are 1..4 verbs (select, with_columns, filter, sort, group_by, head, inner/left
join, ...) with repeated names and aliases on purpose, self joins (a source used twice, B04-b) and
joins over different sources. About 12 % of the cases are *invalid*: injected unknown columns, wrong
operand types, bad sort/join keys, group_by without keys, an aggregation key. The oracle gives
their expected error text from the contract's typing rules (never from Polars).

## The oracle (`oracle.py`)

Evaluation is by Polars 2.0.0 Series operations (arithmetic, comparisons, Kleene logic, sort, group
keys, joins, concat, unique), with the contract applied where it departs from Polars. The list is
in the module's docstring; each item is a separate function, never a blanket ignore:
strict typing and exact error texts (15.3), cardinality (15.4), integer `//` and `%` null on zero
and `MIN // -1` (15.5.1), Neumaier sums in row order and f32 integer means (15.5.3), std/var/median
(15.5.4), cast/try_cast and the `cast <from> to <to>: row <i> holds <cell>` error (15.5.5), group_by
in first-appearance order. A case the oracle cannot answer faithfully (`Uncertain`) is T2.1-only
and counted; an oracle exception is reported as `oracle error` and fails the run.

## Speed

Interpreted, 200 cases per program: a 1000-case run is ~5 s of Bend (a program of 1000 `do` steps
overflows the machine stack, hence the 200-case batches). A native compile is 10-25 s per
200-case program (clang -O3 on the generated C), so `--backend both` for 1000 cases is ~3 minutes
when the machine is idle and compiles run in parallel; the interpreter alone is the default
(`make diff`). A crash is isolated by bisection; a program that does not compile at all aborts the
run with Bend's message (it does not bisect).

## Known blind spots

* Masking: a known defect that fails every case containing some feature hides the rest of those
  cases. `--features noreductions,noselfjoin` (B04-a / B04-b when they were open) remove those
  features; `deep` adds larger frames and longer plans.
* Joins with large outputs: the interpreter overflows its stack on results of about 2^15 rows or
  more (classified NEW-2); the generator can produce them from low-cardinality keys.
* F32 literals are written as shortest decimals; the oracle trusts Bend's literal parser to round
  like numpy (a double rounding could differ in a last bit for exotic literals; the pools avoid them).
* The oracle takes -0.0 = 0.0 ties from the contract, not from Polars (Polars orders -0.0 first in a
  sort), and reductions over a scalar argument (`lit(1).sum()` is 1) as Polars does.
* T2.3 (reductions against an f64 reference) is not part of this generator.
* NaN payloads are not compared (contract); an x86-64 run may print other NaN bits.
* Guessed, untested until the facade has them: the eager `concat_vertical` wrapper and the
  signatures of `drop`, `rename`, `slice`, `tail`, `unique`, `semi_join`, `anti_join`.
