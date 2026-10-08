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
| T2.3 | F32 reductions vs an exact reference, see "T2.3" below | derived bound, not bit equality |

A symptom is reported once: a lazy result equal to the eager one is not reported against the
oracle again (same defect). Classes: `T2.2 eager`, `T2.1 eager!=raw`, `T2.1 raw!=opt`, `T2.1 raw!=full`,
`T2.2 lazy ..` (only where the oracle says eager and lazy may differ), `T2.4 ..`, `crash`,
`oracle error`.

**Inadmissible programs.** DESIGN.md 15.7 types the whole plan before running it (`collect`), but
eager verbs run one by one: a runtime error (a failing `cast`) in an inner verb is reported
before a static error (unknown column) in an outer one, while lazy reports the static one.
The oracle computes both answers; where they differ the program is "inadmissible" for the
eager-vs-lazy comparison and is counted apart (`inadmissible_for_T2.1`). DESIGN.md 15.9
("admissible programs") states this rule; it is not a defect of the code.

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
| `reduce.py`, `reduce_gen.py`, `reduce_ref.py`, `reduce_shrink.py`, `reduce_regress.py`, `reduce_selftest.py` | T2.3 (`make diff-reduce`), below |

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
* T2.3 (reductions against an exact reference) is a separate driver, `reduce.py` (below), not part of the program generator.
* NaN payloads are not compared (contract); an x86-64 run may print other NaN bits.
* Guessed, untested until the facade has them: the eager `concat_vertical` wrapper and the
  signatures of `drop`, `rename`, `slice`, `tail`, `unique`, `semi_join`, `anti_join`.

## T2.3: F32 reductions against an exact reference

```
make diff-reduce SEED=1 REDUCE_N=2000                  # ~2.5 min: 2000 cases, ~1.1M input rows
cd bench && uv run python diff/reduce.py --seed 1 --n 2000 --classes cancel,special   # some generator classes only
uv run python diff/reduce.py --seed 1 --n 2000 --shrink [--write --xfail NEW-7]       # minimise one case per finding group
uv run python diff/run.py --reductions --seed 1 --n 2000                              # the same, through run.py
make diff-reduce-selftest                                                             # the reference's own tests + mutants
uv run python diff/reduce_regress.py                                                  # rewrite tests/diff/r0001..r0006.bend
```

`reduce_gen.py` makes a frame `t(g: u32, x: f32)` per case (seed and index fix it): 0..10 000 rows
(biased to 4..64, 3 % empty, ~3 % at 5k-10k), a class of values (`uniform`, `wide` exponents,
`cancel` = `[1e8, 1, -1e8]`-style / alternating / near-pairs / ladders, `equal`, `tinyhuge` = many
tiny and one huge, `special` = inf / -inf / NaN / -0.0 injected, `zeros`, small `ints`, `subnormal`,
`ordered`), null rates 0 / 5 / 10 / 50 / 90 / 100 %, and a group layout (1, 2, 3, 7, 64, n/2, n
groups; keys `mod`, random, blocks, one-big-plus-singletons, ids shuffled). Frames are built from
literal chunks of 100 joined by `List.concat` (a 10k literal list overflows the interpreter's stack);
the literals are shortest-decimal f32 text, and the `in` dump of every case is compared with the
intended bits before anything else is checked (so a literal that parsed differently is an
infrastructure error, not a reduction defect). Each case prints, through `DF.dump`:

| tag | what runs |
|-----|-----------|
| `in` | the input frame |
| `sel_e` / `sel_r` / `sel_f` | `select([x.sum() as s, x.mean() as m])` eager / `DF.collect_raw` / `DF.collect_full` |
| `grp_e` / `grp_r` / `grp_f` | `group_by([g], [same])` eager / raw lazy / fully optimised |
| `desc` | `DF.describe` of the `x` column alone (count, null_count, mean, std, min, 25/50/75 %, max) |

`std`, `var` and `median` are emitted as extra aggregations (`s, m, std, var, median` columns) as
soon as `frame.bend` defines `DF.std` / `DF.var` / `DF.median` (`reduce_gen.available_aggs`); the
checks for them (`reduce_ref.model_std/var/median`, bounds (3)-(4)) are already in and exercised
through describe's std. Until the AggOps land, describe is the only std source, and describe's
"50%" is the nearest-rank quantile (idx = round(0.5 (n-1)) half away), which is NOT the contract's
median for even n (`lo*0.5 + hi*0.5`): it is checked as the nearest rank, not as the median.

### Three references, three kinds of check

1. **Exact.** The inputs are f32 bit patterns; sums are Python integers in units of 2^-149 (every f32
   is such a multiple), so sum, mean, centred sum of squares are exact rationals (`reduce_ref.Exact`)
   and `round_f32` rounds them ONCE, to nearest even (tested against numpy, ties and the overflow tie
   `2^128 - 2^103 -> inf` included). "`==RN`" below counts results bit-equal to that value.
2. **Model.** DESIGN.md 15.5.3 / 15.5.4 re-implemented step by step with numpy float32 scalars
   (Neumaier with the non-finite guard in ascending row order; two-pass var/std with every term in
   f32; the median definition; describe's nearest ranks). The contract makes the reduction order
   part of the semantics, so Bend must equal it bit for bit (`model` findings).
3. **Bound.** For finite data whose guarded run stays finite, the answer must lie within a derived
   absolute error of the exact value (`bound` findings). The derivation (full text in
   `reduce_ref.py`'s docstring), u = 2^-24, gamma_k = ku/(1-ku), n valid cells, S the exact sum,
   A = sum |x_i|:
   * sum: `|res - S| <= u|S| + gamma_{n-1}^2 A` (Ogita-Rump-Oishi "Sum2", Prop. 4.4: Neumaier's
     branch makes every step an exact Fast2Sum, `c` collects the n-1 errors in f32, then `s + c`).
     The first term is the last rounding, the second the price of an f32 `c`. For n = 1e4
     `gamma^2 ~ 6u`; for `[1e8, 1, -1e8]` it is ~1e-14, so the answer is exactly 1, while a naive f32
     sum is off by 1 and violates the bound by many orders. Plus 2^-148 slack (subnormals).
   * mean `= fl(s_hat / n)`: `(B_sum + u(|S| + B_sum)) / n` + slack.
   * var / std (ddof 1) about the f32 mean m_hat the algorithm used: each term
     `fl(fl(x - m_hat)^2)` has relative error <= (1+u)^3 - 1 (+ 2^-150 when it underflows), the terms
     are non-negative so Sum2 applies with A = S, the exact sum about m_hat is the centred sum plus
     `n (mu - m_hat)^2`, one more rounding for `/ (n-1)`; std: `|sqrt a - sqrt b| <=
     min(|a-b| / sqrt b, sqrt|a-b|)` plus `u * std`. For a constant column (exact variance 0) the
     answer is `sqrt` of the squared mean error, which the bound includes (below).
   The bound is sharp: `err/bound` reaches 0.9999+ on correctly rounded results (a half-way sum
   16777219 -> 16777220: the last rounding is a whole `u|S|`), so it is not slack in disguise.
   *Tight tier*: if the data are well conditioned (`A <= 2|S|`) and n <= 256, sum must be within 1 ulp and
   mean within 2 ulp of the correctly rounded value (`tight` findings; follows from the bound since
   `u|S| <= 1 ulp`).
   Cases where a partial sum (or a square, in std) of FINITE data overflows are "overflow": the
   contract's guard answers inf/NaN (`[3e38, 3e38, -3e38]` -> inf though the exact sum is finite);
   Bend must equal the model, and these are counted apart.

Non-finite data ("special") are tested apart, against IEEE's order-independent answer
(any NaN -> NaN; +inf with -inf -> NaN; else the inf; std/var of n >= 2 with any non-finite value
-> NaN; n < 2 -> null) as well as against the model. Empty and all-null samples: sum 0.0 (`+0.0`
bits), mean null, std null; sums of `-0.0` are `+0.0` (the accumulator starts at `+0.0`).
Cancellation (`cancel`: conditioning A/|S| > 16 or S = 0) is reported as its own category: its ulp
errors are huge by construction (the answer may be 1 against inputs of 1e8), only the bound applies.

Also checked: raw-lazy and optimised-lazy text equals the eager text (`lazy`), grouped result rows are in
first-appearance order with the right keys and height (`order`/`shape`), a group of all-null rows
has sum 0.0 / mean null, describe's `count`/`null_count`, its min/25/50/75/max against the
stable-sorted valid cells at nearest ranks (`order`, the 25/50/75% rows: Polars `describe` is nearest rank), and
describe's min/max against the min/max rule of 15.5.2 (`minmax`: NaN skipped, `-0.0` before `0.0` on a tie;
NEW-T23-1/2, fixed). `--selftest` also runs the checker over
fake outputs from mutants (naive f32 sum, Kahan without Neumaier's branch, an f64 accumulator, Neumaier
without the guard): the faithful model produces no finding, each weaker sum is flagged, and the f64
accumulator violates only the bit-exact model check, never the bound, as it should.

Exit status is 1 on a `bound`, `special`, `null`, `err`, `lazy`, `order`, `shape`, `model`, `tight` or `minmax` finding, a
crash or an infrastructure error (a `model` mismatch means Bend did not follow the contract's reduction
order: the selftest asserts the faithful model gives none; `minmax` is describe's min/max versus 15.5.2,
which tests/diff/r0001.bend and r0002.bend pin).
