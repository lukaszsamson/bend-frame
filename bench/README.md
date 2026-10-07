# bench: Polars reference + golden outputs

Requires [`uv`](https://docs.astral.sh/uv/); Polars is pinned to `>=2.0,<3` in `pyproject.toml`.

```sh
uv run --project bench python bench/gen.py [n ...]   # default 1_000 100_000 1_000_000 -> bench/data/ (gitignored)
(cd bench && uv run python golden.py)                # regenerate bench/golden/q1..q6.csv from fixtures/tiny.csv
scripts/bench.sh                                     # gen if missing, then time Polars -> bench/results/polars.json
```

Data is seeded and deterministic. `fixtures/tiny.csv` (20 rows, includes null discounts) and
`fixtures/products.csv` (64 rows) are tracked; golden floats are written with 4 decimals.
`fixtures/` and `data/` use the same schema, so a Bend implementation can load either.

## Queries (`queries.py`, all signature `qK(sales, products)`; floats are Float32)

| q | what |
|---|------|
| q1 | filter `ok and qty > 50`, select `id, region, price` (file order) |
| q2 | add `revenue = qty * price * (1 - fill_null(discount, 0))` |
| q3 | q2, then group by `region`: sum(revenue), mean(price), count, max(qty), sorted by region |
| q4 | sort by `region` asc, `price` desc (ties broken by `id` asc), first 10 rows |
| q5 | inner join `products` on `product`, group by `category`: sum(qty), sorted by category |
| q6 | `describe()` of `id, qty, price, discount` |

## Timing

`run_polars.py` parses each CSV once (untimed), then times `collect()` per query: best of 5, with
the default engine (streaming in Polars 2.0). It runs twice in subprocesses, once with default
threads and once with `POLARS_MAX_THREADS=1` (must be set before import) for comparison with
single-threaded Bend. Results: `results/polars.json` as `{query, n, seconds, threads}`.
Note q6 includes the `describe()` computation (eager) inside the timed call.
