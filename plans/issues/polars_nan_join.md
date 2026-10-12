# Draft issue for pola-rs/polars

**Title:** Eager `DataFrame.join` on a float key never matches NaN when both key columns are flagged sorted (lazy matches)

### Checks

- [ ] I have checked that this issue has not already been reported. *(search "NaN join sorted" before filing)*
- [x] I have confirmed this bug exists on the latest version of Polars (2.0.0 at the time of writing).

### Reproducible example

```python
import polars as pl

nan = float("nan")

# A 1-row Series is flagged sorted, so the smallest case already shows it.
a = pl.DataFrame({"k": [nan]}, schema={"k": pl.Float32})
print(a.join(a, on="k", how="inner").height)                              # 0
print(a.lazy().join(a.lazy(), on="k", how="inner").collect().height)      # 1

# Same data, with and without the sorted flag.
b = pl.DataFrame({"k": [1.0, 2.0, nan, nan]}, schema={"k": pl.Float32})
bs = b.with_columns(pl.col("k").set_sorted())
print(b.join(b, on="k", how="inner").height)                              # 6
print(bs.join(bs, on="k", how="inner").height)                            # 2
print(bs.lazy().join(bs.lazy(), on="k", how="inner").collect().height)    # 6

# A sort sets the flag, so ordinary pipelines hit it too.
c = pl.DataFrame({"k": [2.0, nan, 1.0, nan]}, schema={"k": pl.Float64}).sort("k")
print(c.join(c, on="k", how="inner").height)                              # 2
print(c.join(c, on="k", how="left").height)                               # 4
print(c.lazy().join(c.lazy(), on="k", how="left").collect().height)       # 6
```

### Log output

```
0
1
6
2
6
2
4
6
```

### Issue description

The result of an eager `DataFrame.join` on a `Float32` / `Float64` key depends on the hidden `SORTED_ASC` flag of the key columns:

- When both key columns are flagged sorted, NaN keys never match each other. That is IEEE `==` behaviour, and it looks like a sorted-merge fast path.
- When either column is not flagged, NaN matches NaN.
- The lazy engine (default and streaming) matches NaN with NaN in every case.

So the same data joined through `DataFrame.join` and `LazyFrame.join` gives different row counts, and so does the same data before and after a no-op `set_sorted()`.

The flag is set implicitly by `sort`, by joins, and on any 1-row Series. That makes the difference easy to hit and hard to see.

- **Affected:** `inner` and `left` joins.
- **Not affected:** `semi` and `anti` joins agree between eager and lazy in the cases above.
- **Scope of testing:** Float32 and Float64, single key column.

We found this while using Polars 2.0.0 as a reference oracle for a dataframe library. In a 3,000-case randomized comparison of joins against a brute-force reference with "NaN equals NaN, -0.0 equals 0.0, null never matches":
- the lazy engine had 0 deviations;
- the eager path had 322, all on inputs where both key columns carried the sorted flag.

### Expected behavior

Eager and lazy joins should give the same result regardless of the sorted flag. Given the lazy engine's behaviour, and that `group_by` / `unique` treat all NaNs as one value, that result is NaN matching NaN. If the intended semantics is IEEE (NaN never matches), then the lazy engine and the unsorted eager path disagree with it instead. Either way, the answer should not depend on metadata the user didn't set.

### Installed versions

```
polars 2.0.0
Python 3.14.3, macOS 26.7 (arm64)
```

*(paste `pl.show_versions()` output here when filing)*
