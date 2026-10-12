import polars as pl
print(pl.__version__)
nan = float("nan")

# 1. one-row frame: a 1-row Series is flagged sorted
a = pl.DataFrame({"k": [nan]}, schema={"k": pl.Float32})
print("1x1 self join  eager:", a.join(a, on="k", how="inner").height,
      " lazy:", a.lazy().join(a.lazy(), on="k", how="inner").collect().height)

# 2. same data, sorted flag set explicitly vs not
b = pl.DataFrame({"k": [1.0, 2.0, nan, nan]}, schema={"k": pl.Float32})
bs = b.with_columns(pl.col("k").set_sorted())
print("4-row, unflagged eager:", b.join(b, on="k", how="inner").height,
      " flagged eager:", bs.join(bs, on="k", how="inner").height,
      " flagged lazy:", bs.lazy().join(bs.lazy(), on="k", how="inner").collect().height)

# 3. flag only on the left / only on the right
print("flag left only eager:", bs.join(b, on="k", how="inner").height,
      " flag right only eager:", b.join(bs, on="k", how="inner").height)
