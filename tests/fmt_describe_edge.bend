# Fmt.describe over the edges of the borrowed, fused numeric path (W1c), through the typed
# oracle DF.dump so the f32 results are compared bit for bit (the expected text was produced by
# the pre-W1c describe, the clone-and-six-passes version, and is unchanged):
#  - all-null columns of every numeric dtype, an empty frame, a zero-row frame
#  - NaN (skipped by min / max, greatest in the quantile order), +-inf (non-finite sum guard),
#    -0.0 / 0.0 ties, a u32 beyond 2^24, i32 extremes
#  - validity masks whose valid count is a power of two with NULL rows after the last valid one
#    (the compaction writes slot `kept`), leading nulls, one valid row among nulls
#  - the input frame comes back untouched (Fmt.describe hands it back; it is dumped too)
import ./../frame.bend as DF
import ./../src/dtype.bend as D
import ./../src/err.bend as E
import ./../src/column.bend as C
import ./../src/fmt.bend as F

def mk.k(name: String, r: E.ResT(C.Column)) -> C.Named:
  match r:
    case Fail{e}:
      C.Named{E.Err.show(e), C.CU32{0, 0n, C.AllValid{}, [0 : U32*1n]}}
    case Done{c}:
      C.Named{name, c}

def mk(name: String, xs: List<&2, D.Scalar>, +t: D.DType) -> C.Named:
  mk.k(name, C.Column.from_scalars(xs, t))

def nan() -> F32:
  F32.div(0.0, 0.0)

def inf() -> F32:
  F32.div(1.0, 0.0)

def nz() -> F32:
  F32.neg(0.0)

def f(x: F32) -> D.Scalar:
  D.SF32{x}

def ni(x: U32) -> D.Scalar:
  D.SI32{D.I32.neg(D.I32{x})}

def pi(x: U32) -> D.Scalar:
  D.SI32{D.I32{x}}

# all-null columns of u32 / i32 / f32 (count 0, null_count 3, everything else null)
def allnull() -> E.ResT(C.Frame):
  C.Frame.from_columns([
    mk("u", [D.SNull{}, D.SNull{}, D.SNull{}], D.TU32{}),
    mk("i", [D.SNull{}, D.SNull{}, D.SNull{}], D.TI32{}),
    mk("f", [D.SNull{}, D.SNull{}, D.SNull{}], D.TF32{})])

# no rows: count 0, null_count 0
def zero_rows() -> E.ResT(C.Frame):
  C.Frame.from_columns([mk("u", [], D.TU32{}), mk("f", [], D.TF32{}), mk("s", [], D.TStr{})])

def zero_cols() -> E.ResT(C.Frame):
  Done{C.Frame{3, Nil{}}}

# NaN skipped by min / max and last in the quantile order; the mean and std are NaN
def nan_a() -> E.ResT(C.Frame):
  C.Frame.from_columns([mk("a", [f(3.0), f(nan()), f(1.0), f(2.0), D.SNull{}, f(nan())], D.TF32{})])

def nan_b() -> E.ResT(C.Frame):
  C.Frame.from_columns([mk("b", [f(nan()), f(nan()), f(nan())], D.TF32{})])

# non-finite sums: +inf, +inf and -inf (NaN), -inf only
def withinf() -> E.ResT(C.Frame):
  C.Frame.from_columns([
    mk("p", [f(1.0), f(inf()), f(2.0), f(4.0)], D.TF32{}),
    mk("q", [f(inf()), f(F32.neg(inf())), f(1.0), f(2.0)], D.TF32{}),
    mk("r", [f(F32.neg(inf())), f(5.0), D.SNull{}, f(6.0)], D.TF32{})])

# -0.0 / 0.0 ties: min is -0.0, max is 0.0 whatever the order; mean 0
def zeros_a() -> E.ResT(C.Frame):
  C.Frame.from_columns([mk("a", [f(0.0), f(nz()), f(0.0), f(nz())], D.TF32{})])

def zeros_b() -> E.ResT(C.Frame):
  C.Frame.from_columns([mk("b", [f(nz()), f(0.0)], D.TF32{})])

def zeros_c() -> E.ResT(C.Frame):
  C.Frame.from_columns([mk("c", [f(nz()), f(nz()), D.SNull{}], D.TF32{})])

# huge u32 (beyond 2^24, rounded by U32.to_f32), i32 extremes
def wide_u() -> E.ResT(C.Frame):
  C.Frame.from_columns([mk("u", [D.SU32{4294967295}, D.SU32{16777217}, D.SU32{0}, D.SU32{2147483648}], D.TU32{})])

def wide_i() -> E.ResT(C.Frame):
  C.Frame.from_columns([mk("i", [pi(2147483647), ni(2147483648), pi(0), ni(1), pi(16777217)], D.TI32{})])

# 4 valid of 6 rows with the nulls AFTER the last valid row (the valid count is a power of two),
# then 2 valid of 5 (a null first, between and last), then 1 valid of 4, for u32 / i32 / f32
def tail_a() -> E.ResT(C.Frame):
  C.Frame.from_columns([
    mk("fa", [f(5.0), f(1.5), f(nz()), f(9.0), D.SNull{}, D.SNull{}], D.TF32{}),
    mk("ua", [D.SU32{9}, D.SU32{3}, D.SU32{7}, D.SU32{1}, D.SNull{}, D.SNull{}], D.TU32{}),
    mk("ia", [pi(9), ni(3), pi(7), ni(1), D.SNull{}, D.SNull{}], D.TI32{})])

def tail_b() -> E.ResT(C.Frame):
  C.Frame.from_columns([
    mk("fb", [D.SNull{}, f(2.0), D.SNull{}, f(8.0), D.SNull{}], D.TF32{}),
    mk("ub", [D.SU32{2}, D.SNull{}, D.SU32{8}, D.SNull{}, D.SNull{}], D.TU32{})])

def tail_c() -> E.ResT(C.Frame):
  C.Frame.from_columns([mk("fc", [D.SNull{}, f(3.0), D.SNull{}, D.SNull{}], D.TF32{})])

# power-of-two row counts without nulls: 1, 2, 4, 8 rows
def pow2_a() -> E.ResT(C.Frame):
  C.Frame.from_columns([mk("f1", [f(2.5)], D.TF32{})])

def pow2_b() -> E.ResT(C.Frame):
  C.Frame.from_columns([mk("f2", [f(2.5), f(7.5)], D.TF32{})])

def pow2_c() -> E.ResT(C.Frame):
  C.Frame.from_columns([mk("u4", [D.SU32{4}, D.SU32{1}, D.SU32{3}, D.SU32{2}], D.TU32{})])

def pow2_d() -> E.ResT(C.Frame):
  C.Frame.from_columns([mk("i8", [ni(4), pi(1), ni(3), pi(2), ni(8), pi(7), ni(6), pi(5)], D.TI32{})])

def frame_dump(r: C.Frame & E.ResT(C.Frame)) -> String:
  (g, res) = r
  DF.dump(res) ++ DF.dump(Done{g})

def desc(r: E.ResT(C.Frame)) -> String:
  match r:
    case Fail{e}:
      "error\t" ++ E.Err.show(e)
    case Done{fr}:
      frame_dump(F.Fmt.describe(fr))

def main() -> IO(Unit):
  do IO<Unit>:
    IO.print("-- allnull")
    IO.print(desc(allnull()))
    IO.print("-- zero_rows")
    IO.print(desc(zero_rows()))
    IO.print("-- zero_cols")
    IO.print(desc(zero_cols()))
    IO.print("-- empty")
    IO.print(desc(Done{C.Frame.empty()}))
    IO.print("-- nan_a")
    IO.print(desc(nan_a()))
    IO.print("-- nan_b")
    IO.print(desc(nan_b()))
    IO.print("-- withinf")
    IO.print(desc(withinf()))
    IO.print("-- zeros_a")
    IO.print(desc(zeros_a()))
    IO.print("-- zeros_b")
    IO.print(desc(zeros_b()))
    IO.print("-- zeros_c")
    IO.print(desc(zeros_c()))
    IO.print("-- wide_u")
    IO.print(desc(wide_u()))
    IO.print("-- wide_i")
    IO.print(desc(wide_i()))
    IO.print("-- tail_a")
    IO.print(desc(tail_a()))
    IO.print("-- tail_b")
    IO.print(desc(tail_b()))
    IO.print("-- tail_c")
    IO.print(desc(tail_c()))
    IO.print("-- pow2_a")
    IO.print(desc(pow2_a()))
    IO.print("-- pow2_b")
    IO.print(desc(pow2_b()))
    IO.print("-- pow2_c")
    IO.print(desc(pow2_c()))
    IO.print("-- pow2_d")
    IO.print(desc(pow2_d()))
#|-- allnull
#|frame
#|height	9
#|width	4
#|col	str	"statistic"
#|col	f32	"u"
#|col	f32	"i"
#|col	f32	"f"
#|row	"count"	0x00000000	0x00000000	0x00000000
#|row	"null_count"	0x40400000	0x40400000	0x40400000
#|row	"mean"	null	null	null
#|row	"std"	null	null	null
#|row	"min"	null	null	null
#|row	"25%"	null	null	null
#|row	"50%"	null	null	null
#|row	"75%"	null	null	null
#|row	"max"	null	null	null
#|frame
#|height	3
#|width	3
#|col	u32	"u"
#|col	i32	"i"
#|col	f32	"f"
#|row	null	null	null
#|row	null	null	null
#|row	null	null	null
#|
#|-- zero_rows
#|frame
#|height	9
#|width	4
#|col	str	"statistic"
#|col	f32	"u"
#|col	f32	"f"
#|col	str	"s"
#|row	"count"	0x00000000	0x00000000	"0"
#|row	"null_count"	0x00000000	0x00000000	"0"
#|row	"mean"	null	null	null
#|row	"std"	null	null	null
#|row	"min"	null	null	null
#|row	"25%"	null	null	null
#|row	"50%"	null	null	null
#|row	"75%"	null	null	null
#|row	"max"	null	null	null
#|frame
#|height	0
#|width	3
#|col	u32	"u"
#|col	f32	"f"
#|col	str	"s"
#|
#|-- zero_cols
#|frame
#|height	9
#|width	1
#|col	str	"statistic"
#|row	"count"
#|row	"null_count"
#|row	"mean"
#|row	"std"
#|row	"min"
#|row	"25%"
#|row	"50%"
#|row	"75%"
#|row	"max"
#|frame
#|height	3
#|width	0
#|
#|-- empty
#|frame
#|height	9
#|width	1
#|col	str	"statistic"
#|row	"count"
#|row	"null_count"
#|row	"mean"
#|row	"std"
#|row	"min"
#|row	"25%"
#|row	"50%"
#|row	"75%"
#|row	"max"
#|frame
#|height	0
#|width	0
#|
#|-- nan_a
#|frame
#|height	9
#|width	2
#|col	str	"statistic"
#|col	f32	"a"
#|row	"count"	0x40a00000
#|row	"null_count"	0x3f800000
#|row	"mean"	0x7fc00000
#|row	"std"	0x7fc00000
#|row	"min"	0x3f800000
#|row	"25%"	0x40000000
#|row	"50%"	0x40400000
#|row	"75%"	0x7fc00000
#|row	"max"	0x40400000
#|frame
#|height	6
#|width	1
#|col	f32	"a"
#|row	0x40400000
#|row	0x7fc00000
#|row	0x3f800000
#|row	0x40000000
#|row	null
#|row	0x7fc00000
#|
#|-- nan_b
#|frame
#|height	9
#|width	2
#|col	str	"statistic"
#|col	f32	"b"
#|row	"count"	0x40400000
#|row	"null_count"	0x00000000
#|row	"mean"	0x7fc00000
#|row	"std"	0x7fc00000
#|row	"min"	0x7fc00000
#|row	"25%"	0x7fc00000
#|row	"50%"	0x7fc00000
#|row	"75%"	0x7fc00000
#|row	"max"	0x7fc00000
#|frame
#|height	3
#|width	1
#|col	f32	"b"
#|row	0x7fc00000
#|row	0x7fc00000
#|row	0x7fc00000
#|
#|-- withinf
#|frame
#|height	9
#|width	4
#|col	str	"statistic"
#|col	f32	"p"
#|col	f32	"q"
#|col	f32	"r"
#|row	"count"	0x40800000	0x40800000	0x40400000
#|row	"null_count"	0x00000000	0x00000000	0x3f800000
#|row	"mean"	0x7f800000	0x7fc00000	0xff800000
#|row	"std"	0x7fc00000	0x7fc00000	0x7fc00000
#|row	"min"	0x3f800000	0xff800000	0xff800000
#|row	"25%"	0x40000000	0x3f800000	0x40a00000
#|row	"50%"	0x40800000	0x40000000	0x40a00000
#|row	"75%"	0x40800000	0x40000000	0x40c00000
#|row	"max"	0x7f800000	0x7f800000	0x40c00000
#|frame
#|height	4
#|width	3
#|col	f32	"p"
#|col	f32	"q"
#|col	f32	"r"
#|row	0x3f800000	0x7f800000	0xff800000
#|row	0x7f800000	0xff800000	0x40a00000
#|row	0x40000000	0x3f800000	null
#|row	0x40800000	0x40000000	0x40c00000
#|
#|-- zeros_a
#|frame
#|height	9
#|width	2
#|col	str	"statistic"
#|col	f32	"a"
#|row	"count"	0x40800000
#|row	"null_count"	0x00000000
#|row	"mean"	0x00000000
#|row	"std"	0x00000000
#|row	"min"	0x80000000
#|row	"25%"	0x80000000
#|row	"50%"	0x00000000
#|row	"75%"	0x00000000
#|row	"max"	0x00000000
#|frame
#|height	4
#|width	1
#|col	f32	"a"
#|row	0x00000000
#|row	0x80000000
#|row	0x00000000
#|row	0x80000000
#|
#|-- zeros_b
#|frame
#|height	9
#|width	2
#|col	str	"statistic"
#|col	f32	"b"
#|row	"count"	0x40000000
#|row	"null_count"	0x00000000
#|row	"mean"	0x00000000
#|row	"std"	0x00000000
#|row	"min"	0x80000000
#|row	"25%"	0x80000000
#|row	"50%"	0x00000000
#|row	"75%"	0x00000000
#|row	"max"	0x00000000
#|frame
#|height	2
#|width	1
#|col	f32	"b"
#|row	0x80000000
#|row	0x00000000
#|
#|-- zeros_c
#|frame
#|height	9
#|width	2
#|col	str	"statistic"
#|col	f32	"c"
#|row	"count"	0x40000000
#|row	"null_count"	0x3f800000
#|row	"mean"	0x00000000
#|row	"std"	0x00000000
#|row	"min"	0x80000000
#|row	"25%"	0x80000000
#|row	"50%"	0x80000000
#|row	"75%"	0x80000000
#|row	"max"	0x80000000
#|frame
#|height	3
#|width	1
#|col	f32	"c"
#|row	0x80000000
#|row	0x80000000
#|row	null
#|
#|-- wide_u
#|frame
#|height	9
#|width	2
#|col	str	"statistic"
#|col	f32	"u"
#|row	"count"	0x40800000
#|row	"null_count"	0x00000000
#|row	"mean"	0x4ec08000
#|row	"std"	0x4ef494a2
#|row	"min"	0x00000000
#|row	"25%"	0x4b800000
#|row	"50%"	0x4f000000
#|row	"75%"	0x4f000000
#|row	"max"	0x4f800000
#|frame
#|height	4
#|width	1
#|col	u32	"u"
#|row	4294967295
#|row	16777217
#|row	0
#|row	2147483648
#|
#|-- wide_i
#|frame
#|height	9
#|width	2
#|col	str	"statistic"
#|col	f32	"i"
#|row	"count"	0x40a00000
#|row	"null_count"	0x00000000
#|row	"mean"	0x4a4ccccc
#|row	"std"	0x4eb50584
#|row	"min"	0xcf000000
#|row	"25%"	0xbf800000
#|row	"50%"	0x00000000
#|row	"75%"	0x4b800000
#|row	"max"	0x4f000000
#|frame
#|height	5
#|width	1
#|col	i32	"i"
#|row	2147483647
#|row	-2147483648
#|row	0
#|row	-1
#|row	16777217
#|
#|-- tail_a
#|frame
#|height	9
#|width	4
#|col	str	"statistic"
#|col	f32	"fa"
#|col	f32	"ua"
#|col	f32	"ia"
#|row	"count"	0x40800000	0x40800000	0x40800000
#|row	"null_count"	0x40000000	0x40000000	0x40000000
#|row	"mean"	0x40780000	0x40a00000	0x40400000
#|row	"std"	0x40803ff0	0x4069b1e9	0x40bc6931
#|row	"min"	0x80000000	0x3f800000	0xc0400000
#|row	"25%"	0x3fc00000	0x40400000	0xbf800000
#|row	"50%"	0x40a00000	0x40e00000	0x40e00000
#|row	"75%"	0x40a00000	0x40e00000	0x40e00000
#|row	"max"	0x41100000	0x41100000	0x41100000
#|frame
#|height	6
#|width	3
#|col	f32	"fa"
#|col	u32	"ua"
#|col	i32	"ia"
#|row	0x40a00000	9	9
#|row	0x3fc00000	3	-3
#|row	0x80000000	7	7
#|row	0x41100000	1	-1
#|row	null	null	null
#|row	null	null	null
#|
#|-- tail_b
#|frame
#|height	9
#|width	3
#|col	str	"statistic"
#|col	f32	"fb"
#|col	f32	"ub"
#|row	"count"	0x40000000	0x40000000
#|row	"null_count"	0x40400000	0x40400000
#|row	"mean"	0x40a00000	0x40a00000
#|row	"std"	0x4087c3b6	0x4087c3b6
#|row	"min"	0x40000000	0x40000000
#|row	"25%"	0x40000000	0x40000000
#|row	"50%"	0x41000000	0x41000000
#|row	"75%"	0x41000000	0x41000000
#|row	"max"	0x41000000	0x41000000
#|frame
#|height	5
#|width	2
#|col	f32	"fb"
#|col	u32	"ub"
#|row	null	2
#|row	0x40000000	null
#|row	null	8
#|row	0x41000000	null
#|row	null	null
#|
#|-- tail_c
#|frame
#|height	9
#|width	2
#|col	str	"statistic"
#|col	f32	"fc"
#|row	"count"	0x3f800000
#|row	"null_count"	0x40400000
#|row	"mean"	0x40400000
#|row	"std"	null
#|row	"min"	0x40400000
#|row	"25%"	0x40400000
#|row	"50%"	0x40400000
#|row	"75%"	0x40400000
#|row	"max"	0x40400000
#|frame
#|height	4
#|width	1
#|col	f32	"fc"
#|row	null
#|row	0x40400000
#|row	null
#|row	null
#|
#|-- pow2_a
#|frame
#|height	9
#|width	2
#|col	str	"statistic"
#|col	f32	"f1"
#|row	"count"	0x3f800000
#|row	"null_count"	0x00000000
#|row	"mean"	0x40200000
#|row	"std"	null
#|row	"min"	0x40200000
#|row	"25%"	0x40200000
#|row	"50%"	0x40200000
#|row	"75%"	0x40200000
#|row	"max"	0x40200000
#|frame
#|height	1
#|width	1
#|col	f32	"f1"
#|row	0x40200000
#|
#|-- pow2_b
#|frame
#|height	9
#|width	2
#|col	str	"statistic"
#|col	f32	"f2"
#|row	"count"	0x40000000
#|row	"null_count"	0x00000000
#|row	"mean"	0x40a00000
#|row	"std"	0x40624630
#|row	"min"	0x40200000
#|row	"25%"	0x40200000
#|row	"50%"	0x40f00000
#|row	"75%"	0x40f00000
#|row	"max"	0x40f00000
#|frame
#|height	2
#|width	1
#|col	f32	"f2"
#|row	0x40200000
#|row	0x40f00000
#|
#|-- pow2_c
#|frame
#|height	9
#|width	2
#|col	str	"statistic"
#|col	f32	"u4"
#|row	"count"	0x40800000
#|row	"null_count"	0x00000000
#|row	"mean"	0x40200000
#|row	"std"	0x3fa53f4e
#|row	"min"	0x3f800000
#|row	"25%"	0x40000000
#|row	"50%"	0x40400000
#|row	"75%"	0x40400000
#|row	"max"	0x40800000
#|frame
#|height	4
#|width	1
#|col	u32	"u4"
#|row	4
#|row	1
#|row	3
#|row	2
#|
#|-- pow2_d
#|frame
#|height	9
#|width	2
#|col	str	"statistic"
#|col	f32	"i8"
#|row	"count"	0x41000000
#|row	"null_count"	0x00000000
#|row	"mean"	0xbf400000
#|row	"std"	0x40aad550
#|row	"min"	0xc1000000
#|row	"25%"	0xc0800000
#|row	"50%"	0x3f800000
#|row	"75%"	0x40000000
#|row	"max"	0x40e00000
#|frame
#|height	8
#|width	1
#|col	i32	"i8"
#|row	-4
#|row	1
#|row	-3
#|row	2
#|row	-8
#|row	7
#|row	-6
#|row	5
#|
