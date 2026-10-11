# src/fmt.bend -- Fmt.show (table printer), Fmt.describe and Fmt.fixed.
# DESIGN.md 4.12. ASCII only. Idioms: helpers above callers; a match on a
# parameter comes before any destructuring let; list loops thread pairs.
import Base
import ./dtype.bend as D
import ./err.bend as E
import ./column.bend as C
import ./expr.bend as X
import ./eval.bend as V
import ./kernels.bend as K
import ./sort.bend as O

# a column ready to print: name, dtype text, the DISPLAYED cells (all rows, or
# first 5 + "..." + last 5 of a frame taller than 10 rows) and its width
type FCol is Data:
  FCol{name: String, dty: String, cells: List<&2, String>, w: Nat}

# ---- cells ---------------------------------------------------------------------

# a null prints as an empty cell, strings are not quoted
def Fmt.cell(s: D.Scalar) -> String:
  match s:
    case D.SNull{}:
      ""
    case other:
      D.Scalar.show(other)

def Fmt.cells(xs: List<&2, D.Scalar>) -> List<&2, String>:
  match xs:
    case Nil{}:
      Nil{}
    case h <> t:
      Fmt.cell(h) <> Fmt.cells(t)

# first 5 rows, "...", last 5 rows of a tall column
def Fmt.big.c(hd: List<&2, String>, r: C.Column & List<&2, D.Scalar>) -> C.Column & List<&2, String>:
  (c, tl) = r
  (c, List.append(&2, String, hd, "..." <> Fmt.cells(tl)))

def Fmt.big.b(+h: U32, r: C.Column & List<&2, D.Scalar>) -> C.Column & List<&2, String>:
  (c, hd) = r
  Fmt.big.c(Fmt.cells(hd), C.Column.scalars(c, U32.sub(h, 5), 5))

def Fmt.small.b(r: C.Column & List<&2, D.Scalar>) -> C.Column & List<&2, String>:
  (c, xs) = r
  (c, Fmt.cells(xs))

def Fmt.col_cells.k(big: Bool, +h: U32, c: C.Column) -> C.Column & List<&2, String>:
  match big:
    case True{}:
      Fmt.big.b(h, C.Column.scalars(c, 0, 5))
    case False{}:
      Fmt.small.b(C.Column.scalars(c, 0, h))

def Fmt.col_cells(c: C.Column, +h: U32) -> C.Column & List<&2, String>:
  Fmt.col_cells.k(U32.is_gt(h, 10), h, c)

# ---- widths and padding ---------------------------------------------------------

def Fmt.max_len(xs: List<&2, String>, acc: Nat) -> Nat:
  match xs:
    case Nil{}:
      acc
    case h <> t:
      Fmt.max_len(t, Nat.max(acc, String.length(h)))

# at least 3: the width of the "---" row
def Fmt.width(+name: String, +dty: String, +cells: List<&2, String>) -> Nat:
  Nat.max(3n, Nat.max(String.length(name), Nat.max(String.length(dty), Fmt.max_len(cells, 0n))))

def Fmt.pad(+s: String, +w: Nat) -> String:
  s ++ String.repeat(" ", Nat.sub(w, String.length(s)))

# one table cell: " " + padded + " |"
def Fmt.pads(xs: List<&2, String>, +w: Nat) -> List<&2, String>:
  match xs:
    case Nil{}:
      Nil{}
    case h <> t:
      (" " ++ Fmt.pad(h, w) ++ " |") <> Fmt.pads(t, w)

# ---- frame -> FCol list ------------------------------------------------------------

def Fmt.fcol.b(+name: String, +t: D.DType, r: C.Column & List<&2, String>) -> C.Named & FCol:
  (c, +cells) = r
  (C.Named{name, c}, FCol{name, D.DType.show(t), cells, Fmt.width(name, D.DType.show(t), cells)})

def Fmt.fcol.a(+name: String, +h: U32, r: C.Column & D.DType) -> C.Named & FCol:
  (c, t) = r
  Fmt.fcol.b(name, t, Fmt.col_cells(c, h))

def Fmt.fcol(nc: C.Named, +h: U32) -> C.Named & FCol:
  match nc:
    case C.Named{name, col}:
      Fmt.fcol.a(name, h, C.Column.dtype(col))

def Fmt.fcols.k(r1: C.Named & FCol, r2: List<&1, C.Named> & List<&2, FCol>) -> List<&1, C.Named> & List<&2, FCol>:
  (nc, fc) = r1
  (rest, fcs) = r2
  (nc <> rest, fc <> fcs)

def Fmt.fcols(cols: List<&1, C.Named>, +h: U32) -> List<&1, C.Named> & List<&2, FCol>:
  match cols:
    case Nil{}:
      (Nil{}, Nil{})
    case nc <> rest:
      Fmt.fcols.k(Fmt.fcol(nc, h), Fmt.fcols(rest, h))

# ---- rendering -------------------------------------------------------------------------

# "+" + (ch * (w + 2) + "+") per column
def Fmt.border.go(fcs: List<&2, FCol>, +ch: String) -> String:
  match fcs:
    case Nil{}:
      ""
    case FCol{name, dty, cells, w} <> t:
      String.repeat(ch, Nat.add(w, 2n)) ++ "+" ++ Fmt.border.go(t, ch)

def Fmt.border(fcs: List<&2, FCol>, +ch: String) -> String:
  "+" ++ Fmt.border.go(fcs, ch)

# append column cells to every line (line k gets cell k)
def Fmt.zipcat(lines: List<&2, String>, cells: List<&2, String>) -> List<&2, String>:
  match lines cells:
    case l <> lt c <> ct:
      String.append(l, c) <> Fmt.zipcat(lt, ct)
    case _ _:
      Nil{}

# the three header lines: name, "---", dtype
def Fmt.hdr.go(fcs: List<&2, FCol>, lines: List<&2, String>) -> List<&2, String>:
  match fcs:
    case Nil{}:
      lines
    case FCol{name, dty, cells, w} <> t:
      Fmt.hdr.go(t, Fmt.zipcat(lines, Fmt.pads(name <> "---" <> dty <> Nil{}, w)))

def Fmt.body.go(fcs: List<&2, FCol>, lines: List<&2, String>) -> List<&2, String>:
  match fcs:
    case Nil{}:
      lines
    case FCol{name, dty, cells, w} <> t:
      Fmt.body.go(t, Fmt.zipcat(lines, Fmt.pads(cells, w)))

# displayed body rows (every column has the same count)
def Fmt.nrows(fcs: List<&2, FCol>) -> Nat:
  match fcs:
    case Nil{}:
      0n
    case FCol{name, dty, cells, w} <> t:
      List.length(&2, String, cells)

def Fmt.render.t(shape: String, +top: String, hdr: List<&2, String>, body: List<&2, String>, sep: String) -> String:
  String.join(shape <> top <> List.append(&2, String, hdr, sep <> List.append(&2, String, body, top <> Nil{})), "\n")

def Fmt.render.k(empty: Bool, shape: String, +fcs: List<&2, FCol>) -> String:
  match empty:
    case True{}:
      shape
    case False{}:
      Fmt.render.t(shape, Fmt.border(fcs, "-"), Fmt.hdr.go(fcs, List.replicate(String, 3n, "|")), Fmt.body.go(fcs, List.replicate(String, Fmt.nrows(fcs), "|")), Fmt.border(fcs, "="))

def Fmt.shape(+h: U32, +fcs: List<&2, FCol>) -> String:
  "shape: (" ++ U32.show(h) ++ ", " ++ Nat.show(List.length(&2, FCol, fcs)) ++ ")"

def Fmt.is_nil(fcs: List<&2, FCol>) -> Bool:
  match fcs:
    case Nil{}:
      True{}
    case h <> t:
      False{}

def Fmt.render(+h: U32, +fcs: List<&2, FCol>) -> String:
  Fmt.render.k(Fmt.is_nil(fcs), Fmt.shape(h, fcs), fcs)

def Fmt.show.k(+h: U32, r: List<&1, C.Named> & List<&2, FCol>) -> C.Frame & String:
  (cols, fcs) = r
  (C.Frame{h, cols}, Fmt.render(h, fcs))

# Polars-style ASCII table; a frame of more than 10 rows shows the first 5 and
# the last 5 with a "..." row; a frame without columns prints only its shape.
def Fmt.show(f: C.Frame) -> C.Frame & String:
  match f:
    case C.Frame{+h, cols}:
      Fmt.show.k(h, Fmt.fcols(cols, h))

# ---- Fmt.describe ---------------------------------------------------------------------
# Polars' describe(): a `statistic` Str column (count null_count mean std min 25% 50% 75%
# max) and one column per input column. Numeric (u32 i32 f32) inputs become F32 columns
# (cast to f32, nulls dropped once: count = valid rows, null_count = the rest, mean = the
# DESIGN.md 15.5.3 mean (Neumaier with the non-finite guard, Eval.agg Mean), std = Eval.agg Std
# (15.5.4: sample std, ddof 1, sqrt of the 15.5.3 sum of squared deviations / (count - 1), each
# term an f32; null when count < 2; the kernel DF.std uses),
# min/max = Eval.agg Min/Max (15.5.2: NaN skipped, -0.0 < 0.0 on a tie), the quantiles read from ONE
# stable radix sort of the valid values, by NEAREST rank idx = round(p * (count - 1)), half away
# from zero (Polars describe(interpolation="nearest"), its default, so "50%" is NOT the 15.5.4
# median for an even count: [1,2,3,4] -> 3); all null at count 0).
# Str/Bool inputs become Str columns: count, null_count, min, max as text, null elsewhere.
# The input frame comes back untouched. A numeric column is BORROWED (W1c): a fused cast +
# drop-null loop reads its buffer and hands it back, writing the one dense f32 copy of the valid
# values; the fused sum/min/max pass and the squared-deviation pass borrow that copy and the
# quantile sort consumes it (no Column.clone). A Str / Bool column is cloned (a deep O(n) copy, NOT
# a refcount bump) for Eval.agg Min / Max.

def Fmt.d.sc.c(r: C.Column & D.Scalar) -> D.Scalar:
  (c, s) = r
  s

# row 0 of an aggregation result (null if it failed)
def Fmt.d.sc(r: E.ResT(C.Column)) -> D.Scalar:
  match r:
    case Fail{e}:
      D.SNull{}
    case Done{c}:
      Fmt.d.sc.c(C.Column.cell(c, 0))

def Fmt.d.agg(op: X.AggOp, c: C.Column) -> D.Scalar:
  Fmt.d.sc(V.Eval.agg(op, c))

def Fmt.d.names() -> List<&2, D.Scalar>:
  [D.SStr{"count"}, D.SStr{"null_count"}, D.SStr{"mean"}, D.SStr{"std"}, D.SStr{"min"}, D.SStr{"25%"}, D.SStr{"50%"}, D.SStr{"75%"}, D.SStr{"max"}]

# the sorted rows to read: min, 25%, 50%, 75%, max (k >= 1)
def Fmt.d.idx(+k: U32) -> List<&2, U32>:
  +m = U32.sub(k, 1)
  [0, U32.div(U32.add(m, 2), 4), U32.div(U32.add(m, 1), 2), U32.div(U32.add(U32.mul(3, m), 2), 4), m]

def Fmt.d.cells.put(acc: List<&2, D.Scalar>, r: C.Column & D.Scalar) -> C.Column & List<&2, D.Scalar>:
  (c, s) = r
  (c, s <> acc)

def Fmt.d.cells.step(+i: U32, st: C.Column & List<&2, D.Scalar>) -> C.Column & List<&2, D.Scalar>:
  (c, acc) = st
  Fmt.d.cells.put(acc, C.Column.cell(c, i))

def Fmt.d.cells(idxs: List<&2, U32>, st: C.Column & List<&2, D.Scalar>) -> C.Column & List<&2, D.Scalar>:
  match idxs:
    case Nil{}:
      st
    case +i <> t:
      Fmt.d.cells(t, Fmt.d.cells.step(i, st))

def Fmt.d.cells.fin(r: C.Column & List<&2, D.Scalar>) -> List<&2, D.Scalar>:
  (c, acc) = r
  List.reverse(&2, D.Scalar, acc)

def Fmt.d.sorted.a(+k: U32, r: E.ResT(C.Frame)) -> List<&2, D.Scalar>:
  match r:
    case Fail{e}:
      Nil{}
    case Done{C.Frame{h, C.Named{nm, c} <> Nil{}}}:
      Fmt.d.cells.fin(Fmt.d.cells(Fmt.d.idx(k), (c, Nil{})))
    case other:
      Nil{}

# [min, 25%, 50%, 75%, max] of the dense valid values (consumed)
def Fmt.d.sorted(+k: U32, d: C.Column) -> List<&2, D.Scalar>:
  Fmt.d.sorted.a(k, O.Sort.frame(C.Frame{k, C.Named{"x", d} <> Nil{}}, O.SortKey{"x", False{}, False{}} <> Nil{}))

# qs = [min, 25%, 50%, 75%, max] read off the sort: only its three quantiles are used; min and max
# come from Eval.agg Min/Max (K.Kernel.fmin/fmax: NaN skipped, -0.0 < 0.0 on ties, 15.5.2)
def Fmt.d.assemble(+k: U32, +nn: U32, mean: D.Scalar, std: D.Scalar, mn: D.Scalar, mx: D.Scalar, qs: List<&2, D.Scalar>) -> List<&2, D.Scalar>:
  match qs:
    case lo <> q1 <> q2 <> q3 <> hi <> Nil{}:
      [D.SF32{U32.to_f32(k)}, D.SF32{U32.to_f32(nn)}, mean, std, mn, q1, q2, q3, mx]
    case other:
      Nil{}

def Fmt.d.num.d(+k: U32, +nn: U32, mean: D.Scalar, std: D.Scalar, mn: D.Scalar, mx: D.Scalar, qs: List<&2, D.Scalar>) -> E.ResT(C.Column):
  C.Column.from_scalars(Fmt.d.assemble(k, nn, mean, std, mn, mx, qs), D.TF32{})

def Fmt.d.num.g(+k: U32, +nn: U32, mean: D.Scalar, std: D.Scalar, mn: D.Scalar, mx: D.Scalar, d: C.Column) -> E.ResT(C.Column):
  Fmt.d.num.d(k, nn, mean, std, mn, mx, Fmt.d.sorted(k, d))

# ---- the numeric path (W1c) ----------------------------------------------------------
# One column is BORROWED: a fused cast + drop-null loop reads its buffer (and mask) and hands
# them back, writing ONE dense f32 array of the valid values (the only O(n) allocation here);
# that array goes through the fused count/sum/min/max loop, the squared-deviation loop and is
# finally consumed by the quantile sort. No Column.clone, no separate dropnull / cast / clones.

def Fmt.d.num.nulls(+nn: U32) -> E.ResT(C.Column):
  C.Column.from_scalars([D.SF32{0.0}, D.SF32{U32.to_f32(nn)}, D.SNull{}, D.SNull{}, D.SNull{}, D.SNull{}, D.SNull{}, D.SNull{}, D.SNull{}], D.TF32{})

# the dense valid values: y holds k f32 values in a 2^d array
type DV is Type:
  DV{y: Array<F32>, k: U32, d: Nat}

# the fused first pass: the 15.5.3 Neumaier state (s, c) and the 15.5.2 min / max in one loop
type DS is Data:
  DS{s: F32, c: F32, mn: F32, mx: F32}

def Fmt.d.ds.k(r: K.NS, +mn: F32, +mx: F32) -> DS:
  match r:
    case K.NS{s, c}:
      DS{s, c, mn, mx}

def Fmt.d.ds.step(acc: DS, +x: F32) -> DS:
  match acc:
    case DS{+s, +c, +mn, +mx}:
      Fmt.d.ds.k(K.Kernel.nm.add(s, c, x), K.Kernel.fmin(mn, x), K.Kernel.fmax(mx, x))

# out[i] = cv(a[i]) for i < n (no nulls); a comes back with out
def Fmt.d.cv.go(~T: Data, ~cv: T -> F32, n: Nat, +i: U32, out: Array<F32>, r: Array<T> & T) -> Array<T> & Array<F32>:
  match n:
    case 0n:
      (a, x) = r
      (a, out)
    case 1n+p:
      (a, x) = r
      +j = U32.inc(i)
      Fmt.d.cv.go(~T, ~cv, p, j, Array.set(F32, out, i, cv(x)), Array.get(T, a, j))

# out[k] = cv(a[i]), k += mask[i] (Kernel.compact with the cast fused in); a and the mask come back
def Fmt.d.cm.go(~T: Data, ~cv: T -> F32, n: Nat, +i: U32, +k: U32, out: Array<F32>, rx: Array<T> & T, rm: Array<U32> & U32) -> (Array<T> & Array<U32>) & Array<F32>:
  match n:
    case 0n:
      (a, x) = rx
      (m, b) = rm
      ((a, m), out)
    case 1n+p:
      (a, x) = rx
      (m, b) = rm
      +j = U32.inc(i)
      Fmt.d.cm.go(~T, ~cv, p, j, U32.add(k, b), Array.set(F32, out, k, cv(x)), Array.get(T, a, j), Array.get(U32, m, j))

def Fmt.d.den.a.k(~T: Data, +n: U32, +d: Nat, r: Array<T> & Array<F32>) -> (Array<T> & C.Valid) & DV:
  (x, y) = r
  ((x, C.AllValid{}), DV{y, n, d})

def Fmt.d.den.a(~T: Data, ~cv: T -> F32, +n: U32, x: Array<T>) -> (Array<T> & C.Valid) & DV:
  +d = K.Kernel.depth_for(n)
  Fmt.d.den.a.k(~T, n, d, Fmt.d.cv.go(~T, ~cv, U32.to_nat(n), 0, Array.new(F32, d, 0.0), Array.get(T, x, 0)))

def Fmt.d.den.m.x(~T: Data, +k: U32, +d: Nat, y: Array<F32>, xm: Array<T> & Array<U32>) -> (Array<T> & C.Valid) & DV:
  (x, m) = xm
  ((x, C.Mask{m}), DV{y, k, d})

def Fmt.d.den.m.k(~T: Data, +k: U32, +d: Nat, r: (Array<T> & Array<U32>) & Array<F32>) -> (Array<T> & C.Valid) & DV:
  (xm, y) = r
  Fmt.d.den.m.x(~T, k, d, y, xm)

# kept + 1 slots, as Column.compact: a dropped row after the last kept one writes slot `kept`
def Fmt.d.den.m(~T: Data, ~cv: T -> F32, +n: U32, x: Array<T>, r: Array<U32> & U32) -> (Array<T> & C.Valid) & DV:
  (m, +k) = r
  +d = K.Kernel.depth_for(U32.add(k, 1))
  Fmt.d.den.m.k(~T, k, d, Fmt.d.cm.go(~T, ~cv, U32.to_nat(n), 0, 0, Array.new(F32, d, 0.0), Array.get(T, x, 0), Array.get(U32, m, 0)))

# the valid values of x (validity v, n rows) as f32 through cv; x and v come back
def Fmt.d.den(~T: Data, ~cv: T -> F32, +n: U32, v: C.Valid, x: Array<T>) -> (Array<T> & C.Valid) & DV:
  match v:
    case C.AllValid{}:
      Fmt.d.den.a(~T, ~cv, n, x)
    case C.Mask{m}:
      Fmt.d.den.m(~T, ~cv, n, x, K.Kernel.popcount(n, m))

# the squared-deviation pass (15.5.3 / 15.5.4, ascending order); y comes back with the sum
def Fmt.d.ssd.k(r: Array<F32> & V.VS) -> Array<F32> & F32:
  (y, vs) = r
  (y, V.Eval.vs.fin(vs))

def Fmt.d.ssd(+k: U32, +m: F32, y: Array<F32>) -> Array<F32> & F32:
  Fmt.d.ssd.k(K.Kernel.fold(~F32, ~V.VS, ~(a => w => V.Eval.vs.step(a, w)), k, y, V.VS{m, 0.0, 0.0}))

# the quantile sort consumes the dense values
def Fmt.d.srt(+k: U32, +nn: U32, +d: Nat, mean: D.Scalar, std: D.Scalar, mn: D.Scalar, mx: D.Scalar, y: Array<F32>) -> E.ResT(C.Column):
  Fmt.d.num.g(k, nn, mean, std, mn, mx, C.CF32{k, d, C.AllValid{}, y})

def Fmt.d.std.k(+k: U32, +nn: U32, +d: Nat, mean: D.Scalar, mn: D.Scalar, mx: D.Scalar, r: Array<F32> & F32) -> E.ResT(C.Column):
  (y, ssd) = r
  Fmt.d.srt(k, nn, d, mean, V.Eval.stat.s(True{}, k, ssd), mn, mx, y)

# std: null when k < 2 (no pass), else the squared-deviation pass around the mean
def Fmt.d.std(small: Bool, +k: U32, +nn: U32, +d: Nat, +m: F32, mn: D.Scalar, mx: D.Scalar, y: Array<F32>) -> E.ResT(C.Column):
  match small:
    case True{}:
      Fmt.d.srt(k, nn, d, D.SF32{m}, D.SNull{}, mn, mx, y)
    case False{}:
      Fmt.d.std.k(k, nn, d, D.SF32{m}, mn, mx, Fmt.d.ssd(k, m, y))

def Fmt.d.p1.s(+k: U32, +nn: U32, +d: Nat, s: F32, c: F32, mn: F32, mx: F32, y: Array<F32>) -> E.ResT(C.Column):
  Fmt.d.std(U32.is_lt(k, 2), k, nn, d, V.Eval.mean_f(k, K.Kernel.nm.result(s, c)), D.SF32{mn}, D.SF32{mx}, y)

def Fmt.d.p1.a(+k: U32, +nn: U32, +d: Nat, r: Array<F32> & DS) -> E.ResT(C.Column):
  (y, ds) = r
  match ds:
    case DS{+s, +c, +mn, +mx}:
      Fmt.d.p1.s(k, nn, d, s, c, mn, mx, y)

def Fmt.d.p1.b(+k: U32, +nn: U32, +d: Nat, r: Array<F32> & F32) -> E.ResT(C.Column):
  (y, +x0) = r
  Fmt.d.p1.a(k, nn, d, K.Kernel.fold(~F32, ~DS, ~(a => w => Fmt.d.ds.step(a, w)), k, y, DS{0.0, 0.0, x0, x0}))

# k valid rows (k >= 1), nn nulls: the fused sum / min / max pass seeded with y[0]
def Fmt.d.p1(+k: U32, +nn: U32, +d: Nat, y: Array<F32>) -> E.ResT(C.Column):
  Fmt.d.p1.b(k, nn, d, Array.get(F32, y, 0))

def Fmt.d.res.z(none: Bool, +n: U32, +k: U32, +d: Nat, y: Array<F32>) -> E.ResT(C.Column):
  match none:
    case True{}:
      Fmt.d.num.nulls(n)
    case False{}:
      Fmt.d.p1(k, U32.sub(n, k), d, y)

def Fmt.d.res(+n: U32, dv: DV) -> E.ResT(C.Column):
  match dv:
    case DV{y, +k, +d}:
      Fmt.d.res.z(U32.is_zero(k), n, k, d, y)

# the column comes back as it went in, with its statistics column
def Fmt.d.nw.f(+n: U32, +d: Nat, xv: Array<F32> & C.Valid, res: E.ResT(C.Column)) -> C.Column & E.ResT(C.Column):
  (x, v) = xv
  (C.CF32{n, d, v, x}, res)

def Fmt.d.nw.w(+t: D.DType, +n: U32, +d: Nat, xv: Array<U32> & C.Valid, res: E.ResT(C.Column)) -> C.Column & E.ResT(C.Column):
  (x, v) = xv
  (C.Column.mk_w(t, n, d, v, x), res)

def Fmt.d.nk.f(+n: U32, +d: Nat, r: (Array<F32> & C.Valid) & DV) -> C.Column & E.ResT(C.Column):
  (xv, dv) = r
  Fmt.d.nw.f(n, d, xv, Fmt.d.res(n, dv))

def Fmt.d.nk.w(+t: D.DType, +n: U32, +d: Nat, r: (Array<U32> & C.Valid) & DV) -> C.Column & E.ResT(C.Column):
  (xv, dv) = r
  Fmt.d.nw.w(t, n, d, xv, Fmt.d.res(n, dv))

# u32 / i32 / f32 columns (to f32 as Eval.cast: U32.to_f32, D.I32.to_f32, the identity)
def Fmt.d.num(c: C.Column) -> C.Column & E.ResT(C.Column):
  match c:
    case C.CU32{+n, +d, v, x}:
      Fmt.d.nk.w(D.TU32{}, n, d, Fmt.d.den(~U32, ~(w => U32.to_f32(w)), n, v, x))
    case C.CI32{+n, +d, v, x}:
      Fmt.d.nk.w(D.TI32{}, n, d, Fmt.d.den(~U32, ~(w => D.I32.to_f32(D.I32{w})), n, v, x))
    case C.CF32{+n, +d, v, x}:
      Fmt.d.nk.f(n, d, Fmt.d.den(~F32, ~(w => w), n, v, x))
    case other:
      (other, Fail{E.InvalidOperation{"describe: unexpected column"}})

# Str / Bool columns
def Fmt.d.txt.s(s: D.Scalar) -> D.Scalar:
  match s:
    case D.SNull{}:
      D.SNull{}
    case other:
      D.SStr{D.Scalar.show(other)}

def Fmt.d.txt.c(+n: U32, +nulls: U32, mn: D.Scalar, mx: D.Scalar) -> E.ResT(C.Column):
  C.Column.from_scalars([D.SStr{U32.show(U32.sub(n, nulls))}, D.SStr{U32.show(nulls)}, D.SNull{}, D.SNull{}, Fmt.d.txt.s(mn), D.SNull{}, D.SNull{}, D.SNull{}, Fmt.d.txt.s(mx)], D.TStr{})

def Fmt.d.txt.m(+n: U32, +nulls: U32, r: C.Column & C.Column) -> E.ResT(C.Column):
  (c1, c2) = r
  Fmt.d.txt.c(n, nulls, Fmt.d.agg(X.Min{}, c1), Fmt.d.agg(X.Max{}, c2))

def Fmt.d.txt.a(+n: U32, r: C.Column & U32) -> E.ResT(C.Column):
  (c, +nulls) = r
  Fmt.d.txt.m(n, nulls, C.Column.clone(c))

def Fmt.d.txt.n(r: C.Column & U32) -> E.ResT(C.Column):
  (c, +n) = r
  Fmt.d.txt.a(n, C.Column.null_count(c))

def Fmt.d.col.x(r: C.Column & C.Column) -> C.Column & E.ResT(C.Column):
  (c, c2) = r
  (c, Fmt.d.txt.n(C.Column.len(c2)))

def Fmt.d.col.t(r: C.Column & D.DType) -> C.Column & E.ResT(C.Column):
  (c, t) = r
  match t:
    case D.TStr{}:
      Fmt.d.col.x(C.Column.clone(c))
    case D.TBool{}:
      Fmt.d.col.x(C.Column.clone(c))
    case other:
      Fmt.d.num(c)

# the statistics of one column; the column comes back (numeric ones are borrowed, not cloned)
def Fmt.d.col(c: C.Column) -> C.Column & E.ResT(C.Column):
  Fmt.d.col.t(C.Column.dtype(c))

def Fmt.d.push(r: E.ResT(List<&1, C.Named>), nm: String, col: E.ResT(C.Column)) -> E.ResT(List<&1, C.Named>):
  match r col:
    case Fail{e} _:
      Fail{e}
    case Done{xs} Fail{e}:
      Fail{e}
    case Done{xs} Done{c}:
      Done{C.Named{nm, c} <> xs}

def Fmt.d.step.k(+nm: String, st: List<&1, C.Named> & E.ResT(List<&1, C.Named>), r: C.Column & E.ResT(C.Column)) -> List<&1, C.Named> & E.ResT(List<&1, C.Named>):
  (kept, out) = st
  (c, res) = r
  (C.Named{nm, c} <> kept, Fmt.d.push(out, nm, res))

def Fmt.d.step(nc: C.Named, st: List<&1, C.Named> & E.ResT(List<&1, C.Named>)) -> List<&1, C.Named> & E.ResT(List<&1, C.Named>):
  match nc:
    case C.Named{nm, c}:
      Fmt.d.step.k(nm, st, Fmt.d.col(c))

def Fmt.d.go(cols: List<&1, C.Named>, st: List<&1, C.Named> & E.ResT(List<&1, C.Named>)) -> List<&1, C.Named> & E.ResT(List<&1, C.Named>):
  match cols:
    case Nil{}:
      st
    case nc <> t:
      Fmt.d.go(t, Fmt.d.step(nc, st))

def Fmt.d.build.k(r: E.ResT(C.Column), xs: List<&1, C.Named>) -> E.ResT(C.Frame):
  match r:
    case Fail{e}:
      Fail{e}
    case Done{s}:
      C.Frame.from_columns(C.Named{"statistic", s} <> List.reverse(&1, C.Named, xs))

def Fmt.d.build(out: E.ResT(List<&1, C.Named>)) -> E.ResT(C.Frame):
  match out:
    case Fail{e}:
      Fail{e}
    case Done{xs}:
      Fmt.d.build.k(C.Column.from_scalars(Fmt.d.names(), D.TStr{}), xs)

def Fmt.d.fin(+h: U32, r: List<&1, C.Named> & E.ResT(List<&1, C.Named>)) -> C.Frame & E.ResT(C.Frame):
  (kept, out) = r
  (C.Frame{h, List.reverse(&1, C.Named, kept)}, Fmt.d.build(out))

# ---- the columns in a balanced fork (v0.2 T5.4, DESIGN.md 16.4 D4) -----------------------------------
# Each column's statistics are independent (a column is taken out of the list by its lane and handed
# back; every pass of one column stays sequential, so the F32 sums keep their single in-order pass).
# A lane returns its column and its result; the results are then folded in column order, so the
# first failing column wins exactly as in Fmt.d.go. Small frames (under Fmt.fork_rows() rows) and
# single-column frames take the sequential walk.

# rows from which the columns fork: measured at 1M, 128k, 64k, 32k and 16k rows (bench/w5/t54.bend k = 10,
# 44, 43, 42, 41): 55 -> 29, 7 -> 4, 4 -> 2 ms at 12 threads, and no change at 32k (2 ms) and 16k (1 ms),
# where a lane is under ~0.5 ms and the fork only costs its wake-up; one thread is unchanged everywhere
def Fmt.fork_rows() -> U32:
  65536

type DJ is Type:
  DJ{kept: C.Named, nm: String, res: E.ResT(C.Column)}

def Fmt.d.job.k(+nm: String, r: C.Column & E.ResT(C.Column)) -> DJ:
  (c, res) = r
  DJ{C.Named{nm, c}, nm, res}

def Fmt.d.job(+u: U32, nc: C.Named) -> DJ:
  match nc:
    case C.Named{nm, c}:
      Fmt.d.job.k(nm, Fmt.d.col(c))

def Fmt.d.fold.k(kept: C.Named, nm: String, res: E.ResT(C.Column), st: List<&1, C.Named> & E.ResT(List<&1, C.Named>)) -> List<&1, C.Named> & E.ResT(List<&1, C.Named>):
  (k0, out) = st
  (kept <> k0, Fmt.d.push(out, nm, res))

def Fmt.d.fold(js: List<&1, DJ>, st: List<&1, C.Named> & E.ResT(List<&1, C.Named>)) -> List<&1, C.Named> & E.ResT(List<&1, C.Named>):
  match js:
    case Nil{}:
      st
    case DJ{kept, nm, res} <> t:
      Fmt.d.fold(t, Fmt.d.fold.k(kept, nm, res, st))

def Fmt.d.run(big: Bool, cols: List<&1, C.Named>) -> List<&1, C.Named> & E.ResT(List<&1, C.Named>):
  match big:
    case True{}:
      Fmt.d.fold(O.Sort.pm(~C.Named, ~DJ, ~U32, ~(u => nc => Fmt.d.job(u, nc)), 0, cols), (Nil{}, Done{Nil{}}))
    case False{}:
      Fmt.d.go(cols, (Nil{}, Done{Nil{}}))

def Fmt.describe(f: C.Frame) -> C.Frame & E.ResT(C.Frame):
  match f:
    case C.Frame{+h, cols}:
      Fmt.d.fin(h, Fmt.d.run(U32.is_le(Fmt.fork_rows(), h), cols))

# ---- Fmt.fixed: F32 with a fixed number of decimals ---------------------------------
# Exact: matches Python/Rust `{x:.Np}` on the f32 value (decimal expansion of the
# binary value, round half to even on exact ties). An f32 is M * 2^e with a 24-bit M;
# the fractional part is M' / 2^s (s <= 149), held as seven 24-bit limbs (LSB first)
# and multiplied by 10 digit by digit; values >= 2^23 are integers, expanded exactly
# in base 10^7 by repeated doubling.
# Precision is capped at 9 decimals.

# the fraction after a multiply by 10: limbs (LSB first) and the digit that fell out
type Fm is Data:
  Fm{ls: List<&2, U32>, carry: U32}

# p digits read as a number, the remaining fraction, and the NEXT digit (for rounding)
type Fx is Data:
  Fx{ls: List<&2, U32>, acc: U32, d: U32}

# integer part and fraction digits after rounding
type Ip is Data:
  Ip{i: U32, f: U32}

def Fmt.fx.nz(ls: List<&2, U32>, acc: Bool) -> Bool:
  match ls:
    case Nil{}:
      acc
    case h <> tl:
      Fmt.fx.nz(tl, Bool.or(acc, Bool.not(U32.is_zero(h))))

def Fmt.fx.m10.k(low: U32, r: Fm) -> Fm:
  match r:
    case Fm{ls, carry}:
      Fm{low <> ls, carry}

# multiply the LSB-first limb list by 10, carrying upward
def Fmt.fx.m10(ls: List<&2, U32>, +c: U32) -> Fm:
  match ls:
    case Nil{}:
      Fm{Nil{}, c}
    case h <> tl:
      +v = U32.add(U32.mul(h, 10), c)
      Fmt.fx.m10.k(U32.and(v, 16777215), Fmt.fx.m10(tl, U32.shrn(v, 24n)))

# k more digits; `r` is the multiply just done (its carry is the next digit to take)
def Fmt.fx.dig(k: Nat, acc: U32, r: Fm) -> Fx:
  match k:
    case 0n:
      match r:
        case Fm{ls, c}:
          Fx{ls, acc, c}
    case 1n+p:
      match r:
        case Fm{ls, +c}:
          Fmt.fx.dig(p, U32.add(U32.mul(acc, 10), c), Fmt.fx.m10(ls, 0))

def Fmt.fx.limb(+j: U32, +q: U32, +lo: U32, +hi: U32) -> U32:
  Bool.pick(U32, U32.is_eq(j, q), lo, Bool.pick(U32, U32.is_eq(j, U32.add(q, 1)), hi, 0))

# N * 2^(168-s) as 7 limbs of 24 bits, LSB first (N < 2^s, N < 2^24, 1 <= s <= 149)
def Fmt.fx.limbs(+q: U32, +lo: U32, +hi: U32) -> List<&2, U32>:
  Fmt.fx.limb(0, q, lo, hi) <> Fmt.fx.limb(1, q, lo, hi) <> Fmt.fx.limb(2, q, lo, hi) <> Fmt.fx.limb(3, q, lo, hi) <> Fmt.fx.limb(4, q, lo, hi) <> Fmt.fx.limb(5, q, lo, hi) <> Fmt.fx.limb(6, q, lo, hi) <> Nil{}

def Fmt.fx.limbs.r(+n: U32, +q: U32, +r: U32) -> List<&2, U32>:
  Fmt.fx.limbs(q, U32.and(U32.shln(n, U32.to_nat(r)), 16777215), U32.shrn(n, U32.to_nat(U32.sub(24, r))))

def Fmt.fx.limbs.t(+n: U32, +t: U32) -> List<&2, U32>:
  Fmt.fx.limbs.r(n, U32.div(t, 24), U32.mod(t, 24))

# round up? next digit d, nonzero remainder, odd last digit (half to even)
def Fmt.fx.up(+d: U32, nz: Bool, odd: Bool) -> Bool:
  Bool.or(U32.is_gt(d, 5), Bool.and(U32.is_eq(d, 5), Bool.or(nz, odd)))

def Fmt.fx.bump.k(+i: U32, +f1: U32, +p10: U32) -> Ip:
  Ip{U32.add(i, Bool.to_u32(U32.is_eq(f1, p10))), Bool.pick(U32, U32.is_eq(f1, p10), 0, f1)}

def Fmt.fx.bump(i: U32, +f: U32, p10: U32, up: Bool) -> Ip:
  Fmt.fx.bump.k(i, U32.add(f, Bool.to_u32(up)), p10)

# the last printed digit decides ties: the integer part's when there are no decimals
def Fmt.fx.round(+i: U32, +p: U32, dg: Fx) -> Ip:
  match dg:
    case Fx{ls, +acc, +d}:
      Fmt.fx.bump(i, acc, U32.pow(10, U32.to_nat(p)), Fmt.fx.up(d, Fmt.fx.nz(ls, False{}), Bool.pick(Bool, U32.is_eq(p, 0), Bool.not(U32.is_even(i)), Bool.not(U32.is_even(acc)))))

# `i` is the integer part, `n`/`s` the fraction n / 2^s
def Fmt.fx.frac(+i: U32, +n: U32, +s: U32, +p: U32) -> Ip:
  Fmt.fx.round(i, p, Fmt.fx.dig(U32.to_nat(p), 0, Fmt.fx.m10(Fmt.fx.limbs.t(n, U32.sub(168, s)), 0)))

def Fmt.fx.pad(f: U32, +p: U32) -> String:
  +s = U32.show(f)
  String.repeat("0", Nat.sub(U32.to_nat(p), String.length(s))) ++ s

def Fmt.fx.fpart(f: U32, +p: U32) -> String:
  Bool.pick(String, U32.is_eq(p, 0), "", "." ++ Fmt.fx.pad(f, p))

def Fmt.fx.out(neg: Bool, +p: U32, r: Ip) -> String:
  match r:
    case Ip{i, f}:
      Bool.pick(String, neg, "-", "") ++ U32.show(i) ++ Fmt.fx.fpart(f, p)

# value = m / 2^s, s in 1..149: integer part m >> s, fraction (m mod 2^s) / 2^s
def Fmt.fx.small(neg: Bool, +m: U32, +s: U32, +p: U32) -> String:
  +sc = U32.min(s, 31)
  Fmt.fx.out(neg, p, Fmt.fx.frac(U32.shrn(m, U32.to_nat(sc)), U32.and(m, U32.sub(U32.shln(1, U32.to_nat(sc)), 1)), s, p))

# base 10^7 limbs (LSB first) times k (k <= 256), carry c < 256
def Fmt.fx.mulb(ls: List<&2, U32>, +c: U32, +k: U32) -> List<&2, U32>:
  match ls:
    case Nil{}:
      Bool.pick(List<&2, U32>, U32.is_zero(c), Nil{}, c <> Nil{})
    case h <> tl:
      +v = U32.add(U32.mul(h, k), c)
      U32.mod(v, 10000000) <> Fmt.fx.mulb(tl, U32.div(v, 10000000), k)

def Fmt.fx.shl8(k: Nat, ls: List<&2, U32>) -> List<&2, U32>:
  match k:
    case 0n:
      ls
    case 1n+p:
      Fmt.fx.shl8(p, Fmt.fx.mulb(ls, 0, 256))

# m * 2^sh in base 10^7, LSB first
def Fmt.fx.shl(+m: U32, +sh: U32) -> List<&2, U32>:
  Fmt.fx.mulb(Fmt.fx.shl8(U32.to_nat(U32.div(sh, 8)), Fmt.fx.mulb(m <> Nil{}, 0, 1)), 0, U32.shln(1, U32.to_nat(U32.mod(sh, 8))))

def Fmt.fx.dec.rest(ls: List<&2, U32>) -> String:
  match ls:
    case Nil{}:
      ""
    case h <> tl:
      Fmt.fx.pad(h, 7) ++ Fmt.fx.dec.rest(tl)

# most significant limb first
def Fmt.fx.dec(ls: List<&2, U32>) -> String:
  match ls:
    case Nil{}:
      "0"
    case h <> tl:
      U32.show(h) ++ Fmt.fx.dec.rest(tl)

# value = m * 2^sh, sh >= 0: an exact integer (decimal expansion by repeated doubling)
def Fmt.fx.large(neg: Bool, +m: U32, +sh: U32, +p: U32) -> String:
  Bool.pick(String, neg, "-", "") ++ Fmt.fx.dec(List.reverse(&2, U32, Fmt.fx.shl(m, sh))) ++ Fmt.fx.fpart(0, p)

# e: biased exponent field (1..254), value = m * 2^(e - 150)
def Fmt.fx.finite(lt: Bool, neg: Bool, +m: U32, +e: U32, +p: U32) -> String:
  match lt:
    case True{}:
      Fmt.fx.small(neg, m, U32.sub(150, e), p)
    case False{}:
      Fmt.fx.large(neg, m, U32.sub(e, 150), p)

def Fmt.fx.num.k(special: Bool, +x: F32, neg: Bool, +m: U32, +e: U32, +p: U32) -> String:
  match special:
    case True{}:
      F32.show(x)
    case False{}:
      Fmt.fx.finite(U32.is_lt(e, 150), neg, m, e, p)

def Fmt.fx.num(+bits: U32, x: F32, +p: U32) -> String:
  +e = U32.and(U32.shrn(bits, 23n), 255)
  +man = U32.and(bits, 8388607)
  Fmt.fx.num.k(U32.is_eq(e, 255), x, U32.is_ne(U32.shrn(bits, 31n), 0), Bool.pick(U32, U32.is_eq(e, 0), man, U32.or(man, 8388608)), U32.max(e, 1), p)

# x with `prec` decimals (at most 9), as Python's f"{x:.{prec}f}" prints the f32 value
def Fmt.fixed(+x: F32, prec: U32) -> String:
  Fmt.fx.num(F32.bits(x), x, U32.min(prec, 9))
