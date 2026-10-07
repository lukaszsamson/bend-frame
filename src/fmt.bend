# src/fmt.bend -- Fmt.show (table printer) and the Fmt.describe stub.
# DESIGN.md 4.12. ASCII only. Idioms: helpers above callers; a match on a
# parameter comes before any destructuring let; list loops thread pairs.
import Base
import ./dtype.bend as D
import ./err.bend as E
import ./column.bend as C

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

# TODO(later milestone): Polars-style describe (count null_count mean std min
# 25% 50% 75% max; needs eval aggregations), DESIGN.md 4.12 and
# bench/golden/q6.csv. A deliberate STUB: an open `law` would make `bend`
# refuse to run every program that imports this file ("1 TODO found"), so it
# is a def that answers an error value until the describe milestone fills it.
def Fmt.describe(f: C.Frame) -> C.Frame & E.ResT(C.Frame):
  (f, Fail{E.InvalidOperation{"Fmt.describe: not implemented yet (TODO)"}})
