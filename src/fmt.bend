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
