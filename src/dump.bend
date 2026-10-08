# src/dump.bend -- the typed oracle: DF.dump (plan M_01 T1, DESIGN.md 15.1).
#
# A deterministic, line-oriented text form of a Frame (or of the error a
# ResT(Frame) holds) that tests compare byte for byte. Unlike Fmt.show it loses
# nothing: dtype, column order, height, validity, F32 bit patterns, the empty
# string vs null, a zero-column frame's height.
#
# Grammar (DESIGN.md 15.1; lines end in "\n", fields are TAB separated):
#
#   frame
#   height <TAB> <H>
#   width <TAB> <W>
#   col <TAB> <dtype> <TAB> "<name>"        one per column, in order
#   row (<TAB> <cell>){W}                   one per row (none when W = 0)
#
#   error <TAB> <E.Err.show text>           for a Fail result
#
# Cells: null | true | false | <u32 decimal> | <i32 decimal, "-" if negative>
#        | 0x<8 lowercase hex digits> (f32 bits, every NaN as 0x7fc00000)
#        | "<escaped string>".
# Escapes: \" \\ \n \r \t, \xHH for the other C0 controls and U+007F; every
# other code point is written as is.
#
# Idioms: helpers above callers; match on parameters; `+` on a second use.
import Base
import ./dtype.bend as D
import ./err.bend as E
import ./column.bend as C

# ---- hex --------------------------------------------------------------------

def Dump.digit.k(lt: Bool, +d: U32) -> Char:
  match lt:
    case True{}:
      Chr{U32.add(48, d)}
    case False{}:
      Chr{U32.add(87, d)}

def Dump.digit(+d: U32) -> Char:
  Dump.digit.k(U32.is_lt(d, 10), d)

# the low n hex digits of x, high digit first
def Dump.hex(n: Nat, +x: U32) -> String:
  match n:
    case 0n:
      SNil{}
    case 1n+p:
      Dump.hex(p, U32.shrn(x, 4n)) ++ SCon{Dump.digit(U32.and(x, 15)), SNil{}}

# ---- strings ----------------------------------------------------------------

def Dump.chr(c: U32) -> String:
  SCon{Chr{c}, SNil{}}

def Dump.esc.ctl(ctl: Bool, +c: U32) -> String:
  match ctl:
    case True{}:
      "\\x" ++ Dump.hex(2n, c)
    case False{}:
      Dump.chr(c)

def Dump.esc.tab(q: Bool, +c: U32) -> String:
  match q:
    case True{}:
      "\\t"
    case False{}:
      Dump.esc.ctl(Bool.or(U32.is_lt(c, 32), U32.is_eq(c, 127)), c)

def Dump.esc.cr(q: Bool, +c: U32) -> String:
  match q:
    case True{}:
      "\\r"
    case False{}:
      Dump.esc.tab(U32.is_eq(c, 9), c)

def Dump.esc.nl(q: Bool, +c: U32) -> String:
  match q:
    case True{}:
      "\\n"
    case False{}:
      Dump.esc.cr(U32.is_eq(c, 13), c)

def Dump.esc.bs(q: Bool, +c: U32) -> String:
  match q:
    case True{}:
      "\\\\"
    case False{}:
      Dump.esc.nl(U32.is_eq(c, 10), c)

def Dump.esc.q(q: Bool, +c: U32) -> String:
  match q:
    case True{}:
      "\\\""
    case False{}:
      Dump.esc.bs(U32.is_eq(c, 92), c)

# the char c followed by the escaped rest
def Dump.esc.c(+c: U32, rest: String) -> String:
  Dump.esc.q(U32.is_eq(c, 34), c) ++ rest

def Dump.esc(s: String) -> String:
  match s:
    case SNil{}:
      SNil{}
    case SCon{Chr{c}, t}:
      Dump.esc.c(c, Dump.esc(t))

def Dump.quote(s: String) -> String:
  "\"" ++ Dump.esc(s) ++ "\""

# ---- cells ------------------------------------------------------------------

# the bits printed for an f32 cell: every NaN (any sign, any payload) prints as the quiet
# NaN 0x7fc00000, because NaN bits are not portable (arm64 makes 0x7fc00000 where x86-64
# makes 0xffc00000 for `inf - inf`, and payloads propagate); DESIGN.md 14 (B03 NaN dump)
def Dump.fbits.b(+b: U32) -> U32:
  Bool.pick(U32, U32.is_gt(U32.and(b, 2147483647), 2139095040), 2143289344, b)

def Dump.fbits(x: F32) -> U32:
  Dump.fbits.b(F32.bits(x))

def Dump.cell(s: D.Scalar) -> String:
  match s:
    case D.SNull{}:
      "null"
    case D.SBool{b}:
      D.Scalar.show(D.SBool{b})
    case D.SU32{v}:
      U32.show(v)
    case D.SI32{v}:
      D.Scalar.show(D.SI32{v})
    case D.SF32{x}:
      "0x" ++ Dump.hex(8n, Dump.fbits(x))

    case D.SStr{t}:
      Dump.quote(t)

# the cell texts in reverse order (tail recursive: the interpreter's JS lane overflows the
# host stack on a non-tail recursion ~2^15 deep, cons-guarded or not)
def Dump.cell_rev(xs: List<&2, D.Scalar>, acc: List<&2, String>) -> List<&2, String>:
  match xs:
    case Nil{}:
      acc
    case h <> t:
      Dump.cell_rev(t, Dump.cell(h) <> acc)

def Dump.cell_list(xs: List<&2, D.Scalar>) -> List<&2, String>:
  List.reverse(&2, String, Dump.cell_rev(xs, Nil{}))

# ---- columns ------------------------------------------------------------------

# the dtype name and the cell texts; the column comes back
def Dump.col.b(+t: D.DType, r: C.Column & List<&2, D.Scalar>) -> C.Column & (String & List<&2, String>):
  (c, xs) = r
  (c, (D.DType.show(t), Dump.cell_list(xs)))

def Dump.col.a(r: C.Column & D.DType) -> C.Column & (String & List<&2, String>):
  (c, +t) = r
  Dump.col.b(t, C.Column.to_scalars(c))

def Dump.col(c: C.Column) -> C.Column & (String & List<&2, String>):
  Dump.col.a(C.Column.dtype(c))

# the "col" lines, and the cell texts of each column (columns outermost)
def Dump.cols.k(+n: String, r: C.Column & (String & List<&2, String>), rest: List<&1, C.Named> & (String & List<&2, List<&2, String>>)) -> List<&1, C.Named> & (String & List<&2, List<&2, String>>):
  (c, ds) = r
  (d, cs) = ds
  (cols, hc) = rest
  (hdr, cc) = hc
  (C.Named{n, c} <> cols, ("col\t" ++ d ++ "\t" ++ Dump.quote(n) ++ "\n" ++ hdr, cs <> cc))

def Dump.cols(cols: List<&1, C.Named>) -> List<&1, C.Named> & (String & List<&2, List<&2, String>>):
  match cols:
    case Nil{}:
      (Nil{}, (SNil{}, Nil{}))
    case C.Named{+n, col} <> rest:
      Dump.cols.k(n, Dump.col(col), Dump.cols(rest))

def Dump.count(xs: List<&2, String>, acc: U32) -> U32:
  match xs:
    case Nil{}:
      acc
    case h <> t:
      Dump.count(t, U32.add(acc, 1))

# ---- rows ---------------------------------------------------------------------

# the next row: its cells, each preceded by a TAB, and every column minus its head
# (a column that ran out contributes "?": a column shorter than the height; "?" is not a
# cell, so bench/check.py rejects the dump)
def Dump.step.k(cell: String, rest: List<&2, String>, r: String & List<&2, List<&2, String>>) -> String & List<&2, List<&2, String>>:
  (line, tails) = r
  ("\t" ++ cell ++ line, rest <> tails)

def Dump.step.h(h: List<&2, String>, r: String & List<&2, List<&2, String>>) -> String & List<&2, List<&2, String>>:
  match h:
    case Nil{}:
      (line, tails) = r
      ("\t?" ++ line, Nil{} <> tails)
    case c <> rest:
      Dump.step.k(c, rest, r)

def Dump.step(cols: List<&2, List<&2, String>>) -> String & List<&2, List<&2, String>>:
  match cols:
    case Nil{}:
      (SNil{}, Nil{})
    case h <> t:
      Dump.step.h(h, Dump.step(t))

# the state of the row loop: the lines so far (newest first) and the columns' tails
def Dump.rows.next.k(acc: List<&2, String>, r: String & List<&2, List<&2, String>>) -> List<&2, String> & List<&2, List<&2, String>>:
  (line, tails) = r
  (("row" ++ line ++ "\n") <> acc, tails)

def Dump.rows.next(st: List<&2, String> & List<&2, List<&2, String>>) -> List<&2, String> & List<&2, List<&2, String>>:
  (acc, cols) = st
  Dump.rows.next.k(acc, Dump.step(cols))

# the lines (newest first) joined oldest first in front of `acc`: each step copies one short
# line (String.append copies its left operand only), and the loop is a tail call. Base
# String.concat recurses once per line (not a tail call), which overflowed the interpreter's
# stack past ~2^15 rows.
def Dump.cat(xs: List<&2, String>, acc: String) -> String:
  match xs:
    case Nil{}:
      acc
    case h <> t:
      Dump.cat(t, h ++ acc)

# after the last row: nothing when every column is used up, else the line "excess" (a column
# longer than the height; not in the grammar, so bench/check.py rejects the dump and a
# correct expectation never shows it -- without it the extra cells would vanish from the dump)
def Dump.excess(cols: List<&2, List<&2, String>>) -> String:
  match cols:
    case Nil{}:
      SNil{}
    case h <> t:
      match h:
        case Nil{}:
          Dump.excess(t)
        case c <> rest:
          "excess\n"

def Dump.rows(n: Nat, st: List<&2, String> & List<&2, List<&2, String>>) -> String:
  match n:
    case 0n:
      (acc, cols) = st
      Dump.cat(acc, Dump.excess(cols))
    case 1n+p:
      Dump.rows(p, Dump.rows.next(st))

# no rows for a zero-column frame, whatever its height
def Dump.rows.w(cols: List<&2, List<&2, String>>, n: Nat) -> String:
  match cols:
    case Nil{}:
      SNil{}
    case h <> t:
      Dump.rows(n, (Nil{}, h <> t))

# ---- frames -------------------------------------------------------------------

def Dump.frame.k(+h: U32, +w: U32, r: List<&1, C.Named> & (String & List<&2, List<&2, String>>)) -> C.Frame & String:
  (cols, hc) = r
  (hdr, cc) = hc
  (C.Frame{h, cols}, "frame\nheight\t" ++ U32.show(h) ++ "\nwidth\t" ++ U32.show(w) ++ "\n" ++ hdr ++ Dump.rows.w(cc, U32.to_nat(h)))

def Dump.frame.n(+h: U32, r: List<&1, C.Named> & List<&2, String>) -> C.Frame & String:
  (cols, ns) = r
  Dump.frame.k(h, Dump.count(ns, 0), Dump.cols(cols))

# the dump text; the frame comes back
def Dump.frame_k(f: C.Frame) -> C.Frame & String:
  match f:
    case C.Frame{+h, cols}:
      Dump.frame.n(h, C.Cols.names(cols))

def Dump.frame.s(r: C.Frame & String) -> String:
  (f, s) = r
  s

# the dump text of a frame (the frame is consumed)
def Dump.frame(f: C.Frame) -> String:
  Dump.frame.s(Dump.frame_k(f))

# ---- results ------------------------------------------------------------------

# "error<TAB>" and E.Err.show, or the frame's dump
def Dump.result(r: E.ResT(C.Frame)) -> String:
  match r:
    case Fail{e}:
      "error\t" ++ E.Err.show(e) ++ "\n"
    case Done{f}:
      Dump.frame(f)
