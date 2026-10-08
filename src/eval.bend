# src/eval.bend -- eager expression evaluation. DESIGN.md 4.7.
#
# Shape: an Expr is type checked against the frame's schema FIRST (Expr.type,
# strict, every error early), then compiled into a postfix instruction list
# (pure Data) and run by a small stack machine whose state (frame + stack of
# columns) threads through ONE tail-recursive loop (`Eval.run`). That keeps
# the evaluator free of mutual recursion (R2/R4) while each instruction is a
# whole-column operation: dispatch once on (op, dtype), then one flat
# template kernel loop (Kernel.map/zip/fold/...) over the Array. No per-row
# Scalar dispatch, no column <-> list conversion on hot paths.
#
# Broadcasting: every stack slot carries a Kind. KFull = a real column of the
# frame's height; KLit = a 1-row column built from literals only; KAgg = a
# 1-row aggregation result. A binary op broadcasts a 1-row side to the other
# side's length (KFull wins), so `col a > lit 3` and `col a - mean(col a)` work
# and `sum(col a) + lit 1` stays 1 row. `Eval.expr` broadcasts a KLit result
# to the frame height (literals broadcast) and keeps a KAgg result at 1 row.
# An aggregate of a literal aggregates the 1-row literal (`sum(lit 2)` = 2),
# except Len, which counts the frame's rows (pl.len()). `select` of only
# literals/aggregates is 1 row (Polars).
#
# Nulls (DESIGN.md section 5): validity masks are ANDed by every op (bool and/or
# are Kleene; first/last keep a null row; n_unique counts null as a value); the
# result of an op over a Mask column has its null slots reset to the dtype
# default (`Eval.fix`), so the column invariant "an invalid slot holds
# DType.default" is kept by every result.
#
# Idioms (DESIGN.md section 9): helpers above callers; match only on params;
# pairs taken apart in the next helper's parameter; ~T templates.
import Base
import ./dtype.bend as D
import ./err.bend as E
import ./kernels.bend as K
import ./column.bend as C
import ./schema.bend as S
import ./expr.bend as X

type SKind is Data:
  KFull{}
  KLit{}
  KAgg{}

type Slot is Type:
  Slot{k: SKind, col: C.Column}

# postfix code of an Expr (Alias compiles to nothing; a typed null literal
# `Cast{Lit{SNull}, t}` compiles to IConst{SNull, t})
type Instr is Data:
  IConst{v: D.Scalar, t: D.DType}
  ICol{name: String}
  IUn{op: X.UnOp}
  IBin{op: X.BinOp}
  ICast{to: D.DType}
  IFill{}
  IAgg{op: X.AggOp}

type EvSt is Type:
  EvSt{f: C.Frame, r: E.ResT(List<&1, Slot>)}

# one evaluated output of select / with_columns
type Out is Type:
  Out{name: String, k: SKind, col: C.Column}

type SelSt is Type:
  SelSt{f: C.Frame, r: E.ResT(List<&1, Out>)}

def Eval.bug(what: String) -> E.Err:
  E.InvalidOperation{"eval: unexpected " ++ what ++ " (expression not type checked?)"}

# ---- small generic helpers --------------------------------------------------------

def Eval.snd(~T: Data, ~A: Data, r: Array<T> & A) -> A:
  (a, x) = r
  x

# slot i of a (consumed)
def Eval.at(~T: Data, a: Array<T>, +i: U32) -> T:
  Eval.snd(~T, ~T, Array.get(T, a, i))

def Eval.fold1.k(~T: Data, ~f: T -> T -> T, +n: U32, r: Array<T> & T) -> T:
  (a, x0) = r
  Eval.snd(~T, ~T, K.Kernel.fold(~T, ~T, ~f, n, a, x0))

# a reduction seeded with a[0] (n >= 1; for n = 0 it answers slot 0)
def Eval.fold1(~T: Data, ~f: T -> T -> T, +n: U32, a: Array<T>) -> T:
  Eval.fold1.k(~T, ~f, n, Array.get(T, a, 0))

def Eval.i32_lt(a: U32, b: U32) -> Bool:
  U32.is_lt(U32.xor(a, 2147483648), U32.xor(b, 2147483648))

def Eval.i32_min(+a: U32, +b: U32) -> U32:
  Bool.pick(U32, Eval.i32_lt(a, b), a, b)

def Eval.i32_max(+a: U32, +b: U32) -> U32:
  Bool.pick(U32, Eval.i32_lt(a, b), b, a)

def Eval.str_min(+a: String, +b: String) -> String:
  Bool.pick(String, String.is_le(a, b), a, b)

def Eval.str_max(+a: String, +b: String) -> String:
  Bool.pick(String, String.is_le(a, b), b, a)

def Eval.show_bool(w: U32) -> String:
  Bool.pick(String, U32.is_ne(w, 0), "true", "false")

# F32 -> I32 bits, truncating toward zero
def Eval.f2i(+x: F32) -> U32:
  Bool.pick(U32, F32.is_lt(x, 0.0), U32.sub(0, F32.to_u32(F32.neg(x))), F32.to_u32(x))

def Eval.i32_bits(m: Maybe<&2, D.I32>) -> Maybe<&2, U32>:
  match m:
    case Some{D.I32{x}}:
      Some{x}
    case None{}:
      None{}

def Eval.read_bool.k(t: Bool, f: Bool) -> Maybe<&2, U32>:
  match t f:
    case True{} _:
      Some{1}
    case False{} True{}:
      Some{0}
    case False{} False{}:
      None{}

# the CSV boolean spellings: true/false/True/False
def Eval.read_bool(+s: String) -> Maybe<&2, U32>:
  Eval.read_bool.k(Bool.or(String.eq(s, "true"), String.eq(s, "True")), Bool.or(String.eq(s, "false"), String.eq(s, "False")))

def Eval.is_cmp(op: X.BinOp) -> Bool:
  match op:
    case X.Eq{}:
      True{}
    case X.Ne{}:
      True{}
    case X.Lt{}:
      True{}
    case X.Le{}:
      True{}
    case X.Gt{}:
      True{}
    case X.Ge{}:
      True{}
    case X.And{}:
      True{}
    case X.Or{}:
      True{}
    case _:
      False{}

# ---- constant columns / broadcasting ------------------------------------------------

def Eval.const_null(t: D.DType, +n: U32, +d: Nat) -> C.Column:
  match t:
    case D.TBool{}:
      C.CBool{n, d, C.Mask{Array.new(U32, d, 0)}, Array.new(U32, d, 0)}
    case D.TU32{}:
      C.CU32{n, d, C.Mask{Array.new(U32, d, 0)}, Array.new(U32, d, 0)}
    case D.TI32{}:
      C.CI32{n, d, C.Mask{Array.new(U32, d, 0)}, Array.new(U32, d, 0)}
    case D.TF32{}:
      C.CF32{n, d, C.Mask{Array.new(U32, d, 0)}, Array.new(F32, d, 0.0)}
    case D.TStr{}:
      C.CStr{n, d, C.Mask{Array.new(U32, d, 0)}, Array.new(String, d, "")}

def Eval.const_col.d(s: D.Scalar, t: D.DType, +n: U32, +d: Nat) -> C.Column:
  match s:
    case D.SNull{}:
      Eval.const_null(t, n, d)
    case D.SBool{b}:
      C.CBool{n, d, C.AllValid{}, Array.new(U32, d, Bool.to_u32(b))}
    case D.SU32{v}:
      C.CU32{n, d, C.AllValid{}, Array.new(U32, d, v)}
    case D.SI32{v}:
      C.CI32{n, d, C.AllValid{}, Array.new(U32, d, D.I32.to_u32(v))}
    case D.SF32{v}:
      C.CF32{n, d, C.AllValid{}, Array.new(F32, d, v)}
    case D.SStr{v}:
      C.CStr{n, d, C.AllValid{}, Array.new(String, d, v)}

# n copies of a scalar (SNull: n nulls of dtype t; else t is ignored)
def Eval.const_col(s: D.Scalar, t: D.DType, +n: U32) -> C.Column:
  Eval.const_col.d(s, t, n, K.Kernel.depth_for(n))

def Eval.bcast.b(+n: U32, t: D.DType, r: C.Column & D.Scalar) -> C.Column:
  (c, s) = r
  Eval.const_col(s, t, n)

def Eval.bcast.a(+n: U32, r: C.Column & D.DType) -> C.Column:
  (c, t) = r
  Eval.bcast.b(n, t, C.Column.cell(c, 0))

# row 0 of c repeated n times (validity too)
def Eval.bcast(c: C.Column, +n: U32) -> C.Column:
  Eval.bcast.a(n, C.Column.dtype(c))

# ---- validity -----------------------------------------------------------------------

# the AND of two validities; an AllValid side reuses the other mask as is
def Eval.vand(+n: U32, +d: Nat, a: C.Valid, b: C.Valid) -> C.Valid:
  match a b:
    case C.AllValid{} C.AllValid{}:
      C.AllValid{}
    case C.AllValid{} C.Mask{m}:
      C.Mask{m}
    case C.Mask{m} C.AllValid{}:
      C.Mask{m}
    case C.Mask{m1} C.Mask{m2}:
      C.Mask{K.Kernel.mask_and(n, d, m1, m2)}

def Eval.fix.w2(t: D.DType, +n: U32, d: Nat, r: Array<U32> & Array<U32>) -> C.Column:
  (x, m) = r
  C.Column.mk_w(t, n, d, C.Mask{m}, x)

def Eval.fix.w(t: D.DType, +n: U32, d: Nat, v: C.Valid, x: Array<U32>) -> C.Column:
  match v:
    case C.AllValid{}:
      C.Column.mk_w(t, n, d, C.AllValid{}, x)
    case C.Mask{m}:
      Eval.fix.w2(t, n, d, K.Kernel.mask_data(~U32, n, x, m, 0))

def Eval.fix.f2(+n: U32, d: Nat, r: Array<F32> & Array<U32>) -> C.Column:
  (x, m) = r
  C.CF32{n, d, C.Mask{m}, x}

def Eval.fix.f(+n: U32, d: Nat, v: C.Valid, x: Array<F32>) -> C.Column:
  match v:
    case C.AllValid{}:
      C.CF32{n, d, C.AllValid{}, x}
    case C.Mask{m}:
      Eval.fix.f2(n, d, K.Kernel.mask_data(~F32, n, x, m, 0.0))

def Eval.fix.s2(+n: U32, d: Nat, r: Array<String> & Array<U32>) -> C.Column:
  (x, m) = r
  C.CStr{n, d, C.Mask{m}, x}

def Eval.fix.s(+n: U32, d: Nat, v: C.Valid, x: Array<String>) -> C.Column:
  match v:
    case C.AllValid{}:
      C.CStr{n, d, C.AllValid{}, x}
    case C.Mask{m}:
      Eval.fix.s2(n, d, K.Kernel.mask_data(~String, n, x, m, ""))

# reset the slots of invalid rows to the dtype default (no-op when AllValid)
def Eval.fix(c: C.Column) -> C.Column:
  match c:
    case C.CBool{n, d, v, x}:
      Eval.fix.w(D.TBool{}, n, d, v, x)
    case C.CU32{n, d, v, x}:
      Eval.fix.w(D.TU32{}, n, d, v, x)
    case C.CI32{n, d, v, x}:
      Eval.fix.w(D.TI32{}, n, d, v, x)
    case C.CF32{n, d, v, x}:
      Eval.fix.f(n, d, v, x)
    case C.CStr{n, d, v, x}:
      Eval.fix.s(n, d, v, x)

# ---- unary ops ------------------------------------------------------------------------

def Eval.un.isnull(neg: Bool, +n: U32, +d: Nat, v: C.Valid) -> C.Column:
  match neg v:
    case True{} C.AllValid{}:
      C.CBool{n, d, C.AllValid{}, Array.new(U32, d, 0)}
    case False{} C.AllValid{}:
      C.CBool{n, d, C.AllValid{}, Array.new(U32, d, 1)}
    case True{} C.Mask{m}:
      C.CBool{n, d, C.AllValid{}, K.Kernel.mask_not(n, d, m)}
    case False{} C.Mask{m}:
      C.CBool{n, d, C.AllValid{}, m}

# is_null (neg = True) / is_not_null: the validity as data, never null
def Eval.un.nulls(neg: Bool, c: C.Column) -> C.Column:
  match c:
    case C.CBool{n, d, v, x}:
      Eval.un.isnull(neg, n, d, v)
    case C.CU32{n, d, v, x}:
      Eval.un.isnull(neg, n, d, v)
    case C.CI32{n, d, v, x}:
      Eval.un.isnull(neg, n, d, v)
    case C.CF32{n, d, v, x}:
      Eval.un.isnull(neg, n, d, v)
    case C.CStr{n, d, v, x}:
      Eval.un.isnull(neg, n, d, v)

def Eval.un.b(op: X.UnOp, +n: U32, +d: Nat, v: C.Valid, x: Array<U32>) -> E.ResT(C.Column):
  match op:
    case X.Not{}:
      Done{Eval.fix(C.CBool{n, d, v, K.Kernel.map(~U32, ~U32, ~(w => U32.xor(w, 1)), n, d, x, 0)})}
    case _:
      Fail{Eval.bug("unary op on bool")}

def Eval.un.i(op: X.UnOp, +n: U32, +d: Nat, v: C.Valid, x: Array<U32>) -> E.ResT(C.Column):
  match op:
    case X.Neg{}:
      Done{C.CI32{n, d, v, K.Kernel.map(~U32, ~U32, ~(w => U32.sub(0, w)), n, d, x, 0)}}
    case X.Abs{}:
      Done{C.CI32{n, d, v, K.Kernel.map(~U32, ~U32, ~(w => D.I32.mag(D.I32{w})), n, d, x, 0)}}
    case _:
      Fail{Eval.bug("unary op on i32")}

def Eval.un.f(op: X.UnOp, +n: U32, +d: Nat, v: C.Valid, x: Array<F32>) -> E.ResT(C.Column):
  match op:
    case X.Neg{}:
      Done{C.CF32{n, d, v, K.Kernel.map(~F32, ~F32, ~(w => F32.neg(w)), n, d, x, 0.0)}}
    case X.Abs{}:
      Done{C.CF32{n, d, v, K.Kernel.map(~F32, ~F32, ~(w => F32.abs(w)), n, d, x, 0.0)}}
    case X.Sqrt{}:
      Done{C.CF32{n, d, v, K.Kernel.map(~F32, ~F32, ~(w => F32.sqrt(w)), n, d, x, 0.0)}}
    case _:
      Fail{Eval.bug("unary op on f32")}

def Eval.un.v(op: X.UnOp, c: C.Column) -> E.ResT(C.Column):
  match c:
    case C.CBool{n, d, v, x}:
      Eval.un.b(op, n, d, v, x)
    case C.CI32{n, d, v, x}:
      Eval.un.i(op, n, d, v, x)
    case C.CF32{n, d, v, x}:
      Eval.un.f(op, n, d, v, x)
    case _:
      Fail{Eval.bug("unary op")}

# Neg/Abs (i32, f32), Not (bool), Sqrt (f32): null in, null out (the mask is
# kept as is; neg/abs/sqrt of a default slot is the default again, Not is fixed)
def Eval.un(op: X.UnOp, c: C.Column) -> E.ResT(C.Column):
  match op:
    case X.IsNull{}:
      Done{Eval.un.nulls(True{}, c)}
    case X.IsNotNull{}:
      Done{Eval.un.nulls(False{}, c)}
    case other:
      Eval.un.v(other, c)

# ---- binary ops ----------------------------------------------------------------------

# U32 words (also Bool 0/1 words: comparisons, and/or)
def Eval.zip.u(op: X.BinOp, +n: U32, +d: Nat, a: Array<U32>, b: Array<U32>) -> Array<U32>:
  match op:
    case X.Add{}:
      K.Kernel.zip(~U32, ~U32, ~U32, ~(x => y => U32.add(x, y)), n, d, a, b, 0)
    case X.Sub{}:
      K.Kernel.zip(~U32, ~U32, ~U32, ~(x => y => U32.sub(x, y)), n, d, a, b, 0)
    case X.Mul{}:
      K.Kernel.zip(~U32, ~U32, ~U32, ~(x => y => U32.mul(x, y)), n, d, a, b, 0)
    case X.Div{}:
      K.Kernel.zip(~U32, ~U32, ~U32, ~(x => y => U32.div(x, y)), n, d, a, b, 0)
    case X.Mod{}:
      K.Kernel.zip(~U32, ~U32, ~U32, ~(x => y => U32.mod(x, y)), n, d, a, b, 0)
    case X.Eq{}:
      K.Kernel.zip(~U32, ~U32, ~U32, ~(x => y => Bool.to_u32(U32.is_eq(x, y))), n, d, a, b, 0)
    case X.Ne{}:
      K.Kernel.zip(~U32, ~U32, ~U32, ~(x => y => Bool.to_u32(U32.is_ne(x, y))), n, d, a, b, 0)
    case X.Lt{}:
      K.Kernel.zip(~U32, ~U32, ~U32, ~(x => y => Bool.to_u32(U32.is_lt(x, y))), n, d, a, b, 0)
    case X.Le{}:
      K.Kernel.zip(~U32, ~U32, ~U32, ~(x => y => Bool.to_u32(U32.is_le(x, y))), n, d, a, b, 0)
    case X.Gt{}:
      K.Kernel.zip(~U32, ~U32, ~U32, ~(x => y => Bool.to_u32(U32.is_gt(x, y))), n, d, a, b, 0)
    case X.Ge{}:
      K.Kernel.zip(~U32, ~U32, ~U32, ~(x => y => Bool.to_u32(U32.is_ge(x, y))), n, d, a, b, 0)
    case X.And{}:
      K.Kernel.zip(~U32, ~U32, ~U32, ~(x => y => U32.and(x, y)), n, d, a, b, 0)
    case X.Or{}:
      K.Kernel.zip(~U32, ~U32, ~U32, ~(x => y => U32.or(x, y)), n, d, a, b, 0)

# I32 bits: add/sub/mul/eq/ne are the unsigned word ops (two's complement)
def Eval.zip.i(op: X.BinOp, +n: U32, +d: Nat, a: Array<U32>, b: Array<U32>) -> Array<U32>:
  match op:
    case X.Div{}:
      K.Kernel.zip(~U32, ~U32, ~U32, ~(x => y => D.I32.to_u32(D.I32.div(D.I32{x}, D.I32{y}))), n, d, a, b, 0)
    case X.Mod{}:
      K.Kernel.zip(~U32, ~U32, ~U32, ~(x => y => D.I32.to_u32(D.I32.mod(D.I32{x}, D.I32{y}))), n, d, a, b, 0)
    case X.Lt{}:
      K.Kernel.zip(~U32, ~U32, ~U32, ~(x => y => Bool.to_u32(Eval.i32_lt(x, y))), n, d, a, b, 0)
    case X.Le{}:
      K.Kernel.zip(~U32, ~U32, ~U32, ~(x => y => Bool.to_u32(Bool.not(Eval.i32_lt(y, x)))), n, d, a, b, 0)
    case X.Gt{}:
      K.Kernel.zip(~U32, ~U32, ~U32, ~(x => y => Bool.to_u32(Eval.i32_lt(y, x))), n, d, a, b, 0)
    case X.Ge{}:
      K.Kernel.zip(~U32, ~U32, ~U32, ~(x => y => Bool.to_u32(Bool.not(Eval.i32_lt(x, y)))), n, d, a, b, 0)
    case other:
      Eval.zip.u(other, n, d, a, b)

def Eval.zip.fa(op: X.BinOp, +n: U32, +d: Nat, a: Array<F32>, b: Array<F32>) -> Array<F32>:
  match op:
    case X.Sub{}:
      K.Kernel.zip(~F32, ~F32, ~F32, ~(x => y => F32.sub(x, y)), n, d, a, b, 0.0)
    case X.Mul{}:
      K.Kernel.zip(~F32, ~F32, ~F32, ~(x => y => F32.mul(x, y)), n, d, a, b, 0.0)
    case X.Div{}:
      K.Kernel.zip(~F32, ~F32, ~F32, ~(x => y => F32.div(x, y)), n, d, a, b, 0.0)
    case X.Mod{}:
      K.Kernel.zip(~F32, ~F32, ~F32, ~(x => y => F32.mod(x, y)), n, d, a, b, 0.0)
    case _:
      K.Kernel.zip(~F32, ~F32, ~F32, ~(x => y => F32.add(x, y)), n, d, a, b, 0.0)

def Eval.zip.fc(op: X.BinOp, +n: U32, +d: Nat, a: Array<F32>, b: Array<F32>) -> Array<U32>:
  match op:
    case X.Ne{}:
      K.Kernel.zip(~F32, ~F32, ~U32, ~(x => y => Bool.to_u32(F32.is_ne(x, y))), n, d, a, b, 0)
    case X.Lt{}:
      K.Kernel.zip(~F32, ~F32, ~U32, ~(x => y => Bool.to_u32(F32.is_lt(x, y))), n, d, a, b, 0)
    case X.Le{}:
      K.Kernel.zip(~F32, ~F32, ~U32, ~(x => y => Bool.to_u32(F32.is_le(x, y))), n, d, a, b, 0)
    case X.Gt{}:
      K.Kernel.zip(~F32, ~F32, ~U32, ~(x => y => Bool.to_u32(F32.is_gt(x, y))), n, d, a, b, 0)
    case X.Ge{}:
      K.Kernel.zip(~F32, ~F32, ~U32, ~(x => y => Bool.to_u32(F32.is_ge(x, y))), n, d, a, b, 0)
    case _:
      K.Kernel.zip(~F32, ~F32, ~U32, ~(x => y => Bool.to_u32(F32.is_eq(x, y))), n, d, a, b, 0)

def Eval.zip.s(op: X.BinOp, +n: U32, +d: Nat, a: Array<String>, b: Array<String>) -> Array<U32>:
  match op:
    case X.Ne{}:
      K.Kernel.zip(~String, ~String, ~U32, ~(x => y => Bool.to_u32(Bool.not(String.eq(x, y)))), n, d, a, b, 0)
    case X.Lt{}:
      K.Kernel.zip(~String, ~String, ~U32, ~(x => y => Bool.to_u32(String.is_lt(x, y))), n, d, a, b, 0)
    case X.Le{}:
      K.Kernel.zip(~String, ~String, ~U32, ~(x => y => Bool.to_u32(String.is_le(x, y))), n, d, a, b, 0)
    case X.Gt{}:
      K.Kernel.zip(~String, ~String, ~U32, ~(x => y => Bool.to_u32(String.is_gt(x, y))), n, d, a, b, 0)
    case X.Ge{}:
      K.Kernel.zip(~String, ~String, ~U32, ~(x => y => Bool.to_u32(String.is_ge(x, y))), n, d, a, b, 0)
    case _:
      K.Kernel.zip(~String, ~String, ~U32, ~(x => y => Bool.to_u32(String.eq(x, y))), n, d, a, b, 0)

# a word column out of a binary kernel (null slots reset)
def Eval.bin.w(t: D.DType, +n: U32, d: Nat, v: C.Valid, x: Array<U32>) -> E.ResT(C.Column):
  Done{Eval.fix(C.Column.mk_w(t, n, d, v, x))}

def Eval.bin.f(cmp: Bool, +op: X.BinOp, +n: U32, +d: Nat, v: C.Valid, a: Array<F32>, b: Array<F32>) -> E.ResT(C.Column):
  match cmp:
    case True{}:
      Eval.bin.w(D.TBool{}, n, d, v, Eval.zip.fc(op, n, d, a, b))
    case False{}:
      Done{Eval.fix.f(n, d, v, Eval.zip.fa(op, n, d, a, b))}

def Eval.bin.t(cmp: Bool, t: D.DType) -> D.DType:
  match cmp:
    case True{}:
      D.TBool{}
    case False{}:
      t

# ---- Kleene and/or ---------------------------------------------------------------------------
# A bool cell is encoded as a 2-bit state word: 0 null, 2 false, 3 true (valid*2 + value, the
# value forced to 0 on a null row). false & null = false, true | null = true, otherwise a null
# operand makes the result null (Polars). Used only when a side has a validity mask.

# a mask (popcount answer) as a validity; AllValid if every row is set (cast parses, Kleene)
def Eval.cast.allv(+n: U32, r: Array<U32> & U32) -> C.Valid:
  (m, k) = r
  Bool.pick(C.Valid, U32.is_eq(k, n), C.AllValid{}, C.Mask{m})

def Eval.kl.cell(+v: U32, +w: U32) -> U32:
  U32.add(U32.add(v, v), U32.and(w, v))

def Eval.kl.enc(+n: U32, +d: Nat, v: C.Valid, x: Array<U32>) -> Array<U32>:
  match v:
    case C.AllValid{}:
      K.Kernel.map(~U32, ~U32, ~(w => U32.or(w, 2)), n, d, x, 0)
    case C.Mask{m}:
      K.Kernel.zip(~U32, ~U32, ~U32, ~(a => w => Eval.kl.cell(a, w)), n, d, m, x, 0)

def Eval.kl.and(+a: U32, +b: U32) -> U32:
  Bool.pick(U32, Bool.or(U32.is_eq(a, 2), U32.is_eq(b, 2)), 2, Bool.pick(U32, Bool.and(U32.is_eq(a, 3), U32.is_eq(b, 3)), 3, 0))

def Eval.kl.or(+a: U32, +b: U32) -> U32:
  Bool.pick(U32, Bool.or(U32.is_eq(a, 3), U32.is_eq(b, 3)), 3, Bool.pick(U32, Bool.and(U32.is_eq(a, 2), U32.is_eq(b, 2)), 2, 0))

def Eval.kl.st(is_and: Bool, +n: U32, +d: Nat, a: Array<U32>, b: Array<U32>) -> Array<U32>:
  match is_and:
    case True{}:
      K.Kernel.zip(~U32, ~U32, ~U32, ~(x => y => Eval.kl.and(x, y)), n, d, a, b, 0)
    case False{}:
      K.Kernel.zip(~U32, ~U32, ~U32, ~(x => y => Eval.kl.or(x, y)), n, d, a, b, 0)

def Eval.kl.some.b(known: Bool, +r: U32) -> Maybe<&2, U32>:
  match known:
    case True{}:
      Some{U32.and(r, 1)}
    case False{}:
      None{}

# state word -> value if known (valid), else None
def Eval.kl.some(+r: U32) -> Maybe<&2, U32>:
  Eval.kl.some.b(U32.is_ge(r, 2), r)

def Eval.kl.fin(+n: U32, +d: Nat, r: Array<U32> & Array<U32>) -> C.Column:
  (x, ok) = r
  C.CBool{n, d, Eval.cast.allv(n, K.Kernel.popcount(n, ok)), x}

def Eval.kleene(is_and: Bool, +n: U32, +d: Nat, va: C.Valid, vb: C.Valid, xa: Array<U32>, xb: Array<U32>) -> C.Column:
  Eval.kl.fin(n, d, K.Kernel.map_maybe(~U32, ~U32, ~(r => Eval.kl.some(r)), n, d, Eval.kl.st(is_and, n, d, Eval.kl.enc(n, d, va, xa), Eval.kl.enc(n, d, vb, xb)), 0))

# and/or: both sides dense -> the plain word op, else Kleene
def Eval.bin.logic(is_and: Bool, op: X.BinOp, +n: U32, +d: Nat, va: C.Valid, vb: C.Valid, xa: Array<U32>, xb: Array<U32>) -> E.ResT(C.Column):
  match va vb:
    case C.AllValid{} C.AllValid{}:
      Eval.bin.w(D.TBool{}, n, d, C.AllValid{}, Eval.zip.u(op, n, d, xa, xb))
    case C.AllValid{} C.Mask{mb}:
      Done{Eval.kleene(is_and, n, d, C.AllValid{}, C.Mask{mb}, xa, xb)}
    case C.Mask{ma} C.AllValid{}:
      Done{Eval.kleene(is_and, n, d, C.Mask{ma}, C.AllValid{}, xa, xb)}
    case C.Mask{ma} C.Mask{mb}:
      Done{Eval.kleene(is_and, n, d, C.Mask{ma}, C.Mask{mb}, xa, xb)}

def Eval.bin.bool(+op: X.BinOp, +n: U32, +d: Nat, va: C.Valid, vb: C.Valid, xa: Array<U32>, xb: Array<U32>) -> E.ResT(C.Column):
  match op:
    case X.And{}:
      Eval.bin.logic(True{}, op, n, d, va, vb, xa, xb)
    case X.Or{}:
      Eval.bin.logic(False{}, op, n, d, va, vb, xa, xb)
    case _:
      Eval.bin.w(D.TBool{}, n, d, Eval.vand(n, d, va, vb), Eval.zip.u(op, n, d, xa, xb))

# a op b over two columns of the same dtype and length n (the depth of a is
# the output's); validity = AND of both (Kleene for bool and/or)
def Eval.bin(+op: X.BinOp, a: C.Column, b: C.Column) -> E.ResT(C.Column):
  match a b:
    case C.CBool{+n, +d, va, xa} C.CBool{n2, d2, vb, xb}:
      Eval.bin.bool(op, n, d, va, vb, xa, xb)
    case C.CU32{+n, +d, va, xa} C.CU32{n2, d2, vb, xb}:
      Eval.bin.w(Eval.bin.t(Eval.is_cmp(op), D.TU32{}), n, d, Eval.vand(n, d, va, vb), Eval.zip.u(op, n, d, xa, xb))
    case C.CI32{+n, +d, va, xa} C.CI32{n2, d2, vb, xb}:
      Eval.bin.w(Eval.bin.t(Eval.is_cmp(op), D.TI32{}), n, d, Eval.vand(n, d, va, vb), Eval.zip.i(op, n, d, xa, xb))
    case C.CF32{+n, +d, va, xa} C.CF32{n2, d2, vb, xb}:
      Eval.bin.f(Eval.is_cmp(op), op, n, d, Eval.vand(n, d, va, vb), xa, xb)
    case C.CStr{+n, +d, va, xa} C.CStr{n2, d2, vb, xb}:
      Eval.bin.w(D.TBool{}, n, d, Eval.vand(n, d, va, vb), Eval.zip.s(op, n, d, xa, xb))
    case _ _:
      Fail{Eval.bug("operand dtypes in " ++ X.BinOp.name(op))}

# ---- fill_null --------------------------------------------------------------------------

def Eval.fill.t2(~T: Data, +n: U32, +d: Nat, vb: C.Valid, r: Array<U32> & Array<T>) -> C.Valid & Array<T>:
  match vb:
    case C.AllValid{}:
      (m, out) = r
      (C.AllValid{}, out)
    case C.Mask{mb}:
      (m, out) = r
      (C.Mask{K.Kernel.mask_or(n, d, m, mb)}, out)

# e where valid, else v; null only where both are null
def Eval.fill.t(~T: Data, +n: U32, +d: Nat, va: C.Valid, vb: C.Valid, a: Array<T>, b: Array<T>) -> C.Valid & Array<T>:
  match va:
    case C.AllValid{}:
      (C.AllValid{}, a)
    case C.Mask{m}:
      Eval.fill.t2(~T, n, d, vb, K.Kernel.choose(~T, n, m, a, b))

def Eval.fill.w(t: D.DType, +n: U32, d: Nat, r: C.Valid & Array<U32>) -> E.ResT(C.Column):
  (v, x) = r
  Done{C.Column.mk_w(t, n, d, v, x)}

def Eval.fill.f(+n: U32, d: Nat, r: C.Valid & Array<F32>) -> E.ResT(C.Column):
  (v, x) = r
  Done{C.CF32{n, d, v, x}}

def Eval.fill.s(+n: U32, d: Nat, r: C.Valid & Array<String>) -> E.ResT(C.Column):
  (v, x) = r
  Done{C.CStr{n, d, v, x}}

def Eval.fill(a: C.Column, b: C.Column) -> E.ResT(C.Column):
  match a b:
    case C.CBool{+n, +d, va, xa} C.CBool{n2, d2, vb, xb}:
      Eval.fill.w(D.TBool{}, n, d, Eval.fill.t(~U32, n, d, va, vb, xa, xb))
    case C.CU32{+n, +d, va, xa} C.CU32{n2, d2, vb, xb}:
      Eval.fill.w(D.TU32{}, n, d, Eval.fill.t(~U32, n, d, va, vb, xa, xb))
    case C.CI32{+n, +d, va, xa} C.CI32{n2, d2, vb, xb}:
      Eval.fill.w(D.TI32{}, n, d, Eval.fill.t(~U32, n, d, va, vb, xa, xb))
    case C.CF32{+n, +d, va, xa} C.CF32{n2, d2, vb, xb}:
      Eval.fill.f(n, d, Eval.fill.t(~F32, n, d, va, vb, xa, xb))
    case C.CStr{+n, +d, va, xa} C.CStr{n2, d2, vb, xb}:
      Eval.fill.s(n, d, Eval.fill.t(~String, n, d, va, vb, xa, xb))
    case _ _:
      Fail{Eval.bug("operand dtypes in fill_null")}

# ---- cast ---------------------------------------------------------------------------------

def Eval.cast.err(t: D.DType, +to: D.DType) -> E.ResT(C.Column):
  Fail{E.TypeMismatch{"cast", "castable to " ++ D.DType.show(to), D.DType.show(t)}}

def Eval.cast.pv(+n: U32, +d: Nat, v: C.Valid, ok: Array<U32>) -> C.Valid:
  match v:
    case C.AllValid{}:
      Eval.cast.allv(n, K.Kernel.popcount(n, ok))
    case C.Mask{m}:
      Eval.cast.allv(n, K.Kernel.popcount(n, K.Kernel.mask_and(n, d, ok, m)))

def Eval.cast.pw(t: D.DType, +n: U32, +d: Nat, v: C.Valid, r: Array<U32> & Array<U32>) -> E.ResT(C.Column):
  (x, ok) = r
  Done{Eval.fix(C.Column.mk_w(t, n, d, Eval.cast.pv(n, d, v, ok), x))}

def Eval.cast.pf(+n: U32, +d: Nat, v: C.Valid, r: Array<F32> & Array<U32>) -> E.ResT(C.Column):
  (x, ok) = r
  Done{Eval.fix(C.CF32{n, d, Eval.cast.pv(n, d, v, ok), x})}

def Eval.cast.b(+to: D.DType, +n: U32, +d: Nat, v: C.Valid, x: Array<U32>) -> E.ResT(C.Column):
  match to:
    case D.TBool{}:
      Done{C.CBool{n, d, v, x}}
    case D.TU32{}:
      Done{C.CU32{n, d, v, x}}
    case D.TI32{}:
      Done{C.CI32{n, d, v, x}}
    case D.TF32{}:
      Done{C.CF32{n, d, v, K.Kernel.map(~U32, ~F32, ~(w => U32.to_f32(w)), n, d, x, 0.0)}}
    case D.TStr{}:
      Done{Eval.fix(C.CStr{n, d, v, K.Kernel.map(~U32, ~String, ~(w => Eval.show_bool(w)), n, d, x, "")})}

def Eval.cast.u(+to: D.DType, +n: U32, +d: Nat, v: C.Valid, x: Array<U32>) -> E.ResT(C.Column):
  match to:
    case D.TU32{}:
      Done{C.CU32{n, d, v, x}}
    case D.TI32{}:
      Done{C.CI32{n, d, v, x}}
    case D.TF32{}:
      Done{C.CF32{n, d, v, K.Kernel.map(~U32, ~F32, ~(w => U32.to_f32(w)), n, d, x, 0.0)}}
    case D.TStr{}:
      Done{Eval.fix(C.CStr{n, d, v, K.Kernel.map(~U32, ~String, ~(w => U32.show(w)), n, d, x, "")})}
    case D.TBool{}:
      Eval.cast.err(D.TU32{}, to)

def Eval.cast.i(+to: D.DType, +n: U32, +d: Nat, v: C.Valid, x: Array<U32>) -> E.ResT(C.Column):
  match to:
    case D.TU32{}:
      Done{C.CU32{n, d, v, x}}
    case D.TI32{}:
      Done{C.CI32{n, d, v, x}}
    case D.TF32{}:
      Done{C.CF32{n, d, v, K.Kernel.map(~U32, ~F32, ~(w => D.I32.to_f32(D.I32{w})), n, d, x, 0.0)}}
    case D.TStr{}:
      Done{Eval.fix(C.CStr{n, d, v, K.Kernel.map(~U32, ~String, ~(w => D.I32.show(D.I32{w})), n, d, x, "")})}
    case D.TBool{}:
      Eval.cast.err(D.TI32{}, to)

def Eval.cast.f(+to: D.DType, +n: U32, +d: Nat, v: C.Valid, x: Array<F32>) -> E.ResT(C.Column):
  match to:
    case D.TU32{}:
      Done{C.CU32{n, d, v, K.Kernel.map(~F32, ~U32, ~(w => F32.to_u32(w)), n, d, x, 0)}}
    case D.TI32{}:
      Done{C.CI32{n, d, v, K.Kernel.map(~F32, ~U32, ~(w => Eval.f2i(w)), n, d, x, 0)}}
    case D.TF32{}:
      Done{C.CF32{n, d, v, x}}
    case D.TStr{}:
      Done{Eval.fix(C.CStr{n, d, v, K.Kernel.map(~F32, ~String, ~(w => F32.show(w)), n, d, x, "")})}
    case D.TBool{}:
      Eval.cast.err(D.TF32{}, to)

# Str -> anything parses the TRIMMED text; a failed parse is null (lenient)
def Eval.cast.s(+to: D.DType, +n: U32, +d: Nat, v: C.Valid, x: Array<String>) -> E.ResT(C.Column):
  match to:
    case D.TStr{}:
      Done{C.CStr{n, d, v, x}}
    case D.TU32{}:
      Eval.cast.pw(D.TU32{}, n, d, v, K.Kernel.map_maybe(~String, ~U32, ~(s => U32.read(String.trim(s))), n, d, x, 0))
    case D.TI32{}:
      Eval.cast.pw(D.TI32{}, n, d, v, K.Kernel.map_maybe(~String, ~U32, ~(s => Eval.i32_bits(D.I32.read(String.trim(s)))), n, d, x, 0))
    case D.TBool{}:
      Eval.cast.pw(D.TBool{}, n, d, v, K.Kernel.map_maybe(~String, ~U32, ~(s => Eval.read_bool(String.trim(s))), n, d, x, 0))
    case D.TF32{}:
      Eval.cast.pf(n, d, v, K.Kernel.map_maybe(~String, ~F32, ~(s => F32.read(String.trim(s))), n, d, x, 0.0))

# the cast table of DESIGN.md 4.6 (U32<->I32 and Bool->U32/I32 only retag)
def Eval.cast(+to: D.DType, c: C.Column) -> E.ResT(C.Column):
  match c:
    case C.CBool{n, d, v, x}:
      Eval.cast.b(to, n, d, v, x)
    case C.CU32{n, d, v, x}:
      Eval.cast.u(to, n, d, v, x)
    case C.CI32{n, d, v, x}:
      Eval.cast.i(to, n, d, v, x)
    case C.CF32{n, d, v, x}:
      Eval.cast.f(to, n, d, v, x)
    case C.CStr{n, d, v, x}:
      Eval.cast.s(to, n, d, v, x)

# ---- aggregations ------------------------------------------------------------------------

# a 1-row column holding s (SNull: one null of dtype t)
def Eval.unit(s: D.Scalar, t: D.DType) -> C.Column:
  Eval.const_col(s, t, 1)

# null when there is no valid row
def Eval.nz(+k: U32, s: D.Scalar) -> D.Scalar:
  Bool.pick(D.Scalar, U32.is_zero(k), D.SNull{}, s)

def Eval.mean_s(+k: U32, s: F32) -> D.Scalar:
  Eval.nz(k, D.SF32{F32.div(s, U32.to_f32(k))})

def Eval.dropnull.c(c: C.Column, r: Array<U32> & U32) -> C.Column:
  (m, +k) = r
  C.Column.slice.c(C.Column.compact(c, m, k))

def Eval.dropnull.b(+n: U32, r: C.Column & C.Valid) -> C.Column:
  (c, v) = r
  match v:
    case C.AllValid{}:
      c
    case C.Mask{m}:
      Eval.dropnull.c(c, K.Kernel.popcount(n, m))

def Eval.dropnull.a(r: C.Column & U32) -> C.Column:
  (c, +n) = r
  Eval.dropnull.b(n, C.Column.take_valid(c))

# the valid rows only (AllValid, len = valid count); AllValid columns as they are
def Eval.dropnull(c: C.Column) -> C.Column:
  Eval.dropnull.a(C.Column.len(c))

# distinct values of a sorted list (eq = equality of neighbours)
def Eval.distinct.go(~T: Data, ~eq: T -> T -> Bool, xs: List<&2, T>, +prev: T, acc: U32) -> U32:
  match xs:
    case Nil{}:
      acc
    case +h <> t:
      Eval.distinct.go(~T, ~eq, t, h, U32.add(acc, U32.sub(1, Bool.to_u32(eq(prev, h)))))

def Eval.distinct(~T: Data, ~eq: T -> T -> Bool, xs: List<&2, T>) -> U32:
  match xs:
    case Nil{}:
      0
    case +h <> t:
      Eval.distinct.go(~T, ~eq, t, h, 1)

def Eval.nuniq.l(~T: Data, ~le: T -> T -> Bool, ~eq: T -> T -> Bool, r: Array<T> & List<&2, T>) -> U32:
  (a, xs) = r
  Eval.distinct(~T, ~eq, List.sort(~T, ~le, xs))

# the number of distinct values among a[0..k) (sort, then count runs)
def Eval.nuniq(~T: Data, ~le: T -> T -> Bool, ~eq: T -> T -> Bool, +k: U32, a: Array<T>) -> U32:
  Eval.nuniq.l(~T, ~le, ~eq, K.Kernel.to_list(~T, k, a))

# compensated F32 sum of a word column as numbers (I32 signed, else unsigned)
def Eval.agg.wsum(t: D.DType, +k: U32, x: Array<U32>) -> F32:
  match t:
    case D.TI32{}:
      K.Kernel.fsum(~U32, ~(w => D.I32.to_f32(D.I32{w})), k, x)
    case _:
      K.Kernel.fsum(~U32, ~(w => U32.to_f32(w)), k, x)

def Eval.agg.wmin(t: D.DType, +k: U32, x: Array<U32>) -> U32:
  match t:
    case D.TI32{}:
      Eval.fold1(~U32, ~(a => b => Eval.i32_min(a, b)), k, x)
    case _:
      Eval.fold1(~U32, ~(a => b => U32.min(a, b)), k, x)

def Eval.agg.wmax(t: D.DType, +k: U32, x: Array<U32>) -> U32:
  match t:
    case D.TI32{}:
      Eval.fold1(~U32, ~(a => b => Eval.i32_max(a, b)), k, x)
    case _:
      Eval.fold1(~U32, ~(a => b => U32.max(a, b)), k, x)

# word columns (Bool / U32 / I32), all k rows valid
def Eval.agg.w(op: X.AggOp, +t: D.DType, +k: U32, x: Array<U32>) -> E.ResT(C.Column):
  match op:
    case X.Sum{}:
      Done{Eval.unit(C.Column.cell.word(t, Eval.snd(~U32, ~U32, K.Kernel.fold(~U32, ~U32, ~(a => b => U32.add(a, b)), k, x, 0))), t)}
    case X.Mean{}:
      Done{Eval.unit(Eval.mean_s(k, Eval.agg.wsum(t, k, x)), D.TF32{})}
    case X.Min{}:
      Done{Eval.unit(Eval.nz(k, C.Column.cell.word(t, Eval.agg.wmin(t, k, x))), t)}
    case X.Max{}:
      Done{Eval.unit(Eval.nz(k, C.Column.cell.word(t, Eval.agg.wmax(t, k, x))), t)}
    case X.First{}:
      Done{Eval.unit(Eval.nz(k, C.Column.cell.word(t, Eval.at(~U32, x, 0))), t)}
    case X.Last{}:
      Done{Eval.unit(Eval.nz(k, C.Column.cell.word(t, Eval.at(~U32, x, U32.sub(k, 1)))), t)}
    case X.NUnique{}:
      Done{Eval.unit(D.SU32{Eval.nuniq(~U32, ~(a => b => U32.is_le(a, b)), ~(a => b => U32.is_eq(a, b)), k, x)}, D.TU32{})}
    case _:
      Done{Eval.unit(D.SU32{k}, D.TU32{})}

def Eval.agg.f(op: X.AggOp, +k: U32, x: Array<F32>) -> E.ResT(C.Column):
  match op:
    case X.Sum{}:
      Done{Eval.unit(D.SF32{K.Kernel.fsum(~F32, ~(w => w), k, x)}, D.TF32{})}
    case X.Mean{}:
      Done{Eval.unit(Eval.mean_s(k, K.Kernel.fsum(~F32, ~(w => w), k, x)), D.TF32{})}
    case X.Min{}:
      Done{Eval.unit(Eval.nz(k, D.SF32{Eval.fold1(~F32, ~(a => b => F32.min(a, b)), k, x)}), D.TF32{})}
    case X.Max{}:
      Done{Eval.unit(Eval.nz(k, D.SF32{Eval.fold1(~F32, ~(a => b => F32.max(a, b)), k, x)}), D.TF32{})}
    case X.First{}:
      Done{Eval.unit(Eval.nz(k, D.SF32{Eval.at(~F32, x, 0)}), D.TF32{})}
    case X.Last{}:
      Done{Eval.unit(Eval.nz(k, D.SF32{Eval.at(~F32, x, U32.sub(k, 1))}), D.TF32{})}
    case X.NUnique{}:
      Done{Eval.unit(D.SU32{Eval.nuniq(~F32, ~(a => b => F32.is_le(a, b)), ~(a => b => F32.is_eq(a, b)), k, x)}, D.TU32{})}
    case _:
      Done{Eval.unit(D.SU32{k}, D.TU32{})}

def Eval.agg.s(op: X.AggOp, +k: U32, x: Array<String>) -> E.ResT(C.Column):
  match op:
    case X.Min{}:
      Done{Eval.unit(Eval.nz(k, D.SStr{Eval.fold1(~String, ~(a => b => Eval.str_min(a, b)), k, x)}), D.TStr{})}
    case X.Max{}:
      Done{Eval.unit(Eval.nz(k, D.SStr{Eval.fold1(~String, ~(a => b => Eval.str_max(a, b)), k, x)}), D.TStr{})}
    case X.First{}:
      Done{Eval.unit(Eval.nz(k, D.SStr{Eval.at(~String, x, 0)}), D.TStr{})}
    case X.Last{}:
      Done{Eval.unit(Eval.nz(k, D.SStr{Eval.at(~String, x, U32.sub(k, 1))}), D.TStr{})}
    case X.NUnique{}:
      Done{Eval.unit(D.SU32{Eval.nuniq(~String, ~(a => b => String.is_le(a, b)), ~(a => b => String.eq(a, b)), k, x)}, D.TU32{})}
    case X.Sum{}:
      Fail{Eval.bug("sum over str")}
    case X.Mean{}:
      Fail{Eval.bug("mean over str")}
    case _:
      Done{Eval.unit(D.SU32{k}, D.TU32{})}

# an aggregation over a column with no nulls (k = its length)
def Eval.agg.dense(op: X.AggOp, c: C.Column) -> E.ResT(C.Column):
  match c:
    case C.CBool{k, d, v, x}:
      Eval.agg.w(op, D.TBool{}, k, x)
    case C.CU32{k, d, v, x}:
      Eval.agg.w(op, D.TU32{}, k, x)
    case C.CI32{k, d, v, x}:
      Eval.agg.w(op, D.TI32{}, k, x)
    case C.CF32{k, d, v, x}:
      Eval.agg.f(op, k, x)
    case C.CStr{k, d, v, x}:
      Eval.agg.s(op, k, x)

def Eval.agg.count.b(+n: U32, r: C.Column & U32) -> C.Column:
  (c, nulls) = r
  Eval.unit(D.SU32{U32.sub(n, nulls)}, D.TU32{})

def Eval.agg.count(r: C.Column & U32) -> C.Column:
  (c, +n) = r
  Eval.agg.count.b(n, C.Column.null_count(c))

def Eval.agg.len(r: C.Column & U32) -> C.Column:
  (c, n) = r
  Eval.unit(D.SU32{n}, D.TU32{})

# n_unique (Polars): the distinct valid values, plus one when any row is null
def Eval.nu.s(+nulls: U32, r: C.Column & D.Scalar) -> E.ResT(C.Column):
  (c, s) = r
  match s:
    case D.SU32{k}:
      Done{Eval.unit(D.SU32{U32.add(k, Bool.to_u32(U32.is_ne(nulls, 0)))}, D.TU32{})}
    case _:
      Fail{Eval.bug("n_unique")}

def Eval.nu.r(+nulls: U32, r: E.ResT(C.Column)) -> E.ResT(C.Column):
  match r:
    case Fail{e}:
      Fail{e}
    case Done{c}:
      Eval.nu.s(nulls, C.Column.cell(c, 0))

def Eval.nu.c(r: C.Column & U32) -> E.ResT(C.Column):
  (c, +nulls) = r
  Eval.nu.r(nulls, Eval.agg.dense(X.NUnique{}, Eval.dropnull(c)))

# first / last (Polars): row 0 / row n-1 as is, null included; null of the dtype when empty
def Eval.pick.c(+t: D.DType, +empty: Bool, r: C.Column & D.Scalar) -> C.Column:
  (c, s) = r
  Eval.unit(Bool.pick(D.Scalar, empty, D.SNull{}, s), t)

def Eval.pick.b(+empty: Bool, +i: U32, r: C.Column & D.DType) -> C.Column:
  (c, +t) = r
  Eval.pick.c(t, empty, C.Column.cell(c, i))

def Eval.pick.a(last: Bool, r: C.Column & U32) -> C.Column:
  (c, +n) = r
  Eval.pick.b(U32.is_zero(n), Bool.pick(U32, last, U32.sub(n, 1), 0), C.Column.dtype(c))

# a 1-row column: Len counts rows, Count valid rows, the others skip nulls
# (DESIGN.md 4.7 / section 5). The column is consumed.
def Eval.agg(op: X.AggOp, c: C.Column) -> E.ResT(C.Column):
  match op:
    case X.Len{}:
      Done{Eval.agg.len(C.Column.len(c))}
    case X.Count{}:
      Done{Eval.agg.count(C.Column.len(c))}
    case X.NUnique{}:
      Eval.nu.c(C.Column.null_count(c))
    case X.First{}:
      Done{Eval.pick.a(False{}, C.Column.len(c))}
    case X.Last{}:
      Done{Eval.pick.a(True{}, C.Column.len(c))}
    case other:
      Eval.agg.dense(other, Eval.dropnull(c))

# ---- compile ----------------------------------------------------------------------------

def SKind.is_full(k: SKind) -> Bool:
  match k:
    case KFull{}:
      True{}
    case _:
      False{}

def SKind.is_agg(k: SKind) -> Bool:
  match k:
    case KAgg{}:
      True{}
    case _:
      False{}

def SKind.comb(a: SKind, b: SKind) -> SKind:
  match a b:
    case KFull{} _:
      KFull{}
    case _ KFull{}:
      KFull{}
    case KAgg{} _:
      KAgg{}
    case _ KAgg{}:
      KAgg{}
    case _ _:
      KLit{}

# the static kind of an expression's result (what the stack machine computes)
def Eval.kind(e: X.Expr) -> SKind:
  match e:
    case X.Col{n}:
      KFull{}
    case X.Lit{v}:
      KLit{}
    case X.Alias{e2, n}:
      Eval.kind(e2)
    case X.Cast{e2, t}:
      Eval.kind(e2)
    case X.Un{op, e2}:
      Eval.kind(e2)
    case X.Bin{op, a, b}:
      SKind.comb(Eval.kind(a), Eval.kind(b))
    case X.FillNull{e2, v}:
      SKind.comb(Eval.kind(e2), Eval.kind(v))
    case X.Agg{op, e2}:
      KAgg{}

def Eval.compile.lit(+v: D.Scalar) -> Instr:
  IConst{v, Maybe.default(&2, D.DType, D.Scalar.dtype(v), D.TBool{})}

def Eval.compile.cast(null_lit: Bool, +to: D.DType, +acc: List<&2, Instr>, code: List<&2, Instr>) -> List<&2, Instr>:
  match null_lit:
    case True{}:
      IConst{D.SNull{}, to} <> acc
    case False{}:
      code

# postfix code of e, followed by acc
def Eval.compile(e: X.Expr, +acc: List<&2, Instr>) -> List<&2, Instr>:
  match e:
    case X.Col{n}:
      ICol{n} <> acc
    case X.Lit{v}:
      Eval.compile.lit(v) <> acc
    case X.Alias{e2, n}:
      Eval.compile(e2, acc)
    case X.Cast{+e2, +to}:
      Eval.compile.cast(X.Expr.is_null_lit(e2), to, acc, Eval.compile(e2, ICast{to} <> acc))
    case X.Un{op, e2}:
      Eval.compile(e2, IUn{op} <> acc)
    case X.Bin{op, a, b}:
      Eval.compile(a, Eval.compile(b, IBin{op} <> acc))
    case X.FillNull{e2, v}:
      Eval.compile(e2, Eval.compile(v, IFill{} <> acc))
    case X.Agg{op, e2}:
      Eval.compile(e2, IAgg{op} <> acc)

# ---- the stack machine ---------------------------------------------------------------------

def Eval.wrap(k: SKind, r: E.ResT(C.Column)) -> E.ResT(Slot):
  match r:
    case Fail{e}:
      Fail{e}
    case Done{c}:
      Done{Slot{k, c}}

def Eval.push(rest: List<&1, Slot>, r: E.ResT(Slot)) -> E.ResT(List<&1, Slot>):
  match r:
    case Fail{e}:
      Fail{e}
    case Done{s}:
      Done{s <> rest}

# a 1-row side takes the length n of the other side
def Eval.fit(k: SKind, c: C.Column, +n: U32) -> C.Column:
  match k:
    case KFull{}:
      c
    case _:
      Eval.bcast(c, n)

def Eval.fit_len(k: SKind, c: C.Column, +h: U32) -> C.Column:
  match k:
    case KLit{}:
      Eval.bcast(c, h)
    case _:
      c

# An aggregation over a literal aggregates the 1-row literal (Polars:
# `pl.lit(2).sum()` = 2). The one exception is Len: `pl.len()` is encoded as
# `Agg{Len, Lit 1}` and must count the frame's rows, so only Len broadcasts.
def Eval.fit_agg(op: X.AggOp, k: SKind, c: C.Column, +h: U32) -> C.Column:
  match op:
    case X.Len{}:
      Eval.fit_len(k, c, h)
    case _:
      c

def Eval.do1(+h: U32, i: Instr, k: SKind, c: C.Column) -> E.ResT(Slot):
  match i:
    case IUn{op}:
      Eval.wrap(k, Eval.un(op, c))
    case ICast{to}:
      Eval.wrap(k, Eval.cast(to, c))
    case IAgg{+op}:
      Eval.wrap(KAgg{}, Eval.agg(op, Eval.fit_agg(op, k, c, h)))
    case _:
      Fail{Eval.bug("instruction")}

def Eval.op2(i: Instr, a: C.Column, b: C.Column) -> E.ResT(C.Column):
  match i:
    case IBin{op}:
      Eval.bin(op, a, b)
    case IFill{}:
      Eval.fill(a, b)
    case _:
      Fail{Eval.bug("instruction")}

def Eval.do2.b(bad: Bool, i: Instr, k: SKind, +la: U32, +lb: U32, a: C.Column, b: C.Column) -> E.ResT(Slot):
  match bad:
    case True{}:
      Fail{E.ShapeMismatch{la, lb}}
    case False{}:
      Eval.wrap(k, Eval.op2(i, a, b))

def Eval.do2.a(i: Instr, +ka: SKind, +kb: SKind, ra: C.Column & U32, rb: C.Column & U32) -> E.ResT(Slot):
  (a, +la) = ra
  (b, +lb) = rb
  +fa = SKind.is_full(ka)
  +fb = SKind.is_full(kb)
  +n = Bool.pick(U32, fa, la, Bool.pick(U32, fb, lb, 1))
  Eval.do2.b(Bool.and(Bool.and(fa, fb), U32.is_ne(la, lb)), i, SKind.comb(ka, kb), la, lb, Eval.fit(ka, a, n), Eval.fit(kb, b, n))

def Eval.do2(i: Instr, ka: SKind, a: C.Column, kb: SKind, b: C.Column) -> E.ResT(Slot):
  Eval.do2.a(i, ka, kb, C.Column.len(a), C.Column.len(b))

def Eval.app1(+h: U32, i: Instr, stk: List<&1, Slot>) -> E.ResT(List<&1, Slot>):
  match stk:
    case Nil{}:
      Fail{Eval.bug("empty stack")}
    case Slot{k, c} <> rest:
      Eval.push(rest, Eval.do1(h, i, k, c))

def Eval.app2(i: Instr, stk: List<&1, Slot>) -> E.ResT(List<&1, Slot>):
  match stk:
    case Slot{kb, b} <> Slot{ka, a} <> rest:
      Eval.push(rest, Eval.do2(i, ka, a, kb, b))
    case _:
      Fail{Eval.bug("empty stack")}

def Eval.push_col(stk: List<&1, Slot>, r: C.Frame & E.ResT(C.Column)) -> EvSt:
  (f, rc) = r
  match rc:
    case Fail{e}:
      EvSt{f, Fail{e}}
    case Done{c}:
      EvSt{f, Done{Slot{KFull{}, c} <> stk}}

def Eval.exec(+h: U32, i: Instr, f: C.Frame, stk: List<&1, Slot>) -> EvSt:
  match i:
    case ICol{n}:
      Eval.push_col(stk, C.Frame.get_cloned(f, n))
    case IConst{v, t}:
      EvSt{f, Done{Slot{KLit{}, Eval.unit(v, t)} <> stk}}
    case IBin{op}:
      EvSt{f, Eval.app2(IBin{op}, stk)}
    case IFill{}:
      EvSt{f, Eval.app2(IFill{}, stk)}
    case other:
      EvSt{f, Eval.app1(h, other, stk)}

def Eval.step.r(+h: U32, i: Instr, f: C.Frame, r: E.ResT(List<&1, Slot>)) -> EvSt:
  match r:
    case Fail{e}:
      EvSt{f, Fail{e}}
    case Done{stk}:
      Eval.exec(h, i, f, stk)

def Eval.step(+h: U32, i: Instr, s: EvSt) -> EvSt:
  match s:
    case EvSt{f, r}:
      Eval.step.r(h, i, f, r)

def Eval.run(code: List<&2, Instr>, +h: U32, s: EvSt) -> EvSt:
  match code:
    case Nil{}:
      s
    case i <> t:
      Eval.run(t, h, Eval.step(h, i, s))

def Eval.fin.one(stk: List<&1, Slot>) -> E.ResT(Slot):
  match stk:
    case Slot{k, c} <> Nil{}:
      Done{Slot{k, c}}
    case _:
      Fail{Eval.bug("stack shape")}

def Eval.fin.r(r: E.ResT(List<&1, Slot>)) -> E.ResT(Slot):
  match r:
    case Fail{e}:
      Fail{e}
    case Done{stk}:
      Eval.fin.one(stk)

def Eval.fin(s: EvSt) -> C.Frame & E.ResT(Slot):
  match s:
    case EvSt{f, r}:
      (f, Eval.fin.r(r))

# ---- entry points ---------------------------------------------------------------------------

def Eval.slot.h(+e: X.Expr, r: C.Frame & U32) -> C.Frame & E.ResT(Slot):
  (f, +h) = r
  Eval.fin(Eval.run(Eval.compile(e, Nil{}), h, EvSt{f, Done{Nil{}}}))

def Eval.slot.t(+e: X.Expr, f: C.Frame, t: E.Res(D.DType)) -> C.Frame & E.ResT(Slot):
  match t:
    case Fail{err}:
      (f, Fail{err})
    case Done{t2}:
      Eval.slot.h(e, C.Frame.height(f))

def Eval.slot.s(+e: X.Expr, r: C.Frame & List<&2, S.Field>) -> C.Frame & E.ResT(Slot):
  (f, s) = r
  Eval.slot.t(e, f, X.Expr.type(e, s))

# type check e against the frame's schema, then evaluate it to a kinded slot
def Eval.slot(f: C.Frame, +e: X.Expr) -> C.Frame & E.ResT(Slot):
  Eval.slot.s(e, S.Frame.schema(f))

# the column of a slot: a literal broadcasts to the height h; an aggregation
# stays 1 row unless `full`
def Eval.unslot.k(full: Bool, k: SKind) -> SKind:
  match full k:
    case True{} _:
      k
    case False{} KLit{}:
      KLit{}
    case False{} _:
      KFull{}

def Eval.unslot(+h: U32, full: Bool, s: Slot) -> C.Column:
  match s:
    case Slot{k, c}:
      Eval.fit(Eval.unslot.k(full, k), c, h)

def Eval.mode.b(+full: Bool, rs: E.ResT(Slot), r: C.Frame & U32) -> C.Frame & E.ResT(C.Column):
  match rs:
    case Fail{e}:
      (f, h) = r
      (f, Fail{e})
    case Done{s}:
      (f, +h) = r
      (f, Done{Eval.unslot(h, full, s)})

def Eval.mode.a(+full: Bool, r: C.Frame & E.ResT(Slot)) -> C.Frame & E.ResT(C.Column):
  (f, rs) = r
  Eval.mode.b(full, rs, C.Frame.height(f))

# the frame comes back unchanged; Col clones (Frame.get_cloned); a literal-only
# result has the frame's height; an aggregation answers a 1-row column
def Eval.expr(f: C.Frame, e: X.Expr) -> C.Frame & E.ResT(C.Column):
  Eval.mode.a(False{}, Eval.slot(f, e))

# like Eval.expr, but every 1-row result (literal or aggregation) is broadcast
# to the frame's height (with_columns / filter semantics)
def Eval.full(f: C.Frame, e: X.Expr) -> C.Frame & E.ResT(C.Column):
  Eval.mode.a(True{}, Eval.slot(f, e))

def Eval.scalar.b(r: C.Column & D.Scalar) -> E.Res(D.Scalar):
  (c, s) = r
  Done{s}

def Eval.scalar.a(r: C.Frame & E.ResT(C.Column)) -> E.Res(D.Scalar):
  (f, rc) = r
  match rc:
    case Fail{e}:
      Fail{e}
    case Done{c}:
      Eval.scalar.b(C.Column.cell(c, 0))

# constant folding: evaluate e over a 1-row frame with no columns
def Eval.scalar(e: X.Expr) -> E.Res(D.Scalar):
  Eval.scalar.a(Eval.expr(C.Frame{1, Nil{}}, e))

# ---- eager frame ops: select / with_columns / filter ------------------------------------------

# the first type error of a list of expressions (list order)
def Eval.check.k(r: E.Res(D.DType), rest: Maybe<&2, E.Err>) -> Maybe<&2, E.Err>:
  match r:
    case Fail{e}:
      Some{e}
    case Done{t}:
      rest

def Eval.check(es: List<&2, X.Expr>, +s: List<&2, S.Field>) -> Maybe<&2, E.Err>:
  match es:
    case Nil{}:
      None{}
    case e <> t:
      Eval.check.k(X.Expr.type(e, s), Eval.check(t, s))

def Eval.names(es: List<&2, X.Expr>) -> List<&2, String>:
  match es:
    case Nil{}:
      Nil{}
    case e <> t:
      X.Expr.name(e) <> Eval.names(t)

def Eval.any_kind(~p: SKind -> Bool, es: List<&2, X.Expr>) -> Bool:
  match es:
    case Nil{}:
      False{}
    case e <> t:
      Bool.or(p(Eval.kind(e)), Eval.any_kind(~p, t))

# select's height (Polars): h if any output is a real column, else 1 (an
# agg-select, or literals only)
def Eval.target(+es: List<&2, X.Expr>, +h: U32) -> U32:
  Bool.pick(U32, Eval.any_kind(~(k => SKind.is_full(k)), es), h, 1)

def Eval.many.out(name: String, s: Slot) -> Out:
  match s:
    case Slot{k, c}:
      Out{name, k, c}

def Eval.many.add2(+name: String, acc: List<&1, Out>, rs: E.ResT(Slot), f: C.Frame) -> SelSt:
  match rs:
    case Fail{e}:
      SelSt{f, Fail{e}}
    case Done{s}:
      SelSt{f, Done{Eval.many.out(name, s) <> acc}}

def Eval.many.add(+name: String, acc: List<&1, Out>, r: C.Frame & E.ResT(Slot)) -> SelSt:
  (f, rs) = r
  Eval.many.add2(name, acc, rs, f)

def Eval.many.step.r(+e: X.Expr, f: C.Frame, r: E.ResT(List<&1, Out>)) -> SelSt:
  match r:
    case Fail{err}:
      SelSt{f, Fail{err}}
    case Done{acc}:
      Eval.many.add(X.Expr.name(e), acc, Eval.slot(f, e))

def Eval.many.step(e: X.Expr, st: SelSt) -> SelSt:
  match st:
    case SelSt{f, r}:
      Eval.many.step.r(e, f, r)

# evaluate every expression against the same frame; outputs newest first
def Eval.many(es: List<&2, X.Expr>, st: SelSt) -> SelSt:
  match es:
    case Nil{}:
      st
    case e <> t:
      Eval.many(t, Eval.many.step(e, st))

# outputs (newest first) into named columns in expression order, every 1-row
# output broadcast to n rows
def Eval.outs(outs: List<&1, Out>, +n: U32, acc: List<&1, C.Named>) -> List<&1, C.Named>:
  match outs:
    case Nil{}:
      acc
    case Out{name, k, c} <> t:
      Eval.outs(t, n, C.Named{name, Eval.fit(k, c, n)} <> acc)

def Eval.select.d(+es: List<&2, X.Expr>, r: E.ResT(List<&1, Out>), fh: C.Frame & U32) -> E.ResT(C.Frame):
  match r:
    case Fail{e}:
      Fail{e}
    case Done{outs}:
      (f, +h) = fh
      C.Frame.from_columns(Eval.outs(outs, Eval.target(es, h), Nil{}))

def Eval.select.c(+es: List<&2, X.Expr>, st: SelSt) -> E.ResT(C.Frame):
  match st:
    case SelSt{f, r}:
      Eval.select.d(es, r, C.Frame.height(f))

def Eval.select.b(chk: Maybe<&2, E.Err>, f: C.Frame, +es: List<&2, X.Expr>) -> E.ResT(C.Frame):
  match chk:
    case Some{e}:
      Fail{e}
    case None{}:
      Eval.select.c(es, Eval.many(es, SelSt{f, Done{Nil{}}}))

def Eval.select.a(+es: List<&2, X.Expr>, r: C.Frame & List<&2, S.Field>) -> E.ResT(C.Frame):
  (f, s) = r
  Eval.select.b(Eval.check(es, s), f, es)

# a new frame of the expressions' columns, in order, named by Expr.name.
# Every expression is type checked before anything runs. Mixing real columns
# with 1-row results broadcasts the latter; all-aggregation selects give one
# row. DuplicateColumn on repeated output names, ShapeMismatch on unequal
# lengths. The input frame is consumed.
def Eval.select(f: C.Frame, +es: List<&2, X.Expr>) -> E.ResT(C.Frame):
  Eval.select.a(es, S.Frame.schema(f))

def Eval.wc.put1(r: E.ResT(C.Frame), name: String, c: C.Column) -> E.ResT(C.Frame):
  match r:
    case Fail{e}:
      Fail{e}
    case Done{f}:
      C.Frame.replace(f, name, c)

def Eval.wc.put(cols: List<&1, C.Named>, r: E.ResT(C.Frame)) -> E.ResT(C.Frame):
  match cols:
    case Nil{}:
      r
    case C.Named{n, c} <> t:
      Eval.wc.put(t, Eval.wc.put1(r, n, c))

def Eval.wc.d(r: E.ResT(List<&1, Out>), fh: C.Frame & U32) -> E.ResT(C.Frame):
  match r:
    case Fail{e}:
      Fail{e}
    case Done{outs}:
      (f, +h) = fh
      Eval.wc.put(Eval.outs(outs, h, Nil{}), Done{f})

def Eval.wc.c(st: SelSt) -> E.ResT(C.Frame):
  match st:
    case SelSt{f, r}:
      Eval.wc.d(r, C.Frame.height(f))

def Eval.wc.b(chk: Maybe<&2, E.Err>, f: C.Frame, +es: List<&2, X.Expr>) -> E.ResT(C.Frame):
  match chk:
    case Some{e}:
      Fail{e}
    case None{}:
      Eval.wc.c(Eval.many(es, SelSt{f, Done{Nil{}}}))

def Eval.wc.dup(chk: Maybe<&2, E.Err>, d: Maybe<&2, String>) -> Maybe<&2, E.Err>:
  match chk d:
    case Some{e} _:
      Some{e}
    case None{} Some{n}:
      Some{E.DuplicateColumn{n}}
    case None{} None{}:
      None{}

def Eval.wc.a(+es: List<&2, X.Expr>, r: C.Frame & List<&2, S.Field>) -> E.ResT(C.Frame):
  (f, s) = r
  Eval.wc.b(Eval.wc.dup(Eval.check(es, s), C.Names.dup(Eval.names(es), Nil{}, None{})), f, es)

# Polars with_columns: every expression sees the INPUT frame; results replace
# a column of the same name in place or append in expression order; 1-row
# results (literals, aggregations) broadcast to the height. Type errors first,
# then DuplicateColumn on repeated output names.
def Eval.with_columns(f: C.Frame, +es: List<&2, X.Expr>) -> E.ResT(C.Frame):
  Eval.wc.a(es, S.Frame.schema(f))

# the rows to keep: true AND valid (a null predicate drops the row)
def Eval.pred.v(+n: U32, +d: Nat, v: C.Valid, x: Array<U32>) -> Array<U32> & U32:
  match v:
    case C.AllValid{}:
      (x, n)
    case C.Mask{m}:
      (K.Kernel.mask_and(n, d, x, m), n)

def Eval.pred(c: C.Column) -> Array<U32> & U32:
  match c:
    case C.CBool{n, d, v, x}:
      Eval.pred.v(n, d, v, x)
    case _:
      (Array.new(U32, 0n, 0), 0)

def Eval.filter.q(f: C.Frame, r: Array<U32> & U32) -> E.ResT(C.Frame):
  (m, +kept) = r
  Done{C.Frame.filter_mask(f, m, kept)}

def Eval.filter.p(f: C.Frame, r: Array<U32> & U32) -> E.ResT(C.Frame):
  (m, +n) = r
  Eval.filter.q(f, K.Kernel.popcount(n, m))

def Eval.filter.go2(rc: E.ResT(C.Column), f: C.Frame) -> E.ResT(C.Frame):
  match rc:
    case Fail{e}:
      Fail{e}
    case Done{c}:
      Eval.filter.p(f, Eval.pred(c))

def Eval.filter.go(r: C.Frame & E.ResT(C.Column)) -> E.ResT(C.Frame):
  (f, rc) = r
  Eval.filter.go2(rc, f)

def Eval.filter.t(t: D.DType, f: C.Frame, +pred: X.Expr) -> E.ResT(C.Frame):
  match t:
    case D.TBool{}:
      Eval.filter.go(Eval.full(f, pred))
    case other:
      Fail{E.TypeMismatch{"filter", "bool", D.DType.show(other)}}

def Eval.filter.b(+pred: X.Expr, f: C.Frame, r: E.Res(D.DType)) -> E.ResT(C.Frame):
  match r:
    case Fail{e}:
      Fail{e}
    case Done{t}:
      Eval.filter.t(t, f, pred)

def Eval.filter.a(+pred: X.Expr, r: C.Frame & List<&2, S.Field>) -> E.ResT(C.Frame):
  (f, s) = r
  Eval.filter.b(pred, f, X.Expr.type(pred, s))

# the rows where pred is true (null counts as false), in order; pred must be
# bool (TypeMismatch{"filter", "bool", got}); a 1-row pred broadcasts
def Eval.filter(f: C.Frame, +pred: X.Expr) -> E.ResT(C.Frame):
  Eval.filter.a(pred, S.Frame.schema(f))
