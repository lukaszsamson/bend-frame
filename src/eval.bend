# src/eval.bend -- eager expression evaluation. DESIGN.md 4.7.
#
# Shape: an Expr is type checked against the frame's schema FIRST (the shared
# analysis A.Expr.analyse, src/analysis.bend: strict, every error early), then compiled into a postfix instruction list
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
# default (`Eval.fix`, or written as the default by the op's own masked loop:
# the unary maps, zipv, F4), so the column invariant "an invalid slot holds
# DType.default" is kept by every result. Post-review B1 (DESIGN.md 14): f32 neg
# broke it (+0.0 -> -0.0) and F4 read the slot; src/p0.bend checks it.
#
# Idioms (DESIGN.md section 9): helpers above callers; match only on params;
# pairs taken apart in the next helper's parameter; ~T templates.
import Base
import ./dtype.bend as D
import ./err.bend as E
import ./kernels.bend as K
import ./column.bend as C
import ./strs.bend as ST
import ./schema.bend as S
import ./expr.bend as X
import ./analysis.bend as A
import ./radix.bend as RD
import ./hcode.bend as H
import ./ranks.bend as R

type SKind is Data:
  KFull{}
  KLit{}
  KAgg{}

type Slot is Type:
  Slot{k: SKind, col: C.Column}

# W4 fusion (T4.2, DESIGN.md 16.3): the fused fragments the peephole pass Eval.fuse emits.
# An operand of a fused fragment: the column on top of the stack (owned), or a column of the
# frame read in place by a borrowing kernel (mv False: borrowed, Frame.lend then Frame.replace;
# mv True: the reference was the column's last (Eval.mark's IMove), the stand-in stays)
type Opd is Data:
  OStk{}
  ORef{name: String, mv: Bool}

# the pre-operation of a frame operand folded into the fused loop: none, a cast (F3: fires only
# for the total pairs u32 / i32 / bool -> f32 and the identity), fill_null with a literal (F4:
# fires only for the dtype default; as a pre-operation of a frame column inside Z1 / Z2 it reads the
# null slots as they are, so it relies on the frame column holding the default there: the P0
# invariant every stored column keeps, DESIGN.md 14 "v0.2 post-review: the null-slot invariant";
# Z0 alone resets the slots, so it relies on nothing)
type Pre is Data:
  PNone{}
  PCast{to: D.DType}
  PFill{v: D.Scalar}

# Z0: fill_null(a, default) alone (F4); Z1: a op lit / lit op a (left) with the literal a scalar
# (F1); Z2: a op b, null-propagating arithmetic / comparison in one loop (F2), a total cast folded
# into the template (F3)
type Fz is Data:
  Z0{a: Opd, pa: Pre}
  Z1{op: X.BinOp, v: D.Scalar, left: Bool, a: Opd, pa: Pre}
  Z2{op: X.BinOp, a: Opd, pa: Pre, b: Opd, pb: Pre}

# postfix code of an Expr (Alias compiles to nothing; a typed null literal
# `Cast{Lit{SNull}, t}` compiles to IConst{SNull, t}). Eval.compile emits ICol for every
# column reference (Frame.get_cloned: a copy, the frame keeps the column); the liveness pass
# Eval.mark turns the last reference of a column the operator does not keep into IMove
# (Frame.lend: the column itself, no copy). DESIGN.md 16.2 rule 1. IFz is a fused fragment
# and the code it replaces (Eval.fuse, after Eval.mark; run only by Eval.runz): when the
# fragment's runtime shape has no fused kernel the operands go back and `orig` runs
type Instr is Data:
  IConst{v: D.Scalar, t: D.DType}
  ICol{name: String}
  IUn{op: X.UnOp}
  IBin{op: X.BinOp}
  ICast{to: D.DType}
  ITry{to: D.DType}
  IFill{}
  IAgg{op: X.AggOp}
  IWhen{}
  IIsIn{vals: List<&2, D.Scalar>}
  IClip{lo: D.Scalar, hi: D.Scalar}
  IStr{op: X.StrPredOp, pat: String}
  IMove{name: String}
  IFz{fz: Fz, orig: List<&2, Instr>}

# clip bounds as one Data parameter of a map (words / f32)
type W2 is Data:
  W2{lo: U32, hi: U32}

type F2 is Data:
  F2{lo: F32, hi: F32}

# the second pass of std / var: the mean m and the Neumaier state of the squared deviations
type VS is Data:
  VS{m: F32, s: F32, c: F32}

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
      C.CStr{n, d, C.Mask{Array.new(U32, d, 0)}, ST.SRaw{Array.new(String, d, "")}}

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
      C.CStr{n, d, C.AllValid{}, ST.SRaw{Array.new(String, d, v)}}

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

# M4: a 1-row Str value broadcast next to a Dictionary column becomes a Dictionary of one
# entry (n codes, no n string copies), so `col == lit` codes the literal once and compares
# codes (Eval.zip.dd); every other dtype broadcasts as Eval.bcast does
def Eval.bcd.null(t: D.DType, +n: U32, +d: Nat) -> C.Column:
  match t:
    case D.TStr{}:
      C.CStr{n, d, C.Mask{Array.new(U32, d, 0)}, ST.SDict{Array.new(U32, d, 0), ST.Dict.empty()}}
    case other:
      Eval.const_null(other, n, d)

def Eval.bcd.s(s: D.Scalar, t: D.DType, +n: U32, +d: Nat) -> C.Column:
  match s:
    case D.SStr{v}:
      C.CStr{n, d, C.AllValid{}, ST.Strs.const(d, v)}
    case D.SNull{}:
      Eval.bcd.null(t, n, d)
    case other:
      Eval.const_col.d(other, t, n, d)

def Eval.bcd.b(+n: U32, t: D.DType, r: C.Column & D.Scalar) -> C.Column:
  (c, s) = r
  Eval.bcd.s(s, t, n, K.Kernel.depth_for(n))

def Eval.bcd.a(+n: U32, r: C.Column & D.DType) -> C.Column:
  (c, t) = r
  Eval.bcd.b(n, t, C.Column.cell(c, 0))

def Eval.bcast_dict(c: C.Column, +n: U32) -> C.Column:
  Eval.bcd.a(n, C.Column.dtype(c))

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

def Eval.fix.s2(+n: U32, d: Nat, r: ST.Strs & Array<U32>) -> C.Column:
  (x, m) = r
  C.CStr{n, d, C.Mask{m}, x}

def Eval.fix.s(+n: U32, d: Nat, v: C.Valid, x: ST.Strs) -> C.Column:
  match v:
    case C.AllValid{}:
      C.CStr{n, d, C.AllValid{}, x}
    case C.Mask{m}:
      Eval.fix.s2(n, d, ST.Strs.fix(n, x, m))

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

# ---- the numeric unary maps (post-review B1: the null-slot invariant) ----------------------------
# Over an AllValid column the plain map. Over a Mask, ONE masked loop: Kernel.zipb over the data and
# the mask (both borrowed) writes m[i] != 0 ? f(x[i]) : default, so a null slot of the result holds
# the dtype default whatever f does to the default (f32 neg maps +0.0 to -0.0: before the fix the
# null slot of neg(x) held -0.0, and F4's fill_null(.., 0.0), which only flips the validity, exposed
# it). A valid row is f(x[i]) exactly (a valid -0.0 stays -0.0). The mask comes back as the result's
# validity. Laws: LAWS.bend section 19, un_neg_f32 / un_neg_f32_null / un_neg_f32_valid.

def Eval.un.mi(+n: U32, d: Nat, r: K.ZB<U32, U32, U32>) -> C.Column:
  match r:
    case K.ZB{o, x, m}:
      C.CI32{n, d, C.Mask{m}, o}

def Eval.un.mf(+n: U32, d: Nat, r: K.ZB<F32, U32, F32>) -> C.Column:
  match r:
    case K.ZB{o, x, m}:
      C.CF32{n, d, C.Mask{m}, o}

def Eval.un.ineg(+n: U32, +d: Nat, v: C.Valid, x: Array<U32>) -> C.Column:
  match v:
    case C.AllValid{}:
      C.CI32{n, d, C.AllValid{}, K.Kernel.map(~U32, ~U32, ~(w => U32.sub(0, w)), n, d, x, 0)}
    case C.Mask{m}:
      Eval.un.mi(n, d, K.Kernel.zipb(~U32, ~U32, ~U32, ~(w => k => Bool.pick(U32, U32.is_ne(k, 0), U32.sub(0, w), 0)), n, d, x, m, 0))

def Eval.un.iabs(+n: U32, +d: Nat, v: C.Valid, x: Array<U32>) -> C.Column:
  match v:
    case C.AllValid{}:
      C.CI32{n, d, C.AllValid{}, K.Kernel.map(~U32, ~U32, ~(w => D.I32.mag(D.I32{w})), n, d, x, 0)}
    case C.Mask{m}:
      Eval.un.mi(n, d, K.Kernel.zipb(~U32, ~U32, ~U32, ~(w => k => Bool.pick(U32, U32.is_ne(k, 0), D.I32.mag(D.I32{w}), 0)), n, d, x, m, 0))

def Eval.un.fneg(+n: U32, +d: Nat, v: C.Valid, x: Array<F32>) -> C.Column:
  match v:
    case C.AllValid{}:
      C.CF32{n, d, C.AllValid{}, K.Kernel.map(~F32, ~F32, ~(w => F32.neg(w)), n, d, x, 0.0)}
    case C.Mask{m}:
      Eval.un.mf(n, d, K.Kernel.zipb(~F32, ~U32, ~F32, ~(w => k => Bool.pick(F32, U32.is_ne(k, 0), F32.neg(w), 0.0)), n, d, x, m, 0.0))

def Eval.un.fabs(+n: U32, +d: Nat, v: C.Valid, x: Array<F32>) -> C.Column:
  match v:
    case C.AllValid{}:
      C.CF32{n, d, C.AllValid{}, K.Kernel.map(~F32, ~F32, ~(w => F32.abs(w)), n, d, x, 0.0)}
    case C.Mask{m}:
      Eval.un.mf(n, d, K.Kernel.zipb(~F32, ~U32, ~F32, ~(w => k => Bool.pick(F32, U32.is_ne(k, 0), F32.abs(w), 0.0)), n, d, x, m, 0.0))

def Eval.un.fsqrt(+n: U32, +d: Nat, v: C.Valid, x: Array<F32>) -> C.Column:
  match v:
    case C.AllValid{}:
      C.CF32{n, d, C.AllValid{}, K.Kernel.map(~F32, ~F32, ~(w => F32.sqrt(w)), n, d, x, 0.0)}
    case C.Mask{m}:
      Eval.un.mf(n, d, K.Kernel.zipb(~F32, ~U32, ~F32, ~(w => k => Bool.pick(F32, U32.is_ne(k, 0), F32.sqrt(w), 0.0)), n, d, x, m, 0.0))

def Eval.un.i(op: X.UnOp, +n: U32, +d: Nat, v: C.Valid, x: Array<U32>) -> E.ResT(C.Column):
  match op:
    case X.Neg{}:
      Done{Eval.un.ineg(n, d, v, x)}
    case X.Abs{}:
      Done{Eval.un.iabs(n, d, v, x)}
    case _:
      Fail{Eval.bug("unary op on i32")}

def Eval.un.f(op: X.UnOp, +n: U32, +d: Nat, v: C.Valid, x: Array<F32>) -> E.ResT(C.Column):
  match op:
    case X.Neg{}:
      Done{Eval.un.fneg(n, d, v, x)}
    case X.Abs{}:
      Done{Eval.un.fabs(n, d, v, x)}
    case X.Sqrt{}:
      Done{Eval.un.fsqrt(n, d, v, x)}
    case _:
      Fail{Eval.bug("unary op on f32")}

# len_chars: the number of code points (String.length); a null row holds "" -> 0, the default
# (a Dictionary measures each entry once, then gathers by code: ST.Strs.map)
def Eval.un.s(op: X.UnOp, +n: U32, +d: Nat, v: C.Valid, x: ST.Strs) -> E.ResT(C.Column):
  match op:
    case X.LenChars{}:
      Done{C.CU32{n, d, v, ST.Strs.map(~U32, ~(w => U32.from_nat(String.length(w))), n, d, x, 0)}}
    case _:
      Fail{Eval.bug("unary op on str")}

def Eval.un.v(op: X.UnOp, c: C.Column) -> E.ResT(C.Column):
  match c:
    case C.CBool{n, d, v, x}:
      Eval.un.b(op, n, d, v, x)
    case C.CI32{n, d, v, x}:
      Eval.un.i(op, n, d, v, x)
    case C.CF32{n, d, v, x}:
      Eval.un.f(op, n, d, v, x)
    case C.CStr{n, d, v, x}:
      Eval.un.s(op, n, d, v, x)
    case _:
      Fail{Eval.bug("unary op")}

# Neg/Abs (i32, f32), Not (bool), Sqrt (f32): null in, null out (the mask is kept as is). Every
# result's null slots hold the dtype default: neg/abs/sqrt write it in their masked loop (f32 neg of
# the default +0.0 is -0.0, so "the default again" does NOT hold: post-review B1), Not is fixed
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
    case X.FloorDiv{}:
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

# f32 comparisons by the total order of DESIGN.md 15.5.2 (K.Kernel.fword: NaN == NaN and
# greatest, -0.0 == 0.0), the relation sort, group_by and n_unique use too
def Eval.zip.fc(op: X.BinOp, +n: U32, +d: Nat, a: Array<F32>, b: Array<F32>) -> Array<U32>:
  match op:
    case X.Ne{}:
      K.Kernel.zip(~F32, ~F32, ~U32, ~(x => y => Bool.to_u32(U32.is_ne(K.Kernel.fword(x), K.Kernel.fword(y)))), n, d, a, b, 0)
    case X.Lt{}:
      K.Kernel.zip(~F32, ~F32, ~U32, ~(x => y => Bool.to_u32(U32.is_lt(K.Kernel.fword(x), K.Kernel.fword(y)))), n, d, a, b, 0)
    case X.Le{}:
      K.Kernel.zip(~F32, ~F32, ~U32, ~(x => y => Bool.to_u32(U32.is_le(K.Kernel.fword(x), K.Kernel.fword(y)))), n, d, a, b, 0)
    case X.Gt{}:
      K.Kernel.zip(~F32, ~F32, ~U32, ~(x => y => Bool.to_u32(U32.is_gt(K.Kernel.fword(x), K.Kernel.fword(y)))), n, d, a, b, 0)
    case X.Ge{}:
      K.Kernel.zip(~F32, ~F32, ~U32, ~(x => y => Bool.to_u32(U32.is_ge(K.Kernel.fword(x), K.Kernel.fword(y)))), n, d, a, b, 0)
    case _:
      K.Kernel.zip(~F32, ~F32, ~U32, ~(x => y => Bool.to_u32(U32.is_eq(K.Kernel.fword(x), K.Kernel.fword(y)))), n, d, a, b, 0)

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

# ---- Str comparisons over the two storages (M4) ----------------------------------------------
# Raw x Raw: per row (Eval.zip.s). Dictionary x Dictionary: == / != compare codes, directly when
# the two dictionaries are the same (tag, then every entry verified), else after re-coding the
# smaller dictionary into the larger (an entry the larger lacks gets Dict.miss(), never equal
# to a code); < <= > >= compare ranks: the second dictionary is merged into the first and the
# merged entries are ranked once (R.Rk.dict, the rank stage of src/ranks.bend: code points, a
# prefix first, the order String.is_lt implements). Mixed storages decode the Dictionary side.

def Eval.zd.snd(r: Array<U32> & Array<U32>) -> Array<U32>:
  (a, b) = r
  a

# out[i] = m[c[i]]
def Eval.zd.map(+n: U32, +d: Nat, m: Array<U32>, c: Array<U32>) -> Array<U32>:
  Eval.zd.snd(K.Kernel.gather(~U32, n, d, m, c, 0))

def Eval.zd.eq.r(op: X.BinOp, +n: U32, +d: Nat, ca: Array<U32>, cb: Array<U32>, r: ST.Dict & ST.Dict & Array<U32>) -> Array<U32>:
  (db, da, m) = r
  Eval.zip.u(op, n, d, ca, Eval.zd.map(n, d, m, cb))

def Eval.zd.eq.l(op: X.BinOp, +n: U32, +d: Nat, ca: Array<U32>, cb: Array<U32>, r: ST.Dict & ST.Dict & Array<U32>) -> Array<U32>:
  (da, db, m) = r
  Eval.zip.u(op, n, d, Eval.zd.map(n, d, m, ca), cb)

# re-code the smaller dictionary into the larger, then compare codes
def Eval.zd.eq.n(small_b: Bool, op: X.BinOp, +n: U32, +d: Nat, ca: Array<U32>, da: ST.Dict, cb: Array<U32>, db: ST.Dict) -> Array<U32>:
  match small_b:
    case True{}:
      Eval.zd.eq.r(op, n, d, ca, cb, ST.Dict.recode(db, da))
    case False{}:
      Eval.zd.eq.l(op, n, d, ca, cb, ST.Dict.recode(da, db))

def Eval.zd.eq.s(op: X.BinOp, +n: U32, +d: Nat, ca: Array<U32>, cb: Array<U32>, ra: ST.Dict & U32, rb: ST.Dict & U32) -> Array<U32>:
  (da, +ka) = ra
  (db, +kb) = rb
  Eval.zd.eq.n(U32.is_le(kb, ka), op, n, d, ca, da, cb, db)

def Eval.zd.eq.k(op: X.BinOp, +n: U32, +d: Nat, ca: Array<U32>, cb: Array<U32>, r: ST.Dict & ST.Dict & Bool) -> Array<U32>:
  (da, db, same) = r
  match same:
    case True{}:
      Eval.zip.u(op, n, d, ca, cb)
    case False{}:
      Eval.zd.eq.s(op, n, d, ca, cb, ST.Dict.size(da), ST.Dict.size(db))

def Eval.zd.ord.x(op: X.BinOp, +n: U32, +d: Nat, ca: Array<U32>, cb: Array<U32>, rr: Array<U32> & Array<U32>) -> Array<U32>:
  (r1, r2) = rr
  Eval.zip.u(op, n, d, Eval.zd.map(n, d, r1, ca), Eval.zd.map(n, d, r2, cb))

def Eval.zd.ord.w(op: X.BinOp, +n: U32, +d: Nat, ca: Array<U32>, cb: Array<U32>, mb: Array<U32>, r: ST.Dict & Array<U32>) -> Array<U32>:
  (dm, rk) = r
  Eval.zd.ord.x(op, n, d, ca, Eval.zd.map(n, d, mb, cb), Array.clone(U32, rk))

def Eval.zd.ord.m(op: X.BinOp, +n: U32, +d: Nat, ca: Array<U32>, cb: Array<U32>, r: ST.Dict & ST.Dict & Array<U32>) -> Array<U32>:
  (db, dm, mb) = r
  Eval.zd.ord.w(op, n, d, ca, cb, mb, R.Rk.dict(dm))

# both sides ranked in the order of the merged entries (a's codes are kept by the merge)
def Eval.zd.ord(op: X.BinOp, +n: U32, +d: Nat, ca: Array<U32>, da: ST.Dict, cb: Array<U32>, db: ST.Dict) -> Array<U32>:
  Eval.zd.ord.m(op, n, d, ca, cb, ST.Dict.merge(db, da))

def Eval.zip.dd(op: X.BinOp, +n: U32, +d: Nat, ca: Array<U32>, da: ST.Dict, cb: Array<U32>, db: ST.Dict) -> Array<U32>:
  match op:
    case X.Eq{}:
      Eval.zd.eq.k(X.Eq{}, n, d, ca, cb, ST.Dict.same(da, db))
    case X.Ne{}:
      Eval.zd.eq.k(X.Ne{}, n, d, ca, cb, ST.Dict.same(da, db))
    case other:
      Eval.zd.ord(other, n, d, ca, da, cb, db)

def Eval.zip.str(op: X.BinOp, +n: U32, +d: Nat, xa: ST.Strs, xb: ST.Strs) -> Array<U32>:
  match xa xb:
    case ST.SDict{ca, da} ST.SDict{cb, db}:
      Eval.zip.dd(op, n, d, ca, da, cb, db)
    case a b:
      Eval.zip.s(op, n, d, ST.Strs.decode(n, d, a), ST.Strs.decode(n, d, b))

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

# state word -> (value, 1) if known (valid), else (0, 0): r AND ok is r's value bit when r >= 2
# and 0 otherwise (an unboxed K.R, no per-row Maybe: W1d)
def Eval.kl.r.k(+ok: U32, +r: U32) -> K.R<U32>:
  K.R{U32.and(r, ok), ok}

def Eval.kl.r(+r: U32) -> K.R<U32>:
  Eval.kl.r.k(Bool.to_u32(U32.is_ge(r, 2)), r)

def Eval.kl.fin(+n: U32, +d: Nat, r: Array<U32> & Array<U32>) -> C.Column:
  (x, ok) = r
  C.CBool{n, d, Eval.cast.allv(n, K.Kernel.popcount(n, ok)), x}

def Eval.kleene(is_and: Bool, +n: U32, +d: Nat, va: C.Valid, vb: C.Valid, xa: Array<U32>, xb: Array<U32>) -> C.Column:
  Eval.kl.fin(n, d, K.Kernel.map_r(~U32, ~U32, ~(r => Eval.kl.r(r)), n, d, Eval.kl.st(is_and, n, d, Eval.kl.enc(n, d, va, xa), Eval.kl.enc(n, d, vb, xb)), 0))

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

# ---- integer floor_div / mod (DESIGN.md 15.5.1): null on a zero divisor --------------------

# a validity AND an ok mask (0 where a conversion / division failed); AllValid if every row is set
def Eval.okv(+n: U32, +d: Nat, v: C.Valid, ok: Array<U32>) -> C.Valid:
  match v:
    case C.AllValid{}:
      Eval.cast.allv(n, K.Kernel.popcount(n, ok))
    case C.Mask{m}:
      Eval.cast.allv(n, K.Kernel.popcount(n, K.Kernel.mask_and(n, d, ok, m)))

def Eval.is_idiv(op: X.BinOp) -> Bool:
  match op:
    case X.FloorDiv{}:
      True{}
    case X.Mod{}:
      True{}
    case _:
      False{}

# the per-row results are unboxed K.R records (W1d): (quotient / remainder, 1), or (0, 0) on a
# zero divisor (and for i32 MIN // -1). u32: the value is computed for every row and masked by ok
# (U32.div / U32.mod by 0 are defined: 0 and x). i32: a match on the failure test, as in
# D.I32.floor_div.k / floor_mod.k (the same terms; measured: computing the i32 quotient on every row
# and masking is ~15% slower than branching around it)
def Eval.u_fdiv(+x: U32, +y: U32) -> K.R<U32>:
  K.Kernel.r_w(Bool.to_u32(U32.is_ne(y, 0)), U32.div(x, y))

def Eval.u_fmod(+x: U32, +y: U32) -> K.R<U32>:
  K.Kernel.r_w(Bool.to_u32(U32.is_ne(y, 0)), U32.mod(x, y))

def Eval.i_res(q: D.I32) -> K.R<U32>:
  match q:
    case D.I32{w}:
      K.R{w, 1}

def Eval.i_fdiv.k(none: Bool, +x: U32, +y: U32) -> K.R<U32>:
  match none:
    case True{}:
      K.R{0, 0}
    case False{}:
      +mx = D.I32.mag(D.I32{x})
      +my = D.I32.mag(D.I32{y})
      Eval.i_res(D.I32.floor_div.q(Bool.xor(U32.is_ge(x, 2147483648), U32.is_ge(y, 2147483648)), U32.div(mx, my), U32.is_zero(U32.mod(mx, my))))

def Eval.i_fdiv(+x: U32, +y: U32) -> K.R<U32>:
  Eval.i_fdiv.k(Bool.or(U32.is_zero(y), Bool.and(U32.is_eq(x, 2147483648), U32.is_eq(y, 4294967295))), x, y)

def Eval.i_fmod.k(none: Bool, +x: U32, +y: U32) -> K.R<U32>:
  match none:
    case True{}:
      K.R{0, 0}
    case False{}:
      +my = D.I32.mag(D.I32{y})
      +yneg = U32.is_ge(y, 2147483648)
      Eval.i_res(D.I32.floor_mod.r(yneg, Bool.xor(U32.is_ge(x, 2147483648), yneg), my, U32.mod(D.I32.mag(D.I32{x}), my)))

def Eval.i_fmod(+x: U32, +y: U32) -> K.R<U32>:
  Eval.i_fmod.k(U32.is_zero(y), x, y)

# (quotient or remainder words, ok words)
def Eval.zip.ud(op: X.BinOp, +n: U32, +d: Nat, a: Array<U32>, b: Array<U32>) -> Array<U32> & Array<U32>:
  match op:
    case X.Mod{}:
      K.Kernel.zip_r(~U32, ~U32, ~U32, ~(x => y => Eval.u_fmod(x, y)), n, d, a, b, 0)
    case _:
      K.Kernel.zip_r(~U32, ~U32, ~U32, ~(x => y => Eval.u_fdiv(x, y)), n, d, a, b, 0)

def Eval.zip.id(op: X.BinOp, +n: U32, +d: Nat, a: Array<U32>, b: Array<U32>) -> Array<U32> & Array<U32>:
  match op:
    case X.Mod{}:
      K.Kernel.zip_r(~U32, ~U32, ~U32, ~(x => y => Eval.i_fmod(x, y)), n, d, a, b, 0)
    case _:
      K.Kernel.zip_r(~U32, ~U32, ~U32, ~(x => y => Eval.i_fdiv(x, y)), n, d, a, b, 0)

def Eval.bin.idiv(t: D.DType, +n: U32, +d: Nat, v: C.Valid, r: Array<U32> & Array<U32>) -> E.ResT(C.Column):
  (x, ok) = r
  Done{Eval.fix(C.Column.mk_w(t, n, d, Eval.okv(n, d, v, ok), x))}

def Eval.bin.u(idiv: Bool, +op: X.BinOp, +n: U32, +d: Nat, v: C.Valid, xa: Array<U32>, xb: Array<U32>) -> E.ResT(C.Column):
  match idiv:
    case True{}:
      Eval.bin.idiv(D.TU32{}, n, d, v, Eval.zip.ud(op, n, d, xa, xb))
    case False{}:
      Eval.bin.w(Eval.bin.t(Eval.is_cmp(op), D.TU32{}), n, d, v, Eval.zip.u(op, n, d, xa, xb))

def Eval.bin.i(idiv: Bool, +op: X.BinOp, +n: U32, +d: Nat, v: C.Valid, xa: Array<U32>, xb: Array<U32>) -> E.ResT(C.Column):
  match idiv:
    case True{}:
      Eval.bin.idiv(D.TI32{}, n, d, v, Eval.zip.id(op, n, d, xa, xb))
    case False{}:
      Eval.bin.w(Eval.bin.t(Eval.is_cmp(op), D.TI32{}), n, d, v, Eval.zip.i(op, n, d, xa, xb))

# a op b over two columns of the same dtype and length n (the depth of a is
# the output's); validity = AND of both (Kleene for bool and/or); integer
# floor_div / mod also null the rows with a zero divisor (and i32 MIN // -1)
def Eval.bin(+op: X.BinOp, a: C.Column, b: C.Column) -> E.ResT(C.Column):
  match a b:
    case C.CBool{+n, +d, va, xa} C.CBool{n2, d2, vb, xb}:
      Eval.bin.bool(op, n, d, va, vb, xa, xb)
    case C.CU32{+n, +d, va, xa} C.CU32{n2, d2, vb, xb}:
      Eval.bin.u(Eval.is_idiv(op), op, n, d, Eval.vand(n, d, va, vb), xa, xb)
    case C.CI32{+n, +d, va, xa} C.CI32{n2, d2, vb, xb}:
      Eval.bin.i(Eval.is_idiv(op), op, n, d, Eval.vand(n, d, va, vb), xa, xb)
    case C.CF32{+n, +d, va, xa} C.CF32{n2, d2, vb, xb}:
      Eval.bin.f(Eval.is_cmp(op), op, n, d, Eval.vand(n, d, va, vb), xa, xb)
    case C.CStr{+n, +d, va, xa} C.CStr{n2, d2, vb, xb}:
      Eval.bin.w(D.TBool{}, n, d, Eval.vand(n, d, va, vb), Eval.zip.str(op, n, d, xa, xb))
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
  Done{C.CStr{n, d, v, ST.SRaw{x}}}

def Eval.fill.sd2(+n: U32, d: Nat, dict: ST.Dict, r: C.Valid & Array<U32>) -> E.ResT(C.Column):
  (v, x) = r
  Done{C.CStr{n, d, v, ST.SDict{x, dict}}}

def Eval.fill.sd(+n: U32, +d: Nat, va: C.Valid, vb: C.Valid, ca: Array<U32>, cb: Array<U32>, r: ST.Dict & ST.Dict & Array<U32>) -> E.ResT(C.Column):
  (db, da, m) = r
  Eval.fill.sd2(n, d, da, Eval.fill.t(~U32, n, d, va, vb, ca, Eval.zd.map(n, d, m, cb)))

# fill_null over Str: two Dictionaries merge (b's entries into a's), then the codes are chosen;
# otherwise the strings
def Eval.fill.str(+n: U32, +d: Nat, va: C.Valid, vb: C.Valid, xa: ST.Strs, xb: ST.Strs) -> E.ResT(C.Column):
  match xa xb:
    case ST.SDict{ca, da} ST.SDict{cb, db}:
      Eval.fill.sd(n, d, va, vb, ca, cb, ST.Dict.merge(db, da))
    case a b:
      Eval.fill.s(n, d, Eval.fill.t(~String, n, d, va, vb, ST.Strs.decode(n, d, a), ST.Strs.decode(n, d, b)))

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
      Eval.fill.str(n, d, va, vb, xa, xb)
    case _ _:
      Fail{Eval.bug("operand dtypes in fill_null")}

# ---- when / is_in / clip / string predicates (DESIGN.md 15.2.6) ---------------------------

# the second array of a pair (the chosen mask)
def Eval.msnd(r: Array<U32> & Array<U32>) -> Array<U32>:
  (a, b) = r
  b

# the AND of two choices of validity: row i takes a's validity where m[i] is set, else b's;
# AllValid when both are (one pass otherwise, AllValid again when every row is valid). An AllValid
# side is the 1-slot ones array (indices wrap, so it reads 1 at every row, allocates nothing and
# is never written): Kernel.choose writes into its `a` array, so the AllValid-a case is the
# zip (m[i] != 0) | mb[i] over the 0/1 masks instead (one output array, like choose's).
def Eval.when.valid(+n: U32, +d: Nat, va: C.Valid, vb: C.Valid, m: Array<U32>) -> C.Valid:
  match va vb:
    case C.AllValid{} C.AllValid{}:
      C.AllValid{}
    case C.AllValid{} C.Mask{mb}:
      Eval.cast.allv(n, K.Kernel.popcount(n, K.Kernel.zip(~U32, ~U32, ~U32, ~(x => y => U32.or(Bool.to_u32(U32.is_ne(x, 0)), y)), n, d, m, mb, 0)))
    case C.Mask{ma} C.AllValid{}:
      Eval.cast.allv(n, K.Kernel.popcount(n, Eval.msnd(K.Kernel.choose(~U32, n, m, ma, C.Valid.materialize(C.AllValid{}, 0n)))))
    case C.Mask{ma} C.Mask{mb}:
      Eval.cast.allv(n, K.Kernel.popcount(n, Eval.msnd(K.Kernel.choose(~U32, n, m, ma, mb))))

def Eval.when.w(t: D.DType, +n: U32, +d: Nat, va: C.Valid, vb: C.Valid, r: Array<U32> & Array<U32>) -> E.ResT(C.Column):
  (m, x) = r
  Done{C.Column.mk_w(t, n, d, Eval.when.valid(n, d, va, vb, m), x)}

def Eval.when.f(+n: U32, +d: Nat, va: C.Valid, vb: C.Valid, r: Array<U32> & Array<F32>) -> E.ResT(C.Column):
  (m, x) = r
  Done{C.CF32{n, d, Eval.when.valid(n, d, va, vb, m), x}}

def Eval.when.s(+n: U32, +d: Nat, va: C.Valid, vb: C.Valid, r: Array<U32> & Array<String>) -> E.ResT(C.Column):
  (m, x) = r
  Done{C.CStr{n, d, Eval.when.valid(n, d, va, vb, m), ST.SRaw{x}}}

def Eval.when.sd2(+n: U32, +d: Nat, va: C.Valid, vb: C.Valid, dict: ST.Dict, r: Array<U32> & Array<U32>) -> E.ResT(C.Column):
  (m, x) = r
  Done{C.CStr{n, d, Eval.when.valid(n, d, va, vb, m), ST.SDict{x, dict}}}

def Eval.when.sd(+n: U32, +d: Nat, m: Array<U32>, va: C.Valid, vb: C.Valid, ca: Array<U32>, cb: Array<U32>, r: ST.Dict & ST.Dict & Array<U32>) -> E.ResT(C.Column):
  (db, da, mb) = r
  Eval.when.sd2(n, d, va, vb, da, K.Kernel.choose(~U32, n, m, ca, Eval.zd.map(n, d, mb, cb)))

# when over Str: two Dictionaries merge (b's entries into a's) and the codes are chosen;
# otherwise the strings (M4)
def Eval.when.str(+n: U32, +d: Nat, m: Array<U32>, va: C.Valid, vb: C.Valid, xa: ST.Strs, xb: ST.Strs) -> E.ResT(C.Column):
  match xa xb:
    case ST.SDict{ca, da} ST.SDict{cb, db}:
      Eval.when.sd(n, d, m, va, vb, ca, cb, ST.Dict.merge(db, da))
    case a b:
      Eval.when.s(n, d, va, vb, K.Kernel.choose(~String, n, m, ST.Strs.decode(n, d, a), ST.Strs.decode(n, d, b)))

# row i = a[i] where m[i] (cond true and valid), else b[i]; each row keeps the chosen side's
# validity, and a null slot already holds the default on both sides (no fix needed)
def Eval.when.v(m: Array<U32>, a: C.Column, b: C.Column) -> E.ResT(C.Column):
  match a b:
    case C.CBool{+n, +d, va, xa} C.CBool{n2, d2, vb, xb}:
      Eval.when.w(D.TBool{}, n, d, va, vb, K.Kernel.choose(~U32, n, m, xa, xb))
    case C.CU32{+n, +d, va, xa} C.CU32{n2, d2, vb, xb}:
      Eval.when.w(D.TU32{}, n, d, va, vb, K.Kernel.choose(~U32, n, m, xa, xb))
    case C.CI32{+n, +d, va, xa} C.CI32{n2, d2, vb, xb}:
      Eval.when.w(D.TI32{}, n, d, va, vb, K.Kernel.choose(~U32, n, m, xa, xb))
    case C.CF32{+n, +d, va, xa} C.CF32{n2, d2, vb, xb}:
      Eval.when.f(n, d, va, vb, K.Kernel.choose(~F32, n, m, xa, xb))
    case C.CStr{+n, +d, va, xa} C.CStr{n2, d2, vb, xb}:
      Eval.when.str(n, d, m, va, vb, xa, xb)
    case _ _:
      Fail{Eval.bug("operand dtypes in when")}

def Eval.when.m(a: C.Column, b: C.Column, r: Array<U32> & U32) -> E.ResT(C.Column):
  (m, n) = r
  Eval.when.v(m, a, b)

# the condition as a 0/1 mask, "true and valid" (Eval.pred's rule; a non-bool column, which
# typing excludes, selects nothing)
def Eval.when.cv(+n: U32, +d: Nat, v: C.Valid, x: Array<U32>) -> Array<U32> & U32:
  match v:
    case C.AllValid{}:
      (x, n)
    case C.Mask{m}:
      (K.Kernel.mask_and(n, d, x, m), n)

def Eval.when.c(c: C.Column) -> Array<U32> & U32:
  match c:
    case C.CBool{n, d, v, x}:
      Eval.when.cv(n, d, v, x)
    case _:
      (Array.new(U32, 0n, 0), 0)

# when(c).then(a).otherwise(b) over three columns of one length: a null condition picks b
# (the condition's mask is "true and valid", Eval.when.c)
def Eval.when(c: C.Column, a: C.Column, b: C.Column) -> E.ResT(C.Column):
  Eval.when.m(a, b, Eval.when.c(c))

# is_in: w among the words ws (u32 / i32 / bool words, f32 order words)
def Eval.wmem(+w: U32, ws: List<&2, U32>) -> Bool:
  match ws:
    case Nil{}:
      False{}
    case q <> t:
      Bool.or(U32.is_eq(w, q), Eval.wmem(w, t))

def Eval.smem(+s: String, ss: List<&2, String>) -> Bool:
  match ss:
    case Nil{}:
      False{}
    case q <> t:
      Bool.or(String.eq(s, q), Eval.smem(s, t))

# the literals as the words a cell is compared with: u32 as is, i32 bits, bool 0/1, f32 the
# 15.5.2 order word (NaN = NaN, -0.0 = 0.0); str literals and nulls are skipped (typing)
def Eval.isin.words(vs: List<&2, D.Scalar>) -> List<&2, U32>:
  match vs:
    case Nil{}:
      Nil{}
    case D.SBool{b} <> t:
      Bool.to_u32(b) <> Eval.isin.words(t)
    case D.SU32{v} <> t:
      v <> Eval.isin.words(t)
    case D.SI32{v} <> t:
      D.I32.to_u32(v) <> Eval.isin.words(t)
    case D.SF32{v} <> t:
      K.Kernel.fword(v) <> Eval.isin.words(t)
    case other <> t:
      Eval.isin.words(t)

def Eval.isin.strs(vs: List<&2, D.Scalar>) -> List<&2, String>:
  match vs:
    case Nil{}:
      Nil{}
    case D.SStr{v} <> t:
      v <> Eval.isin.strs(t)
    case other <> t:
      Eval.isin.strs(t)

# is_in (15.2.6): true iff some literal equals the cell under the 15.5 relation; a null
# cell is null (its slot is reset to false)
def Eval.isin(vs: List<&2, D.Scalar>, c: C.Column) -> E.ResT(C.Column):
  match c:
    case C.CBool{+n, +d, v, x}:
      Eval.bin.w(D.TBool{}, n, d, v, K.Kernel.map_p(~U32, ~List<&2, U32>, ~U32, ~(p => w => Bool.to_u32(Eval.wmem(w, p))), n, d, x, Eval.isin.words(vs), 0))
    case C.CU32{+n, +d, v, x}:
      Eval.bin.w(D.TBool{}, n, d, v, K.Kernel.map_p(~U32, ~List<&2, U32>, ~U32, ~(p => w => Bool.to_u32(Eval.wmem(w, p))), n, d, x, Eval.isin.words(vs), 0))
    case C.CI32{+n, +d, v, x}:
      Eval.bin.w(D.TBool{}, n, d, v, K.Kernel.map_p(~U32, ~List<&2, U32>, ~U32, ~(p => w => Bool.to_u32(Eval.wmem(w, p))), n, d, x, Eval.isin.words(vs), 0))
    case C.CF32{+n, +d, v, x}:
      Eval.bin.w(D.TBool{}, n, d, v, K.Kernel.map_p(~F32, ~List<&2, U32>, ~U32, ~(p => w => Bool.to_u32(Eval.wmem(K.Kernel.fword(w), p))), n, d, x, Eval.isin.words(vs), 0))
    case C.CStr{+n, +d, v, x}:
      Eval.bin.w(D.TBool{}, n, d, v, ST.Strs.map_p(~List<&2, String>, ~U32, ~(p => w => Bool.to_u32(Eval.smem(w, p))), n, d, x, Eval.isin.strs(vs), 0))

# a numeric literal's word (u32 as is, i32 bits) / f32 value; typing guarantees the dtype
def Eval.sword(s: D.Scalar) -> U32:
  match s:
    case D.SU32{v}:
      v
    case D.SI32{v}:
      D.I32.to_u32(v)
    case _:
      0

def Eval.sf32(s: D.Scalar) -> F32:
  match s:
    case D.SF32{v}:
      v
    case _:
      0.0

# clip (15.2.6): lo if x < lo, else hi if x > hi, else x; f32 with IEEE < and > (NaN passes,
# -0.0 is not clipped by 0.0); lo > hi gives lo below lo and hi otherwise
def Eval.clip.u(p: W2, +x: U32) -> U32:
  match p:
    case W2{+lo, +hi}:
      Bool.pick(U32, U32.is_lt(x, lo), lo, Bool.pick(U32, U32.is_gt(x, hi), hi, x))

def Eval.clip.i(p: W2, +x: U32) -> U32:
  match p:
    case W2{+lo, +hi}:
      Bool.pick(U32, Eval.i32_lt(x, lo), lo, Bool.pick(U32, Eval.i32_lt(hi, x), hi, x))

def Eval.clip.f(p: F2, +x: F32) -> F32:
  match p:
    case F2{+lo, +hi}:
      Bool.pick(F32, F32.is_lt(x, lo), lo, Bool.pick(F32, F32.is_gt(x, hi), hi, x))

# a null row's slot may be clipped away from the default: Eval.fix resets it
def Eval.clip(+lo: D.Scalar, +hi: D.Scalar, c: C.Column) -> E.ResT(C.Column):
  match c:
    case C.CU32{+n, +d, v, x}:
      Done{Eval.fix(C.CU32{n, d, v, K.Kernel.map_p(~U32, ~W2, ~U32, ~(p => w => Eval.clip.u(p, w)), n, d, x, W2{Eval.sword(lo), Eval.sword(hi)}, 0)})}
    case C.CI32{+n, +d, v, x}:
      Done{Eval.fix(C.CI32{n, d, v, K.Kernel.map_p(~U32, ~W2, ~U32, ~(p => w => Eval.clip.i(p, w)), n, d, x, W2{Eval.sword(lo), Eval.sword(hi)}, 0)})}
    case C.CF32{+n, +d, v, x}:
      Done{Eval.fix(C.CF32{n, d, v, K.Kernel.map_p(~F32, ~F2, ~F32, ~(p => w => Eval.clip.f(p, w)), n, d, x, F2{Eval.sf32(lo), Eval.sf32(hi)}, 0.0)})}
    case _:
      Fail{Eval.bug("clip of a non-numeric column")}

# the literal string predicates: case-sensitive, code-point equality, an empty pattern is true
# (a Dictionary tests each entry once, then gathers by code: ST.Strs.map_p)
def Eval.strpred.k(op: X.StrPredOp, +n: U32, +d: Nat, x: ST.Strs, +pat: String) -> Array<U32>:
  match op:
    case X.Contains{}:
      ST.Strs.map_p(~String, ~U32, ~(p => w => Bool.to_u32(String.contains(w, p))), n, d, x, pat, 0)
    case X.StartsWith{}:
      ST.Strs.map_p(~String, ~U32, ~(p => w => Bool.to_u32(String.starts_with(w, p))), n, d, x, pat, 0)
    case X.EndsWith{}:
      ST.Strs.map_p(~String, ~U32, ~(p => w => Bool.to_u32(String.ends_with(w, p))), n, d, x, pat, 0)

def Eval.strpred(op: X.StrPredOp, +pat: String, c: C.Column) -> E.ResT(C.Column):
  match c:
    case C.CStr{+n, +d, v, x}:
      Eval.bin.w(D.TBool{}, n, d, v, Eval.strpred.k(op, n, d, x, pat))
    case _:
      Fail{Eval.bug("string predicate over a non-str column")}

# ---- cast ---------------------------------------------------------------------------------

def Eval.cast.err(t: D.DType, +to: D.DType) -> E.ResT(C.Column):
  Fail{E.TypeMismatch{"cast", "castable to " ++ D.DType.show(to), D.DType.show(t)}}

# a fallible conversion's (words, ok): failing rows become null
def Eval.cast.pw(t: D.DType, +n: U32, +d: Nat, v: C.Valid, r: Array<U32> & Array<U32>) -> E.ResT(C.Column):
  (x, ok) = r
  Done{Eval.fix(C.Column.mk_w(t, n, d, Eval.okv(n, d, v, ok), x))}

def Eval.cast.pf(+n: U32, +d: Nat, v: C.Valid, r: Array<F32> & Array<U32>) -> E.ResT(C.Column):
  (x, ok) = r
  Done{Eval.fix(C.CF32{n, d, Eval.okv(n, d, v, ok), x})}

# The per-row conversion results are unboxed K.R records (W1d): (bits, 1), or (0, 0) on a
# failure (the converted word is computed for every row and masked by ok).
# u32 -> i32 and i32 -> u32 (DESIGN.md 15.5.5): the same bits when bit 31 is clear
def Eval.lo31(+w: U32) -> K.R<U32>:
  K.Kernel.r_w(Bool.to_u32(U32.is_lt(w, 2147483648)), w)

# f32 -> u32: trunc(x) when -1.0 < x < 4294967296.0 (both bounds exact in f32; NaN fails)
def Eval.f2u(+x: F32) -> K.R<U32>:
  K.Kernel.r_w(Bool.to_u32(Bool.and(F32.is_gt(x, F32.neg(1.0)), F32.is_lt(x, 4294967296.0))), F32.to_u32(x))

# f32 -> i32: trunc(x) toward zero when -2147483648.0 <= x < 2147483648.0 (NaN fails)
def Eval.f2i_m(+x: F32) -> K.R<U32>:
  K.Kernel.r_w(Bool.to_u32(Bool.and(F32.is_ge(x, F32.neg(2147483648.0)), F32.is_lt(x, 2147483648.0))), Eval.f2i(x))

# ---- conversions: the try_cast semantics (a failing valid cell becomes null) ------------------

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
      Done{Eval.fix(C.CStr{n, d, v, ST.SRaw{K.Kernel.map(~U32, ~String, ~(w => Eval.show_bool(w)), n, d, x, "")}})}

def Eval.cast.u(+to: D.DType, +n: U32, +d: Nat, v: C.Valid, x: Array<U32>) -> E.ResT(C.Column):
  match to:
    case D.TU32{}:
      Done{C.CU32{n, d, v, x}}
    case D.TI32{}:
      Eval.cast.pw(D.TI32{}, n, d, v, K.Kernel.map_r(~U32, ~U32, ~(w => Eval.lo31(w)), n, d, x, 0))
    case D.TF32{}:
      Done{C.CF32{n, d, v, K.Kernel.map(~U32, ~F32, ~(w => U32.to_f32(w)), n, d, x, 0.0)}}
    case D.TStr{}:
      Done{Eval.fix(C.CStr{n, d, v, ST.SRaw{K.Kernel.map(~U32, ~String, ~(w => U32.show(w)), n, d, x, "")}})}
    case D.TBool{}:
      Eval.cast.err(D.TU32{}, to)

def Eval.cast.i(+to: D.DType, +n: U32, +d: Nat, v: C.Valid, x: Array<U32>) -> E.ResT(C.Column):
  match to:
    case D.TU32{}:
      Eval.cast.pw(D.TU32{}, n, d, v, K.Kernel.map_r(~U32, ~U32, ~(w => Eval.lo31(w)), n, d, x, 0))
    case D.TI32{}:
      Done{C.CI32{n, d, v, x}}
    case D.TF32{}:
      Done{C.CF32{n, d, v, K.Kernel.map(~U32, ~F32, ~(w => D.I32.to_f32(D.I32{w})), n, d, x, 0.0)}}
    case D.TStr{}:
      Done{Eval.fix(C.CStr{n, d, v, ST.SRaw{K.Kernel.map(~U32, ~String, ~(w => D.I32.show(D.I32{w})), n, d, x, "")}})}
    case D.TBool{}:
      Eval.cast.err(D.TI32{}, to)

def Eval.cast.f(+to: D.DType, +n: U32, +d: Nat, v: C.Valid, x: Array<F32>) -> E.ResT(C.Column):
  match to:
    case D.TU32{}:
      Eval.cast.pw(D.TU32{}, n, d, v, K.Kernel.map_r(~F32, ~U32, ~(w => Eval.f2u(w)), n, d, x, 0))
    case D.TI32{}:
      Eval.cast.pw(D.TI32{}, n, d, v, K.Kernel.map_r(~F32, ~U32, ~(w => Eval.f2i_m(w)), n, d, x, 0))
    case D.TF32{}:
      Done{C.CF32{n, d, v, x}}
    case D.TStr{}:
      Done{Eval.fix(C.CStr{n, d, v, ST.SRaw{K.Kernel.map(~F32, ~String, ~(w => F32.show(w)), n, d, x, "")}})}
    case D.TBool{}:
      Eval.cast.err(D.TF32{}, to)

# F32.read of the text as is; Base's F32.read skips LEADING whitespace (" 3" reads as 3),
# so a cell starting with a space, TAB, CR or LF is refused here: the cast does not trim
# (DESIGN.md 15.5.5 D:, Polars; recorded in DESIGN.md 14 B03)
def Eval.read_f32.k(ws: Bool, s: String) -> Maybe<&2, F32>:
  match ws:
    case True{}:
      None{}
    case False{}:
      F32.read(s)

def Eval.lead_ws(s: String) -> Bool:
  match s:
    case SCon{Chr{+c}, t}:
      Bool.or(Bool.or(U32.is_eq(c, 32), U32.is_eq(c, 9)), Bool.or(U32.is_eq(c, 10), U32.is_eq(c, 13)))
    case SNil{}:
      False{}

def Eval.read_f32(+s: String) -> Maybe<&2, F32>:
  Eval.read_f32.k(Eval.lead_ws(s), s)

# Str -> number / bool reads the text AS IS (DESIGN.md 15.5.5, no trimming): U32.read,
# I32.read, F32.read, true/false/True/False; a cell that does not read is a failure
# (a Dictionary reads each distinct entry once, then gathers by code: ST.Strs.map_r; the readers
# answer a Maybe, turned into a K.R per entry by K.Kernel.r_of)
def Eval.cast.s(+to: D.DType, +n: U32, +d: Nat, v: C.Valid, x: ST.Strs) -> E.ResT(C.Column):
  match to:
    case D.TStr{}:
      Done{C.CStr{n, d, v, x}}
    case D.TU32{}:
      Eval.cast.pw(D.TU32{}, n, d, v, ST.Strs.map_r(~U32, ~(s => K.Kernel.r_of(~U32, U32.read(s), 0)), n, d, x, 0))
    case D.TI32{}:
      Eval.cast.pw(D.TI32{}, n, d, v, ST.Strs.map_r(~U32, ~(s => K.Kernel.r_of(~U32, Eval.i32_bits(D.I32.read(s)), 0)), n, d, x, 0))
    case D.TBool{}:
      Eval.cast.pw(D.TBool{}, n, d, v, ST.Strs.map_r(~U32, ~(s => K.Kernel.r_of(~U32, Eval.read_bool(s), 0)), n, d, x, 0))
    case D.TF32{}:
      Eval.cast.pf(n, d, v, ST.Strs.map_r(~F32, ~(s => K.Kernel.r_of(~F32, Eval.read_f32(s), 0.0)), n, d, x, 0.0))

# try_cast (DESIGN.md 15.5.5): every valid cell converted, a failing one becomes null;
# nulls pass. For a total pair (X.Cast.total) this is also what cast does.
def Eval.try_cast(+to: D.DType, c: C.Column) -> E.ResT(C.Column):
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

# ---- strict cast: the first failing valid cell is an error ---------------------------------

def Eval.cast.fail.c(+from: D.DType, +to: D.DType, +i: U32, r: C.Column & D.Scalar) -> E.Err:
  (c, s) = r
  E.InvalidOperation{"cast " ++ D.DType.show(from) ++ " to " ++ D.DType.show(to) ++ ": row " ++ U32.show(i) ++ " holds " ++ X.Expr.show.lit(s)}

def Eval.cast.fail.b(+from: D.DType, +to: D.DType, src: C.Column, +i: U32) -> E.Err:
  Eval.cast.fail.c(from, to, i, C.Column.data_cell(src, i))

def Eval.cast.fail.a(+from: D.DType, +to: D.DType, +n: U32, rs: C.Column & C.Valid, rt: C.Column & C.Valid) -> E.Err:
  (src, vs) = rs
  (tc, vt) = rt
  Eval.cast.fail.b(from, to, src, K.Kernel.first_drop(n, C.Valid.materialize(vs, 0n), C.Valid.materialize(vt, 0n)))

def Eval.cast.fail.n(+from: D.DType, +to: D.DType, tc: C.Column, r: C.Column & U32) -> E.Err:
  (src, +n) = r
  Eval.cast.fail.a(from, to, n, C.Column.take_valid(src), C.Column.take_valid(tc))

# InvalidOperation{"cast <from> to <to>: row <i> holds <cell>"}: i is the first row valid in
# the source and null after the conversion, the cell as Expr.show.lit shows a literal
def Eval.cast.fail(+from: D.DType, +to: D.DType, src: C.Column, tc: C.Column) -> E.Err:
  Eval.cast.fail.n(from, to, tc, C.Column.len(src))

def Eval.cast.cmp2(same: Bool, +from: D.DType, +to: D.DType, src: C.Column, tc: C.Column) -> E.ResT(C.Column):
  match same:
    case True{}:
      Done{tc}
    case False{}:
      Fail{Eval.cast.fail(from, to, src, tc)}

# a conversion only adds nulls: as many nulls as the source means no cell failed
def Eval.cast.cmp(+from: D.DType, +to: D.DType, rs: C.Column & U32, rt: C.Column & U32) -> E.ResT(C.Column):
  (src, ns) = rs
  (tc, nt) = rt
  Eval.cast.cmp2(U32.is_eq(ns, nt), from, to, src, tc)

def Eval.cast.chk2(+from: D.DType, +to: D.DType, src: C.Column, r: E.ResT(C.Column)) -> E.ResT(C.Column):
  match r:
    case Fail{e}:
      Fail{e}
    case Done{tc}:
      Eval.cast.cmp(from, to, C.Column.null_count(src), C.Column.null_count(tc))

def Eval.cast.chk(+from: D.DType, +to: D.DType, r: C.Column & C.Column) -> E.ResT(C.Column):
  (c1, src) = r
  Eval.cast.chk2(from, to, src, Eval.try_cast(to, c1))

def Eval.cast.sel(total: Bool, +from: D.DType, +to: D.DType, c: C.Column) -> E.ResT(C.Column):
  match total:
    case True{}:
      Eval.try_cast(to, c)
    case False{}:
      Eval.cast.chk(from, to, C.Column.clone(c))

def Eval.cast.a(+to: D.DType, r: C.Column & D.DType) -> E.ResT(C.Column):
  (c, +from) = r
  Eval.cast.sel(X.Cast.total(from, to), from, to, c)

# cast (DESIGN.md 15.5.5): strict. A total pair converts directly; a fallible one converts a
# clone with try_cast and compares null counts, so the source is read again only on failure.
def Eval.cast(+to: D.DType, c: C.Column) -> E.ResT(C.Column):
  Eval.cast.a(to, C.Column.dtype(c))

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

# n_unique over Raw strings (v0.2 W2.3): the number of distinct strings among a[0..k) = the
# packed flat coder's entry count (H.Hc.code.pk: first-appearance ids from 0, so next = the
# distinct count; one walk per row hashes and packs it, a hash hit compares flat words; no cons
# list of rows, no sort). The
# caller (Eval.agg -> Eval.dropnull) passes the VALID rows only and adds one for any null
# (DESIGN 15.2.5).
def Eval.nu.str.k(hj: H.HJ) -> U32:
  match hj:
    case H.HJ{next, a, hs, ix, codes, po, pl, pk, cur, pd}:
      next

def Eval.nu.str(+k: U32, a: Array<String>) -> U32:
  Eval.nu.str.k(H.Hc.code.pk(~(h => h), k, K.Kernel.depth_for(k), a))

# n_unique over WORDS (Bool / U32 / I32 as they are, F32 as its 15.5.2 order words): a stable radix
# sort of the words (the sort of Sort / median; the pair's second array is a scratch perm that is
# never read), then ONE flat loop counting the positions that differ from their predecessor. No
# cons list, nothing allocated per row. The words' order does not matter, only their equality.

# 1 + the number of i in [1, k) with ws[i] != ws[i-1] (k >= 1); the loop reads ws[i] as `x` and
# carries the previous word, so it is one native tail loop (Radix.vary.go's shape)
def Eval.nu.runs.go(n: Nat, +i: U32, +prev: U32, acc: U32, r: Array<U32> & U32) -> U32:
  match n:
    case 0n:
      (ws, x) = r
      acc
    case 1n+p:
      (ws, +x) = r
      Eval.nu.runs.go(p, U32.inc(i), x, U32.add(acc, Bool.to_u32(U32.is_ne(x, prev))), Array.get(U32, ws, U32.inc(i)))

def Eval.nu.runs.b(+k: U32, r: Array<U32> & U32) -> U32:
  (ws, +w0) = r
  Eval.nu.runs.go(U32.to_nat(U32.sub(k, 1)), 1, w0, 1, Array.get(U32, ws, 1))

def Eval.nu.runs.z(z: Bool, +k: U32, ws: Array<U32>) -> U32:
  match z:
    case True{}:
      0
    case False{}:
      Eval.nu.runs.b(k, Array.get(U32, ws, 0))

def Eval.nu.sorted(+k: U32, st: Array<U32> & Array<U32>) -> U32:
  (ws, perm) = st
  Eval.nu.runs.z(U32.is_zero(k), k, ws)

# the number of distinct words among ws[0..k)
def Eval.nu.words(+k: U32, ws: Array<U32>) -> U32:
  Eval.nu.sorted(k, RD.Radix.sort(k, K.Kernel.depth_for(k), (ws, Array.new(U32, K.Kernel.depth_for(k), 0))))

# a Bool column has at most two values: presence bits (1 = some false, 2 = some true)
def Eval.nu.bits(+m: U32) -> U32:
  U32.add(U32.and(m, 1), U32.and(U32.shrn(m, 1n), 1))

def Eval.nu.bool(+k: U32, x: Array<U32>) -> U32:
  Eval.nu.bits(Eval.snd(~U32, ~U32, K.Kernel.fold(~U32, ~U32, ~(a => w => U32.or(a, U32.add(1, Bool.to_u32(U32.is_ne(w, 0))))), k, x, 0)))

def Eval.nu.w(t: D.DType, +k: U32, x: Array<U32>) -> U32:
  match t:
    case D.TBool{}:
      Eval.nu.bool(k, x)
    case _:
      Eval.nu.words(k, x)

# ---- std / var / median (DESIGN.md 15.5.4): shared by Eval.agg, GroupBy and describe -------

# one term of the second pass: (x - m)^2, each step in f32
def Eval.sqdev(+x: F32, +m: F32) -> F32:
  +t = F32.sub(x, m)
  F32.mul(t, t)

def Eval.vs.k(+m: F32, r: K.NS) -> VS:
  match r:
    case K.NS{s, c}:
      VS{m, s, c}

def Eval.vs.step(acc: VS, +x: F32) -> VS:
  match acc:
    case VS{+m, +s, +c}:
      Eval.vs.k(m, K.Kernel.nm.add(s, c, Eval.sqdev(x, m)))

def Eval.vs.fin(acc: VS) -> F32:
  match acc:
    case VS{m, +s, +c}:
      K.Kernel.nm.result(s, c)

# the mean of the first pass: the 15.5.3 sum over k
def Eval.mean_f(+k: U32, s: F32) -> F32:
  F32.div(s, U32.to_f32(k))

def Eval.ssd.b(+k: U32, r: Array<F32> & K.NS) -> F32:
  (x, ns) = r
  Eval.vs.fin(Eval.snd(~F32, ~VS, K.Kernel.fold(~F32, ~VS, ~(a => w => Eval.vs.step(a, w)), k, x, VS{Eval.mean_f(k, K.Kernel.nm.fin(ns)), 0.0, 0.0})))

# the 15.5.3 sum of (x - m)^2 over a[0..k), m = fsum(a) / k (two passes, ascending order)
def Eval.ssd(+k: U32, x: Array<F32>) -> F32:
  Eval.ssd.b(k, K.Kernel.fold(~F32, ~K.NS, ~(a => w => K.Kernel.nm.step(a, w)), k, x, K.NS{0.0, 0.0}))

# var = ssd / (k - 1); std = sqrt(var); null when k < 2 (ddof = 1)
def Eval.var_of(+k: U32, ssd: F32) -> F32:
  F32.div(ssd, U32.to_f32(U32.sub(k, 1)))

def Eval.stat.v(std: Bool, +k: U32, ssd: F32) -> F32:
  match std:
    case True{}:
      F32.sqrt(Eval.var_of(k, ssd))
    case False{}:
      Eval.var_of(k, ssd)

def Eval.stat.s(std: Bool, +k: U32, ssd: F32) -> D.Scalar:
  Bool.pick(D.Scalar, U32.is_lt(k, 2), D.SNull{}, D.SF32{Eval.stat.v(std, k, ssd)})

# the median of a sorted run sorted[start .. start + k) (k >= 1): the middle cell for an odd k,
# lo*0.5 + hi*0.5 of the two middle cells for an even one (no overflow); the array comes back
def Eval.med.fin(+odd: Bool, +lo: F32, hi: F32) -> F32:
  Bool.pick(F32, odd, lo, F32.add(F32.mul(lo, 0.5), F32.mul(hi, 0.5)))

def Eval.med.hi(+k: U32, +lo: F32, r: Array<F32> & F32) -> Array<F32> & F32:
  (a, hi) = r
  (a, Eval.med.fin(U32.is_eq(U32.mod(k, 2), 1), lo, hi))

def Eval.med.lo(+k: U32, +start: U32, r: Array<F32> & F32) -> Array<F32> & F32:
  (a, lo) = r
  Eval.med.hi(k, lo, Array.get(F32, a, U32.add(start, U32.div(k, 2))))

def Eval.med.at(+k: U32, +start: U32, sorted: Array<F32>) -> Array<F32> & F32:
  Eval.med.lo(k, start, Array.get(F32, sorted, U32.add(start, U32.div(U32.sub(k, 1), 2))))

def Eval.med.h(+k: U32, r: Array<F32> & Array<U32>) -> F32:
  (sorted, perm) = r
  Eval.snd(~F32, ~F32, Eval.med.at(k, 0, sorted))

def Eval.med.g(+k: U32, +d: Nat, x: Array<F32>, st: Array<U32> & Array<U32>) -> F32:
  (ws, perm) = st
  Eval.med.h(k, K.Kernel.gather(~F32, k, d, x, perm, 0.0))

def Eval.med.a(+k: U32, +d: Nat, r: Array<F32> & Array<F32>) -> F32:
  (x1, x2) = r
  Eval.med.g(k, d, x2, RD.Radix.sort(k, d, (K.Kernel.map(~F32, ~U32, ~(w => K.Kernel.fword(w)), k, d, x1, 0), K.Kernel.iota(k, d))))

# the median of a[0..k) (k >= 1): a stable radix sort by the 15.5.2 order words (NaN greatest,
# -0.0 = 0.0 keeping input order), then Eval.med.at
def Eval.med(+k: U32, x: Array<F32>) -> F32:
  Eval.med.a(k, K.Kernel.depth_for(k), Array.clone(F32, x))

# std / var / median of k dense f32 values
def Eval.agg.stat(op: X.AggOp, +k: U32, x: Array<F32>) -> D.Scalar:
  match op:
    case X.Std{}:
      Eval.stat.s(True{}, k, Eval.ssd(k, x))
    case X.Var{}:
      Eval.stat.s(False{}, k, Eval.ssd(k, x))
    case _:
      Eval.nz(k, D.SF32{Eval.med(k, x)})

# a word column's values as f32 (i32 signed, else unsigned): std / var / median of integers
def Eval.wf32(t: D.DType, +k: U32, x: Array<U32>) -> Array<F32>:
  match t:
    case D.TI32{}:
      K.Kernel.map(~U32, ~F32, ~(w => D.I32.to_f32(D.I32{w})), k, K.Kernel.depth_for(k), x, 0.0)
    case _:
      K.Kernel.map(~U32, ~F32, ~(w => U32.to_f32(w)), k, K.Kernel.depth_for(k), x, 0.0)

def Eval.is_stat(op: X.AggOp) -> Bool:
  match op:
    case X.Std{}:
      True{}
    case X.Var{}:
      True{}
    case X.Median{}:
      True{}
    case _:
      False{}

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
      Done{Eval.unit(D.SU32{Eval.nu.w(t, k, x)}, D.TU32{})}
    case X.Std{}:
      Done{Eval.unit(Eval.agg.stat(X.Std{}, k, Eval.wf32(t, k, x)), D.TF32{})}
    case X.Var{}:
      Done{Eval.unit(Eval.agg.stat(X.Var{}, k, Eval.wf32(t, k, x)), D.TF32{})}
    case X.Median{}:
      Done{Eval.unit(Eval.agg.stat(X.Median{}, k, Eval.wf32(t, k, x)), D.TF32{})}
    case _:
      Done{Eval.unit(D.SU32{k}, D.TU32{})}

def Eval.agg.f(op: X.AggOp, +k: U32, x: Array<F32>) -> E.ResT(C.Column):
  match op:
    case X.Sum{}:
      Done{Eval.unit(D.SF32{K.Kernel.fsum(~F32, ~(w => w), k, x)}, D.TF32{})}
    case X.Mean{}:
      Done{Eval.unit(Eval.mean_s(k, K.Kernel.fsum(~F32, ~(w => w), k, x)), D.TF32{})}
    case X.Min{}:
      Done{Eval.unit(Eval.nz(k, D.SF32{Eval.fold1(~F32, ~(a => b => K.Kernel.fmin(a, b)), k, x)}), D.TF32{})}
    case X.Max{}:
      Done{Eval.unit(Eval.nz(k, D.SF32{Eval.fold1(~F32, ~(a => b => K.Kernel.fmax(a, b)), k, x)}), D.TF32{})}
    case X.First{}:
      Done{Eval.unit(Eval.nz(k, D.SF32{Eval.at(~F32, x, 0)}), D.TF32{})}
    case X.Last{}:
      Done{Eval.unit(Eval.nz(k, D.SF32{Eval.at(~F32, x, U32.sub(k, 1))}), D.TF32{})}
    case X.NUnique{}:
      Done{Eval.unit(D.SU32{Eval.nu.words(k, K.Kernel.map(~F32, ~U32, ~(w => K.Kernel.fword(w)), k, K.Kernel.depth_for(k), x, 0))}, D.TU32{})}
    case X.Std{}:
      Done{Eval.unit(Eval.agg.stat(X.Std{}, k, x), D.TF32{})}
    case X.Var{}:
      Done{Eval.unit(Eval.agg.stat(X.Var{}, k, x), D.TF32{})}
    case X.Median{}:
      Done{Eval.unit(Eval.agg.stat(X.Median{}, k, x), D.TF32{})}
    case _:
      Done{Eval.unit(D.SU32{k}, D.TU32{})}

def Eval.agg.sr(op: X.AggOp, +k: U32, x: Array<String>) -> E.ResT(C.Column):
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
      Done{Eval.unit(D.SU32{Eval.nu.str(k, x)}, D.TU32{})}
    case X.Sum{}:
      Fail{Eval.bug("sum over str")}
    case X.Mean{}:
      Fail{Eval.bug("mean over str")}
    case X.Std{}:
      Fail{Eval.bug("std over str")}
    case X.Var{}:
      Fail{Eval.bug("var over str")}
    case X.Median{}:
      Fail{Eval.bug("median over str")}
    case _:
      Done{Eval.unit(D.SU32{k}, D.TU32{})}

# ---- Str aggregations over a Dictionary (M4): min / max by the rank of the entries (Map order =
# String order, as Eval.str_min compares), n_unique by distinct codes, first / last by code

def Eval.ds.fst(r: Array<U32> & Array<U32>) -> Array<U32>:
  (a, b) = r
  a

def Eval.ds.ext.s(r: ST.Dict & String) -> String:
  (dict, s) = r
  s

def Eval.ds.ext.c(dict: ST.Dict, +w: U32, inv: Array<U32>) -> String:
  Eval.ds.ext.s(ST.Dict.get(dict, Eval.at(~U32, inv, w)))

def Eval.ds.fold(max: Bool, +k: U32, w: Array<U32>) -> U32:
  match max:
    case True{}:
      Eval.fold1(~U32, ~(a => b => U32.max(a, b)), k, w)
    case False{}:
      Eval.fold1(~U32, ~(a => b => U32.min(a, b)), k, w)

# inv[rank[c]] = c, then the entry of the smallest (max: largest) rank among codes[0..k)
def Eval.ds.ext.w(+max: Bool, +k: U32, +kd: U32, +dd: Nat, dict: ST.Dict, codes: Array<U32>, rr: Array<U32> & Array<U32>) -> String:
  (r1, r2) = rr
  Eval.ds.ext.c(dict, Eval.ds.fold(max, k, Eval.ds.fst(K.Kernel.gather(~U32, k, K.Kernel.depth_for(k), r1, codes, 0))), K.Kernel.scatter(~U32, ~U32, ~(a => v => v), kd, r2, K.Kernel.iota(kd, dd), Array.new(U32, dd, 0)))

def Eval.ds.ext.q(+max: Bool, +k: U32, codes: Array<U32>, rk: Array<U32>, r: ST.Dict & U32) -> String:
  (dict, +kd) = r
  Eval.ds.ext.w(max, k, kd, K.Kernel.depth_for(kd), dict, codes, Array.clone(U32, rk))

def Eval.ds.ext.r(+max: Bool, +k: U32, codes: Array<U32>, r: ST.Dict & Array<U32>) -> String:
  (dict, rk) = r
  Eval.ds.ext.q(max, k, codes, rk, ST.Dict.size(dict))

def Eval.ds.ext(+max: Bool, +k: U32, codes: Array<U32>, dict: ST.Dict) -> String:
  Eval.ds.ext.r(max, k, codes, R.Rk.dict(dict))

# distinct codes among codes[0..k)
def Eval.ds.nu.k(+k: U32, codes: Array<U32>, r: ST.Dict & U32) -> U32:
  (dict, +kd) = r
  Eval.snd(~U32, ~U32, K.Kernel.popcount(kd, K.Kernel.scatter(~U32, ~U32, ~(a => v => v), k, codes, Array.new(U32, 0n, 1), Array.new(U32, K.Kernel.depth_for(kd), 0))))

def Eval.ds.nu(+k: U32, codes: Array<U32>, dict: ST.Dict) -> U32:
  Eval.ds.nu.k(k, codes, ST.Dict.size(dict))

def Eval.ds.at.k(r: ST.Dict & String) -> String:
  (dict, s) = r
  s

def Eval.ds.at(codes: Array<U32>, +i: U32, dict: ST.Dict) -> String:
  Eval.ds.at.k(ST.Dict.get(dict, Eval.at(~U32, codes, i)))

def Eval.agg.sd(op: X.AggOp, +k: U32, codes: Array<U32>, dict: ST.Dict) -> E.ResT(C.Column):
  match op:
    case X.Min{}:
      Done{Eval.unit(Eval.nz(k, D.SStr{Eval.ds.ext(False{}, k, codes, dict)}), D.TStr{})}
    case X.Max{}:
      Done{Eval.unit(Eval.nz(k, D.SStr{Eval.ds.ext(True{}, k, codes, dict)}), D.TStr{})}
    case X.First{}:
      Done{Eval.unit(Eval.nz(k, D.SStr{Eval.ds.at(codes, 0, dict)}), D.TStr{})}
    case X.Last{}:
      Done{Eval.unit(Eval.nz(k, D.SStr{Eval.ds.at(codes, U32.sub(k, 1), dict)}), D.TStr{})}
    case X.NUnique{}:
      Done{Eval.unit(D.SU32{Eval.ds.nu(k, codes, dict)}, D.TU32{})}
    case X.Sum{}:
      Fail{Eval.bug("sum over str")}
    case X.Mean{}:
      Fail{Eval.bug("mean over str")}
    case X.Std{}:
      Fail{Eval.bug("std over str")}
    case X.Var{}:
      Fail{Eval.bug("var over str")}
    case X.Median{}:
      Fail{Eval.bug("median over str")}
    case _:
      Done{Eval.unit(D.SU32{k}, D.TU32{})}

def Eval.agg.s(op: X.AggOp, +k: U32, x: ST.Strs) -> E.ResT(C.Column):
  match x:
    case ST.SRaw{a}:
      Eval.agg.sr(op, k, a)
    case ST.SDict{codes, dict}:
      Eval.agg.sd(op, k, codes, dict)

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
    case X.TryCast{e2, t}:
      Eval.kind(e2)
    case X.Un{op, e2}:
      Eval.kind(e2)
    case X.Bin{op, a, b}:
      SKind.comb(Eval.kind(a), Eval.kind(b))
    case X.FillNull{e2, v}:
      SKind.comb(Eval.kind(e2), Eval.kind(v))
    case X.Agg{op, e2}:
      KAgg{}
    case X.When{c, a, b}:
      SKind.comb(Eval.kind(c), SKind.comb(Eval.kind(a), Eval.kind(b)))
    case X.IsIn{e2, vs}:
      Eval.kind(e2)
    case X.Clip{e2, lo, hi}:
      Eval.kind(e2)
    case X.StrPred{op, e2, p}:
      Eval.kind(e2)

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
    case X.TryCast{+e2, +to}:
      Eval.compile.cast(X.Expr.is_null_lit(e2), to, acc, Eval.compile(e2, ITry{to} <> acc))
    case X.Un{op, e2}:
      Eval.compile(e2, IUn{op} <> acc)
    case X.Bin{op, a, b}:
      Eval.compile(a, Eval.compile(b, IBin{op} <> acc))
    case X.FillNull{e2, v}:
      Eval.compile(e2, Eval.compile(v, IFill{} <> acc))
    case X.Agg{op, e2}:
      Eval.compile(e2, IAgg{op} <> acc)
    case X.When{c, a, b}:
      Eval.compile(c, Eval.compile(a, Eval.compile(b, IWhen{} <> acc)))
    case X.IsIn{e2, vs}:
      Eval.compile(e2, IIsIn{vs} <> acc)
    case X.Clip{e2, lo, hi}:
      Eval.compile(e2, IClip{lo, hi} <> acc)
    case X.StrPred{op, e2, p}:
      Eval.compile(e2, IStr{op, p} <> acc)

# ---- liveness: moves (DESIGN.md 16.2 rule 1) -------------------------------------------------
#
# A static pass over the postfix code, with the operator's other expressions as Data: it runs
# after the static checks (Eval.static, Grp.static) and before any data work, and never changes
# what is computed, only whether a column reference copies (ICol, Frame.get_cloned) or takes
# the column out of the frame (IMove, Frame.lend). A reference becomes IMove when
#   * the operator does not keep the input column (`all`: select and group_by consume their
#     input; otherwise the name must be in `dead`: with_columns' overwritten inputs), and
#   * it is the LAST reference of that name in the operator: none later in this expression's
#     code and none in `later`, the references of the expressions evaluated after it.
# So with k references to a column, the first k - 1 copy and the last one moves; a column the
# output keeps (filter's frame, with_columns' untouched inputs) is never moved. The hollow
# stand-in Frame.lend leaves is never read: every later reference was counted.

# the column names every expression reads, in evaluation order, with repetitions (the
# operator-wide use count: X.Expr.refs is exactly the ICols of Eval.compile)
def Eval.refs(es: List<&2, X.Expr>) -> List<&2, String>:
  match es:
    case Nil{}:
      Nil{}
    case e <> t:
      List.append(&2, String, X.Expr.refs(e), Eval.refs(t))

# the columns the code reads (ICol and IMove), in order
def Eval.reads(code: List<&2, Instr>) -> List<&2, String>:
  match code:
    case Nil{}:
      Nil{}
    case ICol{n} <> t:
      n <> Eval.reads(t)
    case IMove{n} <> t:
      n <> Eval.reads(t)
    case i <> t:
      Eval.reads(t)

def Eval.mark.c(mv: Bool, n: String) -> Instr:
  match mv:
    case True{}:
      IMove{n}
    case False{}:
      ICol{n}

def Eval.mark.i(i: Instr, +rest: List<&2, Instr>, +all: Bool, +dead: List<&2, String>, +later: List<&2, String>) -> Instr:
  match i:
    case ICol{+n}:
      Eval.mark.c(Bool.and(Bool.or(all, C.Names.has(dead, n)), Bool.not(Bool.or(C.Names.has(later, n), C.Names.has(Eval.reads(rest), n)))), n)
    case other:
      other

# the code with every last reference of a movable column turned into IMove (LAWS.bend
# mark_moves_ok: no IMove{n} of the result is followed by a read of n, in the code or in `later`,
# and n is not kept by the operator; mark_reads: the names read, in order, are unchanged)
def Eval.mark(code: List<&2, Instr>, +all: Bool, +dead: List<&2, String>, +later: List<&2, String>) -> List<&2, Instr>:
  match code:
    case Nil{}:
      Nil{}
    case i <> +t:
      Eval.mark.i(i, t, all, dead, later) <> Eval.mark(t, all, dead, later)

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
    case ITry{to}:
      Eval.wrap(k, Eval.try_cast(to, c))

    case IAgg{+op}:
      Eval.wrap(KAgg{}, Eval.agg(op, Eval.fit_agg(op, k, c, h)))
    case IIsIn{vs}:
      Eval.wrap(k, Eval.isin(vs, c))
    case IClip{lo, hi}:
      Eval.wrap(k, Eval.clip(lo, hi, c))
    case IStr{op, pat}:
      Eval.wrap(k, Eval.strpred(op, pat, c))
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

# a 1-row side broadcast next to a Dictionary Str column broadcasts as a Dictionary (M4)
def Eval.fitd(k: SKind, c: C.Column, +n: U32, other_dict: Bool) -> C.Column:
  match k other_dict:
    case KFull{} _:
      c
    case _ True{}:
      Eval.bcast_dict(c, n)
    case _ False{}:
      Eval.bcast(c, n)

def Eval.do2.e(i: Instr, +ka: SKind, +kb: SKind, +la: U32, +lb: U32, ra: C.Column & Bool, rb: C.Column & Bool) -> E.ResT(Slot):
  (a, +da) = ra
  (b, +db) = rb
  +fa = SKind.is_full(ka)
  +fb = SKind.is_full(kb)
  +n = Bool.pick(U32, fa, la, Bool.pick(U32, fb, lb, 1))
  Eval.do2.b(Bool.and(Bool.and(fa, fb), U32.is_ne(la, lb)), i, SKind.comb(ka, kb), la, lb, Eval.fitd(ka, a, n, db), Eval.fitd(kb, b, n, da))

def Eval.do2.a(i: Instr, +ka: SKind, +kb: SKind, ra: C.Column & U32, rb: C.Column & U32) -> E.ResT(Slot):
  (a, +la) = ra
  (b, +lb) = rb
  Eval.do2.e(i, ka, kb, la, lb, C.Column.is_dict(a), C.Column.is_dict(b))

def Eval.do2(i: Instr, ka: SKind, a: C.Column, kb: SKind, b: C.Column) -> E.ResT(Slot):
  Eval.do2.a(i, ka, kb, C.Column.len(a), C.Column.len(b))

def Eval.do3.b(bad: Bool, k: SKind, +n: U32, c: C.Column, a: C.Column, b: C.Column) -> E.ResT(Slot):
  match bad:
    case True{}:
      Fail{E.ShapeMismatch{n, n}}
    case False{}:
      Eval.wrap(k, Eval.when(c, a, b))

# the three operands of when, a 1-row side broadcast to the full sides' length
def Eval.do3.a(+kc: SKind, +ka: SKind, +kb: SKind, rc: C.Column & U32, ra: C.Column & U32, rb: C.Column & U32) -> E.ResT(Slot):
  (c, +lc) = rc
  (a, +la) = ra
  (b, +lb) = rb
  +fc = SKind.is_full(kc)
  +fa = SKind.is_full(ka)
  +fb = SKind.is_full(kb)
  +n = Bool.pick(U32, fc, lc, Bool.pick(U32, fa, la, Bool.pick(U32, fb, lb, 1)))
  +bad = Bool.or(Bool.and(fc, U32.is_ne(lc, n)), Bool.or(Bool.and(fa, U32.is_ne(la, n)), Bool.and(fb, U32.is_ne(lb, n))))
  Eval.do3.b(bad, SKind.comb(kc, SKind.comb(ka, kb)), n, Eval.fit(kc, c, n), Eval.fit(ka, a, n), Eval.fit(kb, b, n))

def Eval.do3(kc: SKind, c: C.Column, ka: SKind, a: C.Column, kb: SKind, b: C.Column) -> E.ResT(Slot):
  Eval.do3.a(kc, ka, kb, C.Column.len(c), C.Column.len(a), C.Column.len(b))

def Eval.app3(stk: List<&1, Slot>) -> E.ResT(List<&1, Slot>):
  match stk:
    case Slot{kb, b} <> Slot{ka, a} <> Slot{kc, c} <> rest:
      Eval.push(rest, Eval.do3(kc, c, ka, a, kb, b))
    case _:
      Fail{Eval.bug("empty stack")}

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
    case IMove{n}:
      Eval.push_col(stk, C.Frame.lend(f, n))
    case IConst{v, t}:
      EvSt{f, Done{Slot{KLit{}, Eval.unit(v, t)} <> stk}}
    case IBin{op}:
      EvSt{f, Eval.app2(IBin{op}, stk)}
    case IFill{}:
      EvSt{f, Eval.app2(IFill{}, stk)}
    case IWhen{}:
      EvSt{f, Eval.app3(stk)}
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

# ---- W4 fusion (T4.2, DESIGN.md 16.3 F1-F4): the peephole pass ------------------------------------
#
# Eval.fuse runs over MARKED code (Eval.mark's ICol / IMove decide borrow vs move) and rewrites
# windows of the postfix code into IFz fragments; nothing is evaluated (a static pass, after the
# static checks, before any data work). R is ICol{n} / IMove{n}; a fragment F is R, R ICast{t} or
# R IConst{v} IFill (a frame column with its pre-operation, Pre). The windows, in priority order:
#   F1 F2 IBin{op}       -> Z2{op, F1, F2}             two frame columns (distinct names)
#   F IConst{v} IBin{op} -> Z1{op, v, right, F}        literal right
#   F IBin{op}           -> Z2{op, stack, F}
#   F                    -> Z0{F}                      a fill nothing above consumed (F4 alone)
#   IConst{v} F IBin{op} -> Z1{op, v, left, F}         literal left
#   IConst{v} IBin{op}   -> Z1{op, v, right, stack}
#   IConst{v} IFill      -> Z0{stack}
#   IBin{op}             -> Z2{op, stack, stack}
# op is a null-propagating arithmetic / comparison (Eval.fz.op_ok): Kleene and/or and the integer
# floor_div / mod keep their own rules (F7). Every IFz keeps the code it replaces (`orig`): the
# executor (Eval.fz.exec) runs a fused kernel only on the runtime shapes it has one for (dtypes,
# a total cast, the fill literal being the default, full-length operands) and otherwise puts the
# operands back and runs `orig`, so a strict (fallible) cast is never folded and keeps its own pass,
# row order and error. Every fused kernel is total: no fused fragment can fail.

# the binary ops a fused zip computes
def Eval.fz.op_ok(op: X.BinOp) -> Bool:
  match op:
    case X.FloorDiv{}:
      False{}
    case X.Mod{}:
      False{}
    case X.And{}:
      False{}
    case X.Or{}:
      False{}
    case _:
      True{}

def Eval.fz.isdiv(op: X.BinOp) -> Bool:
  match op:
    case X.Div{}:
      True{}
    case _:
      False{}

def Eval.fz.is_and(op: X.BinOp) -> Bool:
  match op:
    case X.And{}:
      True{}
    case _:
      False{}

# the six comparisons
def Eval.fz.isrel(op: X.BinOp) -> Bool:
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
    case _:
      False{}

# the scan state: the output so far (newest first) and the code still to scan
type FzS is Data:
  FzS{out: List<&2, Instr>, rest: List<&2, Instr>}

# xs reversed onto acc
def Eval.fz.revon(xs: List<&2, Instr>, acc: List<&2, Instr>) -> List<&2, Instr>:
  match xs:
    case Nil{}:
      acc
    case x <> t:
      Eval.fz.revon(t, x <> acc)

def Eval.fz.opname(o: Opd) -> String:
  match o:
    case OStk{}:
      ""
    case ORef{n, mv}:
      n

# a fragment no fused instruction consumes: Z0 when it is a fill (F4), else its code as is
def Eval.fz.solo(out: List<&2, Instr>, o: Opd, pre: Pre, frag: List<&2, Instr>, rest: List<&2, Instr>) -> FzS:
  match pre:
    case PFill{v}:
      FzS{IFz{Z0{o, PFill{v}}, frag} <> out, rest}
    case _:
      FzS{Eval.fz.revon(frag, out), rest}

def Eval.fz.p1.go(go: Bool, out: List<&2, Instr>, +o1: Opd, +p1: Pre, +f1: List<&2, Instr>, +o2: Opd, +p2: Pre, +f2: List<&2, Instr>, +op: X.BinOp, t: List<&2, Instr>) -> FzS:
  match go:
    case True{}:
      FzS{IFz{Z2{op, o1, p1, o2, p2}, List.append(&2, Instr, f1, List.append(&2, Instr, f2, IBin{op} <> Nil{}))} <> out, t}
    case False{}:
      Eval.fz.solo(out, o1, p1, f1, List.append(&2, Instr, f2, IBin{op} <> t))

# F1 F2 then IBin{op}: Z2 over two distinct frame columns
def Eval.fz.p1(out: List<&2, Instr>, +o1: Opd, +p1: Pre, +f1: List<&2, Instr>, +o2: Opd, +p2: Pre, +f2: List<&2, Instr>, t: List<&2, Instr>) -> FzS:
  match t:
    case IBin{+op} <> t2:
      Eval.fz.p1.go(Bool.and(Bool.not(String.eq(Eval.fz.opname(o1), Eval.fz.opname(o2))), Eval.fz.op_ok(op)), out, o1, p1, f1, o2, p2, f2, op, t2)
    case other:
      Eval.fz.solo(out, o1, p1, f1, List.append(&2, Instr, f2, other))

# a second frame column (o2, its instruction i2) after the first fragment: its pre-operation
def Eval.fz.f2(out: List<&2, Instr>, +o1: Opd, +p1: Pre, +f1: List<&2, Instr>, +o2: Opd, +i2: Instr, t: List<&2, Instr>) -> FzS:
  match t:
    case IConst{+v, +ty} <> IFill{} <> t2:
      Eval.fz.p1(out, o1, p1, f1, o2, PFill{v}, i2 <> IConst{v, ty} <> IFill{} <> Nil{}, t2)
    case ICast{+to} <> t2:
      Eval.fz.p1(out, o1, p1, f1, o2, PCast{to}, i2 <> ICast{to} <> Nil{}, t2)
    case other:
      Eval.fz.p1(out, o1, p1, f1, o2, PNone{}, i2 <> Nil{}, other)

def Eval.fz.p2(go: Bool, out: List<&2, Instr>, +o: Opd, +p: Pre, +f: List<&2, Instr>, +v: D.Scalar, +ty: D.DType, +op: X.BinOp, t: List<&2, Instr>) -> FzS:
  match go:
    case True{}:
      FzS{IFz{Z1{op, v, False{}, o, p}, List.append(&2, Instr, f, IConst{v, ty} <> IBin{op} <> Nil{})} <> out, t}
    case False{}:
      Eval.fz.solo(out, o, p, f, IConst{v, ty} <> IBin{op} <> t)

def Eval.fz.p6(go: Bool, out: List<&2, Instr>, +o: Opd, +p: Pre, +f: List<&2, Instr>, +op: X.BinOp, t: List<&2, Instr>) -> FzS:
  match go:
    case True{}:
      FzS{IFz{Z2{op, OStk{}, PNone{}, o, p}, List.append(&2, Instr, f, IBin{op} <> Nil{})} <> out, t}
    case False{}:
      Eval.fz.solo(out, o, p, f, IBin{op} <> t)

# what follows the first fragment (o, its pre-operation p, its code f)
def Eval.fz.after(out: List<&2, Instr>, +o: Opd, +p: Pre, +f: List<&2, Instr>, t: List<&2, Instr>) -> FzS:
  match t:
    case ICol{+m} <> t2:
      Eval.fz.f2(out, o, p, f, ORef{m, False{}}, ICol{m}, t2)
    case IMove{+m} <> t2:
      Eval.fz.f2(out, o, p, f, ORef{m, True{}}, IMove{m}, t2)
    case IConst{+v, +ty} <> IBin{+op} <> t2:
      Eval.fz.p2(Eval.fz.op_ok(op), out, o, p, f, v, ty, op, t2)
    case IBin{+op} <> t2:
      Eval.fz.p6(Eval.fz.op_ok(op), out, o, p, f, op, t2)
    case other:
      Eval.fz.solo(out, o, p, f, other)

# a frame column (o, its instruction i0) at the scan position: its pre-operation
def Eval.fz.ref(out: List<&2, Instr>, +o: Opd, +i0: Instr, t: List<&2, Instr>) -> FzS:
  match t:
    case IConst{+v, +ty} <> IFill{} <> t2:
      Eval.fz.after(out, o, PFill{v}, i0 <> IConst{v, ty} <> IFill{} <> Nil{}, t2)
    case ICast{+to} <> t2:
      Eval.fz.after(out, o, PCast{to}, i0 <> ICast{to} <> Nil{}, t2)
    case other:
      Eval.fz.after(out, o, PNone{}, i0 <> Nil{}, other)

def Eval.fz.p3.go(go: Bool, out: List<&2, Instr>, +v: D.Scalar, +ty: D.DType, +o: Opd, +p: Pre, +f: List<&2, Instr>, +op: X.BinOp, t: List<&2, Instr>) -> FzS:
  match go:
    case True{}:
      FzS{IFz{Z1{op, v, True{}, o, p}, IConst{v, ty} <> List.append(&2, Instr, f, IBin{op} <> Nil{})} <> out, t}
    case False{}:
      FzS{IConst{v, ty} <> out, List.append(&2, Instr, f, IBin{op} <> t)}

# IConst{v} and a fragment: IBin{op} makes the literal-left Z1
def Eval.fz.p3(out: List<&2, Instr>, +v: D.Scalar, +ty: D.DType, +o: Opd, +p: Pre, +f: List<&2, Instr>, t: List<&2, Instr>) -> FzS:
  match t:
    case IBin{+op} <> t2:
      Eval.fz.p3.go(Eval.fz.op_ok(op), out, v, ty, o, p, f, op, t2)
    case other:
      FzS{IConst{v, ty} <> out, List.append(&2, Instr, f, other)}

def Eval.fz.p3.f(out: List<&2, Instr>, +v: D.Scalar, +ty: D.DType, +o: Opd, +i0: Instr, t: List<&2, Instr>) -> FzS:
  match t:
    case IConst{+w, +ty2} <> IFill{} <> t2:
      Eval.fz.p3(out, v, ty, o, PFill{w}, i0 <> IConst{w, ty2} <> IFill{} <> Nil{}, t2)
    case ICast{+to} <> t2:
      Eval.fz.p3(out, v, ty, o, PCast{to}, i0 <> ICast{to} <> Nil{}, t2)
    case other:
      Eval.fz.p3(out, v, ty, o, PNone{}, i0 <> Nil{}, other)

def Eval.fz.p5(go: Bool, out: List<&2, Instr>, +v: D.Scalar, +ty: D.DType, +op: X.BinOp, t: List<&2, Instr>) -> FzS:
  match go:
    case True{}:
      FzS{IFz{Z1{op, v, False{}, OStk{}, PNone{}}, IConst{v, ty} <> IBin{op} <> Nil{}} <> out, t}
    case False{}:
      FzS{IBin{op} <> IConst{v, ty} <> out, t}

# a literal at the scan position
def Eval.fz.cst(out: List<&2, Instr>, +v: D.Scalar, +ty: D.DType, t: List<&2, Instr>) -> FzS:
  match t:
    case IBin{+op} <> t2:
      Eval.fz.p5(Eval.fz.op_ok(op), out, v, ty, op, t2)
    case IFill{} <> t2:
      FzS{IFz{Z0{OStk{}, PFill{v}}, IConst{v, ty} <> IFill{} <> Nil{}} <> out, t2}
    case ICol{+m} <> t2:
      Eval.fz.p3.f(out, v, ty, ORef{m, False{}}, ICol{m}, t2)
    case IMove{+m} <> t2:
      Eval.fz.p3.f(out, v, ty, ORef{m, True{}}, IMove{m}, t2)
    case other:
      FzS{IConst{v, ty} <> out, other}

def Eval.fz.p7(go: Bool, out: List<&2, Instr>, +op: X.BinOp, t: List<&2, Instr>) -> FzS:
  match go:
    case True{}:
      FzS{IFz{Z2{op, OStk{}, PNone{}, OStk{}, PNone{}}, IBin{op} <> Nil{}} <> out, t}
    case False{}:
      FzS{IBin{op} <> out, t}

# one scan step: at least one instruction leaves `rest`
def Eval.fz.step(s: FzS) -> FzS:
  match s:
    case FzS{out, Nil{}}:
      FzS{out, Nil{}}
    case FzS{out, ICol{+n} <> t}:
      Eval.fz.ref(out, ORef{n, False{}}, ICol{n}, t)
    case FzS{out, IMove{+n} <> t}:
      Eval.fz.ref(out, ORef{n, True{}}, IMove{n}, t)
    case FzS{out, IConst{+v, +ty} <> t}:
      Eval.fz.cst(out, v, ty, t)
    case FzS{out, IBin{+op} <> t}:
      Eval.fz.p7(Eval.fz.op_ok(op), out, op, t)
    case FzS{out, i <> t}:
      FzS{i <> out, t}

def Eval.fz.go(n: Nat, s: FzS) -> FzS:
  match n:
    case 0n:
      s
    case 1n+p:
      Eval.fz.go(p, Eval.fz.step(s))

def Eval.fz.fin(s: FzS) -> List<&2, Instr>:
  match s:
    case FzS{out, rest}:
      Eval.fz.revon(out, rest)

# the peephole pass (one left-to-right scan; each step consumes at least one instruction, so the
# code's length is enough fuel, and whatever is left unscanned is kept as is)
def Eval.fuse(+code: List<&2, Instr>) -> List<&2, Instr>:
  Eval.fz.fin(Eval.fz.go(List.length(&2, Instr, code), FzS{Nil{}, code}))

# ---- W4 fusion: the column-level fused operations (each hands its operands back) ----------------
#
# Every operation below reads its operand buffers through a borrowing kernel of src/kernels.bend
# (map_pb, zipb, zipv) and hands them back: the executor lends a frame column (Frame.lend), runs
# the operation and puts the column back (Frame.replace), so a column the frame keeps is read in
# place, not copied (DESIGN.md 16.2 rule 1). An AllValid side is the 1-slot ones array, a literal
# a scalar parameter (map_pb) or a 1-slot array (zipv). The templates are Eval.zip.u / zip.i /
# zip.fa / zip.fc's, verbatim (F32 rounding as written: no reassociation, no FMA); a cast (F3) is
# Eval.cast's template composed in front of the operand. The answer carries Some{column} when a
# kernel ran and None (the operands untouched) when the shape has none: the caller then runs the
# unfused code. LAWS.bend section 19.

# the 1-slot ones array: an AllValid side as the fused kernels read it (indices wrap; never written)
def Eval.fz.ones() -> Array<U32>:
  Array.new(U32, 0n, 1)

# a validity handed back by zipv: a real mask, or the ones array of an AllValid side (dropped)
def Eval.fz.back(m: Bool, w: Array<U32>) -> C.Valid:
  match m:
    case True{}:
      C.Mask{w}
    case False{}:
      C.AllValid{}

# a fused zip's answer: the result column and the operands' validity and data
type ZR<-T: Data, -U: Data> is Type:
  ZR{c: C.Column, va: C.Valid, a: Array<T>, vb: C.Valid, b: Array<U>}

def Eval.fz.zw.b(~T: Data, ~U: Data, rt: D.DType, +n: U32, d: Nat, r: K.ZB<T, U, U32>) -> ZR<T, U>:
  match r:
    case K.ZB{o, a, b}:
      ZR{C.Column.mk_w(rt, n, d, C.AllValid{}, o), C.AllValid{}, a, C.AllValid{}, b}

def Eval.fz.zw.v(~T: Data, ~U: Data, rt: D.DType, +n: U32, d: Nat, ma: Bool, mb: Bool, r: K.ZV<T, U, U32>) -> ZR<T, U>:
  match r:
    case K.ZV{o, vo, a, va, b, vb}:
      ZR{C.Column.mk_w(rt, n, d, C.Mask{vo}, o), Eval.fz.back(ma, va), a, Eval.fz.back(mb, vb), b}

# F2 into words (comparisons, u32 / i32 arithmetic): zipb when both sides are AllValid (the result
# AllValid), else zipv (the result's validity the AND of the two, its null slots 0: Eval.vand +
# the zip + Eval.fix in one loop)
def Eval.fz.zw(~T: Data, ~U: Data, ~f: T -> U -> U32, rt: D.DType, +n: U32, +d: Nat, va: C.Valid, a: Array<T>, vb: C.Valid, b: Array<U>) -> ZR<T, U>:
  match va vb:
    case C.AllValid{} C.AllValid{}:
      Eval.fz.zw.b(~T, ~U, rt, n, d, K.Kernel.zipb(~T, ~U, ~U32, ~f, n, d, a, b, 0))
    case C.AllValid{} C.Mask{mb}:
      Eval.fz.zw.v(~T, ~U, rt, n, d, False{}, True{}, K.Kernel.zipv(~T, ~U, ~U32, ~f, n, d, a, Eval.fz.ones(), b, mb, 0))
    case C.Mask{ma} C.AllValid{}:
      Eval.fz.zw.v(~T, ~U, rt, n, d, True{}, False{}, K.Kernel.zipv(~T, ~U, ~U32, ~f, n, d, a, ma, b, Eval.fz.ones(), 0))
    case C.Mask{ma} C.Mask{mb}:
      Eval.fz.zw.v(~T, ~U, rt, n, d, True{}, True{}, K.Kernel.zipv(~T, ~U, ~U32, ~f, n, d, a, ma, b, mb, 0))

def Eval.fz.zf.b(~T: Data, ~U: Data, +n: U32, d: Nat, r: K.ZB<T, U, F32>) -> ZR<T, U>:
  match r:
    case K.ZB{o, a, b}:
      ZR{C.CF32{n, d, C.AllValid{}, o}, C.AllValid{}, a, C.AllValid{}, b}

def Eval.fz.zf.v(~T: Data, ~U: Data, +n: U32, d: Nat, ma: Bool, mb: Bool, r: K.ZV<T, U, F32>) -> ZR<T, U>:
  match r:
    case K.ZV{o, vo, a, va, b, vb}:
      ZR{C.CF32{n, d, C.Mask{vo}, o}, Eval.fz.back(ma, va), a, Eval.fz.back(mb, vb), b}

# F2 / F3 into f32 (f32 arithmetic)
def Eval.fz.zf(~T: Data, ~U: Data, ~f: T -> U -> F32, +n: U32, +d: Nat, va: C.Valid, a: Array<T>, vb: C.Valid, b: Array<U>) -> ZR<T, U>:
  match va vb:
    case C.AllValid{} C.AllValid{}:
      Eval.fz.zf.b(~T, ~U, n, d, K.Kernel.zipb(~T, ~U, ~F32, ~f, n, d, a, b, 0.0))
    case C.AllValid{} C.Mask{mb}:
      Eval.fz.zf.v(~T, ~U, n, d, False{}, True{}, K.Kernel.zipv(~T, ~U, ~F32, ~f, n, d, a, Eval.fz.ones(), b, mb, 0.0))
    case C.Mask{ma} C.AllValid{}:
      Eval.fz.zf.v(~T, ~U, n, d, True{}, False{}, K.Kernel.zipv(~T, ~U, ~F32, ~f, n, d, a, ma, b, Eval.fz.ones(), 0.0))
    case C.Mask{ma} C.Mask{mb}:
      Eval.fz.zf.v(~T, ~U, n, d, True{}, True{}, K.Kernel.zipv(~T, ~U, ~F32, ~f, n, d, a, ma, b, mb, 0.0))

# Eval.zip.u's templates (u32 words; the i32 add / sub / mul / eq / ne are the same word ops)
def Eval.fz.wu(op: X.BinOp, rt: D.DType, +n: U32, +d: Nat, va: C.Valid, a: Array<U32>, vb: C.Valid, b: Array<U32>) -> ZR<U32, U32>:
  match op:
    case X.Add{}:
      Eval.fz.zw(~U32, ~U32, ~(x => y => U32.add(x, y)), rt, n, d, va, a, vb, b)
    case X.Sub{}:
      Eval.fz.zw(~U32, ~U32, ~(x => y => U32.sub(x, y)), rt, n, d, va, a, vb, b)
    case X.Mul{}:
      Eval.fz.zw(~U32, ~U32, ~(x => y => U32.mul(x, y)), rt, n, d, va, a, vb, b)
    case X.Eq{}:
      Eval.fz.zw(~U32, ~U32, ~(x => y => Bool.to_u32(U32.is_eq(x, y))), rt, n, d, va, a, vb, b)
    case X.Ne{}:
      Eval.fz.zw(~U32, ~U32, ~(x => y => Bool.to_u32(U32.is_ne(x, y))), rt, n, d, va, a, vb, b)
    case X.Lt{}:
      Eval.fz.zw(~U32, ~U32, ~(x => y => Bool.to_u32(U32.is_lt(x, y))), rt, n, d, va, a, vb, b)
    case X.Le{}:
      Eval.fz.zw(~U32, ~U32, ~(x => y => Bool.to_u32(U32.is_le(x, y))), rt, n, d, va, a, vb, b)
    case X.Gt{}:
      Eval.fz.zw(~U32, ~U32, ~(x => y => Bool.to_u32(U32.is_gt(x, y))), rt, n, d, va, a, vb, b)
    case _:
      Eval.fz.zw(~U32, ~U32, ~(x => y => Bool.to_u32(U32.is_ge(x, y))), rt, n, d, va, a, vb, b)

# Eval.zip.i's comparisons (the rest are u32 word ops)
def Eval.fz.wi(op: X.BinOp, rt: D.DType, +n: U32, +d: Nat, va: C.Valid, a: Array<U32>, vb: C.Valid, b: Array<U32>) -> ZR<U32, U32>:
  match op:
    case X.Lt{}:
      Eval.fz.zw(~U32, ~U32, ~(x => y => Bool.to_u32(Eval.i32_lt(x, y))), rt, n, d, va, a, vb, b)
    case X.Le{}:
      Eval.fz.zw(~U32, ~U32, ~(x => y => Bool.to_u32(Bool.not(Eval.i32_lt(y, x)))), rt, n, d, va, a, vb, b)
    case X.Gt{}:
      Eval.fz.zw(~U32, ~U32, ~(x => y => Bool.to_u32(Eval.i32_lt(y, x))), rt, n, d, va, a, vb, b)
    case X.Ge{}:
      Eval.fz.zw(~U32, ~U32, ~(x => y => Bool.to_u32(Bool.not(Eval.i32_lt(x, y)))), rt, n, d, va, a, vb, b)
    case other:
      Eval.fz.wu(other, rt, n, d, va, a, vb, b)

# Eval.zip.fc's templates (the 15.5.2 total order through Kernel.fword)
def Eval.fz.fc(op: X.BinOp, +n: U32, +d: Nat, va: C.Valid, a: Array<F32>, vb: C.Valid, b: Array<F32>) -> ZR<F32, F32>:
  match op:
    case X.Ne{}:
      Eval.fz.zw(~F32, ~F32, ~(x => y => Bool.to_u32(U32.is_ne(K.Kernel.fword(x), K.Kernel.fword(y)))), D.TBool{}, n, d, va, a, vb, b)
    case X.Lt{}:
      Eval.fz.zw(~F32, ~F32, ~(x => y => Bool.to_u32(U32.is_lt(K.Kernel.fword(x), K.Kernel.fword(y)))), D.TBool{}, n, d, va, a, vb, b)
    case X.Le{}:
      Eval.fz.zw(~F32, ~F32, ~(x => y => Bool.to_u32(U32.is_le(K.Kernel.fword(x), K.Kernel.fword(y)))), D.TBool{}, n, d, va, a, vb, b)
    case X.Gt{}:
      Eval.fz.zw(~F32, ~F32, ~(x => y => Bool.to_u32(U32.is_gt(K.Kernel.fword(x), K.Kernel.fword(y)))), D.TBool{}, n, d, va, a, vb, b)
    case X.Ge{}:
      Eval.fz.zw(~F32, ~F32, ~(x => y => Bool.to_u32(U32.is_ge(K.Kernel.fword(x), K.Kernel.fword(y)))), D.TBool{}, n, d, va, a, vb, b)
    case _:
      Eval.fz.zw(~F32, ~F32, ~(x => y => Bool.to_u32(U32.is_eq(K.Kernel.fword(x), K.Kernel.fword(y)))), D.TBool{}, n, d, va, a, vb, b)

# Eval.zip.fa's templates (f32 add / sub / mul / div)
def Eval.fz.fa(op: X.BinOp, +n: U32, +d: Nat, va: C.Valid, a: Array<F32>, vb: C.Valid, b: Array<F32>) -> ZR<F32, F32>:
  match op:
    case X.Sub{}:
      Eval.fz.zf(~F32, ~F32, ~(x => y => F32.sub(x, y)), n, d, va, a, vb, b)
    case X.Mul{}:
      Eval.fz.zf(~F32, ~F32, ~(x => y => F32.mul(x, y)), n, d, va, a, vb, b)
    case X.Div{}:
      Eval.fz.zf(~F32, ~F32, ~(x => y => F32.div(x, y)), n, d, va, a, vb, b)
    case _:
      Eval.fz.zf(~F32, ~F32, ~(x => y => F32.add(x, y)), n, d, va, a, vb, b)

def Eval.fz.ff(cmp: Bool, op: X.BinOp, +n: U32, +d: Nat, va: C.Valid, a: Array<F32>, vb: C.Valid, b: Array<F32>) -> ZR<F32, F32>:
  match cmp:
    case True{}:
      Eval.fz.fc(op, n, d, va, a, vb, b)
    case False{}:
      Eval.fz.fa(op, n, d, va, a, vb, b)

# F3: f32(a) op b, a's u32 (or bool 0/1) words through Eval.cast.u / cast.b's U32.to_f32
def Eval.fz.cu(op: X.BinOp, +n: U32, +d: Nat, va: C.Valid, a: Array<U32>, vb: C.Valid, b: Array<F32>) -> ZR<U32, F32>:
  match op:
    case X.Sub{}:
      Eval.fz.zf(~U32, ~F32, ~(x => y => F32.sub(U32.to_f32(x), y)), n, d, va, a, vb, b)
    case X.Mul{}:
      Eval.fz.zf(~U32, ~F32, ~(x => y => F32.mul(U32.to_f32(x), y)), n, d, va, a, vb, b)
    case X.Div{}:
      Eval.fz.zf(~U32, ~F32, ~(x => y => F32.div(U32.to_f32(x), y)), n, d, va, a, vb, b)
    case _:
      Eval.fz.zf(~U32, ~F32, ~(x => y => F32.add(U32.to_f32(x), y)), n, d, va, a, vb, b)

# F3: f32(a) op b, a's i32 bits through Eval.cast.i's I32.to_f32
def Eval.fz.ci(op: X.BinOp, +n: U32, +d: Nat, va: C.Valid, a: Array<U32>, vb: C.Valid, b: Array<F32>) -> ZR<U32, F32>:
  match op:
    case X.Sub{}:
      Eval.fz.zf(~U32, ~F32, ~(x => y => F32.sub(D.I32.to_f32(D.I32{x}), y)), n, d, va, a, vb, b)
    case X.Mul{}:
      Eval.fz.zf(~U32, ~F32, ~(x => y => F32.mul(D.I32.to_f32(D.I32{x}), y)), n, d, va, a, vb, b)
    case X.Div{}:
      Eval.fz.zf(~U32, ~F32, ~(x => y => F32.div(D.I32.to_f32(D.I32{x}), y)), n, d, va, a, vb, b)
    case _:
      Eval.fz.zf(~U32, ~F32, ~(x => y => F32.add(D.I32.to_f32(D.I32{x}), y)), n, d, va, a, vb, b)

# F3: a op f32(b), b's u32 (or bool) words
def Eval.fz.uc(op: X.BinOp, +n: U32, +d: Nat, va: C.Valid, a: Array<F32>, vb: C.Valid, b: Array<U32>) -> ZR<F32, U32>:
  match op:
    case X.Sub{}:
      Eval.fz.zf(~F32, ~U32, ~(x => y => F32.sub(x, U32.to_f32(y))), n, d, va, a, vb, b)
    case X.Mul{}:
      Eval.fz.zf(~F32, ~U32, ~(x => y => F32.mul(x, U32.to_f32(y))), n, d, va, a, vb, b)
    case X.Div{}:
      Eval.fz.zf(~F32, ~U32, ~(x => y => F32.div(x, U32.to_f32(y))), n, d, va, a, vb, b)
    case _:
      Eval.fz.zf(~F32, ~U32, ~(x => y => F32.add(x, U32.to_f32(y))), n, d, va, a, vb, b)

# F3: a op f32(b), b's i32 bits
def Eval.fz.ic(op: X.BinOp, +n: U32, +d: Nat, va: C.Valid, a: Array<F32>, vb: C.Valid, b: Array<U32>) -> ZR<F32, U32>:
  match op:
    case X.Sub{}:
      Eval.fz.zf(~F32, ~U32, ~(x => y => F32.sub(x, D.I32.to_f32(D.I32{y}))), n, d, va, a, vb, b)
    case X.Mul{}:
      Eval.fz.zf(~F32, ~U32, ~(x => y => F32.mul(x, D.I32.to_f32(D.I32{y}))), n, d, va, a, vb, b)
    case X.Div{}:
      Eval.fz.zf(~F32, ~U32, ~(x => y => F32.div(x, D.I32.to_f32(D.I32{y}))), n, d, va, a, vb, b)
    case _:
      Eval.fz.zf(~F32, ~U32, ~(x => y => F32.add(x, D.I32.to_f32(D.I32{y}))), n, d, va, a, vb, b)

# ---- the operand's side: what the pre-operation makes of it --------------------------------------

# fill_null's literal is the dtype default of a word / f32 column (+0.0 by its bits, never -0.0), so
# F4 fires: Z0 resets the null slots to it (Eval.fz.z0 / dc); a fill side of Z1 / Z2 (a frame column
# only) reads the slots as stored, which hold it by the P0 invariant of every stored column
def Eval.fz.isdef(v: D.Scalar, t: D.DType) -> Bool:
  match v t:
    case D.SU32{w} D.TU32{}:
      U32.is_zero(w)
    case D.SI32{x} D.TI32{}:
      U32.is_zero(D.I32.to_u32(x))
    case D.SBool{b} D.TBool{}:
      Bool.not(b)
    case D.SF32{x} D.TF32{}:
      U32.is_zero(F32.bits(x))
    case _ _:
      False{}

# a side of a fused zip: whether its pre-operation fires, whether that is a fill (the validity is
# then read as AllValid), the dtype the kernel computes in, whether the words are cast to f32
type Side is Data:
  Side{ok: Bool, fill: Bool, t: D.DType, cast: Bool}

# the total casts F3 folds (Eval.cast.u / cast.i / cast.b to f32) and the identity; any other cast
# (fallible: f32 -> u32, str -> ..., u32 -> i32, ...) does not fire
def Eval.fz.cside(t: D.DType, to: D.DType) -> Side:
  match t to:
    case D.TU32{} D.TF32{}:
      Side{True{}, False{}, D.TF32{}, True{}}
    case D.TBool{} D.TF32{}:
      Side{True{}, False{}, D.TF32{}, True{}}
    case D.TI32{} D.TF32{}:
      Side{True{}, False{}, D.TF32{}, True{}}
    case D.TU32{} D.TU32{}:
      Side{True{}, False{}, D.TU32{}, False{}}
    case D.TI32{} D.TI32{}:
      Side{True{}, False{}, D.TI32{}, False{}}
    case D.TF32{} D.TF32{}:
      Side{True{}, False{}, D.TF32{}, False{}}
    case _ _:
      Side{False{}, False{}, D.TStr{}, False{}}

def Eval.fz.side(pre: Pre, +t: D.DType) -> Side:
  match pre:
    case PNone{}:
      Side{True{}, False{}, t, False{}}
    case PFill{v}:
      Side{Eval.fz.isdef(v, t), True{}, t, False{}}
    case PCast{to}:
      Eval.fz.cside(t, to)

# a fired fill reads the column with validity AllValid; the mask is kept aside and put back after.
# Only frame columns get here (the selector folds a fill only after ICol / IMove), and the null slots
# are read as stored: correct because a stored column holds the default under its nulls (P0; the
# producer audit in DESIGN.md 14 "v0.2 post-review: the null-slot invariant", checked on every
# differential result by src/p0.bend)
def Eval.fz.view(fill: Bool, c: C.Column) -> C.Column & C.Valid:
  match fill:
    case True{}:
      C.Column.take_valid(c)
    case False{}:
      (c, C.AllValid{})

def Eval.fz.unview(fill: Bool, c: C.Column, aside: C.Valid) -> C.Column:
  match fill:
    case True{}:
      C.Column.set_valid(c, aside)
    case False{}:
      c

# ---- Z2 (F2 / F3): a op b ------------------------------------------------------------------------

# the kernel family: none; word columns of one dtype (u32 / i32); f32 columns; f32 arithmetic with
# one side's words cast to f32
type K2 is Data:
  KNo{}
  KW{}
  KF{}
  KC{}

def Eval.fz.k2.f(+op: X.BinOp, ca: Bool, cb: Bool) -> K2:
  match ca cb:
    case False{} False{}:
      KF{}
    case True{} True{}:
      KNo{}
    case _ _:
      Bool.pick(K2, Eval.is_cmp(op), KNo{}, KC{})

def Eval.fz.k2.t(t: D.DType, +op: X.BinOp, ca: Bool, cb: Bool) -> K2:
  match t:
    case D.TU32{}:
      Bool.pick(K2, Eval.fz.isdiv(op), KNo{}, KW{})
    case D.TI32{}:
      Bool.pick(K2, Eval.fz.isdiv(op), KNo{}, KW{})
    case D.TF32{}:
      Eval.fz.k2.f(op, ca, cb)
    case _:
      KNo{}

def Eval.fz.k2.g(go: Bool, t: D.DType, +op: X.BinOp, ca: Bool, cb: Bool) -> K2:
  match go:
    case True{}:
      Eval.fz.k2.t(t, op, ca, cb)
    case False{}:
      KNo{}

# the family of a op b over operands of equal length (eq) after their pre-operations: both fire,
# one dtype, a fused op
def Eval.fz.k2(eq: Bool, +op: X.BinOp, sa: Side, sb: Side) -> K2:
  match sa sb:
    case Side{oka, fa, +ta, ca} Side{okb, fb, tb, cb}:
      Eval.fz.k2.g(Bool.and(Bool.and(oka, okb), Bool.and(eq, Bool.and(Eval.fz.op_ok(op), D.DType.eq(ta, tb)))), ta, op, ca, cb)

type Z2R is Type:
  Z2R{r: Maybe<&1, C.Column>, a: C.Column, b: C.Column}

def Eval.fz.zr.ww(ta: D.DType, tb: D.DType, +n: U32, +d: Nat, +n2: U32, +d2: Nat, r: ZR<U32, U32>) -> Z2R:
  match r:
    case ZR{c, va, a, vb, b}:
      Z2R{Some{c}, C.Column.mk_w(ta, n, d, va, a), C.Column.mk_w(tb, n2, d2, vb, b)}

def Eval.fz.zr.ff(+n: U32, +d: Nat, +n2: U32, +d2: Nat, r: ZR<F32, F32>) -> Z2R:
  match r:
    case ZR{c, va, a, vb, b}:
      Z2R{Some{c}, C.CF32{n, d, va, a}, C.CF32{n2, d2, vb, b}}

def Eval.fz.zr.wf(ta: D.DType, +n: U32, +d: Nat, +n2: U32, +d2: Nat, r: ZR<U32, F32>) -> Z2R:
  match r:
    case ZR{c, va, a, vb, b}:
      Z2R{Some{c}, C.Column.mk_w(ta, n, d, va, a), C.CF32{n2, d2, vb, b}}

def Eval.fz.zr.fw(tb: D.DType, +n: U32, +d: Nat, +n2: U32, +d2: Nat, r: ZR<F32, U32>) -> Z2R:
  match r:
    case ZR{c, va, a, vb, b}:
      Z2R{Some{c}, C.CF32{n, d, va, a}, C.Column.mk_w(tb, n2, d2, vb, b)}

# the kernel of the family over the two columns (validity as the kernel reads it); the output has
# a's length and depth, as Eval.bin's
def Eval.fz.z2k(k: K2, +op: X.BinOp, a: C.Column, b: C.Column) -> Z2R:
  match k a b:
    case KW{} C.CU32{+n, +d, va, xa} C.CU32{+n2, +d2, vb, xb}:
      Eval.fz.zr.ww(D.TU32{}, D.TU32{}, n, d, n2, d2, Eval.fz.wu(op, Eval.bin.t(Eval.is_cmp(op), D.TU32{}), n, d, va, xa, vb, xb))
    case KW{} C.CI32{+n, +d, va, xa} C.CI32{+n2, +d2, vb, xb}:
      Eval.fz.zr.ww(D.TI32{}, D.TI32{}, n, d, n2, d2, Eval.fz.wi(op, Eval.bin.t(Eval.is_cmp(op), D.TI32{}), n, d, va, xa, vb, xb))
    case KF{} C.CF32{+n, +d, va, xa} C.CF32{+n2, +d2, vb, xb}:
      Eval.fz.zr.ff(n, d, n2, d2, Eval.fz.ff(Eval.is_cmp(op), op, n, d, va, xa, vb, xb))
    case KC{} C.CU32{+n, +d, va, xa} C.CF32{+n2, +d2, vb, xb}:
      Eval.fz.zr.wf(D.TU32{}, n, d, n2, d2, Eval.fz.cu(op, n, d, va, xa, vb, xb))
    case KC{} C.CBool{+n, +d, va, xa} C.CF32{+n2, +d2, vb, xb}:
      Eval.fz.zr.wf(D.TBool{}, n, d, n2, d2, Eval.fz.cu(op, n, d, va, xa, vb, xb))
    case KC{} C.CI32{+n, +d, va, xa} C.CF32{+n2, +d2, vb, xb}:
      Eval.fz.zr.wf(D.TI32{}, n, d, n2, d2, Eval.fz.ci(op, n, d, va, xa, vb, xb))
    case KC{} C.CF32{+n, +d, va, xa} C.CU32{+n2, +d2, vb, xb}:
      Eval.fz.zr.fw(D.TU32{}, n, d, n2, d2, Eval.fz.uc(op, n, d, va, xa, vb, xb))
    case KC{} C.CF32{+n, +d, va, xa} C.CBool{+n2, +d2, vb, xb}:
      Eval.fz.zr.fw(D.TBool{}, n, d, n2, d2, Eval.fz.uc(op, n, d, va, xa, vb, xb))
    case KC{} C.CF32{+n, +d, va, xa} C.CI32{+n2, +d2, vb, xb}:
      Eval.fz.zr.fw(D.TI32{}, n, d, n2, d2, Eval.fz.ic(op, n, d, va, xa, vb, xb))
    case _ a2 b2:
      Z2R{None{}, a2, b2}

def Eval.fz.z2.e(fa: Bool, fb: Bool, xa: C.Valid, xb: C.Valid, r: Z2R) -> Z2R:
  match r:
    case Z2R{res, a, b}:
      Z2R{res, Eval.fz.unview(fa, a, xa), Eval.fz.unview(fb, b, xb)}

def Eval.fz.z2.d(k: K2, +op: X.BinOp, fa: Bool, fb: Bool, ra: C.Column & C.Valid, rb: C.Column & C.Valid) -> Z2R:
  (a, xa) = ra
  (b, xb) = rb
  Eval.fz.z2.e(fa, fb, xa, xb, Eval.fz.z2k(k, op, a, b))

def Eval.fz.z2.c(k: K2, +op: X.BinOp, +fa: Bool, +fb: Bool, a: C.Column, b: C.Column) -> Z2R:
  match k:
    case KNo{}:
      Z2R{None{}, a, b}
    case k2:
      Eval.fz.z2.d(k2, op, fa, fb, Eval.fz.view(fa, a), Eval.fz.view(fb, b))

def Eval.fz.z2.b(+op: X.BinOp, +eq: Bool, sa: Side, sb: Side, a: C.Column, b: C.Column) -> Z2R:
  match sa sb:
    case Side{oka, +fa, +ta, ca} Side{okb, +fb, +tb, cb}:
      Eval.fz.z2.c(Eval.fz.k2(eq, op, Side{oka, fa, ta, ca}, Side{okb, fb, tb, cb}), op, fa, fb, a, b)

def Eval.fz.z2.a(+op: X.BinOp, pa: Pre, pb: Pre, +eq: Bool, ra: C.Column & D.DType, rb: C.Column & D.DType) -> Z2R:
  (a, +ta) = ra
  (b, +tb) = rb
  Eval.fz.z2.b(op, eq, Eval.fz.side(pa, ta), Eval.fz.side(pb, tb), a, b)

def Eval.fz.z2.l(+op: X.BinOp, pa: Pre, pb: Pre, ra: C.Column & U32, rb: C.Column & U32) -> Z2R:
  (a, +la) = ra
  (b, +lb) = rb
  Eval.fz.z2.a(op, pa, pb, U32.is_eq(la, lb), C.Column.dtype(a), C.Column.dtype(b))

# F2 / F3: a op b over two columns of one length (pre-operations pa, pb), both handed back
def Eval.fz.z2(+op: X.BinOp, pa: Pre, pb: Pre, a: C.Column, b: C.Column) -> Z2R:
  Eval.fz.z2.l(op, pa, pb, C.Column.len(a), C.Column.len(b))

# ---- Z1 (F1): a op lit, lit op a ------------------------------------------------------------------

type LR<-T: Data> is Type:
  LR{c: C.Column, v: C.Valid, a: Array<T>}

def Eval.fz.lw.m(~T: Data, rt: D.DType, +n: U32, d: Nat, r: Array<U32> & Array<T>) -> LR<T>:
  (o, a) = r
  LR{C.Column.mk_w(rt, n, d, C.AllValid{}, o), C.AllValid{}, a}

def Eval.fz.lw.r(~T: Data, rt: D.DType, +n: U32, d: Nat, r: K.ZV<T, T, U32>) -> LR<T>:
  match r:
    case K.ZV{o, vo, a, va, b, vb}:
      LR{C.Column.mk_w(rt, n, d, C.Mask{vo}, o), C.Mask{va}, a}

def Eval.fz.lw.l(~T: Data, rt: D.DType, +n: U32, d: Nat, r: K.ZV<T, T, U32>) -> LR<T>:
  match r:
    case K.ZV{o, vo, a, va, b, vb}:
      LR{C.Column.mk_w(rt, n, d, C.Mask{vo}, o), C.Mask{vb}, b}

# F1 into words: the literal p a scalar parameter of map_pb (an AllValid operand), or a 1-slot array
# of zipv next to the operand's mask (the result's validity the operand's, its null slots 0)
def Eval.fz.lw(~T: Data, ~f: T -> T -> U32, rt: D.DType, left: Bool, +n: U32, +d: Nat, v: C.Valid, a: Array<T>, +p: T) -> LR<T>:
  match left v:
    case False{} C.AllValid{}:
      Eval.fz.lw.m(~T, rt, n, d, K.Kernel.map_pb(~T, ~T, ~U32, ~(q => x => f(x, q)), n, d, a, p, 0))
    case True{} C.AllValid{}:
      Eval.fz.lw.m(~T, rt, n, d, K.Kernel.map_pb(~T, ~T, ~U32, ~(q => x => f(q, x)), n, d, a, p, 0))
    case False{} C.Mask{m}:
      Eval.fz.lw.r(~T, rt, n, d, K.Kernel.zipv(~T, ~T, ~U32, ~f, n, d, a, m, Array.new(T, 0n, p), Eval.fz.ones(), 0))
    case True{} C.Mask{m}:
      Eval.fz.lw.l(~T, rt, n, d, K.Kernel.zipv(~T, ~T, ~U32, ~f, n, d, Array.new(T, 0n, p), Eval.fz.ones(), a, m, 0))

def Eval.fz.lf.m(+n: U32, d: Nat, r: Array<F32> & Array<F32>) -> LR<F32>:
  (o, a) = r
  LR{C.CF32{n, d, C.AllValid{}, o}, C.AllValid{}, a}

def Eval.fz.lf.r(+n: U32, d: Nat, r: K.ZV<F32, F32, F32>) -> LR<F32>:
  match r:
    case K.ZV{o, vo, a, va, b, vb}:
      LR{C.CF32{n, d, C.Mask{vo}, o}, C.Mask{va}, a}

def Eval.fz.lf.l(+n: U32, d: Nat, r: K.ZV<F32, F32, F32>) -> LR<F32>:
  match r:
    case K.ZV{o, vo, a, va, b, vb}:
      LR{C.CF32{n, d, C.Mask{vo}, o}, C.Mask{vb}, b}

# F1 into f32 (f32 arithmetic)
def Eval.fz.lf(~f: F32 -> F32 -> F32, left: Bool, +n: U32, +d: Nat, v: C.Valid, a: Array<F32>, +p: F32) -> LR<F32>:
  match left v:
    case False{} C.AllValid{}:
      Eval.fz.lf.m(n, d, K.Kernel.map_pb(~F32, ~F32, ~F32, ~(q => x => f(x, q)), n, d, a, p, 0.0))
    case True{} C.AllValid{}:
      Eval.fz.lf.m(n, d, K.Kernel.map_pb(~F32, ~F32, ~F32, ~(q => x => f(q, x)), n, d, a, p, 0.0))
    case False{} C.Mask{m}:
      Eval.fz.lf.r(n, d, K.Kernel.zipv(~F32, ~F32, ~F32, ~f, n, d, a, m, Array.new(F32, 0n, p), Eval.fz.ones(), 0.0))
    case True{} C.Mask{m}:
      Eval.fz.lf.l(n, d, K.Kernel.zipv(~F32, ~F32, ~F32, ~f, n, d, Array.new(F32, 0n, p), Eval.fz.ones(), a, m, 0.0))

# u32 words with a literal (Eval.zip.u's templates)
def Eval.fz.lu(op: X.BinOp, rt: D.DType, left: Bool, +n: U32, +d: Nat, v: C.Valid, a: Array<U32>, +p: U32) -> LR<U32>:
  match op:
    case X.Add{}:
      Eval.fz.lw(~U32, ~(x => y => U32.add(x, y)), rt, left, n, d, v, a, p)
    case X.Sub{}:
      Eval.fz.lw(~U32, ~(x => y => U32.sub(x, y)), rt, left, n, d, v, a, p)
    case X.Mul{}:
      Eval.fz.lw(~U32, ~(x => y => U32.mul(x, y)), rt, left, n, d, v, a, p)
    case X.Eq{}:
      Eval.fz.lw(~U32, ~(x => y => Bool.to_u32(U32.is_eq(x, y))), rt, left, n, d, v, a, p)
    case X.Ne{}:
      Eval.fz.lw(~U32, ~(x => y => Bool.to_u32(U32.is_ne(x, y))), rt, left, n, d, v, a, p)
    case X.Lt{}:
      Eval.fz.lw(~U32, ~(x => y => Bool.to_u32(U32.is_lt(x, y))), rt, left, n, d, v, a, p)
    case X.Le{}:
      Eval.fz.lw(~U32, ~(x => y => Bool.to_u32(U32.is_le(x, y))), rt, left, n, d, v, a, p)
    case X.Gt{}:
      Eval.fz.lw(~U32, ~(x => y => Bool.to_u32(U32.is_gt(x, y))), rt, left, n, d, v, a, p)
    case _:
      Eval.fz.lw(~U32, ~(x => y => Bool.to_u32(U32.is_ge(x, y))), rt, left, n, d, v, a, p)

# i32 bits with a literal (Eval.zip.i's comparisons, else the word ops)
def Eval.fz.li(op: X.BinOp, rt: D.DType, left: Bool, +n: U32, +d: Nat, v: C.Valid, a: Array<U32>, +p: U32) -> LR<U32>:
  match op:
    case X.Lt{}:
      Eval.fz.lw(~U32, ~(x => y => Bool.to_u32(Eval.i32_lt(x, y))), rt, left, n, d, v, a, p)
    case X.Le{}:
      Eval.fz.lw(~U32, ~(x => y => Bool.to_u32(Bool.not(Eval.i32_lt(y, x)))), rt, left, n, d, v, a, p)
    case X.Gt{}:
      Eval.fz.lw(~U32, ~(x => y => Bool.to_u32(Eval.i32_lt(y, x))), rt, left, n, d, v, a, p)
    case X.Ge{}:
      Eval.fz.lw(~U32, ~(x => y => Bool.to_u32(Bool.not(Eval.i32_lt(x, y)))), rt, left, n, d, v, a, p)
    case other:
      Eval.fz.lu(other, rt, left, n, d, v, a, p)

# f32 with a literal: comparisons into words (Eval.zip.fc), arithmetic into f32 (Eval.zip.fa)
def Eval.fz.lfo(op: X.BinOp, left: Bool, +n: U32, +d: Nat, v: C.Valid, a: Array<F32>, +p: F32) -> LR<F32>:
  match op:
    case X.Ne{}:
      Eval.fz.lw(~F32, ~(x => y => Bool.to_u32(U32.is_ne(K.Kernel.fword(x), K.Kernel.fword(y)))), D.TBool{}, left, n, d, v, a, p)
    case X.Lt{}:
      Eval.fz.lw(~F32, ~(x => y => Bool.to_u32(U32.is_lt(K.Kernel.fword(x), K.Kernel.fword(y)))), D.TBool{}, left, n, d, v, a, p)
    case X.Le{}:
      Eval.fz.lw(~F32, ~(x => y => Bool.to_u32(U32.is_le(K.Kernel.fword(x), K.Kernel.fword(y)))), D.TBool{}, left, n, d, v, a, p)
    case X.Gt{}:
      Eval.fz.lw(~F32, ~(x => y => Bool.to_u32(U32.is_gt(K.Kernel.fword(x), K.Kernel.fword(y)))), D.TBool{}, left, n, d, v, a, p)
    case X.Ge{}:
      Eval.fz.lw(~F32, ~(x => y => Bool.to_u32(U32.is_ge(K.Kernel.fword(x), K.Kernel.fword(y)))), D.TBool{}, left, n, d, v, a, p)
    case X.Eq{}:
      Eval.fz.lw(~F32, ~(x => y => Bool.to_u32(U32.is_eq(K.Kernel.fword(x), K.Kernel.fword(y)))), D.TBool{}, left, n, d, v, a, p)
    case X.Sub{}:
      Eval.fz.lf(~(x => y => F32.sub(x, y)), left, n, d, v, a, p)
    case X.Mul{}:
      Eval.fz.lf(~(x => y => F32.mul(x, y)), left, n, d, v, a, p)
    case X.Div{}:
      Eval.fz.lf(~(x => y => F32.div(x, y)), left, n, d, v, a, p)
    case _:
      Eval.fz.lf(~(x => y => F32.add(x, y)), left, n, d, v, a, p)

type Z1R is Type:
  Z1R{r: Maybe<&1, C.Column>, a: C.Column}

def Eval.fz.l.w(t: D.DType, +n: U32, +d: Nat, r: LR<U32>) -> Z1R:
  match r:
    case LR{c, v, a}:
      Z1R{Some{c}, C.Column.mk_w(t, n, d, v, a)}

def Eval.fz.l.f(+n: U32, +d: Nat, r: LR<F32>) -> Z1R:
  match r:
    case LR{c, v, a}:
      Z1R{Some{c}, C.CF32{n, d, v, a}}

# F1 over a column (its validity as the kernel reads it) and a literal of its dtype; any other
# pair (a bool or str column, a null or other-dtype literal) has no kernel
def Eval.fz.z1c(+op: X.BinOp, left: Bool, c: C.Column, v: D.Scalar) -> Z1R:
  match c v:
    case C.CU32{+n, +d, va, a} D.SU32{+p}:
      Eval.fz.l.w(D.TU32{}, n, d, Eval.fz.lu(op, Eval.bin.t(Eval.is_cmp(op), D.TU32{}), left, n, d, va, a, p))
    case C.CI32{+n, +d, va, a} D.SI32{+p}:
      Eval.fz.l.w(D.TI32{}, n, d, Eval.fz.li(op, Eval.bin.t(Eval.is_cmp(op), D.TI32{}), left, n, d, va, a, D.I32.to_u32(p)))
    case C.CF32{+n, +d, va, a} D.SF32{+p}:
      Eval.fz.l.f(n, d, Eval.fz.lfo(op, left, n, d, va, a, p))
    case c2 v2:
      Z1R{None{}, c2}

def Eval.fz.z1.e(fill: Bool, x: C.Valid, r: Z1R) -> Z1R:
  match r:
    case Z1R{res, a}:
      Z1R{res, Eval.fz.unview(fill, a, x)}

def Eval.fz.z1.d(+fill: Bool, +op: X.BinOp, left: Bool, v: D.Scalar, r: C.Column & C.Valid) -> Z1R:
  (c, x) = r
  Eval.fz.z1.e(fill, x, Eval.fz.z1c(op, left, c, v))

def Eval.fz.z1.c(go: Bool, +fill: Bool, +op: X.BinOp, left: Bool, v: D.Scalar, c: C.Column) -> Z1R:
  match go:
    case True{}:
      Eval.fz.z1.d(fill, op, left, v, Eval.fz.view(fill, c))
    case False{}:
      Z1R{None{}, c}

def Eval.fz.z1.b(+op: X.BinOp, left: Bool, v: D.Scalar, s: Side, c: C.Column) -> Z1R:
  match s:
    case Side{ok, +fill, t, cast}:
      Eval.fz.z1.c(Bool.and(Bool.and(ok, Bool.not(cast)), Bool.and(Eval.fz.op_ok(op), Bool.or(D.DType.eq(t, D.TF32{}), Bool.not(Eval.fz.isdiv(op))))), fill, op, left, v, c)

def Eval.fz.z1.a(+op: X.BinOp, left: Bool, v: D.Scalar, pre: Pre, r: C.Column & D.DType) -> Z1R:
  (c, +t) = r
  Eval.fz.z1.b(op, left, v, Eval.fz.side(pre, t), c)

# F1: c op v (left False) or v op c (left True), c's pre-operation pre (none or a fill of the
# default); c handed back
def Eval.fz.z1(+op: X.BinOp, v: D.Scalar, left: Bool, pre: Pre, c: C.Column) -> Z1R:
  Eval.fz.z1.a(op, left, v, pre, C.Column.dtype(c))

# ---- Z0 (F4): fill_null(c, default) ----------------------------------------------------------------

type Z0R is Type:
  Z0R{ok: Bool, c: C.Column}

# F4 fires: a fill of a word / f32 column with its dtype default
def Eval.fz.f4(pre: Pre, +t: D.DType) -> Bool:
  match pre:
    case PFill{v}:
      Eval.fz.isdef(v, t)
    case _:
      False{}

# F4 fires on an owned column: the null slots reset to the default IN PLACE (Eval.fix: one
# Kernel.mask_data pass, nothing allocated; nothing at all when AllValid), then validity AllValid.
# Post-review B1: v0.2 skipped the reset on the premise that every null slot already holds the
# default (P0), which F32 neg broke; the reset makes F4 equal Eval.fill whatever the operand's slots
# hold (LAWS peep_f4_cell has no slot hypothesis), so a producer that breaks P0 can no longer make a
# null row of fill_null(e, default) answer anything but the default.
def Eval.fz.z0.b(go: Bool, c: C.Column) -> Z0R:
  match go:
    case True{}:
      Z0R{True{}, C.Column.set_valid(Eval.fix(c), C.AllValid{})}
    case False{}:
      Z0R{False{}, c}

def Eval.fz.z0.a(pre: Pre, r: C.Column & D.DType) -> Z0R:
  (c, +t) = r
  Eval.fz.z0.b(Eval.fz.f4(pre, t), c)

# F4 on an owned column: fill_null with the dtype default is the column with its null slots reset to
# the default (in place) and validity AllValid. NOT a no-op: the validity changes
def Eval.fz.z0(pre: Pre, c: C.Column) -> Z0R:
  Eval.fz.z0.a(pre, C.Column.dtype(c))

def Eval.fz.dc.w(+t: D.DType, +n: U32, +d: Nat, r: Array<U32> & Array<U32>) -> Z1R:
  (x1, x2) = r
  Z1R{Some{C.Column.mk_w(t, n, d, C.AllValid{}, x1)}, C.Column.mk_w(t, n, d, C.AllValid{}, x2)}

def Eval.fz.dc.f(+n: U32, +d: Nat, r: Array<F32> & Array<F32>) -> Z1R:
  (x1, x2) = r
  Z1R{Some{C.CF32{n, d, C.AllValid{}, x1}}, C.CF32{n, d, C.AllValid{}, x2}}

def Eval.fz.dm.w(+t: D.DType, +n: U32, +d: Nat, r: K.ZB<U32, U32, U32>) -> Z1R:
  match r:
    case K.ZB{o, x, m}:
      Z1R{Some{C.Column.mk_w(t, n, d, C.AllValid{}, o)}, C.Column.mk_w(t, n, d, C.Mask{m}, x)}

def Eval.fz.dm.f(+n: U32, +d: Nat, r: K.ZB<F32, U32, F32>) -> Z1R:
  match r:
    case K.ZB{o, x, m}:
      Z1R{Some{C.CF32{n, d, C.AllValid{}, o}}, C.CF32{n, d, C.Mask{m}, x}}

# a borrowed word column's fill: an AllValid one is copied as is; a masked one gets a masked copy
# (Kernel.zipb over the data and the mask, both handed back: m[i] != 0 ? x[i] : 0, one loop)
def Eval.fz.dc.wv(+t: D.DType, +n: U32, +d: Nat, v: C.Valid, x: Array<U32>) -> Z1R:
  match v:
    case C.AllValid{}:
      Eval.fz.dc.w(t, n, d, Array.clone(U32, x))
    case C.Mask{m}:
      Eval.fz.dm.w(t, n, d, K.Kernel.zipb(~U32, ~U32, ~U32, ~(w => k => Bool.pick(U32, U32.is_ne(k, 0), w, 0)), n, d, x, m, 0))

def Eval.fz.dc.fv(+n: U32, +d: Nat, v: C.Valid, x: Array<F32>) -> Z1R:
  match v:
    case C.AllValid{}:
      Eval.fz.dc.f(n, d, Array.clone(F32, x))
    case C.Mask{m}:
      Eval.fz.dm.f(n, d, K.Kernel.zipb(~F32, ~U32, ~F32, ~(w => k => Bool.pick(F32, U32.is_ne(k, 0), w, 0.0)), n, d, x, m, 0.0))

# F4 on a BORROWED column: the result needs its own payload because the frame keeps the column
# (a move cannot work: the reference is not the column's last); one masked copy of the data buffer
# (the null slots written as the default, post-review B1: the frame's column is not trusted to hold
# it), the column handed back unchanged (v0.1 copied data and mask, then ran Kernel.choose over the copy)
def Eval.fz.dc(c: C.Column) -> Z1R:
  match c:
    case C.CBool{+n, +d, v, x}:
      Eval.fz.dc.wv(D.TBool{}, n, d, v, x)
    case C.CU32{+n, +d, v, x}:
      Eval.fz.dc.wv(D.TU32{}, n, d, v, x)
    case C.CI32{+n, +d, v, x}:
      Eval.fz.dc.wv(D.TI32{}, n, d, v, x)
    case C.CF32{+n, +d, v, x}:
      Eval.fz.dc.fv(n, d, v, x)
    case C.CStr{n, d, v, x}:
      Z1R{None{}, C.CStr{n, d, v, x}}

def Eval.fz.z0b.b(go: Bool, c: C.Column) -> Z1R:
  match go:
    case True{}:
      Eval.fz.dc(c)
    case False{}:
      Z1R{None{}, c}

def Eval.fz.z0b.a(pre: Pre, r: C.Column & D.DType) -> Z1R:
  (c, +t) = r
  Eval.fz.z0b.b(Eval.fz.f4(pre, t), c)

def Eval.fz.z0b(pre: Pre, c: C.Column) -> Z1R:
  Eval.fz.z0b.a(pre, C.Column.dtype(c))

# ---- the executor: a fused fragment over the stack machine's state --------------------------------
#
# The operands are taken (popped, or lent from the frame), the column-level operation runs, and a
# borrowed column goes back into the frame at its place (Frame.replace; a moved one leaves its
# hollow stand-in, as IMove does). When the operation answers None, every operand goes back where
# it was and `orig` runs (Eval.run): the unfused code from the very same state.

# a lent column after the kernel: back into the frame (a borrow), or dropped (a move)
def Eval.fz.put(+h: U32, mv: Bool, name: String, f: C.Frame, c: C.Column) -> C.Frame:
  match mv:
    case True{}:
      f
    case False{}:
      C.Frame.replace.c(f, name, c, h)

def Eval.fz.x1.s(+h: U32, +k: SKind, rest: List<&1, Slot>, orig: List<&2, Instr>, f: C.Frame, r: Z1R) -> EvSt:
  match r:
    case Z1R{Some{c}, a}:
      EvSt{f, Done{Slot{k, c} <> rest}}
    case Z1R{None{}, a}:
      Eval.run(orig, h, EvSt{f, Done{Slot{k, a} <> rest}})

def Eval.fz.x1.stk(+h: U32, +op: X.BinOp, v: D.Scalar, left: Bool, pa: Pre, orig: List<&2, Instr>, f: C.Frame, stk: List<&1, Slot>) -> EvSt:
  match stk:
    case Slot{k, c} <> rest:
      Eval.fz.x1.s(h, k, rest, orig, f, Eval.fz.z1(op, v, left, pa, c))
    case Nil{}:
      Eval.run(orig, h, EvSt{f, Done{Nil{}}})

def Eval.fz.x1.rk(+h: U32, +name: String, mv: Bool, stk: List<&1, Slot>, orig: List<&2, Instr>, f: C.Frame, r: Z1R) -> EvSt:
  match r:
    case Z1R{Some{c}, a}:
      EvSt{Eval.fz.put(h, mv, name, f, a), Done{Slot{KFull{}, c} <> stk}}
    case Z1R{None{}, a}:
      Eval.run(orig, h, EvSt{C.Frame.replace.c(f, name, a, h), Done{stk}})

def Eval.fz.x1.r(+h: U32, +op: X.BinOp, v: D.Scalar, left: Bool, pa: Pre, +name: String, mv: Bool, orig: List<&2, Instr>, stk: List<&1, Slot>, r: C.Frame & E.ResT(C.Column)) -> EvSt:
  (f, rc) = r
  match rc:
    case Done{c}:
      Eval.fz.x1.rk(h, name, mv, stk, orig, f, Eval.fz.z1(op, v, left, pa, c))
    case Fail{e}:
      Eval.run(orig, h, EvSt{f, Done{stk}})

def Eval.fz.x1(+h: U32, +op: X.BinOp, v: D.Scalar, left: Bool, a: Opd, pa: Pre, orig: List<&2, Instr>, f: C.Frame, stk: List<&1, Slot>) -> EvSt:
  match a:
    case OStk{}:
      Eval.fz.x1.stk(h, op, v, left, pa, orig, f, stk)
    case ORef{+name, mv}:
      Eval.fz.x1.r(h, op, v, left, pa, name, mv, orig, stk, C.Frame.lend(f, name))

def Eval.fz.x2.ss.k(+h: U32, ka: SKind, kb: SKind, rest: List<&1, Slot>, orig: List<&2, Instr>, f: C.Frame, r: Z2R) -> EvSt:
  match r:
    case Z2R{Some{c}, a, b}:
      EvSt{f, Done{Slot{KFull{}, c} <> rest}}
    case Z2R{None{}, a, b}:
      Eval.run(orig, h, EvSt{f, Done{Slot{kb, b} <> Slot{ka, a} <> rest}})

# only two full columns fuse: a 1-row side (a literal, an aggregation) broadcasts in `orig`
def Eval.fz.z2f(full: Bool, +op: X.BinOp, pa: Pre, pb: Pre, a: C.Column, b: C.Column) -> Z2R:
  match full:
    case True{}:
      Eval.fz.z2(op, pa, pb, a, b)
    case False{}:
      Z2R{None{}, a, b}

def Eval.fz.x2.ss(+h: U32, +op: X.BinOp, pa: Pre, pb: Pre, orig: List<&2, Instr>, f: C.Frame, stk: List<&1, Slot>) -> EvSt:
  match stk:
    case Slot{+kb, b} <> Slot{+ka, a} <> rest:
      Eval.fz.x2.ss.k(h, ka, kb, rest, orig, f, Eval.fz.z2f(Bool.and(SKind.is_full(ka), SKind.is_full(kb)), op, pa, pb, a, b))
    case other:
      Eval.run(orig, h, EvSt{f, Done{other}})

def Eval.fz.x2.sr.k(+h: U32, ka: SKind, +nb: String, mvb: Bool, rest: List<&1, Slot>, orig: List<&2, Instr>, f: C.Frame, r: Z2R) -> EvSt:
  match r:
    case Z2R{Some{c}, a, b}:
      EvSt{Eval.fz.put(h, mvb, nb, f, b), Done{Slot{KFull{}, c} <> rest}}
    case Z2R{None{}, a, b}:
      Eval.run(orig, h, EvSt{C.Frame.replace.c(f, nb, b, h), Done{Slot{ka, a} <> rest}})

def Eval.fz.x2.sr.b(+h: U32, +op: X.BinOp, pa: Pre, pb: Pre, +nb: String, mvb: Bool, orig: List<&2, Instr>, +ka: SKind, a: C.Column, rest: List<&1, Slot>, r: C.Frame & E.ResT(C.Column)) -> EvSt:
  (f, rc) = r
  match rc:
    case Done{b}:
      Eval.fz.x2.sr.k(h, ka, nb, mvb, rest, orig, f, Eval.fz.z2f(SKind.is_full(ka), op, pa, pb, a, b))
    case Fail{e}:
      Eval.run(orig, h, EvSt{f, Done{Slot{ka, a} <> rest}})

def Eval.fz.x2.sr(+h: U32, +op: X.BinOp, pa: Pre, pb: Pre, +nb: String, mvb: Bool, orig: List<&2, Instr>, f: C.Frame, stk: List<&1, Slot>) -> EvSt:
  match stk:
    case Slot{ka, a} <> rest:
      Eval.fz.x2.sr.b(h, op, pa, pb, nb, mvb, orig, ka, a, rest, C.Frame.lend(f, nb))
    case Nil{}:
      Eval.run(orig, h, EvSt{f, Done{Nil{}}})

def Eval.fz.x2.rr.k(+h: U32, +na: String, mva: Bool, +nb: String, mvb: Bool, stk: List<&1, Slot>, orig: List<&2, Instr>, f: C.Frame, r: Z2R) -> EvSt:
  match r:
    case Z2R{Some{c}, a, b}:
      EvSt{Eval.fz.put(h, mvb, nb, Eval.fz.put(h, mva, na, f, a), b), Done{Slot{KFull{}, c} <> stk}}
    case Z2R{None{}, a, b}:
      Eval.run(orig, h, EvSt{C.Frame.replace.c(C.Frame.replace.c(f, na, a, h), nb, b, h), Done{stk}})

def Eval.fz.x2.rr.b(+h: U32, +op: X.BinOp, pa: Pre, pb: Pre, +na: String, mva: Bool, +nb: String, mvb: Bool, orig: List<&2, Instr>, stk: List<&1, Slot>, a: C.Column, r: C.Frame & E.ResT(C.Column)) -> EvSt:
  (f, rc) = r
  match rc:
    case Done{b}:
      Eval.fz.x2.rr.k(h, na, mva, nb, mvb, stk, orig, f, Eval.fz.z2(op, pa, pb, a, b))
    case Fail{e}:
      Eval.run(orig, h, EvSt{C.Frame.replace.c(f, na, a, h), Done{stk}})

def Eval.fz.x2.rr(+h: U32, +op: X.BinOp, pa: Pre, pb: Pre, +na: String, mva: Bool, +nb: String, mvb: Bool, orig: List<&2, Instr>, stk: List<&1, Slot>, r: C.Frame & E.ResT(C.Column)) -> EvSt:
  (f, rc) = r
  match rc:
    case Done{a}:
      Eval.fz.x2.rr.b(h, op, pa, pb, na, mva, nb, mvb, orig, stk, a, C.Frame.lend(f, nb))
    case Fail{e}:
      Eval.run(orig, h, EvSt{f, Done{stk}})

def Eval.fz.x2(+h: U32, +op: X.BinOp, a: Opd, pa: Pre, b: Opd, pb: Pre, orig: List<&2, Instr>, f: C.Frame, stk: List<&1, Slot>) -> EvSt:
  match a b:
    case OStk{} OStk{}:
      Eval.fz.x2.ss(h, op, pa, pb, orig, f, stk)
    case OStk{} ORef{+nb, mvb}:
      Eval.fz.x2.sr(h, op, pa, pb, nb, mvb, orig, f, stk)
    case ORef{+na, mva} ORef{+nb, mvb}:
      Eval.fz.x2.rr(h, op, pa, pb, na, mva, nb, mvb, orig, stk, C.Frame.lend(f, na))
    case ORef{na, mva} OStk{}:
      Eval.run(orig, h, EvSt{f, Done{stk}})

def Eval.fz.x0.s.k(+h: U32, +k: SKind, rest: List<&1, Slot>, orig: List<&2, Instr>, f: C.Frame, r: Z0R) -> EvSt:
  match r:
    case Z0R{True{}, c}:
      EvSt{f, Done{Slot{k, c} <> rest}}
    case Z0R{False{}, c}:
      Eval.run(orig, h, EvSt{f, Done{Slot{k, c} <> rest}})

def Eval.fz.x0.stk(+h: U32, pa: Pre, orig: List<&2, Instr>, f: C.Frame, stk: List<&1, Slot>) -> EvSt:
  match stk:
    case Slot{k, c} <> rest:
      Eval.fz.x0.s.k(h, k, rest, orig, f, Eval.fz.z0(pa, c))
    case Nil{}:
      Eval.run(orig, h, EvSt{f, Done{Nil{}}})

def Eval.fz.x0.mk(+h: U32, +name: String, orig: List<&2, Instr>, stk: List<&1, Slot>, f: C.Frame, r: Z0R) -> EvSt:
  match r:
    case Z0R{True{}, c}:
      EvSt{f, Done{Slot{KFull{}, c} <> stk}}
    case Z0R{False{}, c}:
      Eval.run(orig, h, EvSt{C.Frame.replace.c(f, name, c, h), Done{stk}})

# a moved column is reused as the result (no copy); a borrowed one gives a copy of its data
def Eval.fz.x0.rm(+h: U32, mv: Bool, pa: Pre, +name: String, orig: List<&2, Instr>, stk: List<&1, Slot>, f: C.Frame, c: C.Column) -> EvSt:
  match mv:
    case True{}:
      Eval.fz.x0.mk(h, name, orig, stk, f, Eval.fz.z0(pa, c))
    case False{}:
      Eval.fz.x1.rk(h, name, False{}, stk, orig, f, Eval.fz.z0b(pa, c))

def Eval.fz.x0.r(+h: U32, pa: Pre, +name: String, mv: Bool, orig: List<&2, Instr>, stk: List<&1, Slot>, r: C.Frame & E.ResT(C.Column)) -> EvSt:
  (f, rc) = r
  match rc:
    case Done{c}:
      Eval.fz.x0.rm(h, mv, pa, name, orig, stk, f, c)
    case Fail{e}:
      Eval.run(orig, h, EvSt{f, Done{stk}})

def Eval.fz.x0(+h: U32, a: Opd, pa: Pre, orig: List<&2, Instr>, f: C.Frame, stk: List<&1, Slot>) -> EvSt:
  match a:
    case OStk{}:
      Eval.fz.x0.stk(h, pa, orig, f, stk)
    case ORef{+name, mv}:
      Eval.fz.x0.r(h, pa, name, mv, orig, stk, C.Frame.lend(f, name))

def Eval.fz.exec(+h: U32, fz: Fz, orig: List<&2, Instr>, f: C.Frame, stk: List<&1, Slot>) -> EvSt:
  match fz:
    case Z0{a, pa}:
      Eval.fz.x0(h, a, pa, orig, f, stk)
    case Z1{+op, v, left, a, pa}:
      Eval.fz.x1(h, op, v, left, a, pa, orig, f, stk)
    case Z2{+op, a, pa, b, pb}:
      Eval.fz.x2(h, op, a, pa, b, pb, orig, f, stk)

def Eval.stepz.i(+h: U32, i: Instr, f: C.Frame, stk: List<&1, Slot>) -> EvSt:
  match i:
    case IFz{fz, orig}:
      Eval.fz.exec(h, fz, orig, f, stk)
    case other:
      Eval.exec(h, other, f, stk)

def Eval.stepz.r(+h: U32, i: Instr, f: C.Frame, r: E.ResT(List<&1, Slot>)) -> EvSt:
  match r:
    case Fail{e}:
      EvSt{f, Fail{e}}
    case Done{stk}:
      Eval.stepz.i(h, i, f, stk)

def Eval.stepz(+h: U32, i: Instr, s: EvSt) -> EvSt:
  match s:
    case EvSt{f, r}:
      Eval.stepz.r(h, i, f, r)

# Eval.run over fused code: Eval.step for every instruction but IFz, which Eval.fz.exec runs
def Eval.runz(code: List<&2, Instr>, +h: U32, s: EvSt) -> EvSt:
  match code:
    case Nil{}:
      s
    case i <> t:
      Eval.runz(t, h, Eval.stepz(h, i, s))

# ---- W4 fusion: the filter predicate's mask and kept count (F5) -----------------------------------
#
# A predicate that is a conjunction (Bin{And} tree) of bool columns and comparisons `column op
# literal` (u32 / i32 / f32, the literal of the column's dtype, on the right) is computed by
# Kernel.pred_count passes over the BORROWED columns (Frame.lend, then Frame.replace: no predicate
# column is copied), each pass ANDing one conjunct into the mask so far and counting the kept rows
# in the same loop; a leading bool column and comparison share one pass (q1's `ok & (qty > 50)`).
# The mask of Kleene `&` under filter is "every conjunct true and valid", which is what the
# passes compute (a null row of any conjunct is dropped); Kleene `|` is not F5. The plan is static
# (the schema's dtypes, checked with the predicate's type); the passes are total.

type P5 is Data:
  T5B{name: String}
  T5C{op: X.BinOp, name: String, v: D.Scalar}
  T5BC{nb: String, op: X.BinOp, name: String, v: D.Scalar}

def Eval.f5.isbool(t: Maybe<&2, D.DType>) -> Bool:
  match t:
    case Some{D.TBool{}}:
      True{}
    case _:
      False{}

# the column's dtype is the literal's, a u32 / i32 / f32
def Eval.f5.num(t: Maybe<&2, D.DType>, v: D.Scalar) -> Bool:
  match t v:
    case Some{D.TU32{}} D.SU32{w}:
      True{}
    case Some{D.TI32{}} D.SI32{w}:
      True{}
    case Some{D.TF32{}} D.SF32{w}:
      True{}
    case _ _:
      False{}

def Eval.f5.one(ok: Bool, +t: P5) -> Maybe<&2, List<&2, P5>>:
  match ok:
    case True{}:
      Some{t <> Nil{}}
    case False{}:
      None{}

def Eval.f5.and(a: Maybe<&2, List<&2, P5>>, b: Maybe<&2, List<&2, P5>>) -> Maybe<&2, List<&2, P5>>:
  match a b:
    case Some{xs} Some{ys}:
      Some{List.append(&2, P5, xs, ys)}
    case _ _:
      None{}

def Eval.f5.cmp(+op: X.BinOp, a: X.Expr, b: X.Expr, +s: List<&2, S.Field>) -> Maybe<&2, List<&2, P5>>:
  match a b:
    case X.Col{+n} X.Lit{+v}:
      Eval.f5.one(Bool.and(Eval.fz.isrel(op), Eval.f5.num(S.Schema.find(s, n), v)), T5C{op, n, v})
    case _ _:
      None{}

def Eval.f5.bin(is_and: Bool, +op: X.BinOp, a: X.Expr, b: X.Expr, +s: List<&2, S.Field>, la: Maybe<&2, List<&2, P5>>, lb: Maybe<&2, List<&2, P5>>) -> Maybe<&2, List<&2, P5>>:
  match is_and:
    case True{}:
      Eval.f5.and(la, lb)
    case False{}:
      Eval.f5.cmp(op, a, b, s)

# the conjuncts of e, or None when some leaf is not a bool column or a fused comparison
def Eval.f5.leaves(e: X.Expr, +s: List<&2, S.Field>) -> Maybe<&2, List<&2, P5>>:
  match e:
    case X.Col{+n}:
      Eval.f5.one(Eval.f5.isbool(S.Schema.find(s, n)), T5B{n})
    case X.Bin{+op, +a, +b}:
      Eval.f5.bin(Eval.fz.is_and(op), op, a, b, s, Eval.f5.leaves(a, s), Eval.f5.leaves(b, s))
    case _:
      None{}

# a leading bool column and comparison share one pass
def Eval.f5.plan.k(xs: List<&2, P5>) -> List<&2, P5>:
  match xs:
    case T5B{+nb} <> T5C{+op, +n, +v} <> t:
      T5BC{nb, op, n, v} <> t
    case T5C{+op, +n, +v} <> T5B{+nb} <> t:
      T5BC{nb, op, n, v} <> t
    case other:
      other

def Eval.f5.plan.m(r: Maybe<&2, List<&2, P5>>) -> Maybe<&2, List<&2, P5>>:
  match r:
    case Some{xs}:
      Some{Eval.f5.plan.k(xs)}
    case None{}:
      None{}

# the F5 passes of a predicate over a frame of schema s, or None (the predicate is evaluated)
def Eval.f5.plan(e: X.Expr, +s: List<&2, S.Field>) -> Maybe<&2, List<&2, P5>>:
  Eval.f5.plan.m(Eval.f5.leaves(e, s))

# a validity as pred_count reads it: its words (AllValid: the 1-slot ones array) and whether a mask
def Eval.f5.vw(v: C.Valid) -> Array<U32> & Bool:
  match v:
    case C.AllValid{}:
      (Eval.fz.ones(), False{})
    case C.Mask{m}:
      (m, True{})

# one conjunct ANDed into the mask so far a (validity words va): m'[i] = (va[i] & vb[i]) != 0 ?
# a[i] & g(b[i], p) : 0, the kept count in the same loop; g is Eval.zip's comparison template with
# the literal p in the right operand's place
def Eval.f5.pk(~T: Data, ~g: T -> T -> U32, +n: U32, +d: Nat, +p: T, a: Array<U32>, va: Array<U32>, b: Array<T>, vb: Array<U32>) -> K.PC<U32, T>:
  K.Kernel.pred_count(~U32, ~T, ~T, ~(p => x => y => U32.and(x, g(y, p))), n, d, p, a, va, b, vb)

def Eval.f5.wu(op: X.BinOp, +n: U32, +d: Nat, +p: U32, a: Array<U32>, va: Array<U32>, b: Array<U32>, vb: Array<U32>) -> K.PC<U32, U32>:
  match op:
    case X.Eq{}:
      Eval.f5.pk(~U32, ~(x => y => Bool.to_u32(U32.is_eq(x, y))), n, d, p, a, va, b, vb)
    case X.Ne{}:
      Eval.f5.pk(~U32, ~(x => y => Bool.to_u32(U32.is_ne(x, y))), n, d, p, a, va, b, vb)
    case X.Lt{}:
      Eval.f5.pk(~U32, ~(x => y => Bool.to_u32(U32.is_lt(x, y))), n, d, p, a, va, b, vb)
    case X.Le{}:
      Eval.f5.pk(~U32, ~(x => y => Bool.to_u32(U32.is_le(x, y))), n, d, p, a, va, b, vb)
    case X.Gt{}:
      Eval.f5.pk(~U32, ~(x => y => Bool.to_u32(U32.is_gt(x, y))), n, d, p, a, va, b, vb)
    case _:
      Eval.f5.pk(~U32, ~(x => y => Bool.to_u32(U32.is_ge(x, y))), n, d, p, a, va, b, vb)

def Eval.f5.wi(op: X.BinOp, +n: U32, +d: Nat, +p: U32, a: Array<U32>, va: Array<U32>, b: Array<U32>, vb: Array<U32>) -> K.PC<U32, U32>:
  match op:
    case X.Lt{}:
      Eval.f5.pk(~U32, ~(x => y => Bool.to_u32(Eval.i32_lt(x, y))), n, d, p, a, va, b, vb)
    case X.Le{}:
      Eval.f5.pk(~U32, ~(x => y => Bool.to_u32(Bool.not(Eval.i32_lt(y, x)))), n, d, p, a, va, b, vb)
    case X.Gt{}:
      Eval.f5.pk(~U32, ~(x => y => Bool.to_u32(Eval.i32_lt(y, x))), n, d, p, a, va, b, vb)
    case X.Ge{}:
      Eval.f5.pk(~U32, ~(x => y => Bool.to_u32(Bool.not(Eval.i32_lt(x, y)))), n, d, p, a, va, b, vb)
    case other:
      Eval.f5.wu(other, n, d, p, a, va, b, vb)

def Eval.f5.fc(op: X.BinOp, +n: U32, +d: Nat, +p: F32, a: Array<U32>, va: Array<U32>, b: Array<F32>, vb: Array<U32>) -> K.PC<U32, F32>:
  match op:
    case X.Ne{}:
      Eval.f5.pk(~F32, ~(x => y => Bool.to_u32(U32.is_ne(K.Kernel.fword(x), K.Kernel.fword(y)))), n, d, p, a, va, b, vb)
    case X.Lt{}:
      Eval.f5.pk(~F32, ~(x => y => Bool.to_u32(U32.is_lt(K.Kernel.fword(x), K.Kernel.fword(y)))), n, d, p, a, va, b, vb)
    case X.Le{}:
      Eval.f5.pk(~F32, ~(x => y => Bool.to_u32(U32.is_le(K.Kernel.fword(x), K.Kernel.fword(y)))), n, d, p, a, va, b, vb)
    case X.Gt{}:
      Eval.f5.pk(~F32, ~(x => y => Bool.to_u32(U32.is_gt(K.Kernel.fword(x), K.Kernel.fword(y)))), n, d, p, a, va, b, vb)
    case X.Ge{}:
      Eval.f5.pk(~F32, ~(x => y => Bool.to_u32(U32.is_ge(K.Kernel.fword(x), K.Kernel.fword(y)))), n, d, p, a, va, b, vb)
    case _:
      Eval.f5.pk(~F32, ~(x => y => Bool.to_u32(U32.is_eq(K.Kernel.fword(x), K.Kernel.fword(y)))), n, d, p, a, va, b, vb)

# one pass's answer: whether the operand had the planned dtype, the mask and count, the mask so far
# (a) with its validity words handed back, the conjunct's column rebuilt
type F5R is Type:
  F5R{ok: Bool, m: Array<U32>, k: U32, a: Array<U32>, va: Array<U32>, c: C.Column}

def Eval.f5.rw(t: D.DType, +n: U32, +d: Nat, mb: Bool, r: K.PC<U32, U32>) -> F5R:
  match r:
    case K.PC{m, k, a, va, b, vb}:
      F5R{True{}, m, k, a, va, C.Column.mk_w(t, n, d, Eval.fz.back(mb, vb), b)}

def Eval.f5.rf(+n: U32, +d: Nat, mb: Bool, r: K.PC<U32, F32>) -> F5R:
  match r:
    case K.PC{m, k, a, va, b, vb}:
      F5R{True{}, m, k, a, va, C.CF32{n, d, Eval.fz.back(mb, vb), b}}

def Eval.f5.c.u(+op: X.BinOp, +n: U32, +d: Nat, +p: U32, a: Array<U32>, va: Array<U32>, b: Array<U32>, r: Array<U32> & Bool) -> F5R:
  (vb, +mb) = r
  Eval.f5.rw(D.TU32{}, n, d, mb, Eval.f5.wu(op, n, d, p, a, va, b, vb))

def Eval.f5.c.i(+op: X.BinOp, +n: U32, +d: Nat, +p: U32, a: Array<U32>, va: Array<U32>, b: Array<U32>, r: Array<U32> & Bool) -> F5R:
  (vb, +mb) = r
  Eval.f5.rw(D.TI32{}, n, d, mb, Eval.f5.wi(op, n, d, p, a, va, b, vb))

def Eval.f5.c.f(+op: X.BinOp, +n: U32, +d: Nat, +p: F32, a: Array<U32>, va: Array<U32>, b: Array<F32>, r: Array<U32> & Bool) -> F5R:
  (vb, +mb) = r
  Eval.f5.rf(n, d, mb, Eval.f5.fc(op, n, d, p, a, va, b, vb))

# the conjunct `c op v` ANDed into a (validity words va)
def Eval.f5.c(+op: X.BinOp, a: Array<U32>, va: Array<U32>, c: C.Column, v: D.Scalar) -> F5R:
  match c v:
    case C.CU32{+n, +d, vb, b} D.SU32{+p}:
      Eval.f5.c.u(op, n, d, p, a, va, b, Eval.f5.vw(vb))
    case C.CI32{+n, +d, vb, b} D.SI32{+p}:
      Eval.f5.c.i(op, n, d, D.I32.to_u32(p), a, va, b, Eval.f5.vw(vb))
    case C.CF32{+n, +d, vb, b} D.SF32{+p}:
      Eval.f5.c.f(op, n, d, p, a, va, b, Eval.f5.vw(vb))
    case c2 v2:
      F5R{False{}, Eval.fz.ones(), 0, a, va, c2}

def Eval.f5.b.k(+n: U32, +d: Nat, mb: Bool, r: K.PC<U32, U32>) -> F5R:
  match r:
    case K.PC{m, k, a, va, b, vb}:
      F5R{True{}, m, k, a, va, C.CBool{n, d, Eval.fz.back(mb, vb), b}}

def Eval.f5.b.v(+n: U32, +d: Nat, a: Array<U32>, va: Array<U32>, b: Array<U32>, r: Array<U32> & Bool) -> F5R:
  (vb, +mb) = r
  Eval.f5.b.k(n, d, mb, K.Kernel.pred_count(~U32, ~U32, ~U32, ~(p => x => y => U32.and(x, y)), n, d, 0, a, va, b, vb))

# the conjunct `c` (a bool column: true and valid) ANDed into a
def Eval.f5.b(a: Array<U32>, va: Array<U32>, c: C.Column) -> F5R:
  match c:
    case C.CBool{+n, +d, vb, b}:
      Eval.f5.b.v(n, d, a, va, b, Eval.f5.vw(vb))
    case c2:
      F5R{False{}, Eval.fz.ones(), 0, a, va, c2}

# the state of the passes: the frame (every predicate column back in place), the mask so far, the
# kept count of the last pass, the first error
type F5St is Type:
  F5St{f: C.Frame, m: Array<U32>, k: U32, err: Maybe<&2, E.Err>}

def Eval.f5.fail(err: Maybe<&2, E.Err>, e: E.Err) -> Maybe<&2, E.Err>:
  match err:
    case Some{x}:
      Some{x}
    case None{}:
      Some{e}

def Eval.f5.err(ok: Bool, err: Maybe<&2, E.Err>) -> Maybe<&2, E.Err>:
  match ok:
    case True{}:
      err
    case False{}:
      Eval.f5.fail(err, Eval.bug("operand dtype in a fused filter"))

def Eval.f5.s.k(+h: U32, +name: String, f: C.Frame, err: Maybe<&2, E.Err>, r: F5R) -> F5St:
  match r:
    case F5R{ok, m, k, a, va, c}:
      F5St{C.Frame.replace.c(f, name, c, h), m, k, Eval.f5.err(ok, err)}

def Eval.f5.s.c(+h: U32, +op: X.BinOp, v: D.Scalar, +name: String, m: Array<U32>, err: Maybe<&2, E.Err>, r: C.Frame & E.ResT(C.Column)) -> F5St:
  (f, rc) = r
  match rc:
    case Done{c}:
      Eval.f5.s.k(h, name, f, err, Eval.f5.c(op, m, Eval.fz.ones(), c, v))
    case Fail{e}:
      F5St{f, m, 0, Eval.f5.fail(err, e)}

def Eval.f5.s.b(+h: U32, +name: String, m: Array<U32>, err: Maybe<&2, E.Err>, r: C.Frame & E.ResT(C.Column)) -> F5St:
  (f, rc) = r
  match rc:
    case Done{c}:
      Eval.f5.s.k(h, name, f, err, Eval.f5.b(m, Eval.fz.ones(), c))
    case Fail{e}:
      F5St{f, m, 0, Eval.f5.fail(err, e)}

def Eval.f5.bc.f(+h: U32, +nb: String, +n1: U32, +d1: Nat, mba: Bool, +name: String, f: C.Frame, err: Maybe<&2, E.Err>, r: F5R) -> F5St:
  match r:
    case F5R{ok, m, k, a, va, c}:
      F5St{C.Frame.replace.c(C.Frame.replace.c(f, name, c, h), nb, C.CBool{n1, d1, Eval.fz.back(mba, va), a}, h), m, k, Eval.f5.err(ok, err)}

def Eval.f5.bc.e(+h: U32, +op: X.BinOp, v: D.Scalar, +nb: String, +n1: U32, +d1: Nat, xb: Array<U32>, +name: String, err: Maybe<&2, E.Err>, rv: Array<U32> & Bool, r: C.Frame & E.ResT(C.Column)) -> F5St:
  (va, +mba) = rv
  (f, rc) = r
  match rc:
    case Done{c}:
      Eval.f5.bc.f(h, nb, n1, d1, mba, name, f, err, Eval.f5.c(op, xb, va, c, v))
    case Fail{e}:
      F5St{C.Frame.replace.c(f, nb, C.CBool{n1, d1, Eval.fz.back(mba, va), xb}, h), Eval.fz.ones(), 0, Eval.f5.fail(err, e)}

def Eval.f5.bc.d(+h: U32, +op: X.BinOp, v: D.Scalar, +nb: String, +name: String, err: Maybe<&2, E.Err>, c: C.Column, f: C.Frame) -> F5St:
  match c:
    case C.CBool{+n1, +d1, vb1, xb}:
      Eval.f5.bc.e(h, op, v, nb, n1, d1, xb, name, err, Eval.f5.vw(vb1), C.Frame.lend(f, name))
    case c2:
      F5St{C.Frame.replace.c(f, nb, c2, h), Eval.fz.ones(), 0, Eval.f5.fail(err, Eval.bug("operand dtype in a fused filter"))}

# the first pass of `nb & (name op v)`: the bool column's data is the mask so far, its validity the
# first validity words (one loop for both conjuncts)
def Eval.f5.bc(+h: U32, +op: X.BinOp, v: D.Scalar, +nb: String, +name: String, err: Maybe<&2, E.Err>, m: Array<U32>, r: C.Frame & E.ResT(C.Column)) -> F5St:
  (f, rc) = r
  match rc:
    case Done{c}:
      Eval.f5.bc.d(h, op, v, nb, name, err, c, f)
    case Fail{e}:
      F5St{f, m, 0, Eval.f5.fail(err, e)}

def Eval.f5.step.k(+h: U32, t: P5, f: C.Frame, m: Array<U32>, err: Maybe<&2, E.Err>) -> F5St:
  match t:
    case T5B{+name}:
      Eval.f5.s.b(h, name, m, err, C.Frame.lend(f, name))
    case T5C{+op, +name, v}:
      Eval.f5.s.c(h, op, v, name, m, err, C.Frame.lend(f, name))
    case T5BC{+nb, +op, +name, v}:
      Eval.f5.bc(h, op, v, nb, name, err, m, C.Frame.lend(f, nb))

def Eval.f5.step(+h: U32, t: P5, st: F5St) -> F5St:
  match st:
    case F5St{f, m, k, err}:
      Eval.f5.step.k(h, t, f, m, err)

def Eval.f5.go(ps: List<&2, P5>, +h: U32, st: F5St) -> F5St:
  match ps:
    case Nil{}:
      st
    case p <> t:
      Eval.f5.go(t, h, Eval.f5.step(h, p, st))

# the state after the passes: the frame back with the mask and the kept count, or the first error
def Eval.f5.fin(st: F5St) -> E.ResT(C.Frame & (Array<U32> & U32)):
  match st:
    case F5St{f, m, +k, None{}}:
      Done{(f, (m, k))}
    case F5St{f, m, k, Some{e}}:
      Fail{e}

def Eval.f5.mask.h(ps: List<&2, P5>, r: C.Frame & U32) -> E.ResT(C.Frame & (Array<U32> & U32)):
  (f, +h) = r
  Eval.f5.fin(Eval.f5.go(ps, h, F5St{f, Eval.fz.ones(), 0, None{}}))

# the F5 passes (Eval.filter.mask's first path): the frame back (every borrowed column put back),
# the mask and the kept count from the pred_count passes, or the first error
def Eval.f5.mask(ps: List<&2, P5>, f: C.Frame) -> E.ResT(C.Frame & (Array<U32> & U32)):
  Eval.f5.mask.h(ps, C.Frame.height(f))

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
  Eval.slot.t(e, f, A.Ana.type(e, s))

# type check e against the frame's schema, then evaluate it to a kinded slot
def Eval.slot(f: C.Frame, +e: X.Expr) -> C.Frame & E.ResT(Slot):
  Eval.slot.s(e, S.Frame.schema(f))

# Eval.slot with the liveness facts (all, dead, later; Eval.mark): the same type check, the
# same instructions and the same answer, except that the last reference of a movable column
# takes it out of the frame (a hollow stand-in stays) instead of copying it, and the fused
# fragments (Eval.fuse, after the marks: W4, DESIGN.md 16.3 F1-F4) read the frame columns they
# name in place (borrowed, or moved on a last reference) instead of copying them
def Eval.slot.mh(+e: X.Expr, +all: Bool, +dead: List<&2, String>, +later: List<&2, String>, r: C.Frame & U32) -> C.Frame & E.ResT(Slot):
  (f, +h) = r
  Eval.fin(Eval.runz(Eval.fuse(Eval.mark(Eval.compile(e, Nil{}), all, dead, later)), h, EvSt{f, Done{Nil{}}}))

def Eval.slot.mt(+e: X.Expr, +all: Bool, +dead: List<&2, String>, +later: List<&2, String>, f: C.Frame, t: E.Res(D.DType)) -> C.Frame & E.ResT(Slot):
  match t:
    case Fail{err}:
      (f, Fail{err})
    case Done{t2}:
      Eval.slot.mh(e, all, dead, later, C.Frame.height(f))

def Eval.slot.ms(+e: X.Expr, +all: Bool, +dead: List<&2, String>, +later: List<&2, String>, r: C.Frame & List<&2, S.Field>) -> C.Frame & E.ResT(Slot):
  (f, s) = r
  Eval.slot.mt(e, all, dead, later, f, A.Ana.type(e, s))

def Eval.slot.mv(f: C.Frame, +e: X.Expr, +all: Bool, +dead: List<&2, String>, +later: List<&2, String>) -> C.Frame & E.ResT(Slot):
  Eval.slot.ms(e, all, dead, later, S.Frame.schema(f))

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

# the frame comes back unchanged; Col clones (Frame.get_cloned: the caller keeps the frame, so
# a move cannot work here; Eval.expr_mv / Eval.full_mv are the moving entries for an operator
# that consumes its frame); a literal-only result has the frame's height; an aggregation
# answers a 1-row column
def Eval.expr(f: C.Frame, e: X.Expr) -> C.Frame & E.ResT(C.Column):
  Eval.mode.a(False{}, Eval.slot(f, e))

# like Eval.expr, but every 1-row result (literal or aggregation) is broadcast
# to the frame's height (with_columns / filter semantics)
def Eval.full(f: C.Frame, e: X.Expr) -> C.Frame & E.ResT(C.Column):
  Eval.mode.a(True{}, Eval.slot(f, e))

# Eval.expr / Eval.full for an operator that consumes its input frame (group_by's keys and
# aggregation inputs): `later` is the references of the expressions the operator evaluates
# after e (Eval.refs of the rest); the last reference of every other column moves it out of
# the frame (Eval.mark with all = True), so the frame that comes back may hold hollow
# stand-ins for the moved columns and must not be read except by those later expressions.
# Same answer as Eval.expr / Eval.full (LAWS.bend lend_observes: a moved column is the column
# get_cloned copies)
def Eval.expr_mv(f: C.Frame, +e: X.Expr, +later: List<&2, String>) -> C.Frame & E.ResT(C.Column):
  Eval.mode.a(False{}, Eval.slot.mv(f, e, True{}, Nil{}, later))

def Eval.full_mv(f: C.Frame, +e: X.Expr, +later: List<&2, String>) -> C.Frame & E.ResT(C.Column):
  Eval.mode.a(True{}, Eval.slot.mv(f, e, True{}, Nil{}, later))

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

# (Expr.type: group_by's Grp.validate, which reports a nested aggregation with
# its own text after the typing errors)
def Eval.check(es: List<&2, X.Expr>, +s: List<&2, S.Field>) -> Maybe<&2, E.Err>:
  match es:
    case Nil{}:
      None{}
    case e <> t:
      Eval.check.k(X.Expr.type(e, s), Eval.check(t, s))

# the first error of the shared analysis (typing, then "nested aggregation", per
# expression in list order): select / with_columns
def Eval.acheck(es: List<&2, X.Expr>, +s: List<&2, S.Field>) -> Maybe<&2, E.Err>:
  match es:
    case Nil{}:
      None{}
    case e <> t:
      Eval.check.k(A.Ana.type(e, s), Eval.acheck(t, s))

def Eval.names(es: List<&2, X.Expr>) -> List<&2, String>:
  match es:
    case Nil{}:
      Nil{}
    case e <> t:
      X.Expr.name(e) <> Eval.names(t)

# the static checks of select / with_columns, in Plan.schema's order (DESIGN.md 15.9): the
# first error of the shared analysis (list order), then DuplicateColumn on the first repeated
# output name. Both run before any data is evaluated, so a data error (a failing strict cast)
# never shadows a static one (eager = lazy, NEW-1).
def Eval.dup(chk: Maybe<&2, E.Err>, d: Maybe<&2, String>) -> Maybe<&2, E.Err>:
  match chk d:
    case Some{e} _:
      Some{e}
    case None{} Some{n}:
      Some{E.DuplicateColumn{n}}
    case None{} None{}:
      None{}

def Eval.static(+es: List<&2, X.Expr>, +s: List<&2, S.Field>) -> Maybe<&2, E.Err>:
  Eval.dup(Eval.acheck(es, s), C.Names.dup(Eval.names(es), Nil{}, None{}))

# select's height (DESIGN.md 15.4): h if some output is KRow (the shared
# analysis, A.Ana.rows), else 1: literals only and reductions only give one row,
# also on a zero-row input
def Eval.target(row: Bool, +h: U32) -> U32:
  Bool.pick(U32, row, h, 1)

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

def Eval.many.step.r(+e: X.Expr, +all: Bool, +dead: List<&2, String>, +later: List<&2, String>, f: C.Frame, r: E.ResT(List<&1, Out>)) -> SelSt:
  match r:
    case Fail{err}:
      SelSt{f, Fail{err}}
    case Done{acc}:
      Eval.many.add(X.Expr.name(e), acc, Eval.slot.mv(f, e, all, dead, later))

def Eval.many.step(e: X.Expr, +all: Bool, +dead: List<&2, String>, +later: List<&2, String>, st: SelSt) -> SelSt:
  match st:
    case SelSt{f, r}:
      Eval.many.step.r(e, all, dead, later, f, r)

# evaluate every expression against the same frame (the input snapshot: a moved column is never
# read again, Eval.mark); outputs newest first. `all` / `dead`: the columns the operator's output
# does not keep (Eval.mark)
def Eval.many(es: List<&2, X.Expr>, +all: Bool, +dead: List<&2, String>, st: SelSt) -> SelSt:
  match es:
    case Nil{}:
      st
    case e <> +t:
      Eval.many(t, all, dead, Eval.many.step(e, all, dead, Eval.refs(t), st))

# outputs (newest first) into named columns in expression order, every 1-row
# output broadcast to n rows
def Eval.outs(outs: List<&1, Out>, +n: U32, acc: List<&1, C.Named>) -> List<&1, C.Named>:
  match outs:
    case Nil{}:
      acc
    case Out{name, k, c} <> t:
      Eval.outs(t, n, C.Named{name, Eval.fit(k, c, n)} <> acc)

def Eval.select.d(row: Bool, r: E.ResT(List<&1, Out>), fh: C.Frame & U32) -> E.ResT(C.Frame):
  match r:
    case Fail{e}:
      Fail{e}
    case Done{outs}:
      (f, +h) = fh
      C.Frame.from_columns(Eval.outs(outs, Eval.target(row, h), Nil{}))

def Eval.select.c(row: Bool, st: SelSt) -> E.ResT(C.Frame):
  match st:
    case SelSt{f, r}:
      Eval.select.d(row, r, C.Frame.height(f))

# select consumes its input: every column's last reference moves it (Eval.mark, all = True)
def Eval.select.b(chk: Maybe<&2, E.Err>, f: C.Frame, +es: List<&2, X.Expr>, row: Bool) -> E.ResT(C.Frame):
  match chk:
    case Some{e}:
      Fail{e}
    case None{}:
      Eval.select.c(row, Eval.many(es, True{}, Nil{}, SelSt{f, Done{Nil{}}}))

def Eval.select.a(+es: List<&2, X.Expr>, r: C.Frame & List<&2, S.Field>) -> E.ResT(C.Frame):
  (f, +s) = r
  Eval.select.b(Eval.static(es, s), f, es, A.Ana.rows(es, s))

# a new frame of the expressions' columns, in order, named by Expr.name.
# Every expression is type checked before anything runs. Mixing real columns
# with 1-row results broadcasts the latter; literal-only and reduction-only
# selects give one row (also on a zero-row input); select([]) is (0, 0)
# (DESIGN.md 15.4). Type errors, then DuplicateColumn on repeated output names,
# both before any column is evaluated (Eval.static). The input frame is consumed.
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

# with_columns keeps its input frame: only an input column an output overwrites (its name is an
# output name, Eval.names) is dead after the operator, so only those move (their last
# reference; Frame.replace then puts the output in the stand-in's place). Every other
# reference copies: the frame keeps the column and a borrow would need every operation to
# hand its operand back (the hand-back kernels are W4's, DESIGN.md 16.3)
def Eval.wc.b(chk: Maybe<&2, E.Err>, f: C.Frame, +es: List<&2, X.Expr>) -> E.ResT(C.Frame):
  match chk:
    case Some{e}:
      Fail{e}
    case None{}:
      Eval.wc.c(Eval.many(es, False{}, Eval.names(es), SelSt{f, Done{Nil{}}}))

def Eval.wc.a(+es: List<&2, X.Expr>, r: C.Frame & List<&2, S.Field>) -> E.ResT(C.Frame):
  (f, s) = r
  Eval.wc.b(Eval.static(es, s), f, es)

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

# the general path's mask: popcount of Eval.pred's mask is the kept count
def Eval.filter.mask.p(f: C.Frame, r: Array<U32> & U32) -> E.ResT(C.Frame & (Array<U32> & U32)):
  (m, +n) = r
  Done{(f, K.Kernel.popcount(n, m))}

def Eval.filter.mask.go2(rc: E.ResT(C.Column), f: C.Frame) -> E.ResT(C.Frame & (Array<U32> & U32)):
  match rc:
    case Fail{e}:
      Fail{e}
    case Done{c}:
      Eval.filter.mask.p(f, Eval.pred(c))

def Eval.filter.mask.go(r: C.Frame & E.ResT(C.Column)) -> E.ResT(C.Frame & (Array<U32> & U32)):
  (f, rc) = r
  Eval.filter.mask.go2(rc, f)

# The predicate: a conjunction of bool columns and `column op literal` comparisons runs the F5
# passes (Eval.f5.mask: one pred_count loop per conjunct over the BORROWED columns, mask and kept
# count together); any other predicate is evaluated by the fused evaluator with no moves (filter
# keeps every input column, all compacted by the mask, so none is dead and a move cannot work):
# its column references are borrowed by the fused fragments (W4) and copied otherwise, and the
# kept count is popcount of Eval.pred's mask
def Eval.filter.mask.x(plan: Maybe<&2, List<&2, P5>>, f: C.Frame, +pred: X.Expr) -> E.ResT(C.Frame & (Array<U32> & U32)):
  match plan:
    case Some{ps}:
      Eval.f5.mask(ps, f)
    case None{}:
      Eval.filter.mask.go(Eval.mode.a(True{}, Eval.slot.mh(pred, False{}, Nil{}, Nil{}, C.Frame.height(f))))

def Eval.filter.mask.t(t: D.DType, f: C.Frame, +pred: X.Expr, plan: Maybe<&2, List<&2, P5>>) -> E.ResT(C.Frame & (Array<U32> & U32)):
  match t:
    case D.TBool{}:
      Eval.filter.mask.x(plan, f, pred)
    case other:
      Fail{E.TypeMismatch{"filter", "bool", D.DType.show(other)}}

def Eval.filter.mask.b(+pred: X.Expr, f: C.Frame, r: E.Res(D.DType), plan: Maybe<&2, List<&2, P5>>) -> E.ResT(C.Frame & (Array<U32> & U32)):
  match r:
    case Fail{e}:
      Fail{e}
    case Done{t}:
      Eval.filter.mask.t(t, f, pred, plan)

# the static work first (the type check, the F5 plan from the schema), then the data work
def Eval.filter.mask.a(+pred: X.Expr, r: C.Frame & List<&2, S.Field>) -> E.ResT(C.Frame & (Array<U32> & U32)):
  (f, +s) = r
  Eval.filter.mask.b(pred, f, A.Ana.type(pred, s), Eval.f5.plan(pred, s))

def Eval.filter.sel.go(sel: Bool, f: C.Frame, m: Array<U32>, +h: U32, +kept: U32) -> C.Frame & (Array<U32> & U32):
  match sel:
    case True{}:
      (C.Frame.take_rows(f, K.Kernel.where(h, K.Kernel.depth_for(U32.inc(kept)), m), kept), (Array.new(U32, 0n, 1), kept))
    case False{}:
      (f, (m, kept))

def Eval.filter.sel.h(m: Array<U32>, +kept: U32, r: C.Frame & U32) -> C.Frame & (Array<U32> & U32):
  (f, +h) = r
  Eval.filter.sel.go(U32.is_le(U32.mul(kept, 8), h), f, m, h, kept)

def Eval.filter.sel.r(f: C.Frame, r: Array<U32> & U32) -> C.Frame & (Array<U32> & U32):
  (m, +kept) = r
  Eval.filter.sel.h(m, kept, C.Frame.height(f))

def Eval.filter.sel.k(x: C.Frame & (Array<U32> & U32)) -> C.Frame & (Array<U32> & U32):
  (f, r) = x
  Eval.filter.sel.r(f, r)

# a selective mask (kept <= h / 8): the kept rows are gathered ONCE by their positions (one pass over
# the mask, then `kept` rows per column) and handed on with an all-ones mask (one slot, read with
# wrapping indices), so the compaction that follows (Frame.filter_mask / Exec.fc, unchanged) walks
# `kept` rows per column instead of h: the same rows in the same order, the same validity and string
# storage (bench/tpch q6: 13 lineitem columns compacted over 1.2M rows to keep 2% of them)
def Eval.filter.sel(r: E.ResT(C.Frame & (Array<U32> & U32))) -> E.ResT(C.Frame & (Array<U32> & U32)):
  match r:
    case Fail{e}:
      Fail{e}
    case Done{x}:
      Done{Eval.filter.sel.k(x)}

# filter's mask: the frame (back as it came, or only its kept rows with an all-ones mask when the
# mask is selective: Eval.filter.sel), the row mask (1 = keep: pred true AND valid) and the kept
# count, or the predicate's error (TypeMismatch{"filter", "bool", got} first, then the evaluation's).
# ONE function for every caller: Eval.filter compacts every column with it (Frame.filter_mask),
# Exec.fs (the Filter + Select step, src/exec.bend) only the selected
def Eval.filter.mask(f: C.Frame, +pred: X.Expr) -> E.ResT(C.Frame & (Array<U32> & U32)):
  Eval.filter.sel(Eval.filter.mask.a(pred, S.Frame.schema(f)))

def Eval.filter.q(f: C.Frame, r: Array<U32> & U32) -> E.ResT(C.Frame):
  (m, +kept) = r
  Done{C.Frame.filter_mask(f, m, kept)}

def Eval.filter.k(x: C.Frame & (Array<U32> & U32)) -> E.ResT(C.Frame):
  (f, r) = x
  Eval.filter.q(f, r)

# a mask result compacted: every column by Frame.filter_mask, or the error
def Eval.filter.r(r: E.ResT(C.Frame & (Array<U32> & U32))) -> E.ResT(C.Frame):
  match r:
    case Fail{e}:
      Fail{e}
    case Done{x}:
      Eval.filter.k(x)

# the rows where pred is true (null counts as false), in order; pred must be
# bool (TypeMismatch{"filter", "bool", got}); a 1-row pred broadcasts
def Eval.filter(f: C.Frame, +pred: X.Expr) -> E.ResT(C.Frame):
  Eval.filter.r(Eval.filter.mask(f, pred))
