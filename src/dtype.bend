# src/dtype.bend -- DType, I32 (vendored two's complement over U32), Scalar.
# DESIGN.md section 4.1. Idioms: helpers above callers; match only on params;
# `+` on every second use.
import Base
import ./err.bend as E

type DType is Data:
  TBool{}
  TU32{}
  TI32{}
  TF32{}
  TStr{}

type I32 is Data:
  I32{bits: U32}

# a scalar value: a literal in an expression, a cell read out of a column
type Scalar is Data:
  SNull{}
  SBool{b: Bool}
  SU32{v: U32}
  SI32{v: I32}
  SF32{v: F32}
  SStr{s: String}

# ---- DType ------------------------------------------------------------------

def DType.eq(a: DType, b: DType) -> Bool:
  match a b:
    case TBool{} TBool{}:
      True{}
    case TU32{} TU32{}:
      True{}
    case TI32{} TI32{}:
      True{}
    case TF32{} TF32{}:
      True{}
    case TStr{} TStr{}:
      True{}
    case _ _:
      False{}

def DType.show(t: DType) -> String:
  match t:
    case TBool{}:
      "bool"
    case TU32{}:
      "u32"
    case TI32{}:
      "i32"
    case TF32{}:
      "f32"
    case TStr{}:
      "str"

# ---- I32 --------------------------------------------------------------------

# the explicit, unchecked reinterpretation of a word as an i32 (2^31.. are negative)
def I32.from_bits(x: U32) -> I32:
  I32{x}

# the old name of I32.from_bits (kept as an alias)
def I32.from_u32(x: U32) -> I32:
  I32{x}

def I32.checked.k(ok: Bool, +v: U32, +x: U32) -> E.Res(I32):
  match ok:
    case True{}:
      Done{I32{x}}
    case False{}:
      Fail{E.InvalidOperation{"i32 out of range: " ++ U32.show(v)}}

# v as an i32 when v < 2^31, else InvalidOperation{"i32 out of range: <v>"} (DESIGN.md 15.2.1)
def I32.checked(+v: U32) -> E.Res(I32):
  I32.checked.k(U32.is_lt(v, 2147483648), v, v)

# -v as an i32 when v <= 2^31 (-2^31 is MIN), else the same error naming v
def I32.checked_neg(+v: U32) -> E.Res(I32):
  I32.checked.k(U32.is_le(v, 2147483648), v, U32.sub(0, v))

def I32.to_u32(a: I32) -> U32:
  match a:
    case I32{x}:
      x

def I32.add(a: I32, b: I32) -> I32:
  match a b:
    case I32{x} I32{y}:
      I32{U32.add(x, y)}

def I32.sub(a: I32, b: I32) -> I32:
  match a b:
    case I32{x} I32{y}:
      I32{U32.sub(x, y)}

def I32.mul(a: I32, b: I32) -> I32:
  match a b:
    case I32{x} I32{y}:
      I32{U32.mul(x, y)}

def I32.neg(a: I32) -> I32:
  match a:
    case I32{x}:
      I32{U32.sub(0, x)}

def I32.is_neg(a: I32) -> Bool:
  match a:
    case I32{x}:
      U32.is_ge(x, 2147483648)

# flipping the sign bit maps signed order onto unsigned order
def I32.cmp(a: I32, b: I32) -> Cmp:
  match a b:
    case I32{x} I32{y}:
      U32.cmp(U32.xor(x, 2147483648), U32.xor(y, 2147483648))

def I32.is_eq(a: I32, b: I32) -> Bool:
  Cmp.is_eq(I32.cmp(a, b))

def I32.is_lt(a: I32, b: I32) -> Bool:
  Cmp.is_lt(I32.cmp(a, b))

def I32.is_le(a: I32, b: I32) -> Bool:
  Cmp.is_le(I32.cmp(a, b))

def I32.is_gt(a: I32, b: I32) -> Bool:
  Cmp.is_gt(I32.cmp(a, b))

def I32.is_ge(a: I32, b: I32) -> Bool:
  Cmp.is_ge(I32.cmp(a, b))

# magnitude as an unsigned word (|-2^31| = 2^31)
def I32.mag(a: I32) -> U32:
  match a:
    case I32{+x}:
      Bool.pick(U32, U32.is_ge(x, 2147483648), U32.sub(0, x), x)

def I32.abs(a: I32) -> I32:
  I32{I32.mag(a)}

def I32.show.if(neg: Bool, x: U32) -> String:
  match neg:
    case True{}:
      "-" ++ U32.show(U32.sub(0, x))
    case False{}:
      U32.show(x)

def I32.show(a: I32) -> String:
  match a:
    case I32{+x}:
      I32.show.if(U32.is_ge(x, 2147483648), x)

# in range: a negative magnitude is at most 2^31, a positive one below it
def I32.read.sign(neg: Bool, m: Maybe<&2, U32>) -> Maybe<&2, I32>:
  match neg m:
    case _ None{}:
      None{}
    case True{} Some{+x}:
      Bool.pick(Maybe<&2, I32>, U32.is_le(x, 2147483648), Some{I32{U32.sub(0, x)}}, None{})
    case False{} Some{+x}:
      Bool.pick(Maybe<&2, I32>, U32.is_lt(x, 2147483648), Some{I32{x}}, None{})

def I32.read(s: String) -> Maybe<&2, I32>:
  match s:
    case SCon{Chr{45}, t}:
      I32.read.sign(True{}, U32.read(t))
    case other:
      I32.read.sign(False{}, U32.read(other))

def I32.to_f32.if(neg: Bool, x: U32) -> F32:
  match neg:
    case True{}:
      F32.neg(U32.to_f32(U32.sub(0, x)))
    case False{}:
      U32.to_f32(x)

def I32.to_f32(a: I32) -> F32:
  match a:
    case I32{+x}:
      I32.to_f32.if(U32.is_ge(x, 2147483648), x)

# truncating toward zero: the quotient's sign is the xor of the operand signs;
# division by zero answers 0 (as U32.div)
def I32.div.sign(neg: Bool, q: U32) -> I32:
  match neg:
    case True{}:
      I32{U32.sub(0, q)}
    case False{}:
      I32{q}

def I32.div(a: I32, b: I32) -> I32:
  match a b:
    case I32{+x} I32{+y}:
      I32.div.sign(Bool.xor(U32.is_ge(x, 2147483648), U32.is_ge(y, 2147483648)), U32.div(I32.mag(I32{x}), I32.mag(I32{y})))

# a - (a / b) * b: the remainder takes the sign of a; by zero it is a
# (truncating helpers; the evaluator's // and % are I32.floor_div / I32.floor_mod)
def I32.mod(+a: I32, +b: I32) -> I32:
  I32.sub(a, I32.mul(I32.div(a, b), b))

# floor(a / b) (DESIGN.md 15.5.1): q = |a| / |b|; when the signs differ the quotient is
# -q, or -(q + 1) when the division is inexact; None for b = 0 and for MIN // -1
def I32.floor_div.q(neg: Bool, +q: U32, exact: Bool) -> I32:
  match neg:
    case True{}:
      I32{U32.sub(0, Bool.pick(U32, exact, q, U32.inc(q)))}
    case False{}:
      I32{q}

def I32.floor_div.k(none: Bool, +x: U32, +y: U32) -> Maybe<&2, I32>:
  match none:
    case True{}:
      None{}
    case False{}:
      +mx = I32.mag(I32{x})
      +my = I32.mag(I32{y})
      Some{I32.floor_div.q(Bool.xor(U32.is_ge(x, 2147483648), U32.is_ge(y, 2147483648)), U32.div(mx, my), U32.is_zero(U32.mod(mx, my)))}

def I32.floor_div(a: I32, b: I32) -> Maybe<&2, I32>:
  match a b:
    case I32{+x} I32{+y}:
      I32.floor_div.k(Bool.or(U32.is_zero(y), Bool.and(U32.is_eq(x, 2147483648), U32.is_eq(y, 4294967295))), x, y)

# the remainder r = |a| mod |b| moved to the divisor's sign: 0 stays 0; when the signs
# differ the magnitude is |b| - r (DESIGN.md 15.5.1: 7 % -2 = -1, -7 % 2 = 1, MIN % -1 = 0)
def I32.floor_mod.r(+yneg: Bool, differ: Bool, +my: U32, +r: U32) -> I32:
  +m = Bool.pick(U32, Bool.and(differ, U32.is_ne(r, 0)), U32.sub(my, r), r)
  I32{Bool.pick(U32, yneg, U32.sub(0, m), m)}

def I32.floor_mod.k(none: Bool, +x: U32, +y: U32) -> Maybe<&2, I32>:
  match none:
    case True{}:
      None{}
    case False{}:
      +my = I32.mag(I32{y})
      +yneg = U32.is_ge(y, 2147483648)
      Some{I32.floor_mod.r(yneg, Bool.xor(U32.is_ge(x, 2147483648), yneg), my, U32.mod(I32.mag(I32{x}), my))}

# a - b * floor(a / b): the result has the divisor's sign or is 0; None for b = 0
def I32.floor_mod(a: I32, b: I32) -> Maybe<&2, I32>:
  match a b:
    case I32{+x} I32{+y}:
      I32.floor_mod.k(U32.is_zero(y), x, y)

# ---- Scalar -----------------------------------------------------------------

# the slot value of a null
def DType.default(t: DType) -> Scalar:
  match t:
    case TBool{}:
      SBool{False{}}
    case TU32{}:
      SU32{0}
    case TI32{}:
      SI32{I32{0}}
    case TF32{}:
      SF32{0.0}
    case TStr{}:
      SStr{""}

def Scalar.dtype(s: Scalar) -> Maybe<&2, DType>:
  match s:
    case SNull{}:
      None{}
    case SBool{b}:
      Some{TBool{}}
    case SU32{v}:
      Some{TU32{}}
    case SI32{v}:
      Some{TI32{}}
    case SF32{v}:
      Some{TF32{}}
    case SStr{s2}:
      Some{TStr{}}

def Scalar.show.bool(b: Bool) -> String:
  match b:
    case True{}:
      "true"
    case False{}:
      "false"

def Scalar.show(s: Scalar) -> String:
  match s:
    case SNull{}:
      "null"
    case SBool{b}:
      Scalar.show.bool(b)
    case SU32{v}:
      U32.show(v)
    case SI32{v}:
      I32.show(v)
    case SF32{v}:
      F32.show(v)
    case SStr{s2}:
      s2
