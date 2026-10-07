# p18: a vendored two's-complement I32 over U32 (what src/i32.bend will be,
# instead of depending on bend-kit-int's 1600-line file): add/sub/mul wrap
# through U32; compare by flipping the sign bit; show/read with '-'.
#   ~/.bend/bin/bend probes/p18_i32_vendored.bend
import Base

type I32 is Data:
  I32{bits: U32}

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

def I32.is_lt(a: I32, b: I32) -> Bool:
  Cmp.is_lt(I32.cmp(a, b))

def I32.is_eq(a: I32, b: I32) -> Bool:
  Cmp.is_eq(I32.cmp(a, b))

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

def I32.read.sign(neg: Bool, m: Maybe<&2, U32>) -> Maybe<&2, I32>:
  match neg m:
    case _ None{}:
      None{}
    case True{} Some{x}:
      Some{I32{U32.sub(0, x)}}
    case False{} Some{x}:
      Some{I32{x}}

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

def mi(m: Maybe<&2, I32>) -> String:
  match m:
    case None{}:
      "None"
    case Some{x}:
      I32.show(x)

def main() -> IO(Unit):
  do IO<Unit>:
    IO.print(mi(I32.read("-42")))
    IO.print(mi(I32.read("7")))
    IO.print(mi(I32.read("-")))
    IO.print(I32.show(I32.add(I32{4294967295}, I32{4294967295})))
    IO.print(I32.show(I32.mul(I32.neg(I32{3}), I32{5})))
    IO.print(Bool.show(I32.is_lt(I32.neg(I32{1}), I32{1})))
    IO.print(Bool.show(I32.is_lt(I32{1}, I32.neg(I32{1}))))
    IO.print(I32.show(I32{2147483648}))
    IO.print(F32.show(I32.to_f32(I32.neg(I32{3}))))

#|-42
#|7
#|None
#|-2
#|-15
#|True
#|False
#|-2147483648
#|-3
