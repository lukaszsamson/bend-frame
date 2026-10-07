# p02: a GENERIC array kernel must take its element type as a template (~T),
# which monomorphizes; see p02b for the erased (-T) version that the C
# emitter refuses ("an open Array element type").
#   ~/.bend/bin/bend probes/p02_template_kernel.bend
import Base

# fold over an array with a template binary op -- balanced fork-join
def Arr.fold(~T: Data, ~f: T -> T -> T, a: Array<T>) -> T:
  match a:
    case ALeaf{x}:
      x
    case ANode{xs, ys}:
      l r = Arr.fold(~T, ~f, xs) Arr.fold(~T, ~f, ys)
      f(l, r)

# elementwise map producing a NEW array of a different element type
def Arr.map2(~T: Data, ~U: Data, ~f: T -> U, a: Array<T>) -> Array<U>:
  match a:
    case ALeaf{x}:
      ALeaf{f(x)}
    case ANode{xs, ys}:
      l r = Arr.map2(~T, ~U, ~f, xs) Arr.map2(~T, ~U, ~f, ys)
      ANode{l, r}

# zip two same-shape arrays (the shape is the power-of-two tree)
def Arr.zip(~T: Data, ~U: Data, ~V: Data, ~f: T -> U -> V, a: Array<T>, b: Array<U>) -> Array<V>:
  match a b:
    case ALeaf{x} ALeaf{y}:
      ALeaf{f(x, y)}
    case ANode{xs, ys} ANode{bs, cs}:
      l r = Arr.zip(~T, ~U, ~V, ~f, xs, bs) Arr.zip(~T, ~U, ~V, ~f, ys, cs)
      ANode{l, r}
    case ALeaf{x} ANode{bs, cs}:
      ALeaf{f(x, Arr.fold(~U, ~(p => q => p), ANode{bs, cs}))}
    case ANode{xs, ys} ALeaf{y}:
      ALeaf{f(Arr.fold(~T, ~(p => q => p), ANode{xs, ys}), y)}

def half(x: U32) -> F32:
  F32.div(U32.to_f32(x), 2.0)

def main() -> IO(Unit):
  do IO<Unit>:
    a : Array<U32> = [3 : U32*4n]
    b : Array<F32> = Arr.map2(~U32, ~F32, ~half, a)
    c : Array<F32> = Arr.zip(~F32, ~F32, ~F32, ~F32.mul, b, [2.0 : F32*4n])
    IO.print(F32.show(Arr.fold(~F32, ~F32.add, c)))
    IO.print(U32.show(Arr.fold(~U32, ~U32.add, [3 : U32*4n])))

#|12
#|12
