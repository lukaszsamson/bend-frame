# M1: the vendored two's-complement I32 (p18 lines first, then div/mod/read ranges).
import Base
import ./../src/dtype.bend as D

def mi(m: Maybe<&2, D.I32>) -> String:
  match m:
    case None{}:
      "None"
    case Some{x}:
      D.I32.show(x)

# an I32 from a signed literal pair: sign and magnitude
def i(neg: Bool, +x: U32) -> D.I32:
  Bool.pick(D.I32, neg, D.I32.neg(D.I32{x}), D.I32{x})

def main() -> IO(Unit):
  do IO<Unit>:
    IO.print(mi(D.I32.read("-42")))
    IO.print(mi(D.I32.read("7")))
    IO.print(mi(D.I32.read("-")))
    IO.print(D.I32.show(D.I32.add(D.I32{4294967295}, D.I32{4294967295})))
    IO.print(D.I32.show(D.I32.mul(D.I32.neg(D.I32{3}), D.I32{5})))
    IO.print(Bool.show(D.I32.is_lt(D.I32.neg(D.I32{1}), D.I32{1})))
    IO.print(Bool.show(D.I32.is_lt(D.I32{1}, D.I32.neg(D.I32{1}))))
    IO.print(D.I32.show(D.I32{2147483648}))
    IO.print(F32.show(D.I32.to_f32(D.I32.neg(D.I32{3}))))
    # sub, comparisons, abs, conversions
    IO.print(D.I32.show(D.I32.sub(D.I32{3}, D.I32{10})))
    IO.print(Bool.show(D.I32.is_le(D.I32.neg(D.I32{2}), D.I32.neg(D.I32{2}))) ++ " " ++ Bool.show(D.I32.is_gt(D.I32{2}, D.I32.neg(D.I32{2}))) ++ " " ++ Bool.show(D.I32.is_ge(D.I32.neg(D.I32{2}), D.I32{0})) ++ " " ++ Bool.show(D.I32.is_eq(D.I32{5}, D.I32{5})) ++ " " ++ Bool.show(D.I32.is_neg(D.I32{2147483648})))
    IO.print(D.I32.show(D.I32.abs(D.I32.neg(D.I32{5}))) ++ " " ++ D.I32.show(D.I32.abs(D.I32{2147483648})))
    IO.print(U32.show(D.I32.to_u32(D.I32.neg(D.I32{1}))) ++ " " ++ D.I32.show(D.I32.from_u32(4294967294)))
    # div / mod truncate toward zero; by zero: 0 / a
    IO.print(D.I32.show(D.I32.div(i(True{}, 7), D.I32{2})) ++ " " ++ D.I32.show(D.I32.div(D.I32{7}, i(True{}, 2))) ++ " " ++ D.I32.show(D.I32.div(i(True{}, 7), i(True{}, 2))) ++ " " ++ D.I32.show(D.I32.div(D.I32{7}, D.I32{2})) ++ " " ++ D.I32.show(D.I32.div(D.I32{7}, D.I32{0})))
    IO.print(D.I32.show(D.I32.mod(i(True{}, 7), D.I32{2})) ++ " " ++ D.I32.show(D.I32.mod(D.I32{7}, i(True{}, 2))) ++ " " ++ D.I32.show(D.I32.mod(i(True{}, 7), i(True{}, 2))) ++ " " ++ D.I32.show(D.I32.mod(D.I32{7}, D.I32{2})) ++ " " ++ D.I32.show(D.I32.mod(D.I32{7}, D.I32{0})))
    # read: range checked
    IO.print(mi(D.I32.read("2147483647")) ++ " " ++ mi(D.I32.read("2147483648")) ++ " " ++ mi(D.I32.read("-2147483648")) ++ " " ++ mi(D.I32.read("-2147483649")) ++ " " ++ mi(D.I32.read("")) ++ " " ++ mi(D.I32.read("-0")) ++ " " ++ mi(D.I32.read("abc")))
#|-42
#|7
#|None
#|-2
#|-15
#|True
#|False
#|-2147483648
#|-3
#|-7
#|True True False True True
#|5 -2147483648
#|4294967295 -2
#|-3 -3 3 3 0
#|-1 1 -1 1 7
#|2147483647 None -2147483648 None None 0 None
