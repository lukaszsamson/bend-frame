#! xfail B03-f
# B03-f (Fable B3): / on integer columns truncates and keeps the integer dtype.
# DESIGN.md 15.5.1, 15.3.1: Bin{Div} is f32 x f32 -> f32 only; TypeMismatch{"div", "f32",
# <left>} when the left is not f32, else {"div", "f32", <right>}: a static error, so
# collect_schema reports it too. f32 / f32 is IEEE (x/0 = +-inf, 0/0 = NaN; Polars same).
# floor_div is M1 API (pending/B03_d_floor_div.bend.txt).
import Base
import ./../../frame.bend as DF
import ./../../src/dtype.bend as D
import ./../../src/err.bend as E
import ./../../src/column.bend as C
import ./../../src/expr.bend as X
import ./../../src/plan.bend as P
import ./lib/rx.bend as R

def t() -> E.ResT(C.Frame):
  R.frame([
    R.mk("a", [R.u(7), R.u(1), R.u(0)], D.TU32{}),
    R.mk("b", [R.u(2), R.u(0), R.u(0)], D.TU32{}),
    R.mk("ai", [R.i(7), R.ineg(7), R.i(0)], D.TI32{}),
    R.mk("bi", [R.i(2), R.i(2), R.i(0)], D.TI32{}),
    R.mk("x", [R.f(1.0), R.f(F32.neg(1.0)), R.f(0.0)], D.TF32{}),
    R.mk("y", [R.f(0.0), R.f(0.0), R.f(0.0)], D.TF32{})])

def env() -> P.Env:
  R.env1("t", t())

def src() -> P.Plan:
  R.src("t", t())

def go(+tag: String, +e: X.Expr) -> IO(Unit):
  do IO<Unit>:
    R.three(tag, R.e_select(t(), [e]), DF.lazy_select(src(), [e]), env(), env())
    IO.print(R.schema(tag, DF.lazy_select(src(), [e])))

def main() -> IO(Unit):
  do IO<Unit>:
    go("B03-f u32-div", DF.alias(DF.div(DF.col("a"), DF.col("b")), "q"))
    go("B03-f i32-div", DF.alias(DF.div(DF.col("ai"), DF.col("bi")), "q"))
    go("B03-f f32-div-u32", DF.alias(DF.div(DF.col("x"), DF.col("a")), "q"))
    go("B03-f f32-div-f32", DF.alias(DF.div(DF.col("x"), DF.col("y")), "q"))
#|-- B03-f u32-div eager
#|error	TypeMismatch in div: expected f32, got u32
#|
#|-- B03-f u32-div raw
#|error	TypeMismatch in div: expected f32, got u32
#|
#|-- B03-f u32-div opt
#|error	TypeMismatch in div: expected f32, got u32
#|
#|-- B03-f u32-div schema
#|error: TypeMismatch in div: expected f32, got u32
#|
#|-- B03-f i32-div eager
#|error	TypeMismatch in div: expected f32, got i32
#|
#|-- B03-f i32-div raw
#|error	TypeMismatch in div: expected f32, got i32
#|
#|-- B03-f i32-div opt
#|error	TypeMismatch in div: expected f32, got i32
#|
#|-- B03-f i32-div schema
#|error: TypeMismatch in div: expected f32, got i32
#|
#|-- B03-f f32-div-u32 eager
#|error	TypeMismatch in div: expected f32, got u32
#|
#|-- B03-f f32-div-u32 raw
#|error	TypeMismatch in div: expected f32, got u32
#|
#|-- B03-f f32-div-u32 opt
#|error	TypeMismatch in div: expected f32, got u32
#|
#|-- B03-f f32-div-u32 schema
#|error: TypeMismatch in div: expected f32, got u32
#|
#|-- B03-f f32-div-f32 eager
#|frame
#|height	3
#|width	1
#|col	f32	"q"
#|row	0x7f800000
#|row	0xff800000
#|row	0x7fc00000
#|
#|-- B03-f f32-div-f32 raw
#|frame
#|height	3
#|width	1
#|col	f32	"q"
#|row	0x7f800000
#|row	0xff800000
#|row	0x7fc00000
#|
#|-- B03-f f32-div-f32 opt
#|frame
#|height	3
#|width	1
#|col	f32	"q"
#|row	0x7f800000
#|row	0xff800000
#|row	0x7fc00000
#|
#|-- B03-f f32-div-f32 schema
#|q:f32
#|
