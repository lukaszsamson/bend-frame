# The M3 facade leftovers (DESIGN.md 15.2.1, section 14 "M3 facade leftovers"): DF.column,
# DF.schema, DF.height and DF.collect_show. DF.column and DF.collect_show each get one
# success case and one invalid input (their error paths); DF.schema and DF.height have no
# error path, so they get success cases only (height of an empty frame is the edge case). Run
# from the repo root (scripts/test.sh does).
import Base
import ./../frame.bend as DF

# a one-column frame "x" from a checked column (an error passes through)
def col_frame(r: DF.ResT(DF.Column())) -> DF.ResT(DF.Frame()):
  match r:
    case Fail{e}:
      Fail{e}
    case Done{c}:
      DF.from_columns([DF.named("x", c)])

# the column x = u32 [1, null, 3]
def three_null() -> DF.ResT(DF.Frame()):
  col_frame(DF.column(DF.t_u32(), [DF.s_u32(1), DF.s_null(), DF.s_u32(3)]))

# invalid: the second scalar is a bool, the first misfit (row 1) is the error
def column_bad() -> DF.ResT(DF.Frame()):
  col_frame(DF.column(DF.t_u32(), [DF.s_u32(1), DF.s_bool(True{}), DF.s_u32(3)]))

# the column x = u32 [1, 2, 3]
def one_two_three() -> DF.ResT(DF.Frame()):
  col_frame(DF.column(DF.t_u32(), [DF.s_u32(1), DF.s_u32(2), DF.s_u32(3)]))

def tiny() -> IO(DF.ResT(DF.Frame())):
  DF.read_csv("bench/fixtures/tiny.csv")

# DF.schema hands the frame back with its schema: the schema text, or the error
def sch.s(x: DF.Frame() & DF.Schema()) -> String:
  (f, s) = x
  DF.schema_show(Done{s})

def schema_text(r: DF.ResT(DF.Frame())) -> String:
  match r:
    case Fail{e}:
      "error: " ++ DF.err_show(e)
    case Done{f}:
      sch.s(DF.schema(f))

# DF.height hands the frame back with its row count
def hgt.s(x: DF.Frame() & U32) -> String:
  (f, h) = x
  U32.show(h)

def height_text(r: DF.ResT(DF.Frame())) -> String:
  match r:
    case Fail{e}:
      "error: " ++ DF.err_show(e)
    case Done{f}:
      hgt.s(DF.height(f))

# the plan keeps x > 1, over a source named "t" bound in its own env
def show_gt.k(x: DF.Env() & DF.Plan()) -> IO(String):
  (env, p) = x
  DF.collect_show(DF.lazy_filter(p, DF.gt(DF.col("x"), DF.lit_u32(1))), env)

def show_gt(r: DF.ResT(DF.Frame())) -> IO(String):
  match r:
    case Fail{e}:
      IO.pure(String, "error: " ++ DF.err_show(e))
    case Done{f}:
      show_gt.k(DF.source("t", f))

# invalid: filtering on the u32 column itself (the static error of collect, before any row)
def show_bad.k(x: DF.Env() & DF.Plan()) -> IO(String):
  (env, p) = x
  DF.collect_show(DF.lazy_filter(p, DF.col("x")), env)

def show_bad(r: DF.ResT(DF.Frame())) -> IO(String):
  match r:
    case Fail{e}:
      IO.pure(String, "error: " ++ DF.err_show(e))
    case Done{f}:
      show_bad.k(DF.source("t", f))

def main() -> IO(Unit):
  do IO<Unit>:
    IO.print(DF.show(three_null()))
    IO.print(DF.show(column_bad()))
    t1 : DF.ResT(DF.Frame()) <- tiny()
    IO.print(schema_text(t1))
    t2 : DF.ResT(DF.Frame()) <- tiny()
    IO.print(height_text(t2))
    IO.print(height_text(DF.from_columns([])))
    s1 : String <- show_gt(one_two_three())
    IO.print(s1)
    s2 : String <- show_bad(one_two_three())
    IO.print(s2)

#|shape: (3, 1)
#|+-----+
#|| x   |
#|| --- |
#|| u32 |
#|+=====+
#|| 1   |
#||     |
#|| 3   |
#|+-----+
#|error: TypeMismatch in from_scalars: expected u32, got bool
#|id:u32, region:str, product:str, qty:u32, price:f32, discount:f32, ok:bool
#|20
#|0
#|shape: (2, 1)
#|+-----+
#|| x   |
#|| --- |
#|| u32 |
#|+=====+
#|| 2   |
#|| 3   |
#|+-----+
#|error: TypeMismatch in filter: expected bool, got u32
