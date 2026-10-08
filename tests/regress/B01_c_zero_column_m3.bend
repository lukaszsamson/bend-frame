# Activated in M3 (table verbs): DF.drop / DF.lazy_drop, DF.unique / DF.lazy_unique,
# DF.concat_vertical / DF.lazy_concat_vertical.
# B01-c, C22-C24 (DESIGN.md 15.4): a zero-column frame keeps its height through every
# verb: drop of every column -> (6, 0); then with_columns([lit 1]) -> (6, 1);
# unique([]) -> (min(h, 1), 0); concat([z, z]) -> (12, 0). Polars 2.0.0:
# bench/contract/cardinality.py C22, C24.
import Base
import ./../../frame.bend as DF
import ./../../src/dtype.bend as D
import ./../../src/err.bend as E
import ./../../src/column.bend as C
import ./../../src/expr.bend as X
import ./../../src/plan.bend as P
import ./lib/rx.bend as R

def t() -> E.ResT(C.Frame):
  R.frame([R.mk("a", [R.u(1), R.u(2), R.null(), R.u(4), R.u(5), R.u(6)], D.TU32{})])

def env() -> P.Env:
  R.env1("t", t())

def src() -> P.Plan:
  R.src("t", t())

def e_drop(r: E.ResT(C.Frame), ns: List<&2, String>) -> E.ResT(C.Frame):
  match r:
    case Fail{e}:
      Fail{e}
    case Done{f}:
      DF.drop(f, ns)

def e_unique(r: E.ResT(C.Frame), ns: List<&2, String>) -> E.ResT(C.Frame):
  match r:
    case Fail{e}:
      Fail{e}
    case Done{f}:
      DF.unique(f, ns)

def zz.k(f: C.Frame, s: E.ResT(C.Frame)) -> E.ResT(C.Frame):
  match s:
    case Fail{e}:
      Fail{e}
    case Done{g}:
      DF.concat_vertical([f, g])

def zz(r: E.ResT(C.Frame), s: E.ResT(C.Frame)) -> E.ResT(C.Frame):
  match r:
    case Fail{e}:
      Fail{e}
    case Done{f}:
      zz.k(f, s)

def o() -> X.Expr:
  DF.alias(DF.lit_u32(1), "o")

def main() -> IO(Unit):
  do IO<Unit>:
    R.three("B01-c C22 drop-all", e_drop(t(), ["a"]), DF.lazy_drop(src(), ["a"]), env(), env())
    R.three("B01-c C22 drop-all-then-literal", R.e_with(e_drop(t(), ["a"]), [o()]), DF.lazy_with_columns(DF.lazy_drop(src(), ["a"]), [o()]), env(), env())
    R.three("B01-c C24 unique-all", e_unique(e_drop(t(), ["a"]), []), DF.lazy_unique(DF.lazy_drop(src(), ["a"]), []), env(), env())
    R.three("B01-c C24 concat", zz(e_drop(t(), ["a"]), e_drop(t(), ["a"])), DF.lazy_concat_vertical([DF.lazy_drop(src(), ["a"]), DF.lazy_drop(R.src("u", t()), ["a"])]), R.env_add(env(), "u", t()), R.env_add(env(), "u", t()))
#|-- B01-c C22 drop-all eager
#|frame
#|height	6
#|width	0
#|
#|-- B01-c C22 drop-all raw
#|frame
#|height	6
#|width	0
#|
#|-- B01-c C22 drop-all opt
#|frame
#|height	6
#|width	0
#|
#|-- B01-c C22 drop-all-then-literal eager
#|frame
#|height	6
#|width	1
#|col	u32	"o"
#|row	1
#|row	1
#|row	1
#|row	1
#|row	1
#|row	1
#|
#|-- B01-c C22 drop-all-then-literal raw
#|frame
#|height	6
#|width	1
#|col	u32	"o"
#|row	1
#|row	1
#|row	1
#|row	1
#|row	1
#|row	1
#|
#|-- B01-c C22 drop-all-then-literal opt
#|frame
#|height	6
#|width	1
#|col	u32	"o"
#|row	1
#|row	1
#|row	1
#|row	1
#|row	1
#|row	1
#|
#|-- B01-c C24 unique-all eager
#|frame
#|height	1
#|width	0
#|
#|-- B01-c C24 unique-all raw
#|frame
#|height	1
#|width	0
#|
#|-- B01-c C24 unique-all opt
#|frame
#|height	1
#|width	0
#|
#|-- B01-c C24 concat eager
#|frame
#|height	12
#|width	0
#|
#|-- B01-c C24 concat raw
#|frame
#|height	12
#|width	0
#|
#|-- B01-c C24 concat opt
#|frame
#|height	12
#|width	0
#|
