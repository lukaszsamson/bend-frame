# DF.dump (the typed oracle, DESIGN.md 15.1): every dtype, nulls, NaN, -0.0, inf,
# "" vs null, an empty frame, a zero-column frame, a zero-row frame, error dumps.
# Fields are TAB separated; the final newline of the dump is trimmed by the runner.
import ./../frame.bend as DF
import ./../src/dtype.bend as D
import ./../src/err.bend as E
import ./../src/column.bend as C

def mk.k(name: String, r: E.ResT(C.Column)) -> C.Named:
  match r:
    case Fail{e}:
      C.Named{E.Err.show(e), C.CU32{0, 0n, C.AllValid{}, [0 : U32*1n]}}
    case Done{c}:
      C.Named{name, c}

def mk(name: String, xs: List<&2, D.Scalar>, +t: D.DType) -> C.Named:
  mk.k(name, C.Column.from_scalars(xs, t))

def ch(c: U32) -> String:
  SCon{Chr{c}, SNil{}}

def nan() -> F32:
  F32.div(0.0, 0.0)

def inf() -> F32:
  F32.div(1.0, 0.0)

def tricky() -> String:
  "a\tb\"c\\d\ne" ++ ch(1) ++ ch(13) ++ ch(127) ++ "f" ++ ch(233)

# every dtype, nulls in each column, specials in the f32 column
def wide() -> E.ResT(C.Frame):
  C.Frame.from_columns([
    mk("b", [D.SBool{True{}}, D.SNull{}, D.SBool{False{}}, D.SBool{True{}}], D.TBool{}),
    mk("u", [D.SU32{0}, D.SU32{4294967295}, D.SNull{}, D.SU32{7}], D.TU32{}),
    mk("i", [D.SI32{D.I32.neg(D.I32{2})}, D.SNull{}, D.SI32{D.I32{2147483648}}, D.SI32{D.I32{0}}], D.TI32{}),
    mk("f", [D.SF32{1.0}, D.SNull{}, D.SF32{F32.neg(0.0)}, D.SF32{0.0}], D.TF32{}),
    mk("s", [D.SStr{""}, D.SNull{}, D.SStr{tricky()}, D.SStr{"plain"}], D.TStr{})])

def specials() -> E.ResT(C.Frame):
  C.Frame.from_columns([
    mk("f", [D.SF32{nan()}, D.SF32{inf()}, D.SF32{F32.neg(inf())}, D.SF32{F32.neg(0.0)}, D.SF32{0.5}, D.SNull{}], D.TF32{})])

# two columns, no rows
def zero_rows() -> E.ResT(C.Frame):
  C.Frame.from_columns([mk("a", [], D.TU32{}), mk("s", [], D.TStr{})])

# a name needing escapes
def odd_name() -> E.ResT(C.Frame):
  C.Frame.from_columns([mk("a\tb\"", [D.SU32{1}], D.TU32{})])

def zero_cols() -> E.ResT(C.Frame):
  Done{C.Frame{3, Nil{}}}

def empty() -> E.ResT(C.Frame):
  Done{C.Frame.empty()}

def sel_bad(r: E.ResT(C.Frame)) -> E.ResT(C.Frame):
  match r:
    case Fail{e}:
      Fail{e}
    case Done{f}:
      DF.select(f, [DF.col("nope")])

def main() -> IO(Unit):
  do IO<Unit>:
    IO.print("-- wide")
    IO.print(DF.dump(wide()))
    IO.print("-- specials")
    IO.print(DF.dump(specials()))
    IO.print("-- zero_rows")
    IO.print(DF.dump(zero_rows()))
    IO.print("-- odd_name")
    IO.print(DF.dump(odd_name()))
    IO.print("-- zero_cols")
    IO.print(DF.dump(zero_cols()))
    IO.print("-- empty")
    IO.print(DF.dump(empty()))
    IO.print("-- error missing column")
    IO.print(DF.dump(sel_bad(wide())))
    IO.print("-- error built")
    IO.print(DF.dump(Fail{E.TypeMismatch{"add", "u32", "str"}}))
    IO.print("-- dump_frame")
    IO.print(DF.dump_frame(C.Frame{2, Nil{}}))
#|-- wide
#|frame
#|height	4
#|width	5
#|col	bool	"b"
#|col	u32	"u"
#|col	i32	"i"
#|col	f32	"f"
#|col	str	"s"
#|row	true	0	-2	0x3f800000	""
#|row	null	4294967295	null	null	null
#|row	false	null	-2147483648	0x80000000	"a\tb\"c\\d\ne\x01\r\x7ffé"
#|row	true	7	0	0x00000000	"plain"
#|
#|-- specials
#|frame
#|height	6
#|width	1
#|col	f32	"f"
#|row	0x7fc00000
#|row	0x7f800000
#|row	0xff800000
#|row	0x80000000
#|row	0x3f000000
#|row	null
#|
#|-- zero_rows
#|frame
#|height	0
#|width	2
#|col	u32	"a"
#|col	str	"s"
#|
#|-- odd_name
#|frame
#|height	1
#|width	1
#|col	u32	"a\tb\""
#|row	1
#|
#|-- zero_cols
#|frame
#|height	3
#|width	0
#|
#|-- empty
#|frame
#|height	0
#|width	0
#|
#|-- error missing column
#|error	ColumnNotFound: nope
#|
#|-- error built
#|error	TypeMismatch in add: expected u32, got str
#|
#|-- dump_frame
#|frame
#|height	2
#|width	0
