# M4 facade: the Str storage option (DESIGN.md 14 "M4 string experiment", 15.2). The readers
# hold a str column as a Dictionary while it has few distinct values (DF.str_auto, the default),
# or as one string per row (DF.str_raw), or always as a Dictionary (DF.str_dict);
# DF.encode_strings converts a frame either way; DF.dict_columns names the Dictionary columns.
# Storage never changes a value: every pair below compares DF.dump texts (`same`).
# tiny.csv: id u32, region str, product str, qty u32, price f32, discount f32, ok bool.
# Run from the repo root (scripts/test.sh does).
import Base
import ./../frame.bend as DF

def path() -> String:
  "bench/fixtures/tiny.csv"

def rd(enc: DF.StrEnc()) -> IO(DF.ResT(DF.Frame())):
  DF.read_csv_enc(path(), DF.csv_opts(',', True{}, 100), [], enc)

def names(xs: List<&2, String>) -> String:
  match xs:
    case Nil{}:
      "[]"
    case h <> t:
      h ++ " " ++ names(t)

def cols.k(x: DF.Frame() & List<&2, String>) -> String:
  (f, ns) = x
  names(ns)

# the Dictionary columns of a read frame, or the error text
def cols(r: DF.ResT(DF.Frame())) -> String:
  match r:
    case Fail{e}:
      "error: " ++ DF.err_show(e)
    case Done{f}:
      cols.k(DF.dict_columns(f))

def same(+tag: String, +a: String, +b: String) -> String:
  Bool.pick(String, String.eq(a, b), tag ++ ": same", tag ++ ": DIFF\n" ++ a ++ "\n" ++ b)

def conv(r: DF.ResT(DF.Frame()), +dict: Bool) -> DF.ResT(DF.Frame()):
  match r:
    case Fail{e}:
      Fail{e}
    case Done{f}:
      Done{DF.encode_strings(f, dict)}

# group by region: sum(qty) (groups in first-seen order); and filter product == "prod_61"
def grp(r: DF.ResT(DF.Frame())) -> String:
  match r:
    case Fail{e}:
      "error: " ++ DF.err_show(e)
    case Done{f}:
      DF.dump(DF.group_by(f, [DF.col("region")], [DF.sum(DF.col("qty"))]))

def flt(r: DF.ResT(DF.Frame())) -> String:
  match r:
    case Fail{e}:
      "error: " ++ DF.err_show(e)
    case Done{f}:
      DF.dump(DF.filter(f, DF.eq(DF.col("product"), DF.lit_str("prod_61"))))

# the same group_by, lazily over the frame bound as "t"
def lazy.k(x: DF.Env() & DF.Plan()) -> IO(String):
  (env, p) = x
  do IO<String>:
    r : DF.ResT(DF.Frame()) <- DF.collect(DF.lazy_group_by(p, [DF.col("region")], [DF.sum(DF.col("qty"))]), env)
    return DF.dump(r)

def lazy(r: DF.ResT(DF.Frame())) -> IO(String):
  match r:
    case Fail{e}:
      IO.pure(String, "error: " ++ DF.err_show(e))
    case Done{f}:
      lazy.k(DF.source("t", f))

def scan.k(r: DF.Res(DF.Plan())) -> IO(String):
  match r:
    case Fail{e}:
      IO.pure(String, "error: " ++ DF.err_show(e))
    case Done{p}:
      do IO<String>:
        f : DF.ResT(DF.Frame()) <- DF.collect(p, DF.empty_env())
        return cols(f)

# scan_csv's collect reads with the default storage
def scan() -> IO(String):
  do IO<String>:
    r : DF.Res(DF.Plan()) <- DF.scan_csv(path())
    scan.k(r)

def lits.k(r: DF.ResT(DF.Column())) -> DF.ResT(DF.Frame()):
  match r:
    case Fail{e}:
      Fail{e}
    case Done{c}:
      DF.from_columns([DF.named("x", c)])

# a frame built from literals: a Raw str column "x" ["a", null, "a", ""]
def lits() -> DF.ResT(DF.Frame()):
  lits.k(DF.column(DF.t_str(), [DF.s_str("a"), DF.s_null(), DF.s_str("a"), DF.s_str("")]))

def rd_dump(enc: DF.StrEnc()) -> IO(String):
  do IO<String>:
    r : DF.ResT(DF.Frame()) <- rd(enc)
    return DF.dump(r)

def rd_conv(enc: DF.StrEnc(), +dict: Bool) -> IO(String):
  do IO<String>:
    r : DF.ResT(DF.Frame()) <- rd(enc)
    return DF.dump(conv(r, dict))

def rd_grp(enc: DF.StrEnc()) -> IO(String):
  do IO<String>:
    r : DF.ResT(DF.Frame()) <- rd(enc)
    return grp(r)

def rd_flt(enc: DF.StrEnc()) -> IO(String):
  do IO<String>:
    r : DF.ResT(DF.Frame()) <- rd(enc)
    return flt(r)

def rd_lazy(enc: DF.StrEnc()) -> IO(String):
  do IO<String>:
    r : DF.ResT(DF.Frame()) <- rd(enc)
    lazy(r)

def main() -> IO(Unit):
  do IO<Unit>:
    a : DF.ResT(DF.Frame()) <- DF.read_csv(path())
    IO.print("read_csv (default auto): " ++ cols(a))
    r : DF.ResT(DF.Frame()) <- rd(DF.str_raw())
    IO.print("raw: " ++ cols(r))
    d : DF.ResT(DF.Frame()) <- rd(DF.str_dict())
    IO.print("dict: " ++ cols(d))
    u : DF.ResT(DF.Frame()) <- rd(DF.str_auto())
    IO.print("auto: " ++ cols(u))
    s : String <- scan()
    IO.print("scan_csv collect: " ++ s)
    r1 : DF.ResT(DF.Frame()) <- rd(DF.str_raw())
    IO.print("encode_strings True: " ++ cols(conv(r1, True{})))
    a1 : DF.ResT(DF.Frame()) <- DF.read_csv(path())
    IO.print("encode_strings False: " ++ cols(conv(a1, False{})))
    IO.print("literal frame: " ++ cols(lits()))
    IO.print("literal frame encoded: " ++ cols(conv(lits(), True{})))
    IO.print(same("literal frame dump", DF.dump(lits()), DF.dump(conv(lits(), True{}))))
    +base : String <- rd_dump(DF.str_raw())
    IO.print(String.trim(String.take(base, 5n)))
    x1 : String <- rd_dump(DF.str_dict())
    IO.print(same("dump dict", base, x1))
    x2 : String <- rd_dump(DF.str_auto())
    IO.print(same("dump auto", base, x2))
    x3 : String <- rd_conv(DF.str_raw(), True{})
    IO.print(same("dump raw encoded", base, x3))
    x4 : String <- rd_conv(DF.str_dict(), False{})
    IO.print(same("dump dict decoded", base, x4))
    +g0 : String <- rd_grp(DF.str_raw())
    IO.print(g0)
    g1 : String <- rd_grp(DF.str_dict())
    IO.print(same("group_by dict", g0, g1))
    +f0 : String <- rd_flt(DF.str_raw())
    IO.print(f0)
    f1 : String <- rd_flt(DF.str_dict())
    IO.print(same("filter dict", f0, f1))
    +l0 : String <- rd_lazy(DF.str_raw())
    l1 : String <- rd_lazy(DF.str_dict())
    IO.print(same("lazy group_by raw vs dict", l0, l1))
    IO.print(same("lazy vs eager group_by", l0, g0))

#|read_csv (default auto): region product []
#|raw: []
#|dict: region product []
#|auto: region product []
#|scan_csv collect: region product []
#|encode_strings True: region product []
#|encode_strings False: []
#|literal frame: []
#|literal frame encoded: x []
#|literal frame dump: same
#|frame
#|dump dict: same
#|dump auto: same
#|dump raw encoded: same
#|dump dict decoded: same
#|frame
#|height	7
#|width	2
#|col	str	"region"
#|col	u32	"qty"
#|row	"inland"	317
#|row	"west"	119
#|row	"south"	104
#|row	"central"	108
#|row	"coastal"	210
#|row	"island"	142
#|row	"north"	33
#|
#|group_by dict: same
#|frame
#|height	1
#|width	7
#|col	u32	"id"
#|col	str	"region"
#|col	str	"product"
#|col	u32	"qty"
#|col	f32	"price"
#|col	f32	"discount"
#|col	bool	"ok"
#|row	1	"inland"	"prod_61"	78	0x43a6af5c	null	true
#|
#|filter dict: same
#|lazy group_by raw vs dict: same
#|lazy vs eager group_by: same
