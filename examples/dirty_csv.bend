# Dirty-CSV cleanup: examples/data/dirty.csv has numbers stored as text ("7 units", "n/a", an
# empty cell, a value past u32), a non-numeric and a negative price, inconsistent status
# spellings and a malformed email. try_cast turns what does not parse into null (cast would stop
# at the first bad cell: shown below), when() and is_in() normalise and mask values, a median
# fills the missing prices, and the rows whose quantity did not parse are reported and dropped.
# The cleaning runs eagerly and as a lazy plan; both print the same table.
# Run from the repo root:  ~/.bend/bin/bend examples/dirty_csv.bend
import ./../frame.bend as DF

def path() -> String:
  "examples/data/dirty.csv"

# step 1: parse the text columns; spellings of "ok" become "ok"; an email needs "@" and ".com"
def parse() -> List<&2, DF.Expr()>:
  [DF.alias(DF.try_cast(DF.col("qty"), DF.t_u32()), "qty_n"),
   DF.alias(DF.try_cast(DF.col("price"), DF.t_f32()), "price_n"),
   DF.alias(DF.when(DF.is_in(DF.col("status"), [DF.s_str("ok"), DF.s_str("OK"), DF.s_str("Ok")]), DF.lit_str("ok"), DF.col("status")), "status"),
   DF.alias(DF.and(DF.contains_literal(DF.col("email"), "@"), DF.ends_with(DF.col("email"), ".com")), "email_ok")]

# step 2: a negative price is not a price
def mask() -> List<&2, DF.Expr()>:
  [DF.alias(DF.when(DF.lt(DF.col("price_n"), DF.lit_f32(0.0)), DF.lit_null(DF.t_f32()), DF.col("price_n")), "price_n")]

# step 3: a missing price takes the median of the known ones (a reduction, broadcast)
def fill() -> List<&2, DF.Expr()>:
  [DF.alias(DF.fill_null(DF.col("price_n"), DF.median(DF.col("price_n"))), "price_n")]

def bad_qty() -> DF.Expr():
  DF.is_null(DF.col("qty_n"))

def rejected() -> List<&2, DF.Expr()>:
  [DF.col("id"), DF.col("name"), DF.col("qty")]

def clean() -> List<&2, DF.Expr()>:
  [DF.col("id"), DF.col("name"), DF.alias(DF.col("qty_n"), "qty"), DF.alias(DF.col("price_n"), "price"),
   DF.alias(DF.mul(DF.cast_f32(DF.col("qty_n")), DF.col("price_n")), "total"), DF.col("status"), DF.col("email_ok")]

def prepared(r: DF.ResT(DF.Frame())) -> DF.ResT(DF.Frame()):
  DF.then(DF.then(DF.then(r,
    f => DF.with_columns(f, parse())),
    f => DF.with_columns(f, mask())),
    f => DF.with_columns(f, fill()))

def plan(p: DF.Plan()) -> DF.Plan():
  DF.lazy_select(DF.lazy_filter(DF.lazy_with_columns(DF.lazy_with_columns(DF.lazy_with_columns(p, parse()), mask()), fill()), DF.not(bad_qty())), clean())

def report.k(x: DF.Frame() & DF.Frame()) -> IO(Unit):
  (f1, f2) = x
  do IO<Unit>:
    IO.print("-- rows whose qty did not parse (dropped)")
    IO.print(DF.show(DF.then(DF.filter(f1, bad_qty()), f => DF.select(f, rejected()))))
    IO.print("-- cleaned (eager)")
    IO.print(DF.show(DF.then(DF.filter(f2, DF.not(bad_qty())), f => DF.select(f, clean()))))

def report(r: DF.ResT(DF.Frame())) -> IO(Unit):
  match r:
    case Fail{e}:
      IO.print("error: " ++ DF.err_show(e))
    case Done{f}:
      report.k(DF.clone(f))

def strict(r: DF.ResT(DF.Frame())) -> IO(Unit):
  do IO<Unit>:
    IO.print("-- a strict cast of qty instead of try_cast")
    IO.print(DF.show(DF.then(r, f => DF.with_columns(f, [DF.cast(DF.col("qty"), DF.t_u32())]))))

def lazy(s: DF.Res(DF.Plan())) -> IO(Unit):
  match s:
    case Fail{e}:
      IO.print("scan error: " ++ DF.err_show(e))
    case Done{+p}:
      do IO<Unit>:
        IO.print("-- schema as scanned: " ++ DF.schema_show(DF.collect_schema(p)))
        r : DF.ResT(DF.Frame()) <- DF.collect(plan(p), DF.empty_env())
        IO.print("-- cleaned (lazy)")
        IO.print(DF.show(r))

def main() -> IO(Unit):
  do IO<Unit>:
    s : DF.Res(DF.Plan()) <- DF.scan_csv(path())
    lazy(s)
    r : DF.ResT(DF.Frame()) <- DF.read_csv(path())
    report(prepared(r))
    r0 : DF.ResT(DF.Frame()) <- DF.read_csv(path())
    strict(r0)
