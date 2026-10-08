# Dedupe plus semi / anti joins. Two monthly signup files are stacked (concat_vertical), each
# email keeps its FIRST signup (unique, keep first, input order), blocked emails are removed
# (anti join), and the customers are split into those with at least one order (semi join: each
# customer once, however many orders) and those with none (anti join). Eager first, then the
# same pipeline as one lazy plan. Only the facade is imported.
# Run from the repo root:  ~/.bend/bin/bend examples/dedupe.bend
import ./../frame.bend as DF

def on_email() -> List<&2, String>:
  ["email"]

# ---- eager: DF.then passes an error through, so each step reads as one call --------------

def stack(a: DF.ResT(DF.Frame()), b: DF.ResT(DF.Frame())) -> DF.ResT(DF.Frame()):
  DF.then(a, fa => DF.then(b, fb => DF.concat_vertical([fa, fb])))

def first_signup(r: DF.ResT(DF.Frame())) -> DF.ResT(DF.Frame()):
  DF.then(r, f => DF.unique(f, on_email()))

def without(r: DF.ResT(DF.Frame()), other: DF.ResT(DF.Frame())) -> DF.ResT(DF.Frame()):
  DF.then(r, f => DF.then(other, g => DF.anti_join(f, g, on_email(), on_email())))

def having(r: DF.ResT(DF.Frame()), other: DF.ResT(DF.Frame())) -> DF.ResT(DF.Frame()):
  DF.then(r, f => DF.then(other, g => DF.semi_join(f, g, on_email(), on_email())))

def tidy(r: DF.ResT(DF.Frame())) -> DF.ResT(DF.Frame()):
  DF.then(r, f => DF.rename(f, [("day", "first_day")]))

def report.k(c: DF.Frame() & DF.Frame(), o: DF.Frame() & DF.Frame()) -> String:
  (c1, c2) = c
  (o1, o2) = o
  "-- customers with an order\n" ++ DF.show(tidy(having(Done{c1}, Done{o1}))) ++ "\n-- customers without one\n" ++ DF.show(tidy(without(Done{c2}, Done{o2})))

# both splits need the customers and the orders, so each is cloned once
def report(cs: DF.ResT(DF.Frame()), os: DF.ResT(DF.Frame())) -> String:
  match cs:
    case Fail{e}:
      "error: " ++ DF.err_show(e)
    case Done{c}:
      match os:
        case Fail{e}:
          "error: " ++ DF.err_show(e)
        case Done{o}:
          report.k(DF.clone(c), DF.clone(o))

# ---- lazy: one plan, typed and explained before anything runs ---------------------------

def plan(sep: DF.Plan(), oct: DF.Plan(), blocked: DF.Plan(), orders: DF.Plan()) -> DF.Plan():
  DF.lazy_rename(
    DF.lazy_semi_join(
      DF.lazy_anti_join(DF.lazy_unique(DF.lazy_concat_vertical([sep, oct]), on_email()), blocked, on_email(), on_email()),
      orders, on_email(), on_email()),
    [("day", "first_day")])

def run_lazy(+p: DF.Plan()) -> IO(Unit):
  do IO<Unit>:
    IO.print("-- lazy: schema, plan, result")
    IO.print(DF.schema_show(DF.collect_schema(p)))
    IO.print(DF.explain(p))
    r : DF.ResT(DF.Frame()) <- DF.collect(p, DF.empty_env())
    IO.print(DF.show(r))

def lazy4(a: DF.Res(DF.Plan()), b: DF.Res(DF.Plan()), c: DF.Res(DF.Plan()), d: DF.Res(DF.Plan())) -> IO(Unit):
  match a b c d:
    case Done{pa} Done{pb} Done{pc} Done{pd}:
      run_lazy(plan(pa, pb, pc, pd))
    case _ _ _ _:
      IO.print("error: a scan failed")

def main() -> IO(Unit):
  do IO<Unit>:
    sep : DF.ResT(DF.Frame()) <- DF.read_csv("bench/fixtures/signups_sep.csv")
    oct : DF.ResT(DF.Frame()) <- DF.read_csv("bench/fixtures/signups_oct.csv")
    blocked : DF.ResT(DF.Frame()) <- DF.read_csv("bench/fixtures/blocked.csv")
    orders : DF.ResT(DF.Frame()) <- DF.read_csv("bench/fixtures/orders.csv")
    IO.print(report(without(first_signup(stack(sep, oct)), blocked), orders))
    ps : DF.Res(DF.Plan()) <- DF.scan_csv("bench/fixtures/signups_sep.csv")
    po : DF.Res(DF.Plan()) <- DF.scan_csv("bench/fixtures/signups_oct.csv")
    pb : DF.Res(DF.Plan()) <- DF.scan_csv("bench/fixtures/blocked.csv")
    pr : DF.Res(DF.Plan()) <- DF.scan_csv("bench/fixtures/orders.csv")
    lazy4(ps, po, pb, pr)
