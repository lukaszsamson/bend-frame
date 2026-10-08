# M5 sort / group_by benchmark over the sales CSV (native; the parse is untimed):
#   ~/.bend/bin/bend bench/m5_groupby.bend -o build/m5_groupby && ./build/m5_groupby bench/data/sales_1000000.csv
import Base
import ./../src/dtype.bend as D
import ./../src/err.bend as E
import ./../src/kernels.bend as K
import ./../src/column.bend as C
import ./../src/expr.bend as X
import ./../src/eval.bend as V
import ./../src/csv.bend as CSV
import ./../src/sort.bend as SO
import ./../src/groupby.bend as G

def promote(xs: List<&1, String>) -> List<&2, String>:
  match xs:
    case Nil{}:
      Nil{}
    case h <> t:
      h <> promote(t)

def fclone.add(+n: String, a: List<&1, C.Named>, b: List<&1, C.Named>, r: C.Column & C.Column) -> List<&1, C.Named> & List<&1, C.Named>:
  (c1, c2) = r
  (C.Named{n, c1} <> a, C.Named{n, c2} <> b)

def fclone.step(+n: String, c: C.Column, st: List<&1, C.Named> & List<&1, C.Named>) -> List<&1, C.Named> & List<&1, C.Named>:
  (a, b) = st
  fclone.add(n, a, b, C.Column.clone(c))

def fclone.go(cols: List<&1, C.Named>, st: List<&1, C.Named> & List<&1, C.Named>) -> List<&1, C.Named> & List<&1, C.Named>:
  match cols:
    case Nil{}:
      st
    case C.Named{n, c} <> t:
      fclone.go(t, fclone.step(n, c, st))

def fclone.k(+h: U32, r: List<&1, C.Named> & List<&1, C.Named>) -> C.Frame & C.Frame:
  (a, b) = r
  (C.Frame{h, List.reverse(&1, C.Named, a)}, C.Frame{h, List.reverse(&1, C.Named, b)})

def fclone(f: C.Frame) -> C.Frame & C.Frame:
  match f:
    case C.Frame{+h, cols}:
      fclone.k(h, fclone.go(cols, (Nil{}, Nil{})))

def shape.k(r: C.Frame & C.FInfo) -> String:
  (f, i) = r
  match i:
    case C.FInfo{h, ns}:
      "rows=" ++ U32.show(h) ++ " cols=" ++ U32.show(U32.from_nat(List.length(&2, String, ns)))

def shape(r: E.ResT(C.Frame)) -> String:
  match r:
    case Fail{e}:
      E.Err.show(e)
    case Done{f}:
      shape.k(C.Frame.info(f))

def col(n: String) -> X.Expr:
  X.Col{n}

def q3aggs() -> List<&2, X.Expr>:
  [X.Alias{X.Agg{X.Sum{}, col("price")}, "price_sum"}, X.Alias{X.Agg{X.Mean{}, col("price")}, "price_mean"}, X.Alias{X.Agg{X.Len{}, X.Lit{D.SU32{1}}}, "count"}, X.Alias{X.Agg{X.Max{}, col("qty")}, "qty_max"}]

def stamp(label: String, t0: Nat) -> IO(Nat):
  do IO<Nat>:
    t1 : Nat <- IO.now()
    IO.print(label ++ ": " ++ Nat.show(Nat.sub(t1, t0)) ++ " ms")
    IO.now()

type Job is Data:
  GRegion{}
  GProduct{}
  GRegionProduct{}
  GId{}
  GStrAggs{}
  SQ4{}
  SProduct{}
  SDiscount{}
  SId{}

def Job.label(j: Job) -> String:
  match j:
    case GRegion{}:
      "group_by region (q3-style aggs)"
    case GProduct{}:
      "group_by product (q3-style aggs)"
    case GRegionProduct{}:
      "group_by region, product (q3-style aggs)"
    case GId{}:
      "group_by id (all distinct), len"
    case GStrAggs{}:
      "group_by region: n_unique/first/min(product)"
    case SQ4{}:
      "sort region, price desc, id (q4)"
    case SProduct{}:
      "sort product"
    case SDiscount{}:
      "sort discount (f32 with nulls) nulls_last"
    case SId{}:
      "sort id desc (u32)"

def Job.run(j: Job, f: C.Frame) -> String:
  match j:
    case GRegion{}:
      shape(G.GroupBy.run(f, [col("region")], q3aggs(), True{}))
    case GProduct{}:
      shape(G.GroupBy.run(f, [col("product")], q3aggs(), True{}))
    case GRegionProduct{}:
      shape(G.GroupBy.run(f, [col("region"), col("product")], q3aggs(), True{}))
    case GId{}:
      shape(G.GroupBy.run(f, [col("id")], [X.Alias{X.Agg{X.Len{}, X.Lit{D.SU32{1}}}, "count"}], True{}))
    case GStrAggs{}:
      shape(G.GroupBy.run(f, [col("region")], [X.Alias{X.Agg{X.NUnique{}, col("product")}, "np"}, X.Alias{X.Agg{X.First{}, col("product")}, "fp"}, X.Alias{X.Agg{X.Min{}, col("product")}, "mp"}], True{}))
    case SQ4{}:
      shape(SO.Sort.frame(f, [SO.SortKey{"region", False{}, False{}}, SO.SortKey{"price", True{}, False{}}, SO.SortKey{"id", False{}, False{}}]))
    case SProduct{}:
      shape(SO.Sort.frame(f, [SO.SortKey{"product", False{}, False{}}]))
    case SDiscount{}:
      shape(SO.Sort.frame(f, [SO.SortKey{"discount", False{}, True{}}]))
    case SId{}:
      shape(SO.Sort.frame(f, [SO.SortKey{"id", True{}, False{}}]))

# each job runs on a fresh clone (timed separately from the job)
def jobs(js: List<&2, Job>, r: C.Frame & C.Frame) -> IO(Unit):
  match js:
    case Nil{}:
      do IO<Unit>:
        return Unit{}
    case +j <> t:
      (keep, use) = r
      do IO<Unit>:
        t0 : Nat <- IO.now()
        +out : String = Job.run(j, use)
        IO.print(out)
        t1 : Nat <- stamp(Job.label(j), t0)
        jobs(t, fclone(keep))

def bench(f: C.Frame) -> IO(Unit):
  jobs([GRegion{}, GProduct{}, GRegionProduct{}, GId{}, GStrAggs{}, SQ4{}, SProduct{}, SDiscount{}, SId{}], fclone(f))

def go(r: E.ResT(C.Frame)) -> IO(Unit):
  match r:
    case Fail{e}:
      IO.print(E.Err.show(e))
    case Done{f}:
      bench(f)

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<String> <- IO.args()
    +as : List<&2, String> = promote(args)
    t0 : Nat <- IO.now()
    r : E.ResT(C.Frame) <- CSV.Csv.read_with(Maybe.default(&2, String, List.get(&2, String, as, 1n), "bench/data/sales_100000.csv"), CSV.Csv.default(), [D.TU32{}, D.TStr{}, D.TStr{}, D.TU32{}, D.TF32{}, D.TF32{}, D.TBool{}])
    t1 : Nat <- stamp("parse (untimed)", t0)
    go(r)
