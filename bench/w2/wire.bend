# W2.3 wiring differential (v0.2): group_by / unique / sort / n_unique / min / max / comparisons
# over Raw (and Dictionary) string keys, at frame level, through the public facade. Prints one line
# per operation: "<op> <shape> <n> <nulls>: h=<height> x=<content hash>" (the content hash is
# bench/m2/driver.bend's Hc.frame: a function of the LOGICAL frame, Raw and Dictionary alike).
# The SAME file is run against the v0.1 coder (the pre-W2.3 tree, a `git archive` copy) and
# against the current tree; bench/w2/wire.sh compares the two outputs line by line
# (bench/w2/results/wire_v01.txt holds the v0.1 lines).
#   ~/.bend/bin/bend bench/w2/wire.bend -o build/w2/wire
#   build/w2/wire <shape> <n> <nulls>      nulls: none | some (row i % 7 == 3) | heavy (i % 4 != 0) | all
# Columns: k (the shape's key, null rows hold "" as the v0.1 invariant says), g = i % 7 (u32),
# id = i (u32), k2 = the shape's key of row (7i + 3) % n (no nulls).
import Base
import ./../../frame.bend as DF
import ./../../src/err.bend as E
import ./../../src/kernels.bend as K
import ./../../src/column.bend as C
import ./../../src/strs.bend as ST
import ./../../tests/lib/w2gen.bend as G
import ./../m2/driver.bend as M

def Nl.is(+mode: U32, +i: U32) -> Bool:
  Bool.pick(Bool, U32.is_eq(mode, 1), U32.is_eq(U32.mod(i, 7), 3), Bool.pick(Bool, U32.is_eq(mode, 2), U32.is_ne(U32.mod(i, 4), 0), U32.is_eq(mode, 3)))

def Nl.put(nul: Bool, +i: U32, a: Array<String>, m: Array<U32>) -> Array<String> & Array<U32>:
  match nul:
    case True{}:
      (Array.set(String, a, i, ""), Array.set(U32, m, i, 0))
    case False{}:
      (a, Array.set(U32, m, i, 1))

def Nl.step(+mode: U32, +i: U32, r: Array<String> & Array<U32>) -> Array<String> & Array<U32>:
  (a, m) = r
  Nl.put(Nl.is(mode, i), i, a, m)

def Nl.go(n: Nat, +mode: U32, +i: U32, r: Array<String> & Array<U32>) -> Array<String> & Array<U32>:
  match n:
    case 0n:
      r
    case 1n+p:
      Nl.go(p, mode, U32.inc(i), Nl.step(mode, i, r))

def K2.go(n: Nat, +i: U32, +tot: U32, +sh: G.Shape, a: Array<String>) -> Array<String>:
  match n:
    case 0n:
      a
    case 1n+p:
      K2.go(p, U32.inc(i), tot, sh, Array.set(String, a, i, G.Gen.key(sh, U32.mod(U32.add(U32.mul(i, 7), 3), tot))))

def Gm.go(n: Nat, +i: U32, a: Array<U32>) -> Array<U32>:
  match n:
    case 0n:
      a
    case 1n+p:
      Gm.go(p, U32.inc(i), Array.set(U32, a, i, U32.mod(i, 7)))

def Mk.valid(+mode: U32, m: Array<U32>) -> C.Valid:
  Bool.pick(C.Valid, U32.is_eq(mode, 0), C.AllValid{}, C.Mask{m})

def Mk.fin(+n: U32, +d: Nat, +mode: U32, +sh: G.Shape, r: Array<String> & Array<U32>) -> C.Frame:
  (a, m) = r
  C.Frame{n, [C.Named{"k", C.CStr{n, d, Mk.valid(mode, m), ST.SRaw{a}}}, C.Named{"g", C.CU32{n, d, C.AllValid{}, Gm.go(U32.to_nat(n), 0, Array.new(U32, d, 0))}}, C.Named{"id", C.CU32{n, d, C.AllValid{}, K.Kernel.iota(n, d)}}, C.Named{"k2", C.CStr{n, d, C.AllValid{}, ST.SRaw{K2.go(U32.to_nat(n), 0, U32.max(n, 1), sh, Array.new(String, d, ""))}}}]}

def Mk.frame(+n: U32, +mode: U32, +sh: G.Shape) -> C.Frame:
  +d = G.Gen.depth(n)
  Mk.fin(n, d, mode, sh, Nl.go(U32.to_nat(n), mode, 0, (G.Gen.mk(n, sh), Array.new(U32, d, 0))))

def Mk.dict(+n: U32, +mode: U32, +sh: G.Shape) -> C.Frame:
  DF.encode_strings(Mk.frame(n, mode, sh), True{})

def Out.f(r: C.Frame & U32) -> String:
  (f, +h) = r
  "h=" ++ U32.show(h) ++ " x=" ++ U32.show(M.Hc.frame(f))

def Out.k(r: E.ResT(C.Frame)) -> String:
  match r:
    case Fail{e}:
      "error " ++ DF.err_show(e)
    case Done{f}:
      Out.f(DF.height(f))

def Out.line(+tag: String, op: String, r: E.ResT(C.Frame)) -> String:
  op ++ " " ++ tag ++ ": " ++ Out.k(r)

type Op is Data:
  OGb{}
  OGbg{}
  OGb2{}
  OUn{}
  OUn2{}
  OUnk{}
  OSo{}
  OSod{}
  OSon{}
  OSodn{}
  OSo2{}
  ONu{}
  OCmp{}

def Op.name(o: Op) -> String:
  match o:
    case OGb{}:
      "gb"
    case OGbg{}:
      "gbg"
    case OGb2{}:
      "gb2"
    case OUn{}:
      "un"
    case OUn2{}:
      "un2"
    case OUnk{}:
      "unk"
    case OSo{}:
      "so"
    case OSod{}:
      "sod"
    case OSon{}:
      "son"
    case OSodn{}:
      "sodn"
    case OSo2{}:
      "so2"
    case ONu{}:
      "nu"
    case OCmp{}:
      "cmp"

def Op.run(o: Op, f: C.Frame) -> E.ResT(C.Frame):
  match o:
    case OGb{}:
      DF.group_by(f, [DF.col("k")], [DF.len(), DF.first(DF.col("id")), DF.alias(DF.sum(DF.col("id")), "s"), DF.n_unique(DF.col("k2"))])
    case OGbg{}:
      DF.group_by(f, [DF.col("g")], [DF.n_unique(DF.col("k")), DF.alias(DF.min(DF.col("k")), "mn"), DF.alias(DF.max(DF.col("k")), "mx"), DF.alias(DF.first(DF.col("k")), "f"), DF.alias(DF.count(DF.col("k")), "c")])
    case OGb2{}:
      DF.group_by(f, [DF.col("k"), DF.col("g")], [DF.len()])
    case OUn{}:
      DF.unique(f, ["k"])
    case OUn2{}:
      DF.unique(f, ["k", "g"])
    case OUnk{}:
      DF.unique(f, ["k2", "k"])
    case OSo{}:
      DF.sort(f, [DF.asc("k")])
    case OSod{}:
      DF.sort(f, [DF.desc("k")])
    case OSon{}:
      DF.sort(f, [DF.sort_key("k", False{}, True{})])
    case OSodn{}:
      DF.sort(f, [DF.sort_key("k", True{}, True{})])
    case OSo2{}:
      DF.sort(f, [DF.desc("k2"), DF.asc("k")])
    case ONu{}:
      DF.select(f, [DF.n_unique(DF.col("k")), DF.alias(DF.n_unique(DF.col("k2")), "n2"), DF.alias(DF.min(DF.col("k")), "mn"), DF.alias(DF.max(DF.col("k")), "mx"), DF.alias(DF.min(DF.col("k2")), "m2")])
    case OCmp{}:
      DF.select(f, [DF.lt(DF.col("k"), DF.col("k2")), DF.alias(DF.ge(DF.col("k2"), DF.col("k")), "ge")])

def Op.all() -> List<&2, Op>:
  [OGb{}, OGbg{}, OGb2{}, OUn{}, OUn2{}, OUnk{}, OSo{}, OSod{}, OSon{}, OSodn{}, OSo2{}, ONu{}, OCmp{}]

def Run.tm(tm: Bool, +name: String, +ms: Nat) -> IO(Unit):
  match tm:
    case True{}:
      IO.print("# ms " ++ name ++ " " ++ Nat.show(ms))
    case False{}:
      IO.pure(Unit, Unit{})

# one line; with timing (a 4th argument), "# ms <op>: build <ms> op+hash <ms>" after it
def Run.one(+tm: Bool, +tag: String, +name: String, f: C.Frame, +op: Op) -> IO(Unit):
  do IO<Unit>:
    t0 : Nat <- IO.now()
    IO.print(Out.line(tag, name, Op.run(op, f)))
    t1 : Nat <- IO.now()
    Run.tm(tm, name, Nat.sub(t1, t0))

def Run.ops(ops: List<&2, Op>, +tm: Bool, +tag: String, +n: U32, +mode: U32, +sh: G.Shape) -> IO(Unit):
  match ops:
    case Nil{}:
      IO.pure(Unit, Unit{})
    case +op <> t:
      do IO<Unit>:
        Run.one(tm, tag, Op.name(op), Mk.frame(n, mode, sh), op)
        Run.one(tm, tag, "d" ++ Op.name(op), Mk.dict(n, mode, sh), op)
        Run.ops(t, tm, tag, n, mode, sh)

def shape_of(+s: String) -> G.Shape:
  Bool.pick(G.Shape, String.eq(s, "prefix"), G.ShP{},
  Bool.pick(G.Shape, String.eq(s, "longprefix"), G.ShQ{},
  Bool.pick(G.Shape, String.eq(s, "skew"), G.ShS{},
  Bool.pick(G.Shape, String.eq(s, "equal"), G.ShE{},
  Bool.pick(G.Shape, String.eq(s, "low"), G.ShL{},
  Bool.pick(G.Shape, String.eq(s, "uni"), G.ShU{},
  Bool.pick(G.Shape, String.eq(s, "empty"), G.ShZ{},
  Bool.pick(G.Shape, String.eq(s, "nul"), G.ShN{},
  Bool.pick(G.Shape, String.eq(s, "aligned"), G.ShM{},
  Bool.pick(G.Shape, String.eq(s, "wide"), G.ShW{}, G.ShD{}))))))))))

def mode_of(+s: String) -> U32:
  Bool.pick(U32, String.eq(s, "some"), 1, Bool.pick(U32, String.eq(s, "heavy"), 2, Bool.pick(U32, String.eq(s, "all"), 3, 0)))

def nth(+i: Nat, xs: List<&2, String>, +d: String) -> String:
  match i xs:
    case _ Nil{}:
      d
    case 0n h <> t:
      h
    case 1n+j h <> t:
      nth(j, t, d)

def promote(xs: List<&1, String>) -> List<&2, String>:
  match xs:
    case Nil{}:
      Nil{}
    case h <> t:
      h <> promote(t)

def num(m: Maybe<&2, U32>) -> U32:
  match m:
    case Some{x}:
      x
    case None{}:
      1000

def go.b(+tm: Bool, +shape: String, +n: U32, +nulls: String) -> IO(Unit):
  Run.ops(Op.all(), tm, shape ++ " " ++ U32.show(n) ++ " " ++ nulls, n, mode_of(nulls), shape_of(shape))

def go(+xs: List<&2, String>) -> IO(Unit):
  go.b(Bool.not(String.eq(nth(3n, xs, ""), "")), nth(0n, xs, "distinct"), num(U32.read(nth(1n, xs, "1000"))), nth(2n, xs, "none"))

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<String> <- IO.args()
    go(List.tail(&2, String, promote(args)))
