# p16: scale checks for the io/sort/groupby paths, natively:
#   - read a 100k-line CSV (2.2 MB) and split it into lines and fields
#   - parse one F32 column and one U32 column from the fields
#   - List.sort of the (key, idx) pairs of 2^17 keys
#   - Map<String> accumulation over 100k rows with 8 distinct keys
#   - the hub CSV parser (bend-csv-parser) on the same text, for comparison
#   ~/.bend/bin/bend probes/p16_scale_bench.bend -o /tmp/p16 && /tmp/p16 <path-to-csv>
import Base
import bend-csv-parser@0.1.0.1/core.bend as Csv

def read_all.go(r: File & Result<&1, &1, (U32 & String), String>) -> IO(String):
  (f, res) = r
  do IO<String>:
    text : String <- IO.pass(String, res)
    File.close(f)
    return text

def read_all.sized(r: File & Result<&1, &1, (U32 & String), U32>) -> IO(String):
  (f, res) = r
  do IO<String>:
    n : U32 <- IO.pass(U32, res)
    r2 : File & Result<&1, &1, (U32 & String), String> <- File.read(f, n)
    read_all.go(r2)

def read_all(path: String) -> IO(String):
  do IO<String>:
    f : File <- IO.try(File, File.open(path, "r"))
    r : File & Result<&1, &1, (U32 & String), U32> <- File.size(f)
    read_all.sized(r)

def promote(xs: List<&1, String>) -> List<&2, String>:
  match xs:
    case Nil{}:
      Nil{}
    case h <> t:
      h <> promote(t)

# rows: each line split on ','
def split_rows(lines: List<&2, String>) -> List<&2, List<&2, String>>:
  match lines:
    case Nil{}:
      Nil{}
    case l <> rest:
      String.split(l, ',') <> split_rows(rest)

def field(row: List<&2, String>, k: Nat) -> String:
  Maybe.default(&2, String, List.get(&2, String, row, k), "")

type KI is Data:
  KI{key: F32, idx: U32}

def le(p: KI, q: KI) -> Bool:
  match p q:
    case KI{x, i} KI{y, j}:
      F32.is_le(x, y)

# the F32 column (index 2) as keyed pairs, and the U32 sum of column 0
def parse_f32s(rows: List<&2, List<&2, String>>, +i: U32, acc: List<&2, KI>) -> List<&2, KI>:
  match rows:
    case Nil{}:
      acc
    case r <> rest:
      parse_f32s(rest, U32.inc(i), KI{Maybe.default(&2, F32, F32.read(field(r, 2n)), 0.0), i} <> acc)

def sum_u32s(rows: List<&2, List<&2, String>>, +acc: U32) -> U32:
  match rows:
    case Nil{}:
      acc
    case r <> rest:
      sum_u32s(rest, U32.add(acc, Maybe.default(&2, U32, U32.read(field(r, 0n)), 0)))

type Agg is Data:
  Agg{count: U32, sum: F32}

def Agg.add(m: Maybe<&2, Agg>, x: F32) -> Agg:
  match m:
    case None{}:
      Agg{1, x}
    case Some{Agg{c, s}}:
      Agg{U32.inc(c), F32.add(s, x)}

def step.put(k: String, x: F32, r: Map<&2, Agg> & Maybe<&2, Agg>) -> Map<&2, Agg>:
  (m, old) = r
  Map.set(&2, Agg, m, k, Agg.add(old, x))

def group(rows: List<&2, List<&2, String>>, m: Map<&2, Agg>) -> Map<&2, Agg>:
  match rows:
    case Nil{}:
      m
    case +r <> rest:
      +k = field(r, 1n)
      group(rest, step.put(k, Maybe.default(&2, F32, F32.read(field(r, 2n)), 0.0), Map.pop(&2, Agg, m, k)))

def show_kv(kv: Sigma<&2, &2, String, _ => Agg>) -> String:
  (k, Agg{c, s}) = kv
  k ++ "=" ++ U32.show(c)

def first_key(ps: List<&2, KI>) -> String:
  match ps:
    case Nil{}:
      "-"
    case KI{x, i} <> rest:
      F32.show(x)

def csv_rows(a: Csv.Ans) -> Nat:
  match a:
    case Csv.Parsed{rows}:
      List.length(&2, List<&2, String>, rows)
    case Csv.Rejected{}:
      0n

def stamp(label: String, t0: Nat) -> IO(Nat):
  do IO<Nat>:
    t1 : Nat <- IO.now()
    IO.print(label ++ ": " ++ Nat.show(Nat.sub(t1, t0)) ++ " ms")
    IO.now()

def run(path: String) -> IO(Unit):
  do IO<Unit>:
    t0 : Nat <- IO.now()
    +text : String <- read_all(path)
    t1 : Nat <- stamp("read " ++ Nat.show(String.length(text)) ++ " chars", t0)
    +lines : List<&2, String> = String.lines(text)
    IO.print("lines: " ++ Nat.show(List.length(&2, String, lines)))
    t2 : Nat <- stamp("lines", t1)
    +rows : List<&2, List<&2, String>> = split_rows(List.tail(&2, String, lines))
    IO.print("rows: " ++ Nat.show(List.length(&2, List<&2, String>, rows)))
    t3 : Nat <- stamp("split", t2)
    +ks : List<&2, KI> = parse_f32s(rows, 0, Nil{})
    IO.print("keys: " ++ Nat.show(List.length(&2, KI, ks)))
    t4 : Nat <- stamp("parse f32", t3)
    IO.print("u32 sum: " ++ U32.show(sum_u32s(rows, 0)))
    t5 : Nat <- stamp("parse u32", t4)
    IO.print("min key: " ++ first_key(List.sort(~KI, ~le, ks)))
    t6 : Nat <- stamp("sort", t5)
    IO.print(List.show(~&2, ~Sigma<&2, &2, String, _ => Agg>, ~show_kv, Map.to_list(&2, Agg, group(rows, Map.new(&2, Agg)))))
    t7 : Nat <- stamp("group", t6)
    IO.print("hub csv rows: " ++ Nat.show(csv_rows(Csv.parse(text))))
    t8 : Nat <- stamp("hub csv parse", t7)
    return Unit{}

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<String> <- IO.args()
    +as : List<&2, String> = promote(args)
    run(Maybe.default(&2, String, List.get(&2, String, as, 1n), "bench_10k.csv"))
