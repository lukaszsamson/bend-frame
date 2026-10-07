# p11: group_by on a String key with Base's Map: accumulate (count, sum)
# per key with Map.pop + Map.set (no default needed), then Map.to_list.
# Also: Map.get with a default on Data values, and Map key order.
#   ~/.bend/bin/bend probes/p11_map_groupby.bend
import Base

type Agg is Data:
  Agg{count: U32, sum: F32}

def Agg.add(m: Maybe<&2, Agg>, x: F32) -> Agg:
  match m:
    case None{}:
      Agg{1, x}
    case Some{Agg{c, s}}:
      Agg{U32.inc(c), F32.add(s, x)}

# helpers go ABOVE their callers (a def may only call defs declared above
# it); the popped pair is taken apart in a parameter
def step.put(k: String, x: F32, r: Map<&2, Agg> & Maybe<&2, Agg>) -> Map<&2, Agg>:
  (m, old) = r
  Map.set(&2, Agg, m, k, Agg.add(old, x))

def step(m: Map<&2, Agg>, +k: String, x: F32) -> Map<&2, Agg>:
  step.put(k, x, Map.pop(&2, Agg, m, k))

# a tuple `A & B` is a Type (Sigma<&1, &1>), so a Data list of pairs needs
# its own Data record
type Row is Data:
  Row{key: String, val: F32}

def group(rows: List<&2, Row>, m: Map<&2, Agg>) -> Map<&2, Agg>:
  match rows:
    case Nil{}:
      m
    case Row{k, x} <> rest:
      group(rest, step(m, k, x))

def show_kv(kv: Sigma<&2, &2, String, _ => Agg>) -> String:
  (k, Agg{c, s}) = kv
  k ++ "=" ++ U32.show(c) ++ "/" ++ F32.show(s)

def main() -> IO(Unit):
  do IO<Unit>:
    rows : List<&2, Row> = [Row{"b", 1.0}, Row{"a", 2.0}, Row{"b", 3.0}, Row{"c", 4.0}, Row{"a", 5.0}]
    +m : Map<&2, Agg> = group(rows, Map.new(&2, Agg))
    IO.print(List.show(~&2, ~Sigma<&2, &2, String, _ => Agg>, ~show_kv, Map.to_list(&2, Agg, m)))
    IO.print(Nat.show(Map.size(&2, Agg, m)))

#|[a=2/7, b=2/4, c=1/4]
#|3
