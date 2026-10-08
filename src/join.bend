# src/join.bend -- Join.run: inner and left equi-joins on one or more keys. DESIGN.md 4.10.
#
# Algorithm (no per-row Map lookups, no per-row key strings):
#  1. Check the keys against both schemas (Join.schema, pure Data: the same
#     function Plan.schema can use): ColumnNotFound, TypeMismatch{"join", ..},
#     DuplicateColumn after suffixing, unequal/empty key lists.
#  2. Encode each key pair into U32 codes. Bool/U32/I32: the data word; F32:
#     the bits (0.0 == -0.0, every NaN equal, as Polars); Str: a dense id from
#     an open-addressing string table built over the RIGHT column (FNV-1a +
#     Fibonacci slot, own string equality), the left column is probed against
#     it (a miss can never match: DEAD), in 16 parallel blocks for big inputs
#     (the string walks are memory bound). Several keys are combined into one
#     dense id per row with a pair table ((id so far, code) -> dense id),
#     built on the right side and probed by the left. Null keys never match:
#     their rows get DEAD.
#  3. Right rows are grouped by id (CSR: counts, exclusive prefix sums, rows
#     in right order). For left row i with id g: m = counts[g] matches.
#     Pass 1 sizes the output (inner: m rows, left: max(m, 1) rows), pass 2
#     writes perm_l / perm_r / valid_r. When every left row has exactly one
#     output row (the common lookup join), perm_l is the identity: the left
#     columns are kept without a gather and perm_r is one gather of rows by
#     the starts (no per-row fill loop).
#  4. Left columns (all, keys included) then right non-key columns, gathered;
#     a right name that clashes with a left name gets `_right` (Polars); on
#     a left join the right columns are nulled where a left row had no match.
# Output order: left row order; the matches of one left row in right row order
# (Polars maintain_order="left_right"), for both inner and left joins.
#
# Idioms (DESIGN.md section 9): helpers above callers; Nat fuel first; a pair
# result is taken apart in the next helper's parameter; loop exits are matched
# on a Bool carried in a pair/record parameter (`Tuple{t, False{}}`,
# `PK{.., False{}}`: Base's Map idiom).
import Base
import ./dtype.bend as D
import ./err.bend as E
import ./kernels.bend as K
import ./column.bend as C
import ./strs.bend as ST
import ./schema.bend as S

type JoinHow is Data:
  Inner{}
  Left{}

# one checked key pair
type KeySpec is Data:
  KeySpec{l: String, r: String, t: D.DType}

# a string-table slot / pair-table slot; id = 0 is an empty slot, else dense id + 1
type SSlot is Data:
  SSlot{key: String, id: U32}

# the id a put/get answers, and the table's next free id
type PRes is Data:
  PRes{id: U32, g: U32}

# open-addressing tables of 2^b slots (load <= 1/2): fuel = 2^b, mask = 2^b - 1,
# pw = 2^(32 - b) (slot = (h * golden) / pw: the top b bits), g = ids handed out
type Dict is Type:
  Dict{fuel: Nat, mask: U32, pw: U32, g: U32, slots: Array<SSlot>}

type PT is Type:
  PT{fuel: Nat, mask: U32, pw: U32, g: U32, ka: Array<U32>, kb: Array<U32>, ids: Array<U32>}

# a probe cursor over the pair table's arrays: keep probing?
type PK is Type:
  PK{ka: Array<U32>, kb: Array<U32>, ids: Array<U32>, more: Bool}

# a key column's codes: code per row, its 0/1 validity, the string table
# (built on the right side, handed to the left side; a dummy for non-strings)
type Enc is Type:
  Enc{codes: Array<U32>, live: Array<U32>, dict: Dict}

# the column walker's slot: the input before the named column is met, the result after
type Slot is Type:
  SIn{d: Dict}
  SOut{e: Enc}

# loop states
type DC is Type:
  DC{codes: Array<U32>, d: Dict}

type SD is Type:
  SD{data: Array<String>, dc: DC}

# two copies of a string table (one per side of a forked probe)
type DD is Type:
  DD{a: Dict, b: Dict}

type DS is Type:
  DS{pt: PT, out: Array<U32>}

type JS is Type:
  JS{first: Bool, g: U32, nl: U32, nr: U32, lcols: List<&1, C.Named>, rcols: List<&1, C.Named>, accl: Array<U32>, accr: Array<U32>}

type CF is Type:
  CF{cur: Array<U32>, rows: Array<U32>}

type CSR is Type:
  CSR{counts: Array<U32>, starts: Array<U32>, rows: Array<U32>}

type TA is Data:
  TA{t: U32, ones: U32, miss: U32}

type FS is Type:
  FS{k: U32, rows: Array<U32>, pl: Array<U32>, pr: Array<U32>, vr: Array<U32>}

type GS is Type:
  GS{perm: Array<U32>, vr: Array<U32>, acc: List<&1, C.Named>}

def JoinHow.show(h: JoinHow) -> String:
  match h:
    case Inner{}:
      "inner"
    case Left{}:
      "left"

def JoinHow.is_left(h: JoinHow) -> Bool:
  match h:
    case Inner{}:
      False{}
    case Left{}:
      True{}

def Join.dead() -> U32:
  4294967295

# ---- schema (pure Data) ------------------------------------------------------------

def Join.check.eq(same: Bool, +a: D.DType, +b: D.DType) -> E.Res(D.DType):
  match same:
    case True{}:
      Done{a}
    case False{}:
      Fail{E.TypeMismatch{"join", D.DType.show(a), D.DType.show(b)}}

def Join.check.key(lt: Maybe<&2, D.DType>, rt: Maybe<&2, D.DType>, ln: String, rn: String) -> E.Res(D.DType):
  match lt rt:
    case None{} _:
      Fail{E.ColumnNotFound{ln}}
    case Some{a} None{}:
      Fail{E.ColumnNotFound{rn}}
    case Some{+a} Some{+b}:
      Join.check.eq(D.DType.eq(a, b), a, b)

def Join.keys.put(+ln: String, +rn: String, r: E.Res(D.DType), rest: E.Res(List<&2, KeySpec>)) -> E.Res(List<&2, KeySpec>):
  match r:
    case Fail{e}:
      Fail{e}
    case Done{t}:
      match rest:
        case Fail{e}:
          Fail{e}
        case Done{ks}:
          Done{KeySpec{ln, rn, t} <> ks}

def Join.keys.len() -> E.Err:
  E.InvalidOperation{"join: left_on and right_on must have the same length"}

def Join.keys.go(lo: List<&2, String>, ro: List<&2, String>, +ls: List<&2, S.Field>, +rs: List<&2, S.Field>) -> E.Res(List<&2, KeySpec>):
  match lo:
    case Nil{}:
      match ro:
        case Nil{}:
          Done{Nil{}}
        case b <> bt:
          Fail{Join.keys.len()}
    case +a <> at:
      match ro:
        case Nil{}:
          Fail{Join.keys.len()}
        case +b <> bt:
          Join.keys.put(a, b, Join.check.key(S.Schema.find(ls, a), S.Schema.find(rs, b), a, b), Join.keys.go(at, bt, ls, rs))

# the checked key pairs, in order; the first bad pair's error wins
def Join.keys(lo: List<&2, String>, ro: List<&2, String>, +ls: List<&2, S.Field>, +rs: List<&2, S.Field>) -> E.Res(List<&2, KeySpec>):
  match lo:
    case Nil{}:
      Fail{E.InvalidOperation{"join: no key columns"}}
    case h <> t:
      Join.keys.go(h <> t, ro, ls, rs)

# a right column name that clashes with a left one gets the suffix `_right`
def Join.rname(+lnames: List<&2, String>, +n: String) -> String:
  Bool.pick(String, C.Names.has(lnames, n), n ++ "_right", n)

def Join.rfields.k(drop: Bool, n: String, t: D.DType, rest: List<&2, S.Field>) -> List<&2, S.Field>:
  match drop:
    case True{}:
      rest
    case False{}:
      S.Field{n, t} <> rest

# the right fields minus the right keys, renamed
def Join.rfields(rs: List<&2, S.Field>, +right_on: List<&2, String>, +lnames: List<&2, String>) -> List<&2, S.Field>:
  match rs:
    case Nil{}:
      Nil{}
    case S.Field{+n, t} <> rest:
      Join.rfields.k(C.Names.has(right_on, n), Join.rname(lnames, n), t, Join.rfields(rest, right_on, lnames))

def Join.schema.c(d: Maybe<&2, String>, fs: List<&2, S.Field>) -> E.Res(List<&2, S.Field>):
  match d:
    case Some{n}:
      Fail{E.DuplicateColumn{n}}
    case None{}:
      Done{fs}

def Join.schema.b(+fs: List<&2, S.Field>) -> E.Res(List<&2, S.Field>):
  Join.schema.c(C.Names.dup(S.Schema.names(fs), Nil{}, None{}), fs)

def Join.schema.a(ks: E.Res(List<&2, KeySpec>), +ls: List<&2, S.Field>, rs: List<&2, S.Field>, right_on: List<&2, String>) -> E.Res(List<&2, S.Field>):
  match ks:
    case Fail{e}:
      Fail{e}
    case Done{k}:
      Join.schema.b(List.append(&2, S.Field, ls, Join.rfields(rs, right_on, S.Schema.names(ls))))

# the output schema of a join (inner and left alike: left fields, then the
# right fields minus right_on, clashing names suffixed `_right`); errors:
# InvalidOperation (no keys / unequal key lists), ColumnNotFound,
# TypeMismatch{"join", left dtype, right dtype}, DuplicateColumn
def Join.schema(+ls: List<&2, S.Field>, +rs: List<&2, S.Field>, left_on: List<&2, String>, +right_on: List<&2, String>) -> E.Res(List<&2, S.Field>):
  Join.schema.a(Join.keys(left_on, right_on, ls, rs), ls, rs, right_on)

# ---- strings: hash and equality -------------------------------------------------------

# FNV-1a over the code points
def Str.hash(s: String, h: U32) -> U32:
  match s:
    case SNil{}:
      h
    case SCon{Chr{c}, t}:
      Str.hash(t, U32.mul(U32.xor(h, c), 16777619))

def Str.eq(a: String, b: String) -> Bool:
  match a b:
    case SNil{} SNil{}:
      True{}
    case SCon{Chr{x}, s} SCon{Chr{y}, t}:
      Bool.and(U32.is_eq(x, y), Str.eq(s, t))
    case _ _:
      False{}

# the top bits of h * golden ratio: a slot of a 2^b table (pw = 2^(32-b))
def Join.slot(h: U32, pw: U32) -> U32:
  U32.div(U32.mul(h, 2654435769), pw)

# 2^b slots for n keys at load <= 1/2: (b, 2^b, 2^(32-b))
def Join.tbits(+n: U32) -> Nat:
  K.Kernel.depth_for(U32.max(U32.add(n, n), 2))

# ---- string table ------------------------------------------------------------------------

def Dict.new.k(+b: Nat) -> Dict:
  +size = U32.shln(1, b)
  Dict{U32.to_nat(size), U32.sub(size, 1), U32.shln(1, Nat.sub(32n, b)), 0, Array.new(SSlot, b, SSlot{"", 0})}

def Dict.new(+n: U32) -> Dict:
  Dict.new.k(Join.tbits(n))

def Dict.empty() -> Dict:
  Dict.new.k(1n)

def Dict.count(d: Dict) -> U32:
  match d:
    case Dict{fuel, mask, pw, g, slots}:
      g

# keep probing while the slot is taken by another key
def Dict.look(+s: String, r: Array<SSlot> & SSlot) -> Array<SSlot> & Bool:
  (t, x) = r
  match x:
    case SSlot{k, +id}:
      (t, Bool.and(U32.is_ne(id, 0), Bool.not(Str.eq(k, s))))

# the slot holding s, or the empty slot where it would go
def Dict.seek.go(n: Nat, r: Array<SSlot> & Bool, +s: String, +mask: U32, +i: U32) -> Array<SSlot> & U32:
  match n r:
    case 0n Tuple{t, c}:
      (t, i)
    case _ Tuple{t, False{}}:
      (t, i)
    case 1n+p Tuple{t, True{}}:
      +j = U32.and(U32.inc(i), mask)
      Dict.seek.go(p, Dict.look(s, Array.get(SSlot, t, j)), s, mask, j)

def Dict.seek(+fuel: Nat, +mask: U32, +pw: U32, slots: Array<SSlot>, +s: String) -> Array<SSlot> & U32:
  +i = Join.slot(Str.hash(s, 2166136261), pw)
  Dict.seek.go(fuel, Dict.look(s, Array.get(SSlot, slots, i)), s, mask, i)

def Dict.put.k(+s: String, +g: U32, +i: U32, r: Array<SSlot> & SSlot) -> Array<SSlot> & PRes:
  (t, x) = r
  match x:
    case SSlot{k, +id}:
      +e = U32.is_eq(id, 0)
      +nid = Bool.pick(U32, e, U32.inc(g), id)
      (Array.set(SSlot, t, i, SSlot{s, nid}), PRes{U32.sub(nid, 1), U32.add(g, Bool.to_u32(e))})

def Dict.put.j(+s: String, +g: U32, r: Array<SSlot> & U32) -> Array<SSlot> & PRes:
  (t, +i) = r
  Dict.put.k(s, g, i, Array.get(SSlot, t, i))

def Dict.get.k(r: Array<SSlot> & SSlot) -> Array<SSlot> & PRes:
  (t, x) = r
  match x:
    case SSlot{k, +id}:
      (t, PRes{Bool.pick(U32, U32.is_eq(id, 0), Join.dead(), U32.sub(id, 1)), 0})

def Dict.get.j(r: Array<SSlot> & U32) -> Array<SSlot> & PRes:
  (t, +i) = r
  Dict.get.k(Array.get(SSlot, t, i))

def Dict.fin(+fuel: Nat, +mask: U32, +pw: U32, +g: U32, +build: Bool, r: Array<SSlot> & PRes) -> Dict & U32:
  (t, x) = r
  match x:
    case PRes{id, ng}:
      (Dict{fuel, mask, pw, Bool.pick(U32, build, ng, g), t}, id)

# build: the id of s, inserted when new; probe: its id or DEAD
def Dict.op(+build: Bool, d: Dict, +s: String) -> Dict & U32:
  match build d:
    case True{} Dict{+fuel, +mask, +pw, +g, slots}:
      Dict.fin(fuel, mask, pw, g, True{}, Dict.put.j(s, g, Dict.seek(fuel, mask, pw, slots, s)))
    case False{} Dict{+fuel, +mask, +pw, +g, slots}:
      Dict.fin(fuel, mask, pw, g, False{}, Dict.get.j(Dict.seek(fuel, mask, pw, slots, s)))

def Dict.row.k(+i: U32, codes: Array<U32>, r: Dict & U32) -> DC:
  (d, id) = r
  DC{Array.set(U32, codes, i, id), d}

def Dict.row(+build: Bool, +i: U32, s: String, st: DC) -> DC:
  match st:
    case DC{codes, d}:
      Dict.row.k(i, codes, Dict.op(build, d, s))

# codes[i] = id of data[i] for i < n (probing: DEAD on a miss; validity is
# applied afterwards); data comes back
def Dict.go(n: Nat, +i: U32, +build: Bool, st: DC, rs: Array<String> & String) -> SD:
  match n:
    case 0n:
      (data, s) = rs
      SD{data, st}
    case 1n+p:
      (data, s) = rs
      +j = U32.inc(i)
      Dict.go(p, j, build, Dict.row(build, i, s, st), Array.get(String, data, j))

# a fresh copy of a string (no cell shared with the original)
def Str.copy(s: String) -> String:
  match s:
    case SNil{}:
      SNil{}
    case SCon{Chr{c}, t}:
      SCon{Chr{c}, Str.copy(t)}

def Dict.copy.put(+i: U32, out: Array<SSlot>, x: SSlot) -> Array<SSlot>:
  match x:
    case SSlot{k, id}:
      Array.set(SSlot, out, i, SSlot{Str.copy(k), id})

# out[i] = src[i] with the key strings copied, for i < n; src comes back
def Dict.copy.go(n: Nat, +i: U32, out: Array<SSlot>, r: Array<SSlot> & SSlot) -> Array<SSlot> & Array<SSlot>:
  match n:
    case 0n:
      (src, x) = r
      (src, out)
    case 1n+p:
      (src, x) = r
      +j = U32.inc(i)
      Dict.copy.go(p, j, Dict.copy.put(i, out, x), Array.get(SSlot, src, j))

def Dict.clone.k(+fuel: Nat, +mask: U32, +pw: U32, +g: U32, r: Array<SSlot> & Array<SSlot>) -> DD:
  (a, b) = r
  DD{Dict{fuel, mask, pw, g, a}, Dict{fuel, mask, pw, g, b}}

# two tables with no string cell in common: the lanes of a forked probe then
# never touch the same reference counts
def Dict.clone(d: Dict) -> DD:
  match d:
    case Dict{+fuel, +mask, +pw, +g, slots}:
      Dict.clone.k(fuel, mask, pw, g, Dict.copy.go(fuel, 0, Array.new(SSlot, K.Kernel.depth_for(U32.from_nat(fuel)), SSlot{"", 0}), Array.get(SSlot, slots, 0)))

# a stand-in that only remembers the id count (the probe consumed the table)
def Dict.stub(+g: U32) -> Dict:
  Dict{2n, 1, 2147483648, g, Array.new(SSlot, 1n, SSlot{"", 0})}

# ---- forked probe: the string walks are memory-latency bound, so the left
# column is probed in 2^k blocks in parallel, each with its own table copy ----

def Probe.one.k(r: Dict & U32) -> U32:
  (d, id) = r
  id

def Probe.one(d: Dict, s: String) -> U32:
  Probe.one.k(Dict.op(False{}, d, s))

def Probe.flat.k(r: SD) -> Array<String> & Array<U32>:
  match r:
    case SD{data, DC{codes, d}}:
      (data, codes)

# the rows of this block that are below n (the last blocks hold padding)
def Probe.cnt(+n: U32, +off: U32, +blk: U32) -> U32:
  U32.min(blk, Bool.pick(U32, U32.is_lt(off, n), U32.sub(n, off), 0))

def Probe.flat(+c: U32, +bd: Nat, d: Dict, a: Array<String>) -> Array<String> & Array<U32>:
  Probe.flat.k(Dict.go(U32.to_nat(c), 0, False{}, DC{Array.new(U32, bd, 0), d}, Array.get(String, a, 0)))

def Probe.join(l: Array<String> & Array<U32>, r: Array<String> & Array<U32>) -> Array<String> & Array<U32>:
  (a1, c1) = l
  (a2, c2) = r
  (ANode{a1, a2}, ANode{c1, c2})

# k fork levels over a (2^bd slots, the first slot is row `off`), then a flat
# probe per block; answers (a, codes) with codes of the same shape
def Probe.fork(k: Nat, +bd: Nat, +n: U32, +off: U32, dd: DD, a: Array<String>) -> Array<String> & Array<U32>:
  match k dd a:
    case _ DD{d1, d2} ALeaf{+x}:
      (ALeaf{x}, ALeaf{Probe.one(d1, x)})
    case 0n DD{d1, d2} ANode{xs, ys}:
      Probe.flat(Probe.cnt(n, off, U32.shln(1, bd)), bd, d1, ANode{xs, ys})
    case 1n++p DD{d1, d2} ANode{xs, ys}:
      +cd = Nat.sub(bd, 1n)
      +off2 = U32.add(off, U32.shln(1, cd))
      l r = Probe.fork(p, cd, n, off, Dict.clone(d1), xs) Probe.fork(p, cd, n, off2, Dict.clone(d2), ys)
      Probe.join(l, r)

# fork levels: none for small inputs or big tables (every block copies the
# table), else 4 (16 blocks; 2 to 6 measured the same on 12 threads)
def Probe.levels(+n: U32, +depth: Nat, +fuel: Nat) -> Nat:
  Bool.pick(Nat, Bool.and(U32.is_ge(n, 65536), Nat.is_le(fuel, 4096n)), Nat.min(4n, depth), 0n)

# ---- pair table (three flat word arrays: no heap record per slot) ----------------------

def PT.new.k(+b: Nat) -> PT:
  +size = U32.shln(1, b)
  PT{U32.to_nat(size), U32.sub(size, 1), U32.shln(1, Nat.sub(32n, b)), 0, Array.new(U32, b, 0), Array.new(U32, b, 0), Array.new(U32, b, 0)}

def PT.new(+n: U32) -> PT:
  PT.new.k(Join.tbits(n))

# keep probing while the slot is taken by another pair
def PT.look(+a: U32, +b: U32, ra: Array<U32> & U32, rb: Array<U32> & U32, ri: Array<U32> & U32) -> PK:
  (ka, xa) = ra
  (kb, xb) = rb
  (ids, id) = ri
  PK{ka, kb, ids, Bool.and(U32.is_ne(id, 0), Bool.or(U32.is_ne(xa, a), U32.is_ne(xb, b)))}

# the slot holding (a, b), or the empty slot where it would go
def PT.seek.go(n: Nat, pk: PK, +a: U32, +b: U32, +mask: U32, +i: U32) -> PK & U32:
  match n pk:
    case 0n PK{ka, kb, ids, c}:
      (PK{ka, kb, ids, c}, i)
    case _ PK{ka, kb, ids, False{}}:
      (PK{ka, kb, ids, False{}}, i)
    case 1n+p PK{ka, kb, ids, True{}}:
      +j = U32.and(U32.inc(i), mask)
      PT.seek.go(p, PT.look(a, b, Array.get(U32, ka, j), Array.get(U32, kb, j), Array.get(U32, ids, j)), a, b, mask, j)

# build: the slot is (a, b) afterwards (written even when found: same words)
def PT.op.r(+build: Bool, +fuel: Nat, +mask: U32, +pw: U32, +g: U32, +a: U32, +b: U32, +i: U32, ka: Array<U32>, kb: Array<U32>, ri: Array<U32> & U32) -> PT & U32:
  match build:
    case True{}:
      (ids, +id) = ri
      +e = U32.is_eq(id, 0)
      (PT{fuel, mask, pw, U32.add(g, Bool.to_u32(e)), Array.set(U32, ka, i, a), Array.set(U32, kb, i, b), Array.set(U32, ids, i, Bool.pick(U32, e, U32.inc(g), id))}, Bool.pick(U32, e, g, U32.sub(id, 1)))
    case False{}:
      (ids, +id) = ri
      (PT{fuel, mask, pw, g, ka, kb, ids}, Bool.pick(U32, U32.is_eq(id, 0), Join.dead(), U32.sub(id, 1)))

def PT.op.j(+build: Bool, +fuel: Nat, +mask: U32, +pw: U32, +g: U32, +a: U32, +b: U32, +i: U32, pk: PK) -> PT & U32:
  match pk:
    case PK{ka, kb, ids, c}:
      PT.op.r(build, fuel, mask, pw, g, a, b, i, ka, kb, Array.get(U32, ids, i))

def PT.op.k(+build: Bool, +fuel: Nat, +mask: U32, +pw: U32, +g: U32, +a: U32, +b: U32, r: PK & U32) -> PT & U32:
  (pk, +i) = r
  PT.op.j(build, fuel, mask, pw, g, a, b, i, pk)

# build: the dense id of (a, b), a new one when absent; probe: its id or DEAD
def PT.op(+build: Bool, pt: PT, +a: U32, +b: U32) -> PT & U32:
  match pt:
    case PT{+fuel, +mask, +pw, +g, ka, kb, ids}:
      +i = Join.slot(U32.xor(U32.mul(a, 2246822519), b), pw)
      PT.op.k(build, fuel, mask, pw, g, a, b, PT.seek.go(fuel, PT.look(a, b, Array.get(U32, ka, i), Array.get(U32, kb, i), Array.get(U32, ids, i)), a, b, mask, i))

def PT.count(pt: PT) -> U32:
  match pt:
    case PT{fuel, mask, pw, g, ka, kb, ids}:
      g

# ---- densify: (id so far, code) -> one dense id ---------------------------------------------

# dead: an earlier key was dead, this key is null, or (string codes) it missed
def Dense.dead(+a: U32, +c: U32, +l: U32, +dict: Bool) -> Bool:
  Bool.or(Bool.or(U32.is_eq(a, Join.dead()), U32.is_eq(l, 0)), Bool.and(dict, U32.is_eq(c, Join.dead())))

def Dense.row.k(+i: U32, +dead: Bool, out: Array<U32>, r: PT & U32) -> DS:
  (pt, +id) = r
  DS{pt, Array.set(U32, out, i, Bool.pick(U32, dead, Join.dead(), id))}

def Dense.row(+build: Bool, +dict: Bool, +i: U32, +a: U32, +c: U32, +l: U32, st: DS) -> DS:
  match st:
    case DS{pt, out}:
      Dense.row.k(i, Dense.dead(a, c, l, dict), out, PT.op(build, pt, a, c))

def Dense.go(n: Nat, +i: U32, +build: Bool, +dict: Bool, st: DS, ra: Array<U32> & U32, rc: Array<U32> & U32, rl: Array<U32> & U32) -> DS:
  match n:
    case 0n:
      st
    case 1n+p:
      (accs, +a) = ra
      (codes, +c) = rc
      (lives, +l) = rl
      +j = U32.inc(i)
      Dense.go(p, j, build, dict, Dense.row(build, dict, i, a, c, l, st), Array.get(U32, accs, j), Array.get(U32, codes, j), Array.get(U32, lives, j))

def Dense.run(+n: U32, +build: Bool, +dict: Bool, pt: PT, acc: Array<U32>, codes: Array<U32>, live: Array<U32>) -> DS:
  Dense.go(U32.to_nat(n), 0, build, dict, DS{pt, Array.new(U32, K.Kernel.depth_for(n), 0)}, Array.get(U32, acc, 0), Array.get(U32, codes, 0), Array.get(U32, live, 0))

# ---- key encoding of one column --------------------------------------------------------------

# F32 key word: 0.0 and -0.0 are one key, every NaN is one key (Polars)
def Key.fbits(+x: F32) -> U32:
  Bool.pick(U32, F32.is_eq(x, 0.0), 0, Bool.pick(U32, F32.is_eq(x, x), F32.bits(x), 2143289344))

def Key.enc.w(t: D.DType, +len: U32, +depth: Nat, vv: C.Valid & C.Valid, dd: Array<U32> & Array<U32>, d: Dict) -> C.Column & Enc:
  (v1, v2) = vv
  (d1, d2) = dd
  (C.Column.mk_w(t, len, depth, v1, d1), Enc{d2, C.Valid.materialize(v2, depth), d})

def Key.enc.f(+len: U32, +depth: Nat, vv: C.Valid & C.Valid, dd: Array<F32> & Array<F32>, d: Dict) -> C.Column & Enc:
  (v1, v2) = vv
  (d1, d2) = dd
  (C.CF32{len, depth, v1, d1}, Enc{K.Kernel.map(~F32, ~U32, ~(x => Key.fbits(x)), len, depth, d2, 0), C.Valid.materialize(v2, depth), d})

# codes of null rows := DEAD
def Key.nulls(+n: U32, +depth: Nat, codes: Array<U32>, m: Array<U32>) -> Array<U32>:
  K.Kernel.zip(~U32, ~U32, ~U32, ~(c => w => Bool.pick(U32, U32.is_ne(w, 0), c, 4294967295)), n, depth, codes, m, 0)

def Key.enc.s3(+len: U32, +depth: Nat, vv: C.Valid & C.Valid, d: Dict, r: Array<String> & Array<U32>) -> C.Column & Enc:
  (v1, v2) = vv
  (data, codes) = r
  (C.CStr{len, depth, v1, ST.SRaw{data}}, Enc{Key.nulls(len, depth, codes, C.Valid.materialize(v2, depth)), Array.new(U32, depth, 1), d})

def Key.enc.s2(+len: U32, +depth: Nat, vv: C.Valid & C.Valid, r: SD) -> C.Column & Enc:
  match r:
    case SD{data, DC{codes, d}}:
      Key.enc.s3(len, depth, vv, d, (data, codes))

# right side: build the table over every row (a null row's "" is inserted
# too: harmless, its rows are DEAD), then null rows -> DEAD
def Key.enc.sb(+len: U32, +depth: Nat, valid: C.Valid, data: Array<String>) -> C.Column & Enc:
  Key.enc.s2(len, depth, C.Valid.clone(valid), Dict.go(U32.to_nat(len), 0, True{}, DC{Array.new(U32, depth, 0), Dict.new(len)}, Array.get(String, data, 0)))

# left side: probe (forked), misses and null rows -> DEAD
def Key.enc.sp(+len: U32, +depth: Nat, valid: C.Valid, data: Array<String>, d: Dict) -> C.Column & Enc:
  match d:
    case Dict{+fuel, +mask, +pw, +g, slots}:
      Key.enc.s3(len, depth, C.Valid.clone(valid), Dict.stub(g), Probe.fork(Probe.levels(len, depth, fuel), depth, len, 0, Dict.clone(Dict{fuel, mask, pw, g, slots}), data))

def Key.enc.s(+build: Bool, +len: U32, +depth: Nat, valid: C.Valid, data: Array<String>, d: Dict) -> C.Column & Enc:
  match build:
    case True{}:
      Key.enc.sb(len, depth, valid, data)
    case False{}:
      Key.enc.sp(len, depth, valid, data, d)

# ---- a Dictionary key column (M4): the string table is built over the RIGHT dictionary's
# entries (k_r inserts, so an entry's id is its code) and probed with the LEFT dictionary's
# entries (k_l probes); each row's id is then its code's id, one gather. Equal strings with
# different codes on the two sides meet in the table, never by comparing codes.

def Key.ids.row.k(r: Array<U32> & Array<U32>) -> Array<U32>:
  (out, codes) = r
  out

# out[i] = ids[codes[i]]
def Key.ids.row(+n: U32, +d: Nat, ids: Array<U32>, codes: Array<U32>) -> Array<U32>:
  Key.ids.row.k(K.Kernel.gather(~U32, n, d, ids, codes, 0))

def Key.enc.dg(+len: U32, +depth: Nat, vv: C.Valid & C.Valid, dict: ST.Dict, cc: Array<U32> & Array<U32>, r: Array<U32> & Dict) -> C.Column & Enc:
  (v1, v2) = vv
  (c1, c2) = cc
  (ids, t) = r
  (C.CStr{len, depth, v1, ST.SDict{c1, dict}}, Enc{Key.nulls(len, depth, Key.ids.row(len, depth, ids, c2), C.Valid.materialize(v2, depth)), Array.new(U32, depth, 1), t})

# build: ids over the entries in a fresh table; probe: the entries looked up in d
def Key.ids.b(r: SD) -> Array<U32> & Dict:
  match r:
    case SD{strs, DC{ids, t}}:
      (ids, t)

def Key.ids.p(+g: U32, r: Array<String> & Array<U32>) -> Array<U32> & Dict:
  (strs, ids) = r
  (ids, Dict.stub(g))

def Key.ids(+build: Bool, +k: U32, +dd: Nat, strs: Array<String>, d: Dict) -> Array<U32> & Dict:
  match build d:
    case True{} _:
      Key.ids.b(Dict.go(U32.to_nat(k), 0, True{}, DC{Array.new(U32, dd, 0), Dict.new(k)}, Array.get(String, strs, 0)))
    case False{} Dict{+fuel, +mask, +pw, +g, slots}:
      Key.ids.p(g, Probe.fork(Probe.levels(k, dd, fuel), dd, k, 0, Dict.clone(Dict{fuel, mask, pw, g, slots}), strs))

def Key.enc.de(+build: Bool, +len: U32, +depth: Nat, valid: C.Valid, codes: Array<U32>, d: Dict, r: ST.Dict & ST.Ents) -> C.Column & Enc:
  (dict, en) = r
  match en:
    case ST.Ents{+k, +dd, strs}:
      Key.enc.dg(len, depth, C.Valid.clone(valid), dict, Array.clone(U32, codes), Key.ids(build, k, dd, strs, d))

def Key.enc.st(+build: Bool, +len: U32, +depth: Nat, valid: C.Valid, x: ST.Strs, d: Dict) -> C.Column & Enc:
  match x:
    case ST.SRaw{a}:
      Key.enc.s(build, len, depth, valid, a, d)
    case ST.SDict{codes, dict}:
      Key.enc.de(build, len, depth, valid, codes, d, ST.Dict.entries(dict))

# the codes of a key column (build: the right side, makes the string table;
# probe: the left side, uses it); the column comes back untouched
def Key.enc(+build: Bool, c: C.Column, d: Dict) -> C.Column & Enc:
  match c:
    case C.CBool{+len, +depth, valid, data}:
      Key.enc.w(D.TBool{}, len, depth, C.Valid.clone(valid), Array.clone(U32, data), d)
    case C.CU32{+len, +depth, valid, data}:
      Key.enc.w(D.TU32{}, len, depth, C.Valid.clone(valid), Array.clone(U32, data), d)
    case C.CI32{+len, +depth, valid, data}:
      Key.enc.w(D.TI32{}, len, depth, C.Valid.clone(valid), Array.clone(U32, data), d)
    case C.CF32{+len, +depth, valid, data}:
      Key.enc.f(len, depth, C.Valid.clone(valid), Array.clone(F32, data), d)
    case C.CStr{+len, +depth, valid, data}:
      Key.enc.st(build, len, depth, valid, data, d)

# walk the columns; the named one is encoded in place (order kept)
def Cols.enc.put(n: String, rest: List<&1, C.Named>, r: C.Column & Enc) -> List<&1, C.Named> & Slot:
  (c, e) = r
  (C.Named{n, c} <> rest, SOut{e})

def Cols.enc.app(+build: Bool, n: String, c: C.Column, rest: List<&1, C.Named>, s: Slot) -> List<&1, C.Named> & Slot:
  match s:
    case SIn{d}:
      Cols.enc.put(n, rest, Key.enc(build, c, d))
    case SOut{e}:
      (C.Named{n, c} <> rest, SOut{e})

def Cols.enc.k(eq: Bool, +build: Bool, n: String, c: C.Column, r: List<&1, C.Named> & Slot) -> List<&1, C.Named> & Slot:
  match eq:
    case True{}:
      (rest, s) = r
      Cols.enc.app(build, n, c, rest, s)
    case False{}:
      (rest, s) = r
      (C.Named{n, c} <> rest, s)

def Cols.enc(cols: List<&1, C.Named>, +name: String, +build: Bool, s: Slot) -> List<&1, C.Named> & Slot:
  match cols:
    case Nil{}:
      (Nil{}, s)
    case C.Named{+n, c} <> rest:
      Cols.enc.k(String.eq(n, name), build, n, c, Cols.enc(rest, name, build, s))

# ---- one key pair -----------------------------------------------------------------------------

def Join.dense.b(+nl: U32, +nr: U32, lcols: List<&1, C.Named>, rcols: List<&1, C.Named>, outr: Array<U32>, r: DS) -> JS:
  match r:
    case DS{pt, outl}:
      JS{False{}, PT.count(pt), nl, nr, lcols, rcols, outl, outr}

def Join.dense.a(+dict: Bool, +nl: U32, +nr: U32, lcols: List<&1, C.Named>, rcols: List<&1, C.Named>, accl: Array<U32>, cl: Array<U32>, ll: Array<U32>, r: DS) -> JS:
  match r:
    case DS{pt, outr}:
      Join.dense.b(nl, nr, lcols, rcols, outr, Dense.run(nl, False{}, dict, pt, accl, cl, ll))

# combine: a first string key's codes are dense ids already; else densify
def Join.comb(direct: Bool, +dict: Bool, +dg: U32, +nl: U32, +nr: U32, lcols: List<&1, C.Named>, rcols: List<&1, C.Named>, accl: Array<U32>, accr: Array<U32>, cl: Array<U32>, ll: Array<U32>, cr: Array<U32>, lr: Array<U32>) -> JS:
  match direct:
    case True{}:
      JS{False{}, dg, nl, nr, lcols, rcols, cl, cr}
    case False{}:
      Join.dense.a(dict, nl, nr, lcols, rcols, accl, cl, ll, Dense.run(nr, True{}, dict, PT.new(nr), accr, cr, lr))

def Join.key.d(+t: D.DType, first: Bool, +nl: U32, +nr: U32, accl: Array<U32>, accr: Array<U32>, rcols: List<&1, C.Named>, cr: Array<U32>, lr: Array<U32>, lcols: List<&1, C.Named>, s: Slot) -> JS:
  match s:
    case SOut{Enc{cl, ll, d}}:
      +str = D.DType.eq(t, D.TStr{})
      Join.comb(Bool.and(first, str), str, Dict.count(d), nl, nr, lcols, rcols, accl, accr, cl, ll, cr, lr)
    case SIn{d}:
      JS{first, 0, nl, nr, lcols, rcols, accl, accr}

def Join.key.c(+t: D.DType, first: Bool, +nl: U32, +nr: U32, accl: Array<U32>, accr: Array<U32>, rcols: List<&1, C.Named>, cr: Array<U32>, lr: Array<U32>, r: List<&1, C.Named> & Slot) -> JS:
  (lcols, s) = r
  Join.key.d(t, first, nl, nr, accl, accr, rcols, cr, lr, lcols, s)

def Join.key.b(+t: D.DType, +ln: String, first: Bool, +nl: U32, +nr: U32, lcols: List<&1, C.Named>, accl: Array<U32>, accr: Array<U32>, rcols: List<&1, C.Named>, s: Slot) -> JS:
  match s:
    case SOut{Enc{cr, lr, d}}:
      Join.key.c(t, first, nl, nr, accl, accr, rcols, cr, lr, Cols.enc(lcols, ln, False{}, SIn{d}))
    case SIn{d}:
      JS{first, 0, nl, nr, lcols, rcols, accl, accr}

def Join.key.a(+t: D.DType, +ln: String, first: Bool, +nl: U32, +nr: U32, lcols: List<&1, C.Named>, accl: Array<U32>, accr: Array<U32>, r: List<&1, C.Named> & Slot) -> JS:
  (rcols, s) = r
  Join.key.b(t, ln, first, nl, nr, lcols, accl, accr, rcols, s)

def Join.key(k: KeySpec, st: JS) -> JS:
  match k:
    case KeySpec{+ln, +rn, +t}:
      match st:
        case JS{first, g, +nl, +nr, lcols, rcols, accl, accr}:
          Join.key.a(t, ln, first, nl, nr, lcols, accl, accr, Cols.enc(rcols, rn, True{}, SIn{Dict.empty()}))

def Join.keys.loop(ks: List<&2, KeySpec>, st: JS) -> JS:
  match ks:
    case Nil{}:
      st
    case k <> rest:
      Join.keys.loop(rest, Join.key(k, st))

# ---- right side: group rows by id (CSR) ---------------------------------------------------------

# out[i] = sum of c[0..i) for i < n; c comes back
def Scan.go(n: Nat, +i: U32, +sum: U32, out: Array<U32>, r: Array<U32> & U32) -> Array<U32> & Array<U32>:
  match n:
    case 0n:
      (c, x) = r
      (c, out)
    case 1n+p:
      (c, x) = r
      +j = U32.inc(i)
      Scan.go(p, j, U32.add(sum, x), Array.set(U32, out, i, sum), Array.get(U32, c, j))

def Csr.fill.row.k(+j: U32, +g: U32, rows: Array<U32>, r: Array<U32> & U32) -> CF:
  (cur, +pos) = r
  CF{Array.set(U32, cur, g, U32.inc(pos)), Array.set(U32, rows, pos, j)}

def Csr.fill.row(+j: U32, +g: U32, st: CF) -> CF:
  match st:
    case CF{cur, rows}:
      Csr.fill.row.k(j, g, rows, Array.get(U32, cur, g))

# rows[cur[g]++] = j over the right rows (dead rows land past the live ones)
def Csr.fill.go(n: Nat, +j: U32, st: CF, rg: Array<U32> & U32) -> CF:
  match n:
    case 0n:
      st
    case 1n+p:
      (gs, +g) = rg
      +j2 = U32.inc(j)
      Csr.fill.go(p, j2, Csr.fill.row(j, g, st), Array.get(U32, gs, j2))

def Join.csr.e(counts: Array<U32>, starts: Array<U32>, cf: CF) -> CSR:
  match cf:
    case CF{cur, rows}:
      CSR{counts, starts, rows}

def Join.csr.d(+nr: U32, +dr: Nat, gids: Array<U32>, counts: Array<U32>, r: Array<U32> & Array<U32>) -> CSR:
  (starts, cur) = r
  Join.csr.e(counts, starts, Csr.fill.go(U32.to_nat(nr), 0, CF{cur, Array.new(U32, dr, 0)}, Array.get(U32, gids, 0)))

def Join.csr.c(+nr: U32, +dr: Nat, gids: Array<U32>, r: Array<U32> & Array<U32>) -> CSR:
  (counts, starts) = r
  Join.csr.d(nr, dr, gids, counts, Array.clone(U32, starts))

def Join.csr.b(+nr: U32, +dc: Nat, +dr: Nat, gids: Array<U32>, counts: Array<U32>) -> CSR:
  Join.csr.c(nr, dr, gids, Scan.go(U32.to_nat(U32.shln(1, dc)), 0, 0, Array.new(U32, dc, 0), Array.get(U32, counts, 0)))

def Join.csr.a(+nr: U32, +dc: Nat, +dr: Nat, r: Array<U32> & Array<U32>) -> CSR:
  (g1, g2) = r
  Join.csr.b(nr, dc, dr, g1, Array.set(U32, K.Kernel.scatter(~U32, ~U32, ~(x => y => U32.add(x, y)), nr, g2, Array.new(U32, dr, 1), Array.new(U32, dc, 0)), Join.dead(), 0))

# counts/starts have 2^dc > g slots: DEAD (wrapping to the last slot) is never
# a group, and its count is reset to 0 so a dead left row finds no match
def Join.csr(+g: U32, +nr: U32, accr: Array<U32>) -> CSR:
  Join.csr.a(nr, K.Kernel.depth_for(U32.inc(g)), K.Kernel.depth_for(nr), Array.clone(U32, accr))

# ---- left side: size, then fill perm_l / perm_r / valid_r ------------------------------------

# the output row count saturates at 2^32 - 1 instead of wrapping: a many-to-many join of
# 65536 x 65536 equal keys has 2^32 output rows, which a wrapped sum would read as 0 and pass
# the row cap (DESIGN.md 15.8). Once saturated, the sum stays saturated (the wrap of
# MAX + m is m - 1 < MAX).
def Tot.sat(+t: U32, +m: U32) -> U32:
  +s = U32.add(t, m)
  Bool.pick(U32, U32.is_lt(s, t), 4294967295, s)

def Tot.inner(acc: TA, +m: U32) -> TA:
  match acc:
    case TA{t, ones, miss}:
      TA{Tot.sat(t, m), U32.add(ones, Bool.to_u32(U32.is_eq(m, 1))), miss}

def Tot.left(acc: TA, +m: U32) -> TA:
  match acc:
    case TA{t, ones, miss}:
      TA{Tot.sat(t, U32.max(m, 1)), U32.add(ones, Bool.to_u32(U32.is_le(m, 1))), U32.add(miss, Bool.to_u32(U32.is_eq(m, 0)))}

def Tot.run(+how: JoinHow, +n: U32, ms: Array<U32>) -> Array<U32> & TA:
  match how:
    case Inner{}:
      K.Kernel.fold(~U32, ~TA, ~(acc => m => Tot.inner(acc, m)), n, ms, TA{0, 0, 0})
    case Left{}:
      K.Kernel.fold(~U32, ~TA, ~(acc => m => Tot.left(acc, m)), n, ms, TA{0, 0, 0})

def Emit.one.k(+i: U32, +k: U32, pl: Array<U32>, pr: Array<U32>, vr: Array<U32>, r: Array<U32> & U32) -> FS:
  (rows, x) = r
  FS{U32.inc(k), rows, Array.set(U32, pl, k, i), Array.set(U32, pr, k, x), vr}

def Emit.one(+i: U32, +s: U32, st: FS) -> FS:
  match st:
    case FS{+k, rows, pl, pr, vr}:
      Emit.one.k(i, k, pl, pr, vr, Array.get(U32, rows, s))

def Emit.go(m: Nat, +i: U32, +s: U32, st: FS) -> FS:
  match m:
    case 0n:
      st
    case 1n+p:
      Emit.go(p, i, U32.inc(s), Emit.one(i, s, st))

# a left-join miss: one row with a null right side
def Emit.miss(+i: U32, st: FS) -> FS:
  match st:
    case FS{+k, rows, pl, pr, vr}:
      FS{U32.inc(k), rows, Array.set(U32, pl, k, i), Array.set(U32, pr, k, 0), Array.set(U32, vr, k, 0)}

def Fill.row(miss: Bool, +i: U32, +m: U32, +s: U32, st: FS) -> FS:
  match miss:
    case True{}:
      Emit.miss(i, st)
    case False{}:
      Emit.go(U32.to_nat(m), i, s, st)

def Fill.go(n: Nat, +i: U32, +left: Bool, st: FS, rm: Array<U32> & U32, rs: Array<U32> & U32) -> FS:
  match n:
    case 0n:
      st
    case 1n+p:
      (ms, +m) = rm
      (ss, +s) = rs
      +j = U32.inc(i)
      Fill.go(p, j, left, Fill.row(Bool.and(left, U32.is_eq(m, 0)), i, m, s, st), Array.get(U32, ms, j), Array.get(U32, ss, j))

# ---- output columns ------------------------------------------------------------------------------

def Join.fix.w2(t: D.DType, +n: U32, +d: Nat, r: Array<U32> & Array<U32>) -> C.Column:
  (x, m) = r
  C.Column.mk_w(t, n, d, C.Mask{m}, x)

def Join.fix.f2(+n: U32, +d: Nat, r: Array<F32> & Array<U32>) -> C.Column:
  (x, m) = r
  C.CF32{n, d, C.Mask{m}, x}

def Join.fix.s2(+n: U32, +d: Nat, r: ST.Strs & Array<U32>) -> C.Column:
  (x, m) = r
  C.CStr{n, d, C.Mask{m}, x}

# validity := validity AND m, and the slots of null rows reset to the default
def Join.fix.v(+n: U32, +d: Nat, v: C.Valid, m: Array<U32>) -> Array<U32>:
  match v:
    case C.AllValid{}:
      m
    case C.Mask{x}:
      K.Kernel.mask_and(n, d, x, m)

def Join.fix(c: C.Column, m: Array<U32>) -> C.Column:
  match c:
    case C.CBool{+n, +d, v, x}:
      Join.fix.w2(D.TBool{}, n, d, K.Kernel.mask_data(~U32, n, x, Join.fix.v(n, d, v, m), 0))
    case C.CU32{+n, +d, v, x}:
      Join.fix.w2(D.TU32{}, n, d, K.Kernel.mask_data(~U32, n, x, Join.fix.v(n, d, v, m), 0))
    case C.CI32{+n, +d, v, x}:
      Join.fix.w2(D.TI32{}, n, d, K.Kernel.mask_data(~U32, n, x, Join.fix.v(n, d, v, m), 0))
    case C.CF32{+n, +d, v, x}:
      Join.fix.f2(n, d, K.Kernel.mask_data(~F32, n, x, Join.fix.v(n, d, v, m), 0.0))
    case C.CStr{+n, +d, v, x}:
      Join.fix.s2(n, d, ST.Strs.fix(n, x, Join.fix.v(n, d, v, m)))

def Gat.nul.k(n: String, acc: List<&1, C.Named>, perm: Array<U32>, c: C.Column, r: Array<U32> & Array<U32>) -> GS:
  (vr, m) = r
  GS{perm, vr, C.Named{n, Join.fix(c, m)} <> acc}

def Gat.add(nul: Bool, n: String, acc: List<&1, C.Named>, vr: Array<U32>, r: C.Column & Array<U32>) -> GS:
  match nul:
    case True{}:
      (c, perm) = r
      Gat.nul.k(n, acc, perm, c, Array.clone(U32, vr))
    case False{}:
      (c, perm) = r
      GS{perm, vr, C.Named{n, c} <> acc}

def Gat.step(drop: Bool, +nul: Bool, n: String, c: C.Column, +t: U32, st: GS) -> GS:
  match drop st:
    case True{} _:
      st
    case False{} GS{perm, vr, acc}:
      Gat.add(nul, n, acc, vr, C.Column.gather(c, perm, t))

# gather every column by perm (t rows) into acc (newest first); `drop` names
# are skipped, `ren` names get `_right`, `nul` ANDs the validity with vr
def Gat.go(cols: List<&1, C.Named>, +drop: List<&2, String>, +ren: List<&2, String>, +nul: Bool, +t: U32, st: GS) -> GS:
  match cols:
    case Nil{}:
      st
    case C.Named{+n, c} <> rest:
      Gat.go(rest, drop, ren, nul, t, Gat.step(C.Names.has(drop, n), nul, Join.rname(ren, n), c, t, st))

def Cols.revonto(xs: List<&1, C.Named>, acc: List<&1, C.Named>) -> List<&1, C.Named>:
  match xs:
    case Nil{}:
      acc
    case h <> t:
      Cols.revonto(t, h <> acc)

def Join.out.b(rcols: List<&1, C.Named>, gl: GS) -> E.ResT(C.Frame):
  match gl:
    case GS{perm, vr, lacc}:
      C.Frame.from_columns(Cols.revonto(lacc, rcols))

def Join.out.a(ident: Bool, +t: U32, lcols: List<&1, C.Named>, pl: Array<U32>, gr: GS) -> E.ResT(C.Frame):
  match ident gr:
    case True{} GS{perm, vr, racc}:
      C.Frame.from_columns(Cols.revonto(List.reverse(&1, C.Named, lcols), List.reverse(&1, C.Named, racc)))
    case False{} GS{perm, vr, racc}:
      Join.out.b(List.reverse(&1, C.Named, racc), Gat.go(lcols, Nil{}, Nil{}, False{}, t, GS{pl, Array.new(U32, 0n, 1), Nil{}}))

def Join.out(+how: JoinHow, +lnames: List<&2, String>, +right_on: List<&2, String>, +nl: U32, lcols: List<&1, C.Named>, rcols: List<&1, C.Named>, ta: TA, fs: FS) -> E.ResT(C.Frame):
  match ta fs:
    case TA{+t, ones, miss} FS{k, rows, pl, pr, vr}:
      Join.out.a(U32.is_eq(ones, nl), t, lcols, pl, Gat.go(rcols, right_on, lnames, U32.is_ne(miss, 0), t, GS{pr, vr, Nil{}}))

# every left row has exactly one output row (at most one match; a left
# join's misses included): perm_l is the identity, perm_r[i] = rows[s[i]]
# and valid_r[i] = (m[i] != 0), so two flat kernels replace the fill loop
def Join.ident.k(+left: Bool, +nl: U32, +dl: Nat, ms: Array<U32>, r: Array<U32> & Array<U32>) -> FS:
  match left:
    case True{}:
      (pr, ss) = r
      FS{nl, Array.new(U32, 0n, 0), Array.new(U32, 0n, 0), pr, K.Kernel.map(~U32, ~U32, ~(m => Bool.to_u32(U32.is_ne(m, 0))), nl, dl, ms, 0)}
    case False{}:
      (pr, ss) = r
      FS{nl, Array.new(U32, 0n, 0), Array.new(U32, 0n, 0), pr, Array.new(U32, 0n, 1)}

def Join.ident(+left: Bool, +nl: U32, rows: Array<U32>, ss: Array<U32>, ms: Array<U32>) -> FS:
  +dl = K.Kernel.depth_for(nl)
  Join.ident.k(left, nl, dl, ms, K.Kernel.gather(~U32, nl, dl, rows, ss, 0))

def Join.fill.b(ident: Bool, +left: Bool, +nl: U32, +dt: Nat, rows: Array<U32>, ss: Array<U32>, ms: Array<U32>) -> FS:
  match ident:
    case True{}:
      Join.ident(left, nl, rows, ss, ms)
    case False{}:
      Fill.go(U32.to_nat(nl), 0, left, FS{0, rows, Array.new(U32, dt, 0), Array.new(U32, dt, 0), Array.new(U32, Bool.pick(Nat, left, dt, 0n), 1)}, Array.get(U32, ms, 0), Array.get(U32, ss, 0))

# the row cap (DESIGN.md 15.8): the output row count t comes from the CSR match counts, so a
# join past the cap is refused here, before perm_l / perm_r / valid_r are allocated
def Join.fill.c(over: Maybe<&2, E.Err>, +how: JoinHow, +lnames: List<&2, String>, +right_on: List<&2, String>, +nl: U32, lcols: List<&1, C.Named>, rcols: List<&1, C.Named>, rows: Array<U32>, ss: Array<U32>, ms: Array<U32>, ta: TA) -> E.ResT(C.Frame):
  match over:
    case Some{e}:
      Fail{e}
    case None{}:
      match ta:
        case TA{+t, +ones, +miss}:
          Join.out(how, lnames, right_on, nl, lcols, rcols, TA{t, ones, miss}, Join.fill.b(U32.is_eq(ones, nl), JoinHow.is_left(how), nl, K.Kernel.depth_for(t), rows, ss, ms))

def Join.fill.a(+how: JoinHow, +lnames: List<&2, String>, +right_on: List<&2, String>, +nl: U32, lcols: List<&1, C.Named>, rcols: List<&1, C.Named>, rows: Array<U32>, ss: Array<U32>, ms: Array<U32>, ta: TA) -> E.ResT(C.Frame):
  match ta:
    case TA{+t, +ones, +miss}:
      Join.fill.c(K.Kernel.check_rows(t), how, lnames, right_on, nl, lcols, rcols, rows, ss, ms, TA{t, ones, miss})

def Join.fill(+how: JoinHow, +lnames: List<&2, String>, +right_on: List<&2, String>, +nl: U32, lcols: List<&1, C.Named>, rcols: List<&1, C.Named>, rows: Array<U32>, ss: Array<U32>, r: Array<U32> & TA) -> E.ResT(C.Frame):
  (ms, ta) = r
  Join.fill.a(how, lnames, right_on, nl, lcols, rcols, rows, ss, ms, ta)

# m[i] = counts[g], s[i] = starts[g] for every left row's id g
def Join.probe.b(+how: JoinHow, +lnames: List<&2, String>, +right_on: List<&2, String>, +nl: U32, lcols: List<&1, C.Named>, rcols: List<&1, C.Named>, rows: Array<U32>, ms: Array<U32>, r: Array<U32> & Array<U32>) -> E.ResT(C.Frame):
  (ss, accl) = r
  Join.fill(how, lnames, right_on, nl, lcols, rcols, rows, ss, Tot.run(how, nl, ms))

def Join.probe.a(+how: JoinHow, +lnames: List<&2, String>, +right_on: List<&2, String>, +nl: U32, lcols: List<&1, C.Named>, rcols: List<&1, C.Named>, starts: Array<U32>, rows: Array<U32>, r: Array<U32> & Array<U32>) -> E.ResT(C.Frame):
  (ms, accl) = r
  Join.probe.b(how, lnames, right_on, nl, lcols, rcols, rows, ms, K.Kernel.gather(~U32, nl, K.Kernel.depth_for(nl), starts, accl, 0))

def Join.probe(+how: JoinHow, +lnames: List<&2, String>, +right_on: List<&2, String>, +nl: U32, lcols: List<&1, C.Named>, rcols: List<&1, C.Named>, accl: Array<U32>, csr: CSR) -> E.ResT(C.Frame):
  match csr:
    case CSR{counts, starts, rows}:
      Join.probe.a(how, lnames, right_on, nl, lcols, rcols, starts, rows, K.Kernel.gather(~U32, nl, K.Kernel.depth_for(nl), counts, accl, 0))

def Join.go(+how: JoinHow, +lnames: List<&2, String>, +right_on: List<&2, String>, st: JS) -> E.ResT(C.Frame):
  match st:
    case JS{first, +g, +nl, +nr, lcols, rcols, accl, accr}:
      Join.probe(how, lnames, right_on, nl, lcols, rcols, accl, Join.csr(g, nr, accr))

# ---- entry ------------------------------------------------------------------------------------------

def Join.exec(+how: JoinHow, keys: List<&2, KeySpec>, +lnames: List<&2, String>, +right_on: List<&2, String>, left: C.Frame, right: C.Frame) -> E.ResT(C.Frame):
  match left:
    case C.Frame{+nl, lcols}:
      match right:
        case C.Frame{+nr, rcols}:
          Join.go(how, lnames, right_on, Join.keys.loop(keys, JS{True{}, 0, nl, nr, lcols, rcols, Array.new(U32, K.Kernel.depth_for(nl), 0), Array.new(U32, K.Kernel.depth_for(nr), 0)}))

def Join.run.c(+how: JoinHow, ks: E.Res(List<&2, KeySpec>), +lnames: List<&2, String>, +right_on: List<&2, String>, left: C.Frame, right: C.Frame) -> E.ResT(C.Frame):
  match ks:
    case Fail{e}:
      Fail{e}
    case Done{keys}:
      Join.exec(how, keys, lnames, right_on, left, right)

def Join.run.b(+how: JoinHow, chk: E.Res(List<&2, S.Field>), +left_on: List<&2, String>, +right_on: List<&2, String>, +ls: List<&2, S.Field>, +rs: List<&2, S.Field>, left: C.Frame, right: C.Frame) -> E.ResT(C.Frame):
  match chk:
    case Fail{e}:
      Fail{e}
    case Done{fs}:
      Join.run.c(how, Join.keys(left_on, right_on, ls, rs), S.Schema.names(ls), right_on, left, right)

def Join.run.a(+how: JoinHow, +left_on: List<&2, String>, +right_on: List<&2, String>, rl: C.Frame & List<&2, S.Field>, rr: C.Frame & List<&2, S.Field>) -> E.ResT(C.Frame):
  (left, +ls) = rl
  (right, +rs) = rr
  Join.run.b(how, Join.schema(ls, rs, left_on, right_on), left_on, right_on, ls, rs, left, right)

# join two frames on left_on[i] == right_on[i] (equal dtypes, nulls never
# match). Output: every left column, then the right columns minus right_on
# (a name clashing with a left column gets `_right`); rows in left order, the
# matches of a left row in right order; a left join keeps unmatched left rows
# with null right columns. Errors (before any work): see Join.schema.
def Join.run(+how: JoinHow, left: C.Frame, right: C.Frame, +left_on: List<&2, String>, +right_on: List<&2, String>) -> E.ResT(C.Frame):
  Join.run.a(how, left_on, right_on, S.Frame.schema(left), S.Frame.schema(right))
