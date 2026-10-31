# src/join.bend -- Join.run: inner and left equi-joins on one or more keys. DESIGN.md 4.10.
#
# Algorithm (no per-row Map lookups, no per-row key strings):
#  1. Check the keys against both schemas (Join.schema, pure Data: the same
#     function Plan.schema can use): ColumnNotFound, TypeMismatch{"join", ..},
#     DuplicateColumn after suffixing, unequal/empty key lists.
#  2. Encode each key pair into U32 codes. Bool/U32/I32: the data word; F32:
#     the bits (0.0 == -0.0, every NaN equal, as Polars); Str: a dense id from
#     the packed coder's flat table (src/hcode.bend Hc.code.pk, W2.4) built
#     sequentially over the RIGHT key (ids = first appearance; per dictionary
#     entry for a Dictionary key; the distinct keys' code points packed flat),
#     the left key looked up in it sequentially (Hc.find.pk; a miss can never
#     match: DEAD). Several keys are combined into one
#     dense id per row with a pair table ((id so far, code) -> dense id),
#     built on the SMALLER side and probed by the other (ids are only labels:
#     the side changes no match); a first word key whose codes span a narrow
#     range takes direct-address ids instead (Join.word). Null keys never
#     match: their rows get DEAD.
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
import ./hcode.bend as H
import ./schema.bend as S

# Semi / Anti (M3, DESIGN.md 15.2.4): the left rows with / without a match, left
# columns only, each left row at most once, in left order (a null key never matches,
# so anti keeps it)
type JoinHow is Data:
  Inner{}
  Left{}
  Semi{}
  Anti{}

# one checked key pair
type KeySpec is Data:
  KeySpec{l: String, r: String, t: D.DType}

# the pair table: open addressing over 2^b slots (load <= 1/2): fuel = 2^b, mask = 2^b - 1,
# pw = 2^(32 - b) (slot = (h * golden) / pw: the top b bits), g = ids handed out
type PT is Type:
  PT{fuel: Nat, mask: U32, pw: U32, g: U32, ka: Array<U32>, kb: Array<U32>, ids: Array<U32>}

# a probe cursor over the pair table's arrays: keep probing?
type PK is Type:
  PK{ka: Array<U32>, kb: Array<U32>, ids: Array<U32>, more: Bool}

# a key column's codes: code per row, its 0/1 validity, and (string keys) the number of
# distinct build-side ids g (0 for the other dtypes)
type Enc is Type:
  Enc{codes: Array<U32>, live: Array<U32>, g: U32}

# the build side's string table (W2.4, DESIGN 17.3.3), handed to the probe side: H.Hc.code.pk's
# table over the right key's n strings (the rows of a Raw column or the entries of a Dictionary;
# g distinct, ids = first appearance from 0) with the distinct keys' code points packed flat. The
# right strings themselves are not held (they went back to the right column after the build).
# Word keys carry an empty one.
type BT is Type:
  BT{n: U32, g: U32, hs: Array<U32>, ix: Array<U32>, po: Array<U32>, pl: Array<U32>, pk: Array<U32>}

# the column walker's slot: the table before the named column is met; its codes and the table
# after (the build side puts its new table there, the probe side hands it back)
type Slot is Type:
  SIn{t: BT}
  SOut{e: Enc, t: BT}

type DS is Type:
  DS{pt: PT, out: Array<U32>}

# direct-address ids of a first word key (Dd.*): ids handed out so far, slot -> id + 1, row -> id
type DD is Type:
  DD{g: U32, table: Array<U32>, out: Array<U32>}

# a key's codes and validity handed back with the live codes' min and max
type DM is Type:
  DM{codes: Array<U32>, live: Array<U32>, mn: U32, mx: U32}

# the build side's ids, the probe side's ids, and the id count
type DR is Type:
  DR{g: U32, ob: Array<U32>, op: Array<U32>}

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
    case Semi{}:
      "semi"
    case Anti{}:
      "anti"

def JoinHow.is_left(h: JoinHow) -> Bool:
  match h:
    case Left{}:
      True{}
    case _:
      False{}

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

def Join.schema.semi.k(ks: E.Res(List<&2, KeySpec>), ls: List<&2, S.Field>) -> E.Res(List<&2, S.Field>):
  match ks:
    case Fail{e}:
      Fail{e}
    case Done{k}:
      Done{ls}

# the output schema of a semi / anti join: the key checks of Join.schema (same order, same
# texts), then the left fields alone (no right column, so no `_right` and no DuplicateColumn)
def Join.schema.semi(+ls: List<&2, S.Field>, +rs: List<&2, S.Field>, left_on: List<&2, String>, right_on: List<&2, String>) -> E.Res(List<&2, S.Field>):
  Join.schema.semi.k(Join.keys(left_on, right_on, ls, rs), ls)

# the output schema of a join of any kind (Plan.schema and Join.run both use it)
def Join.schema.how(how: JoinHow, +ls: List<&2, S.Field>, +rs: List<&2, S.Field>, left_on: List<&2, String>, +right_on: List<&2, String>) -> E.Res(List<&2, S.Field>):
  match how:
    case Semi{}:
      Join.schema.semi(ls, rs, left_on, right_on)
    case Anti{}:
      Join.schema.semi(ls, rs, left_on, right_on)
    case _:
      Join.schema(ls, rs, left_on, right_on)

# ---- strings: hash (kept for callers: tests hash dumps with it; the join's own table hashes in
# H.Hc.code.pk / H.Hc.find.pk's walks, the same FNV-1a over the code points) -------------------

# FNV-1a over the code points (tail loop)
def Str.fnv(s: String, +h: U32) -> U32:
  match s:
    case SNil{}:
      h
    case SCon{Chr{+c}, t}:
      Str.fnv(t, U32.mul(U32.xor(h, c), 16777619))

def Str.hash.z(+h: U32, s: String) -> U32:
  h

# FNV-1a over the code points. s is used after the walk, so the walk borrows it (its cells are
# read, never taken: one drop of s at the end instead of a take per cell; until W2.4 the join's
# own borrowing call made this walk a borrow, the driver's walk of bench/m2 relies on it)
def Str.hash(+s: String, +h: U32) -> U32:
  Str.hash.z(Str.fnv(s, h), s)

# the top bits of h * golden ratio: a slot of a 2^b table (pw = 2^(32-b))
def Join.slot(h: U32, pw: U32) -> U32:
  U32.div(U32.mul(h, 2654435769), pw)

# 2^b slots for n keys at load <= 1/2: (b, 2^b, 2^(32-b))
def Join.tbits(+n: U32) -> Nat:
  K.Kernel.depth_for(U32.max(U32.add(n, n), 2))

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

# (the data and validity of a word key are copied once: the column goes back into its frame
# while the codes and the 0/1 validity travel on to the densify / CSR passes)
def Key.enc.w(t: D.DType, +len: U32, +depth: Nat, vv: C.Valid & C.Valid, dd: Array<U32> & Array<U32>) -> C.Column & Enc:
  (v1, v2) = vv
  (d1, d2) = dd
  (C.Column.mk_w(t, len, depth, v1, d1), Enc{d2, C.Valid.materialize(v2, depth), 0})

def Key.enc.f(+len: U32, +depth: Nat, vv: C.Valid & C.Valid, dd: Array<F32> & Array<F32>) -> C.Column & Enc:
  (v1, v2) = vv
  (d1, d2) = dd
  (C.CF32{len, depth, v1, d1}, Enc{K.Kernel.map(~F32, ~U32, ~(x => Key.fbits(x)), len, depth, d2, 0), C.Valid.materialize(v2, depth), 0})

# the codes of a word key column (Bool / U32 / I32: the data word; F32: Key.fbits); the column
# comes back untouched. A string column is coded by Key.build / Key.probe, never here (the key dtypes are
# checked equal; an unreachable string column gets DEAD codes, no live row).
def Key.enc.word(c: C.Column) -> C.Column & Enc:
  match c:
    case C.CBool{+len, +depth, valid, data}:
      Key.enc.w(D.TBool{}, len, depth, C.Valid.clone(valid), Array.clone(U32, data))
    case C.CU32{+len, +depth, valid, data}:
      Key.enc.w(D.TU32{}, len, depth, C.Valid.clone(valid), Array.clone(U32, data))
    case C.CI32{+len, +depth, valid, data}:
      Key.enc.w(D.TI32{}, len, depth, C.Valid.clone(valid), Array.clone(U32, data))
    case C.CF32{+len, +depth, valid, data}:
      Key.enc.f(len, depth, C.Valid.clone(valid), Array.clone(F32, data))
    case C.CStr{+len, +depth, valid, data}:
      (C.CStr{len, depth, valid, data}, Enc{Array.new(U32, depth, 4294967295), Array.new(U32, depth, 0), 0})

# codes[i] := DEAD where row i is null, in place (the mask is borrowed and handed back)
def Nul.go(n: Nat, +i: U32, rc: Array<U32> & U32, rm: Array<U32> & U32) -> Array<U32> & Array<U32>:
  match n:
    case 0n:
      (codes, c) = rc
      (m, w) = rm
      (m, codes)
    case 1n+p:
      (codes, +c) = rc
      (m, +w) = rm
      +j = U32.inc(i)
      Nul.go(p, j, Array.get(U32, Array.set(U32, codes, i, Bool.pick(U32, U32.is_ne(w, 0), c, 4294967295)), j), Array.get(U32, m, j))

def Key.nulls.m(r: Array<U32> & Array<U32>) -> C.Valid & Array<U32>:
  (m, codes) = r
  (C.Mask{m}, codes)

# a string key's codes with the null rows DEAD (a null key never matches); the validity comes back
# (AllValid: nothing to do, no pass)
def Key.nulls(+n: U32, codes: Array<U32>, v: C.Valid) -> C.Valid & Array<U32>:
  match v:
    case C.AllValid{}:
      (C.AllValid{}, codes)
    case C.Mask{m}:
      Key.nulls.m(Nul.go(U32.to_nat(n), 0, Array.get(U32, codes, 0), Array.get(U32, m, 0)))

# ---- string keys (W2.4, DESIGN 17.3.3 and 14): ONE flat table, built sequentially over the
# RIGHT key's strings by the packed coder (H.Hc.code.pk: ids = first appearance on the right from
# 0, exactly Hc.code's; a null row's "" is coded too, harmless: its rows are made DEAD; each
# distinct key's code points packed flat by the same single walk) and probed sequentially by the
# LEFT key's strings (H.Hc.find.pk: a miss is DEAD; a hash hit compares the left string with the
# packed key, never with a right cons string). The right strings are borrowed by the build walk
# and handed straight back to the right column; nothing per lane, nothing per row allocated. A
# Dictionary key is coded per dictionary ENTRY on both sides (the right entries build the table,
# the left entries probe it), then each row's id is its code's id (one gather): equal strings with
# different codes on the two sides meet in the table, never by comparing codes. ~mix is the
# table's hash template (Join.run: the identity on FNV-1a; a test: a constant, so every probe
# collides and every hit is decided by the compare).

# the table of a word key pair (nothing to probe)
def BT.none() -> BT:
  BT{0, 0, Array.new(U32, 1n, 0), Array.new(U32, 1n, 0), Array.new(U32, 1n, 0), Array.new(U32, 1n, 0), Array.new(U32, 1n, 0)}

# -- build side (right)

def Key.build.rk(+len: U32, +depth: Nat, +g: U32, a: Array<String>, t: BT, r: C.Valid & Array<U32>) -> C.Column & Slot:
  (v, codes) = r
  (C.CStr{len, depth, v, ST.SRaw{a}}, SOut{Enc{codes, Array.new(U32, depth, 1), g}, t})

def Key.build.r(+len: U32, +depth: Nat, valid: C.Valid, hj: H.HJ) -> C.Column & Slot:
  match hj:
    case H.HJ{+next, a, hs, ix, codes, po, pl, pk, cur, pd}:
      Key.build.rk(len, depth, next, a, BT{len, next, hs, ix, po, pl, pk}, Key.nulls(len, codes, valid))

def Key.build.dv(+len: U32, +depth: Nat, +g: U32, codes: Array<U32>, dict: ST.Dict, t: BT, r: C.Valid & Array<U32>) -> C.Column & Slot:
  (v, rids) = r
  (C.CStr{len, depth, v, ST.SDict{codes, dict}}, SOut{Enc{rids, Array.new(U32, depth, 1), g}, t})

def Key.build.dg(+len: U32, +depth: Nat, +g: U32, dict: ST.Dict, t: BT, valid: C.Valid, r: Array<U32> & Array<U32>) -> C.Column & Slot:
  (rids, codes) = r
  Key.build.dv(len, depth, g, codes, dict, t, Key.nulls(len, rids, valid))

def Key.build.de(+len: U32, +depth: Nat, valid: C.Valid, codes: Array<U32>, +k: U32, +dd: Nat, +bb: Nat, slots: Array<ST.SSlot>, +tag: U32, hj: H.HJ) -> C.Column & Slot:
  match hj:
    case H.HJ{+next, strs, hs, ix, ec, po, pl, pk, cur, pd}:
      Key.build.dg(len, depth, next, ST.Dict{k, dd, strs, bb, slots, tag}, BT{k, next, hs, ix, po, pl, pk}, valid, K.Kernel.gather(~U32, len, depth, ec, codes, 0))

# a Dictionary right key: its k entries coded (ids = entry order when the entries are distinct),
# each row's id = its code's id (one gather)
def Key.build.d(~mix: U32 -> U32, +len: U32, +depth: Nat, valid: C.Valid, codes: Array<U32>, dict: ST.Dict) -> C.Column & Slot:
  match dict:
    case ST.Dict{+k, +dd, strs, +bb, slots, +tag}:
      Key.build.de(len, depth, valid, codes, k, dd, bb, slots, tag, H.Hc.code.pk(~mix, k, dd, strs))

# the right key's codes and the table over its strings
def Key.build(~mix: U32 -> U32, +len: U32, +depth: Nat, valid: C.Valid, x: ST.Strs) -> C.Column & Slot:
  match x:
    case ST.SRaw{a}:
      Key.build.r(len, depth, valid, H.Hc.code.pk(~mix, len, depth, a))
    case ST.SDict{codes, dict}:
      Key.build.d(~mix, len, depth, valid, codes, dict)

# -- probe side (left)

def Key.probe.rk(+len: U32, +depth: Nat, q: Array<String>, t: BT, r: C.Valid & Array<U32>) -> C.Column & Slot:
  (v, codes) = r
  (C.CStr{len, depth, v, ST.SRaw{q}}, SOut{Enc{codes, Array.new(U32, depth, 1), 0}, t})

def Key.probe.rf(+len: U32, +depth: Nat, valid: C.Valid, +n: U32, +g: U32, f: H.HQ) -> C.Column & Slot:
  match f:
    case H.HQ{q, hs, ix, po, pl, pk, out}:
      Key.probe.rk(len, depth, q, BT{n, g, hs, ix, po, pl, pk}, Key.nulls(len, out, valid))

# a Raw left key: every row looked up
def Key.probe.r(~mix: U32 -> U32, +len: U32, +depth: Nat, valid: C.Valid, a: Array<String>, t: BT) -> C.Column & Slot:
  match t:
    case BT{+n, +g, hs, ix, po, pl, pk}:
      Key.probe.rf(len, depth, valid, n, g, H.Hc.find.pk(~mix, n, len, depth, hs, ix, po, pl, pk, a))

def Key.probe.dv(+len: U32, +depth: Nat, codes: Array<U32>, dict: ST.Dict, t: BT, r: C.Valid & Array<U32>) -> C.Column & Slot:
  (v, rids) = r
  (C.CStr{len, depth, v, ST.SDict{codes, dict}}, SOut{Enc{rids, Array.new(U32, depth, 1), 0}, t})

def Key.probe.dg(+len: U32, +depth: Nat, dict: ST.Dict, t: BT, valid: C.Valid, r: Array<U32> & Array<U32>) -> C.Column & Slot:
  (rids, codes) = r
  Key.probe.dv(len, depth, codes, dict, t, Key.nulls(len, rids, valid))

def Key.probe.df(+len: U32, +depth: Nat, valid: C.Valid, codes: Array<U32>, +k: U32, +dd: Nat, +bb: Nat, slots: Array<ST.SSlot>, +tag: U32, +n: U32, +g: U32, f: H.HQ) -> C.Column & Slot:
  match f:
    case H.HQ{strs, hs, ix, po, pl, pk, out}:
      Key.probe.dg(len, depth, ST.Dict{k, dd, strs, bb, slots, tag}, BT{n, g, hs, ix, po, pl, pk}, valid, K.Kernel.gather(~U32, len, depth, out, codes, 0))

def Key.probe.dt(~mix: U32 -> U32, +len: U32, +depth: Nat, valid: C.Valid, codes: Array<U32>, +k: U32, +dd: Nat, +bb: Nat, slots: Array<ST.SSlot>, +tag: U32, strs: Array<String>, t: BT) -> C.Column & Slot:
  match t:
    case BT{+n, +g, hs, ix, po, pl, pk}:
      Key.probe.df(len, depth, valid, codes, k, dd, bb, slots, tag, n, g, H.Hc.find.pk(~mix, n, k, dd, hs, ix, po, pl, pk, strs))

# a Dictionary left key: its k entries looked up (once per distinct string), then one gather
def Key.probe.d(~mix: U32 -> U32, +len: U32, +depth: Nat, valid: C.Valid, codes: Array<U32>, t: BT, dict: ST.Dict) -> C.Column & Slot:
  match dict:
    case ST.Dict{+k, +dd, strs, +bb, slots, +tag}:
      Key.probe.dt(~mix, len, depth, valid, codes, k, dd, bb, slots, tag, strs, t)

# the left key's codes through the right side's table (handed back)
def Key.probe(~mix: U32 -> U32, +len: U32, +depth: Nat, valid: C.Valid, t: BT, x: ST.Strs) -> C.Column & Slot:
  match x:
    case ST.SRaw{a}:
      Key.probe.r(~mix, len, depth, valid, a, t)
    case ST.SDict{codes, dict}:
      Key.probe.d(~mix, len, depth, valid, codes, t, dict)

# -- one key column

def Key.enc.wd(t: BT, r: C.Column & Enc) -> C.Column & Slot:
  (c, e) = r
  (c, SOut{e, t})

def Key.enc.st(~mix: U32 -> U32, build: Bool, +len: U32, +depth: Nat, valid: C.Valid, t: BT, x: ST.Strs) -> C.Column & Slot:
  match build:
    case True{}:
      Key.build(~mix, len, depth, valid, x)
    case False{}:
      Key.probe(~mix, len, depth, valid, t, x)

# the codes of a key column (build: the right side, makes the string table; probe: the left side,
# uses it); the column comes back untouched, the table is handed on
def Key.enc(~mix: U32 -> U32, +build: Bool, c: C.Column, t: BT) -> C.Column & Slot:
  match c:
    case C.CStr{+len, +depth, valid, x}:
      Key.enc.st(~mix, build, len, depth, valid, t, x)
    case other:
      Key.enc.wd(t, Key.enc.word(other))

# walk the columns; the named one is encoded in place (order kept)
def Cols.enc.put(n: String, rest: List<&1, C.Named>, r: C.Column & Slot) -> List<&1, C.Named> & Slot:
  (c, s) = r
  (C.Named{n, c} <> rest, s)

def Cols.enc.app(~mix: U32 -> U32, +build: Bool, n: String, c: C.Column, rest: List<&1, C.Named>, s: Slot) -> List<&1, C.Named> & Slot:
  match s:
    case SIn{t}:
      Cols.enc.put(n, rest, Key.enc(~mix, build, c, t))
    case SOut{e, t}:
      (C.Named{n, c} <> rest, SOut{e, t})

def Cols.enc.k(~mix: U32 -> U32, eq: Bool, +build: Bool, n: String, c: C.Column, r: List<&1, C.Named> & Slot) -> List<&1, C.Named> & Slot:
  match eq:
    case True{}:
      (rest, s) = r
      Cols.enc.app(~mix, build, n, c, rest, s)
    case False{}:
      (rest, s) = r
      (C.Named{n, c} <> rest, s)

def Cols.enc(~mix: U32 -> U32, cols: List<&1, C.Named>, +name: String, +build: Bool, s: Slot) -> List<&1, C.Named> & Slot:
  match cols:
    case Nil{}:
      (Nil{}, s)
    case C.Named{+n, c} <> rest:
      Cols.enc.k(~mix, String.eq(n, name), build, n, c, Cols.enc(~mix, rest, name, build, s))

# ---- one key pair -----------------------------------------------------------------------------

def Join.dense.b(+nl: U32, +nr: U32, lcols: List<&1, C.Named>, rcols: List<&1, C.Named>, outr: Array<U32>, r: DS) -> JS:
  match r:
    case DS{pt, outl}:
      JS{False{}, PT.count(pt), nl, nr, lcols, rcols, outl, outr}

def Join.dense.a(+dict: Bool, +nl: U32, +nr: U32, lcols: List<&1, C.Named>, rcols: List<&1, C.Named>, accl: Array<U32>, cl: Array<U32>, ll: Array<U32>, r: DS) -> JS:
  match r:
    case DS{pt, outr}:
      Join.dense.b(nl, nr, lcols, rcols, outr, Dense.run(nl, False{}, dict, pt, accl, cl, ll))

def Join.dense.lb(+nl: U32, +nr: U32, lcols: List<&1, C.Named>, rcols: List<&1, C.Named>, outl: Array<U32>, r: DS) -> JS:
  match r:
    case DS{pt, outr}:
      JS{False{}, PT.count(pt), nl, nr, lcols, rcols, outl, outr}

def Join.dense.l(+dict: Bool, +nl: U32, +nr: U32, lcols: List<&1, C.Named>, rcols: List<&1, C.Named>, accr: Array<U32>, cr: Array<U32>, lr: Array<U32>, r: DS) -> JS:
  match r:
    case DS{pt, outl}:
      Join.dense.lb(nl, nr, lcols, rcols, outl, Dense.run(nr, False{}, dict, pt, accr, cr, lr))

# the pair table is built over the smaller side and probed by the other. A dense id only labels
# an equal (id so far, code) pair: the CSR groups the right rows by id and a left row finds its
# matches through its own id, so which side hands the ids out changes no match, no count and no
# order; a probe miss is DEAD on either side (no match). The table of the smaller side stays in
# cache (q5 of bench/tpch: a 45k-row left side against all 1.2M lineitem rows on the right).
def Join.side(small_left: Bool, +dict: Bool, +nl: U32, +nr: U32, lcols: List<&1, C.Named>, rcols: List<&1, C.Named>, accl: Array<U32>, accr: Array<U32>, cl: Array<U32>, ll: Array<U32>, cr: Array<U32>, lr: Array<U32>) -> JS:
  match small_left:
    case True{}:
      Join.dense.l(dict, nl, nr, lcols, rcols, accr, cr, lr, Dense.run(nl, True{}, dict, PT.new(nl), accl, cl, ll))
    case False{}:
      Join.dense.a(dict, nl, nr, lcols, rcols, accl, cl, ll, Dense.run(nr, True{}, dict, PT.new(nr), accr, cr, lr))

# ---- a first word key over a narrow value range: direct-address ids, no pair table ------------------
#
# The first key's id so far is 0 on every row, so its pairs are just its codes. When the build side's
# live codes span less than max(2^16, 2 (nl + nr)) words, a table indexed by code - min hands out the
# ids (first appearance on the build side, as PT.op's) and the probe side reads them back: one read and
# one write per row instead of a hash and a probe walk. Same ids up to their labels: same matches.

# the min and max of the live codes (mn > mx: no live code); the arrays come back
def Dd.mm.go(n: Nat, +i: U32, +mn: U32, +mx: U32, rc: Array<U32> & U32, rl: Array<U32> & U32) -> DM:
  match n:
    case 0n:
      (codes, x) = rc
      (lives, v) = rl
      DM{codes, lives, mn, mx}
    case 1n+p:
      (codes, +x) = rc
      (lives, +v) = rl
      +j = U32.inc(i)
      Dd.mm.go(p, j, U32.min(mn, U32.or(x, U32.sub(v, 1))), U32.max(mx, U32.and(x, U32.sub(0, v))), Array.get(U32, codes, j), Array.get(U32, lives, j))

def Dd.mm(+n: U32, codes: Array<U32>, live: Array<U32>) -> DM:
  Dd.mm.go(U32.to_nat(n), 0, 4294967295, 0, Array.get(U32, codes, 0), Array.get(U32, live, 0))

# build: a live row's slot gets the next id when empty (the slot keeps its word otherwise; a dead
# row writes back what it read); the row's id, or DEAD when null
def Dd.put.b(+i: U32, +l: U32, +g: U32, out: Array<U32>, +slot: U32, rt: Array<U32> & U32) -> DD:
  (table, +t) = rt
  +live = U32.is_ne(l, 0)
  +id = Bool.pick(U32, U32.is_eq(t, 0), g, U32.sub(t, 1))
  DD{U32.add(g, Bool.to_u32(Bool.and(live, U32.is_eq(t, 0)))), Array.set(U32, table, slot, Bool.pick(U32, live, U32.inc(id), t)), Array.set(U32, out, i, Bool.pick(U32, live, id, Join.dead()))}

# probe: the slot's id when the row is live, its code in range and the slot taken; else DEAD
def Dd.put.p(+i: U32, +ok: Bool, +g: U32, out: Array<U32>, rt: Array<U32> & U32) -> DD:
  (table, +t) = rt
  DD{g, table, Array.set(U32, out, i, Bool.pick(U32, Bool.and(ok, U32.is_ne(t, 0)), U32.sub(t, 1), Join.dead()))}

def Dd.row.k(+build: Bool, +i: U32, +l: U32, +g: U32, out: Array<U32>, +ok: Bool, +slot: U32, rt: Array<U32> & U32) -> DD:
  match build:
    case True{}:
      Dd.put.b(i, l, g, out, slot, rt)
    case False{}:
      Dd.put.p(i, ok, g, out, rt)

def Dd.row(+build: Bool, +i: U32, +mn: U32, +span: U32, +c: U32, +l: U32, st: DD) -> DD:
  match st:
    case DD{+g, table, out}:
      +slot = U32.sub(c, mn)
      Dd.row.k(build, i, l, g, out, Bool.and(U32.is_ne(l, 0), U32.is_le(slot, span)), slot, Array.get(U32, table, slot))

def Dd.go(n: Nat, +i: U32, +build: Bool, +mn: U32, +span: U32, st: DD, rc: Array<U32> & U32, rl: Array<U32> & U32) -> DD:
  match n:
    case 0n:
      st
    case 1n+p:
      (codes, +c) = rc
      (lives, +l) = rl
      +j = U32.inc(i)
      Dd.go(p, j, build, mn, span, Dd.row(build, i, mn, span, c, l, st), Array.get(U32, codes, j), Array.get(U32, lives, j))

def Dd.run(+n: U32, +build: Bool, +mn: U32, +span: U32, st: DD, codes: Array<U32>, live: Array<U32>) -> DD:
  Dd.go(U32.to_nat(n), 0, build, mn, span, st, Array.get(U32, codes, 0), Array.get(U32, live, 0))

def Dd.both.k(outb: Array<U32>, r: DD) -> DR:
  match r:
    case DD{+g, table, outp}:
      DR{g, outb, outp}

def Dd.both.p(+np: U32, +mn: U32, +span: U32, cp: Array<U32>, lp: Array<U32>, r: DD) -> DR:
  match r:
    case DD{+g, table, outb}:
      Dd.both.k(outb, Dd.run(np, False{}, mn, span, DD{g, table, Array.new(U32, K.Kernel.depth_for(np), 0)}, cp, lp))

# the ids of both sides: the build side (nb rows) first, then the probe side (np rows)
def Dd.both(+nb: U32, +np: U32, +mn: U32, +span: U32, cb: Array<U32>, lb: Array<U32>, cp: Array<U32>, lp: Array<U32>) -> DR:
  Dd.both.p(np, mn, span, cp, lp, Dd.run(nb, True{}, mn, span, DD{0, Array.new(U32, K.Kernel.depth_for(U32.inc(span)), 0), Array.new(U32, K.Kernel.depth_for(nb), 0)}, cb, lb))

def Join.narrow(+mn: U32, +mx: U32, +nl: U32, +nr: U32) -> Bool:
  Bool.and(U32.is_le(mn, mx), U32.is_lt(U32.sub(mx, mn), U32.max(65536, U32.add(U32.add(nl, nr), U32.add(nl, nr)))))

def Join.dd.l(+nl: U32, +nr: U32, lcols: List<&1, C.Named>, rcols: List<&1, C.Named>, r: DR) -> JS:
  match r:
    case DR{+g, ob, op}:
      JS{False{}, g, nl, nr, lcols, rcols, ob, op}

def Join.dd.r(+nl: U32, +nr: U32, lcols: List<&1, C.Named>, rcols: List<&1, C.Named>, r: DR) -> JS:
  match r:
    case DR{+g, ob, op}:
      JS{False{}, g, nl, nr, lcols, rcols, op, ob}

# the left side builds (it is the smaller one): direct ids when narrow, else the pair table
def Join.word.lk(ok: Bool, +nl: U32, +nr: U32, lcols: List<&1, C.Named>, rcols: List<&1, C.Named>, accl: Array<U32>, accr: Array<U32>, cl: Array<U32>, ll: Array<U32>, cr: Array<U32>, lr: Array<U32>, +mn: U32, +span: U32) -> JS:
  match ok:
    case True{}:
      Join.dd.l(nl, nr, lcols, rcols, Dd.both(nl, nr, mn, span, cl, ll, cr, lr))
    case False{}:
      Join.side(True{}, False{}, nl, nr, lcols, rcols, accl, accr, cl, ll, cr, lr)

def Join.word.l(+nl: U32, +nr: U32, lcols: List<&1, C.Named>, rcols: List<&1, C.Named>, accl: Array<U32>, accr: Array<U32>, cr: Array<U32>, lr: Array<U32>, m: DM) -> JS:
  match m:
    case DM{cl, ll, +mn, +mx}:
      Join.word.lk(Join.narrow(mn, mx, nl, nr), nl, nr, lcols, rcols, accl, accr, cl, ll, cr, lr, mn, U32.sub(mx, mn))

# the right side builds
def Join.word.rk(ok: Bool, +nl: U32, +nr: U32, lcols: List<&1, C.Named>, rcols: List<&1, C.Named>, accl: Array<U32>, accr: Array<U32>, cl: Array<U32>, ll: Array<U32>, cr: Array<U32>, lr: Array<U32>, +mn: U32, +span: U32) -> JS:
  match ok:
    case True{}:
      Join.dd.r(nl, nr, lcols, rcols, Dd.both(nr, nl, mn, span, cr, lr, cl, ll))
    case False{}:
      Join.side(False{}, False{}, nl, nr, lcols, rcols, accl, accr, cl, ll, cr, lr)

def Join.word.r(+nl: U32, +nr: U32, lcols: List<&1, C.Named>, rcols: List<&1, C.Named>, accl: Array<U32>, accr: Array<U32>, cl: Array<U32>, ll: Array<U32>, m: DM) -> JS:
  match m:
    case DM{cr, lr, +mn, +mx}:
      Join.word.rk(Join.narrow(mn, mx, nl, nr), nl, nr, lcols, rcols, accl, accr, cl, ll, cr, lr, mn, U32.sub(mx, mn))

# a first word key (its ids so far are all 0): the smaller side's codes decide between direct ids
# and the pair table
def Join.word(small_left: Bool, +nl: U32, +nr: U32, lcols: List<&1, C.Named>, rcols: List<&1, C.Named>, accl: Array<U32>, accr: Array<U32>, cl: Array<U32>, ll: Array<U32>, cr: Array<U32>, lr: Array<U32>) -> JS:
  match small_left:
    case True{}:
      Join.word.l(nl, nr, lcols, rcols, accl, accr, cr, lr, Dd.mm(nl, cl, ll))
    case False{}:
      Join.word.r(nl, nr, lcols, rcols, accl, accr, cl, ll, Dd.mm(nr, cr, lr))

def Join.comb.w(word1: Bool, +dict: Bool, +nl: U32, +nr: U32, lcols: List<&1, C.Named>, rcols: List<&1, C.Named>, accl: Array<U32>, accr: Array<U32>, cl: Array<U32>, ll: Array<U32>, cr: Array<U32>, lr: Array<U32>) -> JS:
  match word1:
    case True{}:
      Join.word(U32.is_lt(nl, nr), nl, nr, lcols, rcols, accl, accr, cl, ll, cr, lr)
    case False{}:
      Join.side(U32.is_lt(nl, nr), dict, nl, nr, lcols, rcols, accl, accr, cl, ll, cr, lr)

# combine: a first string key's codes are dense ids already; a first word key may take direct ids
# (Join.word); else densify through the pair table
def Join.comb(direct: Bool, word1: Bool, +dict: Bool, +dg: U32, +nl: U32, +nr: U32, lcols: List<&1, C.Named>, rcols: List<&1, C.Named>, accl: Array<U32>, accr: Array<U32>, cl: Array<U32>, ll: Array<U32>, cr: Array<U32>, lr: Array<U32>) -> JS:
  match direct:
    case True{}:
      JS{False{}, dg, nl, nr, lcols, rcols, cl, cr}
    case False{}:
      Join.comb.w(word1, dict, nl, nr, lcols, rcols, accl, accr, cl, ll, cr, lr)

# dg: the right side's distinct string ids (a word key: 0, unused)
def Join.key.d(+t: D.DType, +first: Bool, +nl: U32, +nr: U32, accl: Array<U32>, accr: Array<U32>, rcols: List<&1, C.Named>, cr: Array<U32>, lr: Array<U32>, +dg: U32, lcols: List<&1, C.Named>, s: Slot) -> JS:
  match s:
    case SOut{Enc{cl, ll, gl}, tb}:
      +str = D.DType.eq(t, D.TStr{})
      Join.comb(Bool.and(first, str), Bool.and(first, Bool.not(str)), str, dg, nl, nr, lcols, rcols, accl, accr, cl, ll, cr, lr)
    case SIn{tb}:
      JS{first, 0, nl, nr, lcols, rcols, accl, accr}

def Join.key.c(+t: D.DType, first: Bool, +nl: U32, +nr: U32, accl: Array<U32>, accr: Array<U32>, rcols: List<&1, C.Named>, cr: Array<U32>, lr: Array<U32>, +dg: U32, r: List<&1, C.Named> & Slot) -> JS:
  (lcols, s) = r
  Join.key.d(t, first, nl, nr, accl, accr, rcols, cr, lr, dg, lcols, s)

def Join.key.b(~mix: U32 -> U32, +t: D.DType, +ln: String, first: Bool, +nl: U32, +nr: U32, lcols: List<&1, C.Named>, accl: Array<U32>, accr: Array<U32>, rcols: List<&1, C.Named>, s: Slot) -> JS:
  match s:
    case SOut{Enc{cr, lr, dg}, tb}:
      Join.key.c(t, first, nl, nr, accl, accr, rcols, cr, lr, dg, Cols.enc(~mix, lcols, ln, False{}, SIn{tb}))
    case SIn{tb}:
      JS{first, 0, nl, nr, lcols, rcols, accl, accr}

def Join.key.a(~mix: U32 -> U32, +t: D.DType, +ln: String, first: Bool, +nl: U32, +nr: U32, lcols: List<&1, C.Named>, accl: Array<U32>, accr: Array<U32>, r: List<&1, C.Named> & Slot) -> JS:
  (rcols, s) = r
  Join.key.b(~mix, t, ln, first, nl, nr, lcols, accl, accr, rcols, s)

def Join.key(~mix: U32 -> U32, k: KeySpec, st: JS) -> JS:
  match k:
    case KeySpec{+ln, +rn, +t}:
      match st:
        case JS{first, g, +nl, +nr, lcols, rcols, accl, accr}:
          Join.key.a(~mix, t, ln, first, nl, nr, lcols, accl, accr, Cols.enc(~mix, rcols, rn, True{}, SIn{BT.none()}))

def Join.keys.loop(~mix: U32 -> U32, ks: List<&2, KeySpec>, st: JS) -> JS:
  match ks:
    case Nil{}:
      st
    case k <> rest:
      Join.keys.loop(~mix, rest, Join.key(~mix, k, st))

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
    case _:
      K.Kernel.fold(~U32, ~TA, ~(acc => m => Tot.inner(acc, m)), n, ms, TA{0, 0, 0})

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

# ---- semi / anti: a 0/1 mask over the left rows from their match counts ---------------------------

def Join.semi.mask(anti: Bool, +nl: U32, ms: Array<U32>) -> Array<U32>:
  match anti:
    case True{}:
      K.Kernel.map(~U32, ~U32, ~(m => Bool.to_u32(U32.is_eq(m, 0))), nl, K.Kernel.depth_for(nl), ms, 0)
    case False{}:
      K.Kernel.map(~U32, ~U32, ~(m => Bool.to_u32(U32.is_ne(m, 0))), nl, K.Kernel.depth_for(nl), ms, 0)

def Join.semi.fin(+nl: U32, lcols: List<&1, C.Named>, r: Array<U32> & U32) -> E.ResT(C.Frame):
  (mask, +kept) = r
  Done{C.Frame.filter_mask(C.Frame{nl, lcols}, mask, kept)}

def Join.semi.b(anti: Bool, +nl: U32, lcols: List<&1, C.Named>, r: Array<U32> & Array<U32>) -> E.ResT(C.Frame):
  (ms, accl) = r
  Join.semi.fin(nl, lcols, K.Kernel.popcount(nl, Join.semi.mask(anti, nl, ms)))

# the left rows with a match (semi) or without one (anti), left columns only, left order; m[i] =
# counts[g] is left row i's match count (a null or missing key has the DEAD id, whose count is 0).
# The right frame is dropped. Never more rows than the left input (no row cap needed, 15.8).
def Join.semi(anti: Bool, +nl: U32, lcols: List<&1, C.Named>, rcols: List<&1, C.Named>, accl: Array<U32>, csr: CSR) -> E.ResT(C.Frame):
  match csr:
    case CSR{counts, starts, rows}:
      Join.semi.b(anti, nl, lcols, K.Kernel.gather(~U32, nl, K.Kernel.depth_for(nl), counts, accl, 0))

def Join.go.k(how: JoinHow, +lnames: List<&2, String>, +right_on: List<&2, String>, +nl: U32, lcols: List<&1, C.Named>, rcols: List<&1, C.Named>, accl: Array<U32>, csr: CSR) -> E.ResT(C.Frame):
  match how:
    case Semi{}:
      Join.semi(False{}, nl, lcols, rcols, accl, csr)
    case Anti{}:
      Join.semi(True{}, nl, lcols, rcols, accl, csr)
    case other:
      Join.probe(other, lnames, right_on, nl, lcols, rcols, accl, csr)

def Join.go(+how: JoinHow, +lnames: List<&2, String>, +right_on: List<&2, String>, st: JS) -> E.ResT(C.Frame):
  match st:
    case JS{first, +g, +nl, +nr, lcols, rcols, accl, accr}:
      Join.go.k(how, lnames, right_on, nl, lcols, rcols, accl, Join.csr(g, nr, accr))

# ---- entry ------------------------------------------------------------------------------------------

def Join.exec(~mix: U32 -> U32, +how: JoinHow, keys: List<&2, KeySpec>, +lnames: List<&2, String>, +right_on: List<&2, String>, left: C.Frame, right: C.Frame) -> E.ResT(C.Frame):
  match left:
    case C.Frame{+nl, lcols}:
      match right:
        case C.Frame{+nr, rcols}:
          Join.go(how, lnames, right_on, Join.keys.loop(~mix, keys, JS{True{}, 0, nl, nr, lcols, rcols, Array.new(U32, K.Kernel.depth_for(nl), 0), Array.new(U32, K.Kernel.depth_for(nr), 0)}))

def Join.run.c(~mix: U32 -> U32, +how: JoinHow, ks: E.Res(List<&2, KeySpec>), +lnames: List<&2, String>, +right_on: List<&2, String>, left: C.Frame, right: C.Frame) -> E.ResT(C.Frame):
  match ks:
    case Fail{e}:
      Fail{e}
    case Done{keys}:
      Join.exec(~mix, how, keys, lnames, right_on, left, right)

def Join.run.b(~mix: U32 -> U32, +how: JoinHow, chk: E.Res(List<&2, S.Field>), +left_on: List<&2, String>, +right_on: List<&2, String>, +ls: List<&2, S.Field>, +rs: List<&2, S.Field>, left: C.Frame, right: C.Frame) -> E.ResT(C.Frame):
  match chk:
    case Fail{e}:
      Fail{e}
    case Done{fs}:
      Join.run.c(~mix, how, Join.keys(left_on, right_on, ls, rs), S.Schema.names(ls), right_on, left, right)

def Join.run.a(~mix: U32 -> U32, +how: JoinHow, +left_on: List<&2, String>, +right_on: List<&2, String>, rl: C.Frame & List<&2, S.Field>, rr: C.Frame & List<&2, S.Field>) -> E.ResT(C.Frame):
  (left, +ls) = rl
  (right, +rs) = rr
  Join.run.b(~mix, how, Join.schema.how(how, ls, rs, left_on, right_on), left_on, right_on, ls, rs, left, right)

# Join.run with the string table's hash template (Join.run: the identity; a test passes a constant,
# so every probe of a string key collides and compares strings: the output must not change)
def Join.run.h(~mix: U32 -> U32, +how: JoinHow, left: C.Frame, right: C.Frame, +left_on: List<&2, String>, +right_on: List<&2, String>) -> E.ResT(C.Frame):
  Join.run.a(~mix, how, left_on, right_on, S.Frame.schema(left), S.Frame.schema(right))

# join two frames on left_on[i] == right_on[i] (equal dtypes, nulls never
# match). Output: every left column, then the right columns minus right_on
# (a name clashing with a left column gets `_right`); rows in left order, the
# matches of a left row in right order; a left join keeps unmatched left rows
# with null right columns. Semi / Anti keep the left rows with / without a match (left
# columns only, left order, each row once). Errors (before any work): see Join.schema.how.
def Join.run(+how: JoinHow, left: C.Frame, right: C.Frame, +left_on: List<&2, String>, +right_on: List<&2, String>) -> E.ResT(C.Frame):
  Join.run.h(~(h => h), how, left, right, left_on, right_on)
