# src/table.bend -- the table verbs of M3 (DESIGN.md 15.2.3, 15.2.4): drop, rename, slice,
# tail, unique and concat_vertical. Semi / anti joins live in join.bend (Join{Semi/Anti}).
#
# Every verb has ONE static rule over schemas (`<Verb>.schema`, pure Data) that Plan.schema
# (collect_schema) and the eager run both use, and ONE frame function (`<Verb>.run`) that the
# eager facade and Exec's runner both call:
#   drop(names)       ColumnNotFound{n} for the first name not present (list order); a name may
#                     repeat; the remaining columns keep their order; dropping every column
#                     keeps the height (Frame{h, []}, Polars)
#   rename(pairs)     simultaneous (from, to) pairs, positions unchanged, swaps allowed:
#                     ColumnNotFound{from} (first missing, list order), then DuplicateColumn{from}
#                     (a from repeated in pairs), then DuplicateColumn{name} (the first repeated
#                     OUTPUT name in frame order)
#   slice(off, len)   rows [start, start + count) with start = min(off, h), count =
#                     min(len, h - start): no overflow is possible (U32 only, no negative offsets)
#   tail(n)           slice(h - min(n, h), min(n, h))
#   unique(subset)    keep first: row i stays iff no earlier row has an equal key tuple, with
#                     group_by's key codes (G.Grp.codes / G.Grp.densify: the 15.5 relation, null
#                     equals null); subset [] means every column; a frame with no column keeps
#                     min(h, 1) rows; ColumnNotFound{n} for the first missing subset name
#   concat_vertical   all rows of input 0, then input 1, ...: input i's schema (names, dtypes and
#                     order) must equal input 0's; the summed height (saturating at 2^32 - 1, so a
#                     sum that would wrap is over the cap) is checked against the 2^23 row cap
#                     before any column is built (15.8)
#
# Lazy concat is a left-nested chain of BINARY nodes P.Concat{i, left, right} (i = the position
# of `right` in the input list; left holds inputs 0 .. i-1; i = 0 marks the empty list): a
# recursion through a List<&2, Plan> field passes `bend` but not `--verdict`, so the Plan has no
# n-ary node (DESIGN.md 14 "M3 table verbs"). `Concat.schema` is that node's static rule and
# `Concat.two` its runtime step; the eager `Concat.frames` checks every schema first and then
# folds `Concat.two`, so the first prefix whose height sum passes the cap is the one reported,
# as in the lazy chain.
#
# Idioms (DESIGN.md section 9): helpers above callers; match only on params; pairs taken apart
# in the next helper's parameter; `+` on every reused binder.
import Base
import ./dtype.bend as D
import ./err.bend as E
import ./kernels.bend as K
import ./column.bend as C
import ./strs.bend as ST
import ./schema.bend as S
import ./groupby.bend as G

# ---- shared ----------------------------------------------------------------------------------

def Tbl.miss.k(has: Bool, n: String, rest: Maybe<&2, E.Err>) -> Maybe<&2, E.Err>:
  match has:
    case True{}:
      rest
    case False{}:
      Some{E.ColumnNotFound{n}}

# ColumnNotFound for the first name of ns that is not a field of s (list order)
def Tbl.miss(ns: List<&2, String>, +s: List<&2, S.Field>) -> Maybe<&2, E.Err>:
  match ns:
    case Nil{}:
      None{}
    case +n <> t:
      Tbl.miss.k(S.Schema.has(s, n), n, Tbl.miss(t, s))

def Tbl.res(m: Maybe<&2, E.Err>, s: List<&2, S.Field>) -> E.Res(List<&2, S.Field>):
  match m:
    case Some{e}:
      Fail{e}
    case None{}:
      Done{s}

def Tbl.dup(d: Maybe<&2, String>) -> Maybe<&2, E.Err>:
  match d:
    case Some{n}:
      Some{E.DuplicateColumn{n}}
    case None{}:
      None{}

# gather every column by perm (m rows) into acc (newest first); perm comes back
def Tbl.gather.add(n: String, acc: List<&1, C.Named>, r: C.Column & Array<U32>) -> Array<U32> & List<&1, C.Named>:
  (c, perm) = r
  (perm, C.Named{n, c} <> acc)

def Tbl.gather.step(n: String, +m: U32, c: C.Column, st: Array<U32> & List<&1, C.Named>) -> Array<U32> & List<&1, C.Named>:
  (perm, acc) = st
  Tbl.gather.add(n, acc, C.Column.gather(c, perm, m))

def Tbl.gather(cols: List<&1, C.Named>, +m: U32, st: Array<U32> & List<&1, C.Named>) -> Array<U32> & List<&1, C.Named>:
  match cols:
    case Nil{}:
      st
    case C.Named{n, c} <> rest:
      Tbl.gather(rest, m, Tbl.gather.step(n, m, c, st))

def Tbl.gather.fin(+m: U32, r: Array<U32> & List<&1, C.Named>) -> C.Frame:
  (perm, acc) = r
  C.Frame{m, List.reverse(&1, C.Named, acc)}

# ---- drop ------------------------------------------------------------------------------------

def Drop.keep(dropped: Bool, f: S.Field, rest: List<&2, S.Field>) -> List<&2, S.Field>:
  match dropped:
    case True{}:
      rest
    case False{}:
      f <> rest

def Drop.fields(s: List<&2, S.Field>, +ns: List<&2, String>) -> List<&2, S.Field>:
  match s:
    case Nil{}:
      Nil{}
    case S.Field{+n, t} <> rest:
      Drop.keep(C.Names.has(ns, n), S.Field{n, t}, Drop.fields(rest, ns))

# the schema after drop(ns) over s
def Drop.schema(+ns: List<&2, String>, +s: List<&2, S.Field>) -> E.Res(List<&2, S.Field>):
  Tbl.res(Tbl.miss(ns, s), Drop.fields(s, ns))

def Drop.col(dropped: Bool, nc: C.Named, rest: List<&1, C.Named>) -> List<&1, C.Named>:
  match dropped:
    case True{}:
      rest
    case False{}:
      nc <> rest

def Drop.cols(cols: List<&1, C.Named>, +ns: List<&2, String>) -> List<&1, C.Named>:
  match cols:
    case Nil{}:
      Nil{}
    case C.Named{+n, c} <> rest:
      Drop.col(C.Names.has(ns, n), C.Named{n, c}, Drop.cols(rest, ns))

def Drop.go(m: Maybe<&2, E.Err>, f: C.Frame, +ns: List<&2, String>) -> E.ResT(C.Frame):
  match m:
    case Some{e}:
      Fail{e}
    case None{}:
      match f:
        case C.Frame{h, cols}:
          Done{C.Frame{h, Drop.cols(cols, ns)}}

def Drop.run.a(+ns: List<&2, String>, r: C.Frame & List<&2, S.Field>) -> E.ResT(C.Frame):
  (f, +s) = r
  Drop.go(Tbl.miss(ns, s), f, ns)

# the frame without the named columns (order kept, height kept)
def Drop.run(f: C.Frame, +ns: List<&2, String>) -> E.ResT(C.Frame):
  Drop.run.a(ns, S.Frame.schema(f))

# ---- rename ----------------------------------------------------------------------------------

def Ren.fst(p: Sigma<&2, &2, String, x => String>) -> String:
  (a, b) = p
  a

def Ren.froms(ps: List<&2, Sigma<&2, &2, String, x => String>>) -> List<&2, String>:
  match ps:
    case Nil{}:
      Nil{}
    case p <> t:
      Ren.fst(p) <> Ren.froms(t)

def Ren.find.k(p: Sigma<&2, &2, String, x => String>, +n: String, rest: String) -> String:
  (a, b) = p
  Bool.pick(String, String.eq(a, n), b, rest)

# the new name of column n (n itself when no pair renames it)
def Ren.find(ps: List<&2, Sigma<&2, &2, String, x => String>>, +n: String) -> String:
  match ps:
    case Nil{}:
      n
    case p <> t:
      Ren.find.k(p, n, Ren.find(t, n))

def Ren.fields(s: List<&2, S.Field>, +ps: List<&2, Sigma<&2, &2, String, x => String>>) -> List<&2, S.Field>:
  match s:
    case Nil{}:
      Nil{}
    case S.Field{n, t} <> rest:
      S.Field{Ren.find(ps, n), t} <> Ren.fields(rest, ps)

# the schema after rename(ps) over s
def Rename.schema(+ps: List<&2, Sigma<&2, &2, String, x => String>>, +s: List<&2, S.Field>) -> E.Res(List<&2, S.Field>):
  +fs = Ren.fields(s, ps)
  Tbl.res(Maybe.or(&2, E.Err, Tbl.miss(Ren.froms(ps), s), Maybe.or(&2, E.Err, Tbl.dup(C.Names.dup(Ren.froms(ps), Nil{}, None{})), Tbl.dup(C.Names.dup(S.Schema.names(fs), Nil{}, None{})))), fs)

def Ren.cols(cols: List<&1, C.Named>, +ps: List<&2, Sigma<&2, &2, String, x => String>>) -> List<&1, C.Named>:
  match cols:
    case Nil{}:
      Nil{}
    case C.Named{n, c} <> rest:
      C.Named{Ren.find(ps, n), c} <> Ren.cols(rest, ps)

def Rename.go(r: E.Res(List<&2, S.Field>), f: C.Frame, +ps: List<&2, Sigma<&2, &2, String, x => String>>) -> E.ResT(C.Frame):
  match r:
    case Fail{e}:
      Fail{e}
    case Done{s}:
      match f:
        case C.Frame{h, cols}:
          Done{C.Frame{h, Ren.cols(cols, ps)}}

def Rename.run.a(+ps: List<&2, Sigma<&2, &2, String, x => String>>, r: C.Frame & List<&2, S.Field>) -> E.ResT(C.Frame):
  (f, s) = r
  Rename.go(Rename.schema(ps, s), f, ps)

# every `from` column renamed to its `to`, simultaneously (positions and data unchanged)
def Rename.run(f: C.Frame, +ps: List<&2, Sigma<&2, &2, String, x => String>>) -> E.ResT(C.Frame):
  Rename.run.a(ps, S.Frame.schema(f))

# ---- slice / tail ----------------------------------------------------------------------------

def Slice.cols(cols: List<&1, C.Named>, +start: U32, +cnt: U32) -> List<&1, C.Named>:
  match cols:
    case Nil{}:
      Nil{}
    case C.Named{n, c} <> rest:
      C.Named{n, C.Column.slice(c, start, cnt)} <> Slice.cols(rest, start, cnt)

# start = 0 is a head (no copy); otherwise every column is gathered
def Slice.go(zero: Bool, f: C.Frame, +start: U32, +cnt: U32) -> C.Frame:
  match zero:
    case True{}:
      C.Frame.head(f, cnt)
    case False{}:
      match f:
        case C.Frame{h, cols}:
          C.Frame{cnt, Slice.cols(cols, start, cnt)}

def Slice.at(f: C.Frame, +start: U32, +cnt: U32) -> C.Frame:
  Slice.go(U32.is_zero(start), f, start, cnt)

def Slice.run.a(+off: U32, +len: U32, r: C.Frame & U32) -> C.Frame:
  (f, +h) = r
  +start = U32.min(off, h)
  Slice.at(f, start, U32.min(len, U32.sub(h, start)))

# rows [min(off, h), min(off, h) + min(len, h - min(off, h))): clamped, never overflows
def Slice.run(f: C.Frame, +off: U32, +len: U32) -> C.Frame:
  Slice.run.a(off, len, C.Frame.height(f))

def Tail.run.a(+n: U32, r: C.Frame & U32) -> C.Frame:
  (f, +h) = r
  +k = U32.min(n, h)
  Slice.at(f, U32.sub(h, k), k)

# the last min(n, h) rows
def Tail.run(f: C.Frame, +n: U32) -> C.Frame:
  Tail.run.a(n, C.Frame.height(f))

# ---- unique ----------------------------------------------------------------------------------

# the schema after unique(subset) over s (the input's)
def Unique.schema(+sub: List<&2, String>, +s: List<&2, S.Field>) -> E.Res(List<&2, S.Field>):
  Tbl.res(Tbl.miss(sub, s), s)

# the key names: the subset, or every column for []
def Uniq.keys(sub: List<&2, String>, +s: List<&2, S.Field>) -> List<&2, String>:
  match sub:
    case Nil{}:
      S.Schema.names(s)
    case h <> t:
      h <> t

def Uniq.get.k(+n: String, acc: List<&1, C.Named>, r: C.Frame & E.ResT(C.Column)) -> C.Frame & List<&1, C.Named>:
  (f, rc) = r
  match rc:
    case Fail{e}:
      (f, acc)
    case Done{c}:
      (f, C.Named{n, c} <> acc)

# a name repeated later in the subset is copied here (the later one borrows it)
def Uniq.get.c(again: Bool, f: C.Frame, +n: String) -> C.Frame & E.ResT(C.Column):
  match again:
    case True{}:
      C.Frame.get_cloned(f, n)
    case False{}:
      C.Frame.lend(f, n)

def Uniq.get.step(+n: String, +rest: List<&2, String>, st: C.Frame & List<&1, C.Named>) -> C.Frame & List<&1, C.Named>:
  (f, acc) = st
  Uniq.get.k(n, acc, Uniq.get.c(C.Names.has(rest, n), f, n))

# every key column (newest first, as G.Grp.codes takes them), BORROWED (DESIGN.md 16.2 rule 1):
# the last reference of a name is lent out of the frame (Frame.lend, no copy; Tbl.back puts it
# back after G.Grp.codes hands it back), an earlier repeat of the same name is copied
def Uniq.get(keys: List<&2, String>, st: C.Frame & List<&1, C.Named>) -> C.Frame & List<&1, C.Named>:
  match keys:
    case Nil{}:
      st
    case k <> +t:
      Uniq.get(t, Uniq.get.step(k, t, st))

def Tbl.back.one(r: E.ResT(C.Frame), name: String, c: C.Column) -> E.ResT(C.Frame):
  match r:
    case Fail{e}:
      Fail{e}
    case Done{f}:
      C.Frame.replace(f, name, c)

# the borrowed key columns back into their frame (Frame.replace: in place, the frame's height);
# of a repeated name the last one put back stays (all copies are equal)
def Tbl.back(cols: List<&1, C.Named>, r: E.ResT(C.Frame)) -> E.ResT(C.Frame):
  match cols:
    case Nil{}:
      r
    case C.Named{n, c} <> t:
      Tbl.back(t, Tbl.back.one(r, n, c))

# the first row of every group, in first-appearance order (= ascending row order)
def Uniq.out(g: G.Groups, f: C.Frame) -> E.ResT(C.Frame):
  match g:
    case G.Groups{+ng, gids, first}:
      match f:
        case C.Frame{h, cols}:
          Done{Tbl.gather.fin(ng, Tbl.gather(cols, ng, (first, Nil{})))}

def Uniq.group.e(g: G.Groups, r: E.ResT(C.Frame)) -> E.ResT(C.Frame):
  match r:
    case Fail{e}:
      Fail{e}
    case Done{f}:
      Uniq.out(g, f)

def Uniq.group.c(+n: U32, +d: Nat, f: C.Frame, r: List<&1, C.Named> & G.Codes) -> E.ResT(C.Frame):
  (kc, cd) = r
  match cd:
    case G.Codes{+k, c}:
      Uniq.group.e(G.Grp.densify(n, d, k, c), Tbl.back(kc, Done{f}))

def Uniq.group.h(kc: List<&1, C.Named>, r: C.Frame & U32) -> E.ResT(C.Frame):
  (f, +n) = r
  +d = K.Kernel.depth_for(n)
  Uniq.group.c(n, d, f, G.Grp.codes(kc, n, d, (Nil{}, G.Codes{1, Array.new(U32, d, 0)})))

def Uniq.group(st: C.Frame & List<&1, C.Named>) -> E.ResT(C.Frame):
  (f, kc) = st
  Uniq.group.h(kc, C.Frame.height(f))

# no key column (a frame with no columns, subset []): one row is kept when h > 0
def Uniq.keyed(keys: List<&2, String>, f: C.Frame) -> E.ResT(C.Frame):
  match keys:
    case Nil{}:
      Done{C.Frame.head(f, 1)}
    case k <> t:
      Uniq.group(Uniq.get(k <> t, (f, Nil{})))

def Unique.go(m: Maybe<&2, E.Err>, f: C.Frame, keys: List<&2, String>) -> E.ResT(C.Frame):
  match m:
    case Some{e}:
      Fail{e}
    case None{}:
      Uniq.keyed(keys, f)

def Unique.run.a(+sub: List<&2, String>, r: C.Frame & List<&2, S.Field>) -> E.ResT(C.Frame):
  (f, +s) = r
  Unique.go(Tbl.miss(sub, s), f, Uniq.keys(sub, s))

# the first row of every distinct key tuple (subset [] = every column), input order
def Unique.run(f: C.Frame, +sub: List<&2, String>) -> E.ResT(C.Frame):
  Unique.run.a(sub, S.Frame.schema(f))

# ---- concat_vertical -------------------------------------------------------------------------

def Cat.no_inputs() -> E.Err:
  E.InvalidOperation{"concat_vertical: no inputs"}

def Cat.differs(+i: U32, s: List<&2, S.Field>, s0: List<&2, S.Field>) -> E.Err:
  E.InvalidOperation{"concat_vertical: input " ++ U32.show(i) ++ " schema [" ++ S.Schema.show(s) ++ "] differs from input 0's [" ++ S.Schema.show(s0) ++ "]"}

def Concat.schema.k(empty: Bool, same: Bool, +i: U32, sl: List<&2, S.Field>, sr: List<&2, S.Field>) -> E.Res(List<&2, S.Field>):
  match empty same:
    case True{} _:
      Fail{Cat.no_inputs()}
    case False{} True{}:
      Done{sl}
    case False{} False{}:
      Fail{Cat.differs(i, sr, sl)}

# the static rule of the binary node Concat{i, left, right}: i = 0 is the empty input list;
# otherwise input i's schema sr must equal sl, the schema of inputs 0 .. i-1 (input 0's)
def Concat.schema(+i: U32, +sl: List<&2, S.Field>, +sr: List<&2, S.Field>) -> E.Res(List<&2, S.Field>):
  Concat.schema.k(U32.is_zero(i), S.Schema.eq(sr, sl), i, sl, sr)

# t + m saturating at 2^32 - 1 (a sum that would wrap is over the row cap by definition)
def Cat.sat(+t: U32, +m: U32) -> U32:
  +s = U32.add(t, m)
  Bool.pick(U32, U32.is_lt(s, t), 4294967295, s)

def Cat.valid(va: C.Valid, vb: C.Valid, +na: U32, +nb: U32, +da: Nat, +db: Nat, +d: Nat) -> C.Valid:
  match va vb:
    case C.AllValid{} C.AllValid{}:
      C.AllValid{}
    case x y:
      C.Mask{K.Kernel.append(~U32, na, nb, d, C.Valid.materialize(x, da), C.Valid.materialize(y, db), 0)}

# a's rows then b's rows (same dtype: the schemas were checked), n = len a + len b in 2^d slots
def Cat.col(a: C.Column, b: C.Column, +n: U32, +d: Nat) -> C.Column:
  match a b:
    case C.CBool{+na, +da, va, xa} C.CBool{+nb, +db, vb, xb}:
      C.CBool{n, d, Cat.valid(va, vb, na, nb, da, db, d), K.Kernel.append(~U32, na, nb, d, xa, xb, 0)}
    case C.CU32{+na, +da, va, xa} C.CU32{+nb, +db, vb, xb}:
      C.CU32{n, d, Cat.valid(va, vb, na, nb, da, db, d), K.Kernel.append(~U32, na, nb, d, xa, xb, 0)}
    case C.CI32{+na, +da, va, xa} C.CI32{+nb, +db, vb, xb}:
      C.CI32{n, d, Cat.valid(va, vb, na, nb, da, db, d), K.Kernel.append(~U32, na, nb, d, xa, xb, 0)}
    case C.CF32{+na, +da, va, xa} C.CF32{+nb, +db, vb, xb}:
      C.CF32{n, d, Cat.valid(va, vb, na, nb, da, db, d), K.Kernel.append(~F32, na, nb, d, xa, xb, 0.0)}
    case C.CStr{+na, +da, va, xa} C.CStr{+nb, +db, vb, xb}:
      C.CStr{n, d, Cat.valid(va, vb, na, nb, da, db, d), ST.Strs.append(na, nb, da, db, d, xa, xb)}
    case x y:
      x

def Cat.cols(ca: List<&1, C.Named>, cb: List<&1, C.Named>, +n: U32, +d: Nat) -> List<&1, C.Named>:
  match ca cb:
    case C.Named{nm, a} <> ta C.Named{nb, b} <> tb:
      C.Named{nm, Cat.col(a, b, n, d)} <> Cat.cols(ta, tb, n, d)
    case x y:
      Nil{}

def Cat.join.k(over: Maybe<&2, E.Err>, +t: U32, ca: List<&1, C.Named>, cb: List<&1, C.Named>) -> E.ResT(C.Frame):
  match over:
    case Some{e}:
      Fail{e}
    case None{}:
      Done{C.Frame{t, Cat.cols(ca, cb, t, K.Kernel.depth_for(t))}}

# a's rows then b's rows; the row cap is checked on the saturating sum before any column is built
def Cat.join(a: C.Frame, b: C.Frame) -> E.ResT(C.Frame):
  match a:
    case C.Frame{+ha, ca}:
      match b:
        case C.Frame{+hb, cb}:
          +t = Cat.sat(ha, hb)
          Cat.join.k(K.Kernel.check_rows(t), t, ca, cb)

def Concat.two.b(r: E.Res(List<&2, S.Field>), a: C.Frame, b: C.Frame) -> E.ResT(C.Frame):
  match r:
    case Fail{e}:
      Fail{e}
    case Done{s}:
      Cat.join(a, b)

def Concat.two.a(+i: U32, ra: C.Frame & List<&2, S.Field>, rb: C.Frame & List<&2, S.Field>) -> E.ResT(C.Frame):
  (a, sa) = ra
  (b, sb) = rb
  Concat.two.b(Concat.schema(i, sa, sb), a, b)

# the runtime step of Concat{i, left, right}: left = inputs 0 .. i-1 already concatenated, right
# = input i. Concat.schema's check (the same text), then the row cap, then the rows
def Concat.two(+i: U32, a: C.Frame, b: C.Frame) -> E.ResT(C.Frame):
  Concat.two.a(i, S.Frame.schema(a), S.Frame.schema(b))

def Cat.scan.k(r: C.Frame & List<&2, S.Field>, rest: List<&1, C.Frame> & List<&2, List<&2, S.Field>>) -> List<&1, C.Frame> & List<&2, List<&2, S.Field>>:
  (f, s) = r
  (fs, ss) = rest
  (f <> fs, s <> ss)

# every frame's schema; the frames come back
def Cat.scan(fs: List<&1, C.Frame>) -> List<&1, C.Frame> & List<&2, List<&2, S.Field>>:
  match fs:
    case Nil{}:
      (Nil{}, Nil{})
    case f <> t:
      Cat.scan.k(S.Frame.schema(f), Cat.scan(t))

def Cat.bad.k(same: Bool, +i: U32, s: List<&2, S.Field>, s0: List<&2, S.Field>, rest: Maybe<&2, E.Err>) -> Maybe<&2, E.Err>:
  match same:
    case True{}:
      rest
    case False{}:
      Some{Cat.differs(i, s, s0)}

# the first input i (from 1) whose schema differs from input 0's
def Cat.bad(ss: List<&2, List<&2, S.Field>>, +i: U32, +s0: List<&2, S.Field>) -> Maybe<&2, E.Err>:
  match ss:
    case Nil{}:
      None{}
    case +s <> t:
      Cat.bad.k(S.Schema.eq(s, s0), i, s, s0, Cat.bad(t, U32.inc(i), s0))

def Cat.fold.step(r: E.ResT(C.Frame), +i: U32, f: C.Frame) -> E.ResT(C.Frame):
  match r:
    case Fail{e}:
      Fail{e}
    case Done{a}:
      Concat.two(i, a, f)

def Cat.fold(fs: List<&1, C.Frame>, +i: U32, r: E.ResT(C.Frame)) -> E.ResT(C.Frame):
  match fs:
    case Nil{}:
      r
    case f <> t:
      Cat.fold(t, U32.inc(i), Cat.fold.step(r, i, f))

def Concat.frames.b(m: Maybe<&2, E.Err>, f0: C.Frame, fs: List<&1, C.Frame>) -> E.ResT(C.Frame):
  match m:
    case Some{e}:
      Fail{e}
    case None{}:
      Cat.fold(fs, 1, Done{f0})

def Concat.frames.a(r0: C.Frame & List<&2, S.Field>, rs: List<&1, C.Frame> & List<&2, List<&2, S.Field>>) -> E.ResT(C.Frame):
  (f0, +s0) = r0
  (fs, ss) = rs
  Concat.frames.b(Cat.bad(ss, 1, s0), f0, fs)

# the eager concat_vertical: every schema is checked against input 0's first (the first
# differing input i is the error), then the inputs are appended in order, each step checking
# the row cap on the running (saturating) height sum
def Concat.frames(fs: List<&1, C.Frame>) -> E.ResT(C.Frame):
  match fs:
    case Nil{}:
      Fail{Cat.no_inputs()}
    case f <> rest:
      Concat.frames.a(S.Frame.schema(f), Cat.scan(rest))
