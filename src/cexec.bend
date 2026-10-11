# src/cexec.bend -- the chunked runner of the v0.2 engine (plans/M_02.txt W5 / D1-D4, D7; DESIGN.md 16.5).
# OPT-IN: Exec.run_with(Chunked{grain}, p, env) / Lazy.collect_with; Exec.run / Lazy.collect (the
# Reference engine, src/exec.bend) stay the default and the oracle until W8.
#
# Shape. The runner executes the SAME postfix code as Exec (Q.Exec.compile / Q.Exec.mark unchanged, the
# same root shortcuts as Q.Exec.run_phys: Sort + Head, plain Select over Filter) with a second step
# function whose stack holds XF values: a flat v0.1 frame (XFlat) or a chunked frame (XChk, CH.CFrame,
# which exists only here). Conversions are made where an operator needs the other representation, ONE per
# boundary, forked across columns (CH.CFrame.of_frame / to_frame), inside the clock, and counted (CStats):
#   * a row-wise operator (filter, with_columns, a select of expressions that keeps the rows, the Filter +
#     plain Select root) over a frame of more than 2^g rows runs CHUNKED: XFlat input -> of_frame once (an
#     operator that consumes its input converts only the columns it reads or selects), then the frame
#     stays chunked through every compatible operator (filter -> select -> with_columns -> head ...);
#   * head / slice / tail / plain select / drop / rename / concat run on the trees (no row copied except a
#     slice's boundary leaf, CH.CFrame.slice);
#   * sort, group_by, join, unique, a select of literals / aggregations only (one row) run today's flat
#     code behind a flatten boundary (to_frame once, forked across columns; group_by and select flatten only
#     the columns they read); the output stays flat until a chunked operator needs chunks again;
#   * a frame of at most 2^g rows from a Source runs exactly today's flat path: nothing is converted, no
#     fork (a chunked frame of one leaf converts in O(columns): its buffers are moved).
#
# Row-wise operators reuse the FLAT EVALUATOR at every leaf (V.Eval.full / V.Eval.pred / K.Kernel.popcount /
# Q.Exec.fc on a leaf-sized C.Frame: every v0.1 semantic, the fused kernels and their laws at the leaf),
# forked over the frame's tree with ONE balanced parallel let per node (AGENT_BRIEF_M2 rule 3); a
# with_columns / select evaluates ALL its k expressions per leaf in one walk (16.3 F9); a filter is two
# walks (the predicate's mask per leaf, then the per-leaf compaction, Q.Exec.fc: compact3 / compact4). The
# ragged result is rebalanced (CH.CFrame.rebalance, 16.1's occupancy policy) lazily, by the next walk that
# reads it (CX.wi), never before a flatten boundary.
# An aggregation INSIDE a row-wise expression (`x - mean(x)`, `qty > max(qty)`) is evaluated once, by the
# flat evaluator over the columns it reads (borrowed when flat, a flattened copy when chunked), and the
# per-leaf walk sees its value as a literal (CX.hoist).
#
# Errors are v0.1's, text and precedence, by construction:
#   * static errors: before any data work the reference operator runs on a GHOST, a 0-row frame of the
#     input's schema (CX.ghost: static checks depend on the schema only). A ghost that fails sends the
#     operator to the flat path, whose answer is the reference's (the ghost also gives the output schema);
#   * data errors (a failing strict cast: its text names a GLOBAL row): the per-leaf walk BORROWS its input
#     (V.Eval.full hands the leaf frame back, error or not), so the input frame survives the walk whole. If
#     any leaf (or a hoisted aggregation) failed, the input is flattened and the reference operator runs on
#     it: its error is exactly v0.1's (expression order, then instruction order, then lowest row), whichever
#     leaf or lane failed first. The success path never pays for this (no clone beyond the reference's own).
#
# Dictionary columns (one Dict per column) travel through a walk as their code trees (CX.undict: a CU32 of
# the codes, the Dict kept aside and put back by CX.redict): a leaf needs no dictionary unless an
# expression reads the column; then a copy of that Dict is cloned per split point of the walk (D2 rule 4,
# CX.dclone) and wrapped around the leaf's codes for the evaluation, for Dicts of at most CX.dcap() = 4096
# entries (a larger one, or an output that would overwrite a Dictionary column, takes the flat path).
# Leaves whose outputs carry different Dicts are joined by CH.CStrs.cat (Dict.merge + remap, v0.1's rule).
#
# Idioms (DESIGN.md section 9): helpers above callers, no mutual recursion; match only on parameters; a pair
# is opened in a helper's parameters; the two lanes of a parallel let joined by a non-recursive helper.
import Base
import ./dtype.bend as D
import ./err.bend as E
import ./kernels.bend as K
import ./column.bend as C
import ./strs.bend as ST
import ./schema.bend as S
import ./expr.bend as X
import ./analysis.bend as A
import ./eval.bend as V
import ./csv.bend as R
import ./sort.bend as O
import ./groupby.bend as G
import ./join.bend as J
import ./plan.bend as P
import ./table.bend as TV
import ./exec.bend as Q
import ./chunks.bend as CH
import ./ckernels.bend as KC

# ==== the engine selector (DESIGN.md 16.5) ====

type Engine is Data:
  Reference{}
  Chunked{grain: Nat}

# ==== what the runner counts (G6): conversions and their bytes, per-leaf walks, flat operator runs ====
# bytes: 4 per slot of every copied buffer (data, validity mask; a Raw string slot counts as one word)

type CStats is Data:
  CStats{conv_in: U32, bytes_in: U32, conv_out: U32, bytes_out: U32, walks: U32, flat_ops: U32}

def CStats.zero() -> CStats:
  CStats{0, 0, 0, 0, 0, 0}

def CStats.add_in(st: CStats, +b: U32) -> CStats:
  match st:
    case CStats{ci, bi, co, bo, w, fl}:
      CStats{U32.inc(ci), U32.add(bi, b), co, bo, w, fl}

def CStats.add_out(st: CStats, +b: U32) -> CStats:
  match st:
    case CStats{ci, bi, co, bo, w, fl}:
      CStats{ci, bi, U32.inc(co), U32.add(bo, b), w, fl}

def CStats.walk(st: CStats, +k: U32) -> CStats:
  match st:
    case CStats{ci, bi, co, bo, w, fl}:
      CStats{ci, bi, co, bo, U32.add(w, k), fl}

def CStats.flat(st: CStats) -> CStats:
  match st:
    case CStats{ci, bi, co, bo, w, fl}:
      CStats{ci, bi, co, bo, w, U32.inc(fl)}

def CStats.show(st: CStats) -> String:
  match st:
    case CStats{ci, bi, co, bo, w, fl}:
      "conv_in " ++ U32.show(ci) ++ " bytes_in " ++ U32.show(bi) ++ " conv_out " ++ U32.show(co) ++ " bytes_out " ++ U32.show(bo) ++ " walks " ++ U32.show(w) ++ " flat_ops " ++ U32.show(fl)

# ==== the stack's frames ====

type XF is Type:
  XFlat{f: C.Frame}
  XChk{f: CH.CFrame}

# an operator's answer with the runner's counters
type XR is Type:
  XR{st: CStats, r: E.ResT(XF)}

def CX.xr(st: CStats, r: E.ResT(C.Frame)) -> XR:
  match r:
    case Fail{e}:
      XR{st, Fail{e}}
    case Done{f}:
      XR{st, Done{XFlat{f}}}

# ==== schemas, the ghost frame ====

def CX.cdt(c: CH.CColumn) -> CH.CColumn & D.DType:
  match c:
    case CH.CBool{len, v, x}:
      (CH.CBool{len, v, x}, D.TBool{})
    case CH.CU32{len, v, x}:
      (CH.CU32{len, v, x}, D.TU32{})
    case CH.CI32{len, v, x}:
      (CH.CI32{len, v, x}, D.TI32{})
    case CH.CF32{len, v, x}:
      (CH.CF32{len, v, x}, D.TF32{})
    case CH.CStr{len, v, x}:
      (CH.CStr{len, v, x}, D.TStr{})

def CX.csch.k(+n: String, r: CH.CColumn & D.DType, rest: List<&1, CH.CNamed> & List<&2, S.Field>) -> List<&1, CH.CNamed> & List<&2, S.Field>:
  (c, t) = r
  (cs, fs) = rest
  (CH.CNamed{n, c} <> cs, S.Field{n, t} <> fs)

def CX.csch(cols: List<&1, CH.CNamed>) -> List<&1, CH.CNamed> & List<&2, S.Field>:
  match cols:
    case Nil{}:
      (Nil{}, Nil{})
    case CH.CNamed{+n, c} <> rest:
      CX.csch.k(n, CX.cdt(c), CX.csch(rest))

def CX.cschema.k(+h: U32, r: List<&1, CH.CNamed> & List<&2, S.Field>) -> CH.CFrame & List<&2, S.Field>:
  (cols, s) = r
  (CH.CFrame{h, cols}, s)

# the schema of a chunked frame (the frame comes back)
def CX.cschema(f: CH.CFrame) -> CH.CFrame & List<&2, S.Field>:
  match f:
    case CH.CFrame{+h, cols}:
      CX.cschema.k(h, CX.csch(cols))

def CX.xschema.f(r: C.Frame & List<&2, S.Field>) -> XF & List<&2, S.Field>:
  (f, s) = r
  (XFlat{f}, s)

def CX.xschema.c(r: CH.CFrame & List<&2, S.Field>) -> XF & List<&2, S.Field>:
  (f, s) = r
  (XChk{f}, s)

def CX.xschema(x: XF) -> XF & List<&2, S.Field>:
  match x:
    case XFlat{f}:
      CX.xschema.f(S.Frame.schema(f))
    case XChk{f}:
      CX.xschema.c(CX.cschema(f))

# an empty column of a dtype (0 rows, AllValid, one slot)
def CX.gcol(t: D.DType) -> C.Column:
  match t:
    case D.TF32{}:
      C.CF32{0, 0n, C.AllValid{}, Array.new(F32, 0n, 0.0)}
    case D.TStr{}:
      C.CStr{0, 0n, C.AllValid{}, ST.SRaw{Array.new(String, 0n, "")}}
    case other:
      C.Column.mk_w(other, 0, 0n, C.AllValid{}, Array.new(U32, 0n, 0))

def CX.gcols(s: List<&2, S.Field>) -> List<&1, C.Named>:
  match s:
    case Nil{}:
      Nil{}
    case S.Field{n, t} <> rest:
      C.Named{n, CX.gcol(t)} <> CX.gcols(rest)

# the GHOST of a schema: a frame of 0 rows with exactly these columns. Static checks read the schema only,
# so the reference operator over the ghost fails with the operator's static error, if it has one, before
# any data is touched; otherwise it answers the output schema.
def CX.ghost(s: List<&2, S.Field>) -> C.Frame:
  C.Frame{0, CX.gcols(s)}

type GO is Data:
  GFail{e: E.Err}
  GOk{s: List<&2, S.Field>}

def CX.gok.k(r: C.Frame & List<&2, S.Field>) -> GO:
  (f, s) = r
  GOk{s}

def CX.gok(r: E.ResT(C.Frame)) -> GO:
  match r:
    case Fail{e}:
      GFail{e}
    case Done{f}:
      CX.gok.k(S.Frame.schema(f))

# ==== expression facts (pure Data) ====

# no aggregation anywhere in e: the expression is row-local (every row of the result depends on that row
# of the input only), so evaluating it per leaf is evaluating it on the whole frame, leaf by leaf
def CX.rw(e: X.Expr) -> Bool:
  match e:
    case X.Col{n}:
      True{}
    case X.Lit{v}:
      True{}
    case X.Alias{e2, n}:
      CX.rw(e2)
    case X.Cast{e2, t}:
      CX.rw(e2)
    case X.TryCast{e2, t}:
      CX.rw(e2)
    case X.Un{op, e2}:
      CX.rw(e2)
    case X.Bin{op, a, b}:
      Bool.and(CX.rw(a), CX.rw(b))
    case X.FillNull{e2, v}:
      Bool.and(CX.rw(e2), CX.rw(v))
    case X.Agg{op, e2}:
      False{}
    case X.When{c, a, b}:
      Bool.and(CX.rw(c), Bool.and(CX.rw(a), CX.rw(b)))
    case X.IsIn{e2, vs}:
      CX.rw(e2)
    case X.Clip{e2, lo, hi}:
      CX.rw(e2)
    case X.StrPred{op, e2, p}:
      CX.rw(e2)

def CX.rws(es: List<&2, X.Expr>) -> Bool:
  match es:
    case Nil{}:
      True{}
    case e <> t:
      Bool.and(CX.rw(e), CX.rws(t))

# does any name of xs occur in ns
def CX.any_in(xs: List<&2, String>, +ns: List<&2, String>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case x <> t:
      Bool.or(C.Names.has(ns, x), CX.any_in(t, ns))

# no field of s that the names select (every field when all) has the Str dtype
def CX.nostr(s: List<&2, S.Field>, +all: Bool, +ns: List<&2, String>) -> Bool:
  match s:
    case Nil{}:
      True{}
    case S.Field{+n, t} <> rest:
      Bool.and(Bool.not(Bool.and(Bool.or(all, C.Names.has(ns, n)), D.DType.eq(t, D.TStr{}))), CX.nostr(rest, all, ns))

def CX.nonempty(es: List<&2, X.Expr>) -> Bool:
  match es:
    case Nil{}:
      False{}
    case e <> t:
      True{}

# ==== frame facts: height, width, buffers (the conversion bytes), Dictionary columns ====

def CX.vbufs(v: C.Valid) -> C.Valid & U32:
  match v:
    case C.AllValid{}:
      (C.AllValid{}, 1)
    case C.Mask{m}:
      (C.Mask{m}, 2)

def CX.colbufs.k(t: D.DType, +n: U32, d: Nat, x: Array<U32>, r: C.Valid & U32) -> C.Column & U32:
  (v, +b) = r
  (C.Column.mk_w(t, n, d, v, x), b)

def CX.colbufs.f(+n: U32, d: Nat, x: Array<F32>, r: C.Valid & U32) -> C.Column & U32:
  (v, +b) = r
  (C.CF32{n, d, v, x}, b)

def CX.colbufs.s(+n: U32, d: Nat, x: ST.Strs, r: C.Valid & U32) -> C.Column & U32:
  (v, +b) = r
  (C.CStr{n, d, v, x}, b)

# the buffers of a flat column (data, plus the mask of a Mask column)
def CX.colbufs(c: C.Column) -> C.Column & U32:
  match c:
    case C.CBool{n, d, v, x}:
      CX.colbufs.k(D.TBool{}, n, d, x, CX.vbufs(v))
    case C.CU32{n, d, v, x}:
      CX.colbufs.k(D.TU32{}, n, d, x, CX.vbufs(v))
    case C.CI32{n, d, v, x}:
      CX.colbufs.k(D.TI32{}, n, d, x, CX.vbufs(v))
    case C.CF32{n, d, v, x}:
      CX.colbufs.f(n, d, x, CX.vbufs(v))
    case C.CStr{n, d, v, x}:
      CX.colbufs.s(n, d, x, CX.vbufs(v))

def CX.fbufs.k(+n: String, r: C.Column & U32, rest: List<&1, C.Named> & U32) -> List<&1, C.Named> & U32:
  (c, +a) = r
  (cs, +b) = rest
  (C.Named{n, c} <> cs, U32.add(a, b))

def CX.fbufs(cols: List<&1, C.Named>) -> List<&1, C.Named> & U32:
  match cols:
    case Nil{}:
      (Nil{}, 0)
    case C.Named{+n, c} <> rest:
      CX.fbufs.k(n, CX.colbufs(c), CX.fbufs(rest))

def CX.cvbufs(v: CH.CValid) -> CH.CValid & U32:
  match v:
    case CH.CAllValid{}:
      (CH.CAllValid{}, 1)
    case CH.CMask{m}:
      (CH.CMask{m}, 2)

# a chunked column with another validity (the data tree kept)
def CX.cset_v(c: CH.CColumn, v: CH.CValid) -> CH.CColumn:
  match c:
    case CH.CBool{len, w, x}:
      CH.CBool{len, v, x}
    case CH.CU32{len, w, x}:
      CH.CU32{len, v, x}
    case CH.CI32{len, w, x}:
      CH.CI32{len, v, x}
    case CH.CF32{len, w, x}:
      CH.CF32{len, v, x}
    case CH.CStr{len, w, x}:
      CH.CStr{len, v, x}

def CX.ccolbufs.k(c: CH.CColumn, r: CH.CValid & U32) -> CH.CColumn & U32:
  (v, +b) = r
  (CX.cset_v(c, v), b)

def CX.ctake_v(c: CH.CColumn) -> CH.CColumn & CH.CValid:
  match c:
    case CH.CBool{len, v, x}:
      (CH.CBool{len, CH.CAllValid{}, x}, v)
    case CH.CU32{len, v, x}:
      (CH.CU32{len, CH.CAllValid{}, x}, v)
    case CH.CI32{len, v, x}:
      (CH.CI32{len, CH.CAllValid{}, x}, v)
    case CH.CF32{len, v, x}:
      (CH.CF32{len, CH.CAllValid{}, x}, v)
    case CH.CStr{len, v, x}:
      (CH.CStr{len, CH.CAllValid{}, x}, v)

def CX.ccolbufs.a(r: CH.CColumn & CH.CValid) -> CH.CColumn & U32:
  (c, v) = r
  CX.ccolbufs.k(c, CX.cvbufs(v))

def CX.cbufs.k(+n: String, r: CH.CColumn & U32, rest: List<&1, CH.CNamed> & U32) -> List<&1, CH.CNamed> & U32:
  (c, +a) = r
  (cs, +b) = rest
  (CH.CNamed{n, c} <> cs, U32.add(a, b))

def CX.cbufs(cols: List<&1, CH.CNamed>) -> List<&1, CH.CNamed> & U32:
  match cols:
    case Nil{}:
      (Nil{}, 0)
    case CH.CNamed{+n, c} <> rest:
      CX.cbufs.k(n, CX.ccolbufs.a(CX.ctake_v(c)), CX.cbufs(rest))

# the Dictionary-storage Str columns: every name (ns) and the names of those whose Dict has more than
# CX.dcap() entries (bs: an expression reading one of these runs flat, a per-leaf Dict clone would cost
# more than the walk saves)
def CX.dcap() -> U32:
  4096

def CX.dsz(+n: U32, d: Nat, v: C.Valid, codes: Array<U32>, r: ST.Dict & U32) -> C.Column & U32:
  (dict, +k) = r
  (C.CStr{n, d, v, ST.SDict{codes, dict}}, Bool.pick(U32, U32.is_le(k, CX.dcap()), 1, 2))

# 0: not a Dictionary column, 1: a Dictionary of at most CX.dcap() entries, 2: a larger one
def CX.fdict.c(c: C.Column) -> C.Column & U32:
  match c:
    case C.CStr{+n, d, v, s}:
      match s:
        case ST.SDict{codes, dict}:
          CX.dsz(n, d, v, codes, ST.Dict.size(dict))
        case ST.SRaw{a}:
          (C.CStr{n, d, v, ST.SRaw{a}}, 0)
    case other:
      (other, 0)

type DL is Data:
  DL{ns: List<&2, String>, bs: List<&2, String>}

def CX.dl(+k: U32, +n: String, l: DL) -> DL:
  match k:
    case 0:
      l
    case 1:
      match l:
        case DL{ns, bs}:
          DL{n <> ns, bs}
    case _:
      match l:
        case DL{ns, bs}:
          DL{n <> ns, n <> bs}

def CX.fdict.k(+n: String, r: C.Column & U32, rest: List<&1, C.Named> & DL) -> List<&1, C.Named> & DL:
  (c, +k) = r
  (cs, l) = rest
  (C.Named{n, c} <> cs, CX.dl(k, n, l))

def CX.fdict(cols: List<&1, C.Named>) -> List<&1, C.Named> & DL:
  match cols:
    case Nil{}:
      (Nil{}, DL{Nil{}, Nil{}})
    case C.Named{+n, c} <> rest:
      CX.fdict.k(n, CX.fdict.c(c), CX.fdict(rest))

def CX.cdsz(+n: U32, v: CH.CValid, codes: CH.CW, r: ST.Dict & U32) -> CH.CColumn & U32:
  (dict, +k) = r
  (CH.CStr{n, v, CH.CSDict{codes, dict}}, Bool.pick(U32, U32.is_le(k, CX.dcap()), 1, 2))

def CX.cdict.c(c: CH.CColumn) -> CH.CColumn & U32:
  match c:
    case CH.CStr{+n, v, s}:
      match s:
        case CH.CSDict{codes, dict}:
          CX.cdsz(n, v, codes, ST.Dict.size(dict))
        case CH.CSRaw{t}:
          (CH.CStr{n, v, CH.CSRaw{t}}, 0)
    case other:
      (other, 0)

def CX.cdict.k(+n: String, r: CH.CColumn & U32, rest: List<&1, CH.CNamed> & DL) -> List<&1, CH.CNamed> & DL:
  (c, +k) = r
  (cs, l) = rest
  (CH.CNamed{n, c} <> cs, CX.dl(k, n, l))

def CX.cdict(cols: List<&1, CH.CNamed>) -> List<&1, CH.CNamed> & DL:
  match cols:
    case Nil{}:
      (Nil{}, DL{Nil{}, Nil{}})
    case CH.CNamed{+n, c} <> rest:
      CX.cdict.k(n, CX.cdict.c(c), CX.cdict(rest))

# what the runner needs to know of a frame: its height, its width, chunked or not, its Dictionary columns
type XI is Data:
  XI{h: U32, w: U32, chk: Bool, dicts: DL}

def CX.len(-A: Type, xs: List<&1, A>) -> List<&1, A> & U32:
  CH.Lst.len(A, xs, 0, Nil{})

def CX.xinfo.f2(+h: U32, +ds: DL, r: List<&1, C.Named> & U32) -> XF & XI:
  (cols, +w) = r
  (XFlat{C.Frame{h, cols}}, XI{h, w, False{}, ds})

def CX.xinfo.f(+h: U32, r: List<&1, C.Named> & DL) -> XF & XI:
  (cols, +ds) = r
  CX.xinfo.f2(h, ds, CX.len(C.Named, cols))

def CX.xinfo.c2(+h: U32, +ds: DL, r: List<&1, CH.CNamed> & U32) -> XF & XI:
  (cols, +w) = r
  (XChk{CH.CFrame{h, cols}}, XI{h, w, True{}, ds})

def CX.xinfo.c(+h: U32, r: List<&1, CH.CNamed> & DL) -> XF & XI:
  (cols, +ds) = r
  CX.xinfo.c2(h, ds, CX.len(CH.CNamed, cols))

def CX.xinfo(x: XF) -> XF & XI:
  match x:
    case XFlat{f}:
      match f:
        case C.Frame{+h, cols}:
          CX.xinfo.f(h, CX.fdict(cols))
    case XChk{f}:
      match f:
        case CH.CFrame{+h, cols}:
          CX.xinfo.c(h, CX.cdict(cols))

# the chunked route: at least one column, the frame already chunked or more than 2^g rows, no large
# Dictionary column read by the expressions (refs; a small one is cloned per split point of the walk) and
# no Dictionary column overwritten by an output (outs)
def CX.route(+g: Nat, +refs: List<&2, String>, +outs: List<&2, String>, i: XI) -> Bool:
  match i:
    case XI{+h, +w, +chk, ds}:
      match ds:
        case DL{+ns, +bs}:
          Bool.and(U32.is_ne(w, 0), Bool.and(Bool.or(chk, U32.is_lt(U32.shln(1, g), h)), Bool.not(Bool.or(CX.any_in(refs, bs), CX.any_in(outs, ns)))))

# ==== conversions (counted) ====

def CX.cnt_in(st: CStats, copy: Bool, +b: U32) -> CStats:
  match copy:
    case True{}:
      CStats.add_in(st, b)
    case False{}:
      st

def CX.cnt_out(st: CStats, copy: Bool, +b: U32) -> CStats:
  match copy:
    case True{}:
      CStats.add_out(st, b)
    case False{}:
      st

def CX.of.b(+g: Nat, st: CStats, +h: U32, r: List<&1, C.Named> & U32) -> CStats & CH.CFrame:
  (cols, +nb) = r
  (CX.cnt_in(st, U32.is_lt(U32.shln(1, g), h), U32.mul(U32.mul(4, h), nb)), CH.CFrame.of_frame(g, C.Frame{h, cols}))

# a flat frame chunked at grain g (CH.CFrame.of_frame: forked across columns); a frame of at most 2^g rows
# becomes one leaf per column, its buffers moved (not counted)
def CX.of(+g: Nat, st: CStats, f: C.Frame) -> CStats & CH.CFrame:
  match f:
    case C.Frame{+h, cols}:
      CX.of.b(g, st, h, CX.fbufs(cols))

def CX.to.e(st: CStats, +leaves: U32, +h: U32, r: List<&1, CH.CNamed> & U32) -> CStats & C.Frame:
  (cols, +nb) = r
  (CX.cnt_out(st, U32.is_lt(1, leaves), U32.mul(U32.mul(4, h), nb)), CH.CFrame.to_frame(CH.CFrame{h, cols}))

def CX.to.d(st: CStats, +leaves: U32, +h: U32, f: CH.CFrame) -> CStats & C.Frame:
  match f:
    case CH.CFrame{h2, cols}:
      CX.to.e(st, leaves, h, CX.cbufs(cols))

def CX.to.c(st: CStats, +leaves: U32, r: CH.CFrame & U32) -> CStats & C.Frame:
  (f, +h) = r
  CX.to.d(st, leaves, h, f)

def CX.to.b(st: CStats, r: CH.CFrame & U32) -> CStats & C.Frame:
  (f, +leaves) = r
  CX.to.c(st, leaves, CH.CFrame.height(f))

# a chunked frame flattened (CH.CFrame.to_frame: forked across columns); a one-leaf frame's buffers are
# moved (not counted)
def CX.to(st: CStats, f: CH.CFrame) -> CStats & C.Frame:
  CX.to.b(st, CH.CFrame.leaves(f))

def CX.xflat(st: CStats, x: XF) -> CStats & C.Frame:
  match x:
    case XFlat{f}:
      (st, f)
    case XChk{f}:
      CX.to(st, f)

def CX.xchk(+g: Nat, st: CStats, x: XF) -> CStats & CH.CFrame:
  match x:
    case XFlat{f}:
      CX.of(g, st, f)
    case XChk{f}:
      (st, f)

# ==== the flat path: today's operator over the flattened frame ====

# the flat operators the runner falls back to: a one-input instruction (Q.Exec.unary), the Filter + plain
# Select root step (Q.Exec.fs), group_by over the columns it reads
type FOp is Data:
  FUn{i: Q.Instr}
  FFs{pred: X.Expr, es: List<&2, X.Expr>}

def CX.fop(op: FOp, f: C.Frame) -> E.ResT(C.Frame):
  match op:
    case FUn{i}:
      Q.Exec.unary(i, f)
    case FFs{pred, es}:
      Q.Exec.fs(f, pred, es)

def CX.flat.k(op: FOp, r: CStats & C.Frame) -> XR:
  (st, f) = r
  CX.xr(CStats.flat(st), CX.fop(op, f))

def CX.flat(op: FOp, st: CStats, x: XF) -> XR:
  CX.flat.k(op, CX.xflat(st, x))

# ==== Dictionary columns through a walk: the codes as a CU32, the Dict kept aside ====

type DN is Type:
  DN{name: String, d: ST.Dict}

type UD is Type:
  UD{cols: List<&1, CH.CNamed>, ds: List<&1, DN>}

def CX.undict.k(+nm: String, r: UD, c: CH.CColumn) -> UD:
  match r:
    case UD{cols, ds}:
      match c:
        case CH.CStr{len, v, s}:
          match s:
            case CH.CSDict{codes, dict}:
              UD{CH.CNamed{nm, CH.CU32{len, v, codes}} <> cols, DN{nm, dict} <> ds}
            case CH.CSRaw{t}:
              UD{CH.CNamed{nm, CH.CStr{len, v, CH.CSRaw{t}}} <> cols, ds}
        case other:
          UD{CH.CNamed{nm, other} <> cols, ds}

def CX.undict(cols: List<&1, CH.CNamed>) -> UD:
  match cols:
    case Nil{}:
      UD{Nil{}, Nil{}}
    case CH.CNamed{nm, c} <> rest:
      CX.undict.k(nm, CX.undict(rest), c)

def CX.dtake.k(eq: Bool, nm: String, d: ST.Dict, r: List<&1, DN> & Maybe<&1, ST.Dict>) -> List<&1, DN> & Maybe<&1, ST.Dict>:
  match eq:
    case True{}:
      (ds, m) = r
      (ds, Some{d})
    case False{}:
      (ds, m) = r
      (DN{nm, d} <> ds, m)

# take the Dict of a name out of the list (names are unique)
def CX.dtake(ds: List<&1, DN>, +name: String) -> List<&1, DN> & Maybe<&1, ST.Dict>:
  match ds:
    case Nil{}:
      (Nil{}, None{})
    case DN{+nm, d} <> rest:
      CX.dtake.k(String.eq(nm, name), nm, d, CX.dtake(rest, name))

def CX.redict.c(m: Maybe<&1, ST.Dict>, c: CH.CColumn) -> CH.CColumn:
  match m:
    case None{}:
      c
    case Some{d}:
      match c:
        case CH.CU32{len, v, codes}:
          CH.CStr{len, v, CH.CSDict{codes, d}}
        case other:
          other

type RD is Type:
  RD{ds: List<&1, DN>, acc: List<&1, CH.CNamed>}

def CX.redict.s2(+nm: String, c: CH.CColumn, acc: List<&1, CH.CNamed>, r: List<&1, DN> & Maybe<&1, ST.Dict>) -> RD:
  (ds, m) = r
  RD{ds, CH.CNamed{nm, CX.redict.c(m, c)} <> acc}

def CX.redict.step(+nm: String, c: CH.CColumn, st: RD) -> RD:
  match st:
    case RD{ds, acc}:
      CX.redict.s2(nm, c, acc, CX.dtake(ds, nm))

def CX.redict.go(cols: List<&1, CH.CNamed>, st: RD) -> List<&1, CH.CNamed>:
  match cols:
    case Nil{}:
      match st:
        case RD{ds, acc}:
          List.reverse(&1, CH.CNamed, acc)
    case CH.CNamed{+nm, c} <> rest:
      CX.redict.go(rest, CX.redict.step(nm, c, st))

# every column that left a Dict aside gets it back (a dropped column's Dict is dropped)
def CX.redict(cols: List<&1, CH.CNamed>, ds: List<&1, DN>) -> List<&1, CH.CNamed>:
  CX.redict.go(cols, RD{ds, Nil{}})

def CX.redictf(f: CH.CFrame, ds: List<&1, DN>) -> CH.CFrame:
  match f:
    case CH.CFrame{h, cols}:
      CH.CFrame{h, CX.redict(cols, ds)}

# ---- the Dicts a walk's expressions read: one clone per split point (D2 rule 4), wrapped around the leaf's
# codes for the evaluation and taken off again (the leaf frame keeps the codes) ----

def CX.dclone.k(+nm: String, r: ST.Dict & ST.Dict, rest: List<&1, DN> & List<&1, DN>) -> List<&1, DN> & List<&1, DN>:
  (a, b) = r
  (ra, rb) = rest
  (DN{nm, a} <> ra, DN{nm, b} <> rb)

# a list of Dicts and its copy
def CX.dclone(ds: List<&1, DN>) -> List<&1, DN> & List<&1, DN>:
  match ds:
    case Nil{}:
      (Nil{}, Nil{})
    case DN{+nm, d} <> rest:
      CX.dclone.k(nm, ST.Dict.clone(d), CX.dclone(rest))

def CX.rclone.h(+nm: String, r: ST.Dict & ST.Dict, rest: List<&1, DN> & List<&1, DN>) -> List<&1, DN> & List<&1, DN>:
  (a, b) = r
  (ra, rb) = rest
  (DN{nm, a} <> ra, DN{nm, b} <> rb)

def CX.rclone.k(hit: Bool, +nm: String, d: ST.Dict, rest: List<&1, DN> & List<&1, DN>) -> List<&1, DN> & List<&1, DN>:
  match hit:
    case True{}:
      CX.rclone.h(nm, ST.Dict.clone(d), rest)
    case False{}:
      (ra, rb) = rest
      (DN{nm, d} <> ra, rb)

# the Dicts set aside (back) and a copy of those the expressions read (refs)
def CX.rclone(ds: List<&1, DN>, +refs: List<&2, String>) -> List<&1, DN> & List<&1, DN>:
  match ds:
    case Nil{}:
      (Nil{}, Nil{})
    case DN{+nm, d} <> rest:
      CX.rclone.k(C.Names.has(refs, nm), nm, d, CX.rclone(rest, refs))

def CX.wrap.c(m: Maybe<&1, ST.Dict>, c: C.Column) -> C.Column:
  match m:
    case None{}:
      c
    case Some{d}:
      match c:
        case C.CU32{n, dd, v, codes}:
          C.CStr{n, dd, v, ST.SDict{codes, d}}
        case other:
          other

type WR2 is Type:
  WR2{rd: List<&1, DN>, acc: List<&1, C.Named>}

def CX.wrap.s2(+nm: String, c: C.Column, acc: List<&1, C.Named>, r: List<&1, DN> & Maybe<&1, ST.Dict>) -> WR2:
  (rd, m) = r
  WR2{rd, C.Named{nm, CX.wrap.c(m, c)} <> acc}

def CX.wrap.step(+nm: String, c: C.Column, st: WR2) -> WR2:
  match st:
    case WR2{rd, acc}:
      CX.wrap.s2(nm, c, acc, CX.dtake(rd, nm))

def CX.wrap.go(cols: List<&1, C.Named>, st: WR2) -> List<&1, C.Named>:
  match cols:
    case Nil{}:
      match st:
        case WR2{rd, acc}:
          List.reverse(&1, C.Named, acc)
    case C.Named{+nm, c} <> rest:
      CX.wrap.go(rest, CX.wrap.step(nm, c, st))

# a leaf frame with the Dict of every read Dictionary column around its codes
def CX.wrapf(f: C.Frame, rd: List<&1, DN>) -> C.Frame:
  match f:
    case C.Frame{h, cols}:
      C.Frame{h, CX.wrap.go(cols, WR2{rd, Nil{}})}

def CX.unw.c(c: C.Column) -> C.Column:
  match c:
    case C.CStr{n, d, v, s}:
      match s:
        case ST.SDict{codes, dict}:
          C.CU32{n, d, v, codes}
        case ST.SRaw{a}:
          C.CStr{n, d, v, ST.SRaw{a}}
    case other:
      other

def CX.unw(cols: List<&1, C.Named>) -> List<&1, C.Named>:
  match cols:
    case Nil{}:
      Nil{}
    case C.Named{n, c} <> rest:
      C.Named{n, CX.unw.c(c)} <> CX.unw(rest)

# the leaf frame's codes again (the leaf's Dict clones dropped)
def CX.unwf(f: C.Frame) -> C.Frame:
  match f:
    case C.Frame{h, cols}:
      C.Frame{h, CX.unw(cols)}

# ==== cutting a frame at the root of its trees: one leaf position (flat columns) or two halves ====

def CX.vleaf(v: CH.CValid) -> C.Valid:
  match v:
    case CH.CAllValid{}:
      C.AllValid{}
    case CH.CMask{m}:
      match m:
        case CH.WL{n, d, a}:
          C.Mask{a}
        case CH.WN{rows, lrows, l, r}:
          C.AllValid{}

def CX.vsplit(v: CH.CValid) -> CH.CValid & CH.CValid:
  match v:
    case CH.CAllValid{}:
      (CH.CAllValid{}, CH.CAllValid{})
    case CH.CMask{m}:
      match m:
        case CH.WN{rows, lrows, l, r}:
          (CH.CMask{l}, CH.CMask{r})
        case CH.WL{n, d, a}:
          (CH.CMask{CH.WL{n, d, a}}, CH.CAllValid{})

# one column at the root: its leaf as a flat column, or its two subtrees (the validity cut the same way)
type CC2 is Type:
  CCL{c: C.Column}
  CCN{rows: U32, lrows: U32, a: CH.CColumn, b: CH.CColumn}

def CX.ccut.w(+t: D.DType, +rows: U32, +lrows: U32, l: CH.CW, r: CH.CW, vv: CH.CValid & CH.CValid) -> CC2:
  (va, vb) = vv
  CCN{rows, lrows, CH.CColumn.mk_w(t, lrows, va, l), CH.CColumn.mk_w(t, U32.sub(rows, lrows), vb, r)}

def CX.ccut.f(+rows: U32, +lrows: U32, l: CH.CF, r: CH.CF, vv: CH.CValid & CH.CValid) -> CC2:
  (va, vb) = vv
  CCN{rows, lrows, CH.CF32{lrows, va, l}, CH.CF32{U32.sub(rows, lrows), vb, r}}

def CX.ccut.s(+rows: U32, +lrows: U32, l: CH.CS, r: CH.CS, vv: CH.CValid & CH.CValid) -> CC2:
  (va, vb) = vv
  CCN{rows, lrows, CH.CStr{lrows, va, CH.CSRaw{l}}, CH.CStr{U32.sub(rows, lrows), vb, CH.CSRaw{r}}}

def CX.ccut.cw(t: D.DType, v: CH.CValid, x: CH.CW) -> CC2:
  match x:
    case CH.WL{n, d, a}:
      CCL{C.Column.mk_w(t, n, d, CX.vleaf(v), a)}
    case CH.WN{+rows, +lrows, l, r}:
      CX.ccut.w(t, rows, lrows, l, r, CX.vsplit(v))

def CX.ccut.cf(v: CH.CValid, x: CH.CF) -> CC2:
  match x:
    case CH.FL{n, d, a}:
      CCL{C.CF32{n, d, CX.vleaf(v), a}}
    case CH.FN{+rows, +lrows, l, r}:
      CX.ccut.f(rows, lrows, l, r, CX.vsplit(v))

def CX.ccut.cs(v: CH.CValid, x: CH.CS) -> CC2:
  match x:
    case CH.SL{n, d, a}:
      CCL{C.CStr{n, d, CX.vleaf(v), ST.SRaw{a}}}
    case CH.SN{+rows, +lrows, l, r}:
      CX.ccut.s(rows, lrows, l, r, CX.vsplit(v))

# (a Dictionary column never reaches a cut: CX.undict ran first; a leaf of codes keeps its Dict, a node
# would need it on both sides and keeps it on the left, the right side decoded to nothing: unreachable)
def CX.ccut.cd(v: CH.CValid, x: CH.CW, dict: ST.Dict) -> CC2:
  match x:
    case CH.WL{n, d, a}:
      CCL{C.CStr{n, d, CX.vleaf(v), ST.SDict{a, dict}}}
    case CH.WN{+rows, +lrows, l, r}:
      CX.ccut.w(D.TU32{}, rows, lrows, l, r, CX.vsplit(v))

def CX.ccut(c: CH.CColumn) -> CC2:
  match c:
    case CH.CBool{len, v, x}:
      CX.ccut.cw(D.TBool{}, v, x)
    case CH.CU32{len, v, x}:
      CX.ccut.cw(D.TU32{}, v, x)
    case CH.CI32{len, v, x}:
      CX.ccut.cw(D.TI32{}, v, x)
    case CH.CF32{len, v, x}:
      CX.ccut.cf(v, x)
    case CH.CStr{len, v, x}:
      match x:
        case CH.CSRaw{t}:
          CX.ccut.cs(v, t)
        case CH.CSDict{codes, dict}:
          CX.ccut.cd(v, codes, dict)

# every column of a frame cut at the root (WFCFrame: all leaves or all nodes with the same counts)
type Cuts is Type:
  CsE{}
  CsL{cols: List<&1, C.Named>}
  CsN{rows: U32, lrows: U32, a: List<&1, CH.CNamed>, b: List<&1, CH.CNamed>}

def CX.cuts.k(+nm: String, c: CC2, r: Cuts) -> Cuts:
  match c r:
    case CCL{x} CsE{}:
      CsL{C.Named{nm, x} <> Nil{}}
    case CCL{x} CsL{cs}:
      CsL{C.Named{nm, x} <> cs}
    case CCN{rows, lrows, a, b} CsE{}:
      CsN{rows, lrows, CH.CNamed{nm, a} <> Nil{}, CH.CNamed{nm, b} <> Nil{}}
    case CCN{x1, x2, a, b} CsN{rows, lrows, ca, cb}:
      CsN{rows, lrows, CH.CNamed{nm, a} <> ca, CH.CNamed{nm, b} <> cb}
    case x y:
      y

def CX.cuts(cols: List<&1, CH.CNamed>) -> Cuts:
  match cols:
    case Nil{}:
      CsE{}
    case CH.CNamed{nm, c} <> rest:
      CX.cuts.k(nm, CX.ccut(c), CX.cuts(rest))

type Cut is Type:
  CutL{f: C.Frame}
  CutN{rows: U32, lrows: U32, a: CH.CFrame, b: CH.CFrame}

def CX.cut.k(+h: U32, r: Cuts) -> Cut:
  match r:
    case CsE{}:
      CutL{C.Frame{h, Nil{}}}
    case CsL{cs}:
      CutL{C.Frame{h, cs}}
    case CsN{+rows, +lrows, a, b}:
      CutN{rows, lrows, CH.CFrame{lrows, a}, CH.CFrame{U32.sub(rows, lrows), b}}

# a chunked frame at the root of its trees
def CX.cut(f: CH.CFrame) -> Cut:
  match f:
    case CH.CFrame{+h, cols}:
      CX.cut.k(h, CX.cuts(cols))

# ---- a leaf-sized flat frame back as a one-leaf chunked frame (buffers moved, nothing copied) ----

def CX.lv(+n: U32, +d: Nat, v: C.Valid) -> CH.CValid:
  match v:
    case C.AllValid{}:
      CH.CAllValid{}
    case C.Mask{m}:
      CH.CMask{CH.WL{n, d, m}}

def CX.lcol(c: C.Column) -> CH.CColumn:
  match c:
    case C.CBool{+n, +d, v, x}:
      CH.CBool{n, CX.lv(n, d, v), CH.WL{n, d, x}}
    case C.CU32{+n, +d, v, x}:
      CH.CU32{n, CX.lv(n, d, v), CH.WL{n, d, x}}
    case C.CI32{+n, +d, v, x}:
      CH.CI32{n, CX.lv(n, d, v), CH.WL{n, d, x}}
    case C.CF32{+n, +d, v, x}:
      CH.CF32{n, CX.lv(n, d, v), CH.FL{n, d, x}}
    case C.CStr{+n, +d, v, s}:
      match s:
        case ST.SRaw{a}:
          CH.CStr{n, CX.lv(n, d, v), CH.CSRaw{CH.SL{n, d, a}}}
        case ST.SDict{codes, dict}:
          CH.CStr{n, CX.lv(n, d, v), CH.CSDict{CH.WL{n, d, codes}, dict}}

def CX.lcols(cols: List<&1, C.Named>) -> List<&1, CH.CNamed>:
  match cols:
    case Nil{}:
      Nil{}
    case C.Named{n, c} <> rest:
      CH.CNamed{n, CX.lcol(c)} <> CX.lcols(rest)

def CX.lframe(f: C.Frame) -> CH.CFrame:
  match f:
    case C.Frame{h, cols}:
      CH.CFrame{h, CX.lcols(cols)}

# two chunked frames side by side as one node per tree (a's rows then b's; the same columns in the same
# order: every lane of a walk answers the same schema). CH.CCols.cat joins the validity of an AllValid
# side with a Mask side by a ones tree of that side's shape.
def CX.fj(a: CH.CFrame, b: CH.CFrame) -> CH.CFrame:
  match a:
    case CH.CFrame{+ha, ca}:
      match b:
        case CH.CFrame{+hb, cb}:
          CH.CFrame{U32.add(ha, hb), CH.CCols.cat(U32.add(ha, hb), ha, ca, cb)}

# an expression over a leaf frame as the reference operators evaluate it since W4 (Eval.slot.mv: the type
# check, Eval.mark with nothing movable, the peephole post-pass Eval.fuse and Eval.runz: the fused kernels),
# every 1-row result broadcast to the leaf's rows; the leaf frame comes back whole, error or not (no
# column is moved: all = False, dead = [])
def CX.efull(f: C.Frame, +e: X.Expr) -> C.Frame & E.ResT(C.Column):
  V.Eval.mode.a(True{}, V.Eval.slot.mv(f, e, False{}, Nil{}, Nil{}))

# ==== walk 1 of a filter: the predicate's mask per leaf (the input borrowed) ====

# the per-leaf masks and kept counts, in the frame's shape
type MT is Type:
  ML{m: Array<U32>, kept: U32}
  MN{l: MT, r: MT}
  MX{}

type W1 is Type:
  W1{f: CH.CFrame, m: MT, ok: Bool}

def CX.p1.k(f: C.Frame, r: Array<U32> & U32) -> W1:
  (m, +kept) = r
  W1{CX.lframe(f), ML{m, kept}, True{}}

def CX.p1.m(f: C.Frame, r: Array<U32> & U32) -> W1:
  (m, +n) = r
  CX.p1.k(f, K.Kernel.popcount(n, m))

def CX.p1.c(f: C.Frame, rc: E.ResT(C.Column)) -> W1:
  match rc:
    case Fail{e}:
      W1{CX.lframe(f), MX{}, False{}}
    case Done{c}:
      CX.p1.m(f, V.Eval.pred(c))

def CX.p1.a(r: C.Frame & E.ResT(C.Column)) -> W1:
  (f, rc) = r
  CX.p1.c(CX.unwf(f), rc)

# the F5 passes' state (Eval.f5.go: one pred_count loop per conjunct over the borrowed columns): the leaf
# frame is in it whether a pass failed or not
def CX.p1.f5(st: V.F5St) -> W1:
  match st:
    case V.F5St{f, m, +k, err}:
      match err:
        case None{}:
          W1{CX.lframe(CX.unwf(f)), ML{m, k}, True{}}
        case Some{e}:
          W1{CX.lframe(CX.unwf(f)), MX{}, False{}}

def CX.p1.f5h(ps: List<&2, V.P5>, r: C.Frame & U32) -> W1:
  (f, +h) = r
  CX.p1.f5(V.Eval.f5.go(ps, h, V.F5St{f, V.Eval.fz.ones(), 0, None{}}))

def CX.p1.h(+pred: X.Expr, f: C.Frame, plan: Maybe<&2, List<&2, V.P5>>) -> W1:
  match plan:
    case Some{ps}:
      CX.p1.f5h(ps, C.Frame.height(f))
    case None{}:
      CX.p1.a(CX.efull(f, pred))

def CX.p1.s(+pred: X.Expr, r: C.Frame & List<&2, S.Field>) -> W1:
  (f, +s) = r
  CX.p1.h(pred, f, V.Eval.f5.plan(pred, s))

# a leaf: Eval.filter.mask's chain on the leaf frame (the F5 pred_count passes when the predicate is a
# conjunction of bool columns and column-op-literal comparisons, Eval.f5.plan; else Eval.full, Eval.pred,
# popcount), by the steps that hand the leaf frame back whole, error or not (Eval.filter.mask itself
# answers a bare Fail; the borrow is what the error rerun needs)
def CX.p1.leaf(+pred: X.Expr, rd: List<&1, DN>, f: C.Frame) -> W1:
  CX.p1.s(pred, S.Frame.schema(CX.wrapf(f, rd)))

def CX.p1.j(x: W1, y: W1) -> W1:
  match x:
    case W1{fa, ma, ka}:
      match y:
        case W1{fb, mb, kb}:
          W1{CX.fj(fa, fb), MN{ma, mb}, Bool.and(ka, kb)}

# ---- the frame tree: a chunked frame transposed into a tree of leaf-sized flat frames, built
# SEQUENTIALLY before a walk forks (DESIGN.md 16.10, the T5.3 scaling ceiling). A forking def must do
# nothing but match and fork before its parallel let: a non-flat fork-free helper called there (the cuts
# `CX.cut(a)`, the Dict copies `CX.dclone(ra)` the old walks had in their branch arguments) becomes a task
# the scheduler's grow pass does not run, and the drain then runs the helper's continuation, the fork
# included, in sequential mode: the whole subtree below ran on one thread, so every walk was two
# sequential halves (~1.6-1.9x at 4 and 12 threads alike). The transpose costs the same cuts and the
# same Dict copies (one per split point, D2 rule 4) as the old walks, O(leaves x columns), once. ----

type FT is Type:
  FTL{f: C.Frame, rd: List<&1, DN>}
  FTB{f: CH.CFrame}
  FTN{rows: U32, lrows: U32, l: FT, r: FT}

# sk: the frame's skeleton (the recursion's measure; a cut that disagrees with it, which WFCFrame
# excludes, gives an FTB leaf holding the input: the walk answers ok = False and the flat path runs)
# rr: the Dicts the walk's expressions read, two copies (one per lane of a node; a leaf keeps the first)
def CX.ft(sk: CH.Skel, c: Cut, rr: List<&1, DN> & List<&1, DN>) -> FT:
  match sk c:
    case CH.KLeaf{n} CutL{f}:
      (ra, rb) = rr
      FTL{f, ra}
    case CH.KNode{+rows, +lrows, sl, sr} CutN{r2, l2, a, b}:
      (ra, rb) = rr
      FTN{rows, lrows, CX.ft(sl, CX.cut(a), CX.dclone(ra)), CX.ft(sr, CX.cut(b), CX.dclone(rb))}
    case CH.KLeaf{n} CutN{r2, l2, a, b}:
      FTB{CX.fj(a, b)}
    case CH.KNode{rows, lrows, sl, sr} CutL{f}:
      FTB{CX.lframe(f)}

# walk 1 over the frame tree: ONE balanced parallel let per node and nothing else before it; the leaf
# function and the joins (CX.fj) run as tasks of their own, after the fork
def CX.p1(+pred: X.Expr, t: FT) -> W1:
  match t:
    case FTL{f, rd}:
      CX.p1.leaf(pred, rd, f)
    case FTB{f}:
      W1{f, MX{}, False{}}
    case FTN{rows, lrows, l, r}:
      x y = CX.p1(pred, l) CX.p1(pred, r)
      CX.p1.j(x, y)

# ==== walk 2 of a filter: every leaf compacted by its mask (Q.Exec.fc: compact4 / compact3 groups of
# AllValid columns, Column.compact for the rest; the same answer as Frame.filter_mask, LAWS fc_filter_mask) ====

# (the frame tree and the masks have the shape walk 1 found: the mismatch arms are unreachable; the
# tree is built with no Dicts, so a leaf's rd is empty)
def CX.p2(t: FT, m: MT) -> CH.CFrame:
  match t m:
    case FTL{f, rd} ML{mm, +kept}:
      CX.lframe(Q.Exec.fc(f, mm, kept))
    case FTN{rows, lrows, l, r} MN{ml, mr}:
      x y = CX.p2(l, ml) CX.p2(r, mr)
      CX.fj(x, y)
    case FTL{f, rd} _:
      CX.lframe(f)
    case FTB{f} _:
      f
    case FTN{rows, lrows, l, r} _:
      CX.fj(CX.p2(l, MX{}), CX.p2(r, MX{}))

# ==== the walk of a with_columns / select: all k expressions per leaf (F9), the input borrowed ====

type WS is Type:
  WS{f: C.Frame, outs: List<&1, C.Named>, ok: Bool}

def CX.ev.add(+name: String, outs: List<&1, C.Named>, r: C.Frame & E.ResT(C.Column)) -> WS:
  (f, rc) = r
  match rc:
    case Fail{e}:
      WS{f, outs, False{}}
    case Done{c}:
      WS{f, C.Named{name, c} <> outs, True{}}

def CX.ev.step(+e: X.Expr, st: WS) -> WS:
  match st:
    case WS{f, outs, ok}:
      match ok:
        case True{}:
          CX.ev.add(X.Expr.name(e), outs, CX.efull(f, e))
        case False{}:
          WS{f, outs, False{}}

# every expression in order against the same leaf frame (Eval.full: a literal broadcasts to the leaf's
# rows, which is the frame's broadcast leaf by leaf); the first failure stops the leaf
def CX.ev(es: List<&2, X.Expr>, st: WS) -> WS:
  match es:
    case Nil{}:
      st
    case e <> +t:
      CX.ev(t, CX.ev.step(e, st))

type W2 is Type:
  W2{f: CH.CFrame, o: CH.CFrame, ok: Bool}

def CX.w2.k(+n: U32, r: WS) -> W2:
  match r:
    case WS{f, outs, ok}:
      match ok:
        case True{}:
          W2{CX.lframe(CX.unwf(f)), CH.CFrame{n, CX.lcols(List.reverse(&1, C.Named, outs))}, True{}}
        case False{}:
          W2{CX.lframe(CX.unwf(f)), CH.CFrame{n, Nil{}}, False{}}

def CX.w2.leaf(+es: List<&2, X.Expr>, rd: List<&1, DN>, f: C.Frame) -> W2:
  match f:
    case C.Frame{+n, cols}:
      CX.w2.k(n, CX.ev(es, WS{CX.wrapf(C.Frame{n, cols}, rd), Nil{}, True{}}))

def CX.w2.j(x: W2, y: W2) -> W2:
  match x:
    case W2{fa, oa, ka}:
      match y:
        case W2{fb, ob, kb}:
          W2{CX.fj(fa, fb), CX.fj(oa, ob), Bool.and(ka, kb)}

# over the frame tree (CX.ft): one parallel let per node and nothing else before it
def CX.w2(+es: List<&2, X.Expr>, t: FT) -> W2:
  match t:
    case FTL{f, rd}:
      CX.w2.leaf(es, rd, f)
    case FTB{f}:
      W2{f, CH.CFrame{0, Nil{}}, False{}}
    case FTN{rows, lrows, l, r}:
      x y = CX.w2(es, l) CX.w2(es, r)
      CX.w2.j(x, y)

# ==== frame-level column operations on the trees ====

def CX.cput.pick(eq: Bool, nm: String, c: CH.CColumn, acc: List<&1, CH.CNamed>, slot: Maybe<&1, CH.CColumn>) -> List<&1, CH.CNamed> & Maybe<&1, CH.CColumn>:
  match eq slot:
    case True{} Some{x}:
      (CH.CNamed{nm, x} <> acc, None{})
    case True{} None{}:
      (CH.CNamed{nm, c} <> acc, None{})
    case False{} y:
      (CH.CNamed{nm, c} <> acc, y)

def CX.cput.step(eq: Bool, nm: String, c: CH.CColumn, r: List<&1, CH.CNamed> & Maybe<&1, CH.CColumn>) -> List<&1, CH.CNamed> & Maybe<&1, CH.CColumn>:
  (acc, slot) = r
  CX.cput.pick(eq, nm, c, acc, slot)

def CX.cput.go(cols: List<&1, CH.CNamed>, +name: String, r: List<&1, CH.CNamed> & Maybe<&1, CH.CColumn>) -> List<&1, CH.CNamed> & Maybe<&1, CH.CColumn>:
  match cols:
    case Nil{}:
      r
    case CH.CNamed{+nm, c} <> rest:
      CX.cput.go(rest, name, CX.cput.step(String.eq(nm, name), nm, c, r))

def CX.cput.fin(+name: String, r: List<&1, CH.CNamed> & Maybe<&1, CH.CColumn>) -> List<&1, CH.CNamed>:
  (acc, slot) = r
  match slot:
    case None{}:
      List.reverse(&1, CH.CNamed, acc)
    case Some{c}:
      List.reverse(&1, CH.CNamed, CH.CNamed{name, c} <> acc)

# Frame.replace's rule on the trees: the column of that name replaced in place, else appended
def CX.cput(cols: List<&1, CH.CNamed>, +name: String, col: CH.CColumn) -> List<&1, CH.CNamed>:
  CX.cput.fin(name, CX.cput.go(cols, name, (Nil{}, Some{col})))

# every output column (in order) put into the input's columns
def CX.cputs(outs: List<&1, CH.CNamed>, cols: List<&1, CH.CNamed>) -> List<&1, CH.CNamed>:
  match outs:
    case Nil{}:
      cols
    case CH.CNamed{+n, c} <> rest:
      CX.cputs(rest, CX.cput(cols, n, c))

def CX.ctake.k(eq: Bool, nm: String, c: CH.CColumn, r: List<&1, CH.CNamed> & Maybe<&1, CH.CColumn>) -> List<&1, CH.CNamed> & Maybe<&1, CH.CColumn>:
  match eq:
    case True{}:
      (cs, m) = r
      (cs, Some{c})
    case False{}:
      (cs, m) = r
      (CH.CNamed{nm, c} <> cs, m)

# a column taken out by name (names are unique)
def CX.ctake(cols: List<&1, CH.CNamed>, +name: String) -> List<&1, CH.CNamed> & Maybe<&1, CH.CColumn>:
  match cols:
    case Nil{}:
      (Nil{}, None{})
    case CH.CNamed{+nm, c} <> rest:
      CX.ctake.k(String.eq(nm, name), nm, c, CX.ctake(rest, name))

type PK is Type:
  PK{cols: List<&1, CH.CNamed>, acc: List<&1, CH.CNamed>}

def CX.pick.s2(+n: String, acc: List<&1, CH.CNamed>, r: List<&1, CH.CNamed> & Maybe<&1, CH.CColumn>) -> PK:
  (cols, m) = r
  match m:
    case None{}:
      PK{cols, acc}
    case Some{c}:
      PK{cols, CH.CNamed{n, c} <> acc}

def CX.pick.step(+n: String, st: PK) -> PK:
  match st:
    case PK{cols, acc}:
      CX.pick.s2(n, acc, CX.ctake(cols, n))

def CX.pick.go(ns: List<&2, String>, st: PK) -> List<&1, CH.CNamed>:
  match ns:
    case Nil{}:
      match st:
        case PK{cols, acc}:
          List.reverse(&1, CH.CNamed, acc)
    case +n <> rest:
      CX.pick.go(rest, CX.pick.step(n, st))

# the named columns, in the order of the names (moved; the others dropped). The names were checked by the
# ghost (present, no repetition)
def CX.pick(cols: List<&1, CH.CNamed>, ns: List<&2, String>) -> List<&1, CH.CNamed>:
  CX.pick.go(ns, PK{cols, Nil{}})

def CX.keep.p(hit: Bool, nm: String, c: CH.CColumn, rest: List<&1, CH.CNamed>) -> List<&1, CH.CNamed>:
  match hit:
    case True{}:
      CH.CNamed{nm, c} <> rest
    case False{}:
      rest

# the columns whose names are in ns (frame order kept)
def CX.keep(cols: List<&1, CH.CNamed>, +ns: List<&2, String>) -> List<&1, CH.CNamed>:
  match cols:
    case Nil{}:
      Nil{}
    case CH.CNamed{+nm, c} <> rest:
      CX.keep.p(C.Names.has(ns, nm), nm, c, CX.keep(rest, ns))

def CX.fkeep.p(hit: Bool, nm: String, c: C.Column, rest: List<&1, C.Named>) -> List<&1, C.Named>:
  match hit:
    case True{}:
      C.Named{nm, c} <> rest
    case False{}:
      rest

def CX.fkeep(cols: List<&1, C.Named>, +ns: List<&2, String>) -> List<&1, C.Named>:
  match cols:
    case Nil{}:
      Nil{}
    case C.Named{+nm, c} <> rest:
      CX.fkeep.p(C.Names.has(ns, nm), nm, c, CX.fkeep(rest, ns))

# an operator that consumes its input and reads only the columns ns (a select of expressions, the Filter +
# plain Select root): the others are dropped before any conversion (moved, nothing copied; the ghost has
# already reported the static errors, and the height is kept)
def CX.xkeep(x: XF, +ns: List<&2, String>) -> XF:
  match x:
    case XFlat{f}:
      match f:
        case C.Frame{h, cols}:
          XFlat{C.Frame{h, CX.fkeep(cols, ns)}}
    case XChk{f}:
      match f:
        case CH.CFrame{h, cols}:
          XChk{CH.CFrame{h, CX.keep(cols, ns)}}

# the columns renamed by position to the names of a schema (the ghost's answer of a rename)
def CX.renm(cols: List<&1, CH.CNamed>, s: List<&2, S.Field>) -> List<&1, CH.CNamed>:
  match cols s:
    case CH.CNamed{nm, c} <> rest S.Field{n2, t} <> srest:
      CH.CNamed{n2, c} <> CX.renm(rest, srest)
    case x y:
      x

def CX.names(s: List<&2, S.Field>) -> List<&2, String>:
  S.Schema.names(s)

# ==== the row-wise operators, chunked ====

def CX.pushc(st: CStats, f: CH.CFrame) -> XR:
  XR{st, Done{XChk{f}}}

def CX.skel.k(+h: U32, nm: String, rest: List<&1, CH.CNamed>, r: CH.CColumn & CH.Skel) -> CH.CFrame & CH.Skel:
  (c, sk) = r
  (CH.CFrame{h, CH.CNamed{nm, c} <> rest}, sk)

# the skeleton of a frame's trees (its first column's; one leaf for a frame with no columns)
def CX.skel(f: CH.CFrame) -> CH.CFrame & CH.Skel:
  match f:
    case CH.CFrame{+h, cols}:
      match cols:
        case Nil{}:
          (CH.CFrame{h, Nil{}}, CH.KLeaf{h})
        case CH.CNamed{nm, c} <> rest:
          CX.skel.k(h, nm, rest, CH.CColumn.skel(c))

# the input of a walk: chunked (counted), Dictionary columns set aside, WFCFrame checked once
# (ds: every Dict set aside; rd: a copy of those the expressions read)
type WI is Type:
  WI{st: CStats, f: CH.CFrame, ds: List<&1, DN>, rd: List<&1, DN>, ok: Bool, sk: CH.Skel}

def CX.wi.d(st: CStats, ds: List<&1, DN>, rd: List<&1, DN>, ok: Bool, r: CH.CFrame & CH.Skel) -> WI:
  (f, sk) = r
  WI{st, f, ds, rd, ok, sk}

def CX.wi.c(st: CStats, dd: List<&1, DN> & List<&1, DN>, r: CH.CFrame & Bool) -> WI:
  (ds, rd) = dd
  (f, ok) = r
  CX.wi.d(st, ds, rd, ok, CX.skel(f))

def CX.wi.b(st: CStats, +h: U32, +refs: List<&2, String>, u: UD) -> WI:
  match u:
    case UD{cols, ds}:
      CX.wi.c(st, CX.rclone(ds, refs), CH.CFrame.check(CH.CFrame{h, cols}))

def CX.wi.a(+refs: List<&2, String>, r: CStats & CH.CFrame) -> WI:
  (st, f) = r
  match f:
    case CH.CFrame{+h, cols}:
      CX.wi.b(st, h, refs, CX.undict(cols))

def CX.wi.r(+g: Nat, r: CStats & CH.CFrame) -> CStats & CH.CFrame:
  (st, f) = r
  (st, CH.CFrame.rebalance(g, f))

# the rechunk policy (16.1) runs HERE, lazily: a frame that rows were dropped from (filter, head, slice,
# concat of small parts) is rebalanced when the next walk reads it (occupancy under a half: every subtree
# that fits 2^g becomes one leaf), not when it is made: a flatten boundary or the result's to_frame after a
# filter would only copy the rows twice. The amortised bound is unchanged (a walk's input is rebalanced
# at most once, and only after its row count halved).
def CX.wi(+g: Nat, +refs: List<&2, String>, st: CStats, x: XF) -> WI:
  CX.wi.a(refs, CX.wi.r(g, CX.xchk(g, st, x)))

# back to the flat path from a walk's input (WFCFrame failed, or a leaf failed: the reference answers)
def CX.bail(op: FOp, st: CStats, f: CH.CFrame, ds: List<&1, DN>) -> XR:
  CX.flat(op, st, XChk{CX.redictf(f, ds)})

# ---- copies of chunked columns and frames (every leaf cloned) ----

def CX.wclone.l(+n: U32, +d: Nat, r: Array<U32> & Array<U32>) -> CH.CW & CH.CW:
  (a, b) = r
  (CH.WL{n, d, a}, CH.WL{n, d, b})

def CX.wclone.n(+rows: U32, +lrows: U32, x: CH.CW & CH.CW, y: CH.CW & CH.CW) -> CH.CW & CH.CW:
  (a1, b1) = x
  (a2, b2) = y
  (CH.WN{rows, lrows, a1, a2}, CH.WN{rows, lrows, b1, b2})

def CX.wclone(t: CH.CW) -> CH.CW & CH.CW:
  match t:
    case CH.WL{+n, +d, a}:
      CX.wclone.l(n, d, Array.clone(U32, a))
    case CH.WN{+rows, +lrows, l, r}:
      CX.wclone.n(rows, lrows, CX.wclone(l), CX.wclone(r))

def CX.fclone.l(+n: U32, +d: Nat, r: Array<F32> & Array<F32>) -> CH.CF & CH.CF:
  (a, b) = r
  (CH.FL{n, d, a}, CH.FL{n, d, b})

def CX.fclone.n(+rows: U32, +lrows: U32, x: CH.CF & CH.CF, y: CH.CF & CH.CF) -> CH.CF & CH.CF:
  (a1, b1) = x
  (a2, b2) = y
  (CH.FN{rows, lrows, a1, a2}, CH.FN{rows, lrows, b1, b2})

def CX.fclone(t: CH.CF) -> CH.CF & CH.CF:
  match t:
    case CH.FL{+n, +d, a}:
      CX.fclone.l(n, d, Array.clone(F32, a))
    case CH.FN{+rows, +lrows, l, r}:
      CX.fclone.n(rows, lrows, CX.fclone(l), CX.fclone(r))

def CX.sclone.l(+n: U32, +d: Nat, r: Array<String> & Array<String>) -> CH.CS & CH.CS:
  (a, b) = r
  (CH.SL{n, d, a}, CH.SL{n, d, b})

def CX.sclone.n(+rows: U32, +lrows: U32, x: CH.CS & CH.CS, y: CH.CS & CH.CS) -> CH.CS & CH.CS:
  (a1, b1) = x
  (a2, b2) = y
  (CH.SN{rows, lrows, a1, a2}, CH.SN{rows, lrows, b1, b2})

def CX.sclone(t: CH.CS) -> CH.CS & CH.CS:
  match t:
    case CH.SL{+n, +d, a}:
      CX.sclone.l(n, d, Array.clone(String, a))
    case CH.SN{+rows, +lrows, l, r}:
      CX.sclone.n(rows, lrows, CX.sclone(l), CX.sclone(r))

def CX.vclone.k(r: CH.CW & CH.CW) -> CH.CValid & CH.CValid:
  (a, b) = r
  (CH.CMask{a}, CH.CMask{b})

def CX.vclone(v: CH.CValid) -> CH.CValid & CH.CValid:
  match v:
    case CH.CAllValid{}:
      (CH.CAllValid{}, CH.CAllValid{})
    case CH.CMask{m}:
      CX.vclone.k(CX.wclone(m))

def CX.cclone.w(+t: D.DType, +len: U32, vv: CH.CValid & CH.CValid, xx: CH.CW & CH.CW) -> CH.CColumn & CH.CColumn:
  (va, vb) = vv
  (xa, xb) = xx
  (CH.CColumn.mk_w(t, len, va, xa), CH.CColumn.mk_w(t, len, vb, xb))

def CX.cclone.f(+len: U32, vv: CH.CValid & CH.CValid, xx: CH.CF & CH.CF) -> CH.CColumn & CH.CColumn:
  (va, vb) = vv
  (xa, xb) = xx
  (CH.CF32{len, va, xa}, CH.CF32{len, vb, xb})

def CX.cclone.r(+len: U32, vv: CH.CValid & CH.CValid, xx: CH.CS & CH.CS) -> CH.CColumn & CH.CColumn:
  (va, vb) = vv
  (xa, xb) = xx
  (CH.CStr{len, va, CH.CSRaw{xa}}, CH.CStr{len, vb, CH.CSRaw{xb}})

def CX.cclone.d(+len: U32, vv: CH.CValid & CH.CValid, xx: CH.CW & CH.CW, dd: ST.Dict & ST.Dict) -> CH.CColumn & CH.CColumn:
  (va, vb) = vv
  (xa, xb) = xx
  (da, db) = dd
  (CH.CStr{len, va, CH.CSDict{xa, da}}, CH.CStr{len, vb, CH.CSDict{xb, db}})

def CX.cclone(c: CH.CColumn) -> CH.CColumn & CH.CColumn:
  match c:
    case CH.CBool{+len, v, x}:
      CX.cclone.w(D.TBool{}, len, CX.vclone(v), CX.wclone(x))
    case CH.CU32{+len, v, x}:
      CX.cclone.w(D.TU32{}, len, CX.vclone(v), CX.wclone(x))
    case CH.CI32{+len, v, x}:
      CX.cclone.w(D.TI32{}, len, CX.vclone(v), CX.wclone(x))
    case CH.CF32{+len, v, x}:
      CX.cclone.f(len, CX.vclone(v), CX.fclone(x))
    case CH.CStr{+len, v, x}:
      match x:
        case CH.CSRaw{t}:
          CX.cclone.r(len, CX.vclone(v), CX.sclone(t))
        case CH.CSDict{codes, dict}:
          CX.cclone.d(len, CX.vclone(v), CX.wclone(codes), ST.Dict.clone(dict))

def CX.ccols.k(+n: String, cc: CH.CColumn & CH.CColumn, r: List<&1, CH.CNamed> & List<&1, CH.CNamed>) -> List<&1, CH.CNamed> & List<&1, CH.CNamed>:
  (a, b) = cc
  (ra, rb) = r
  (CH.CNamed{n, a} <> ra, CH.CNamed{n, b} <> rb)

def CX.ccols(cols: List<&1, CH.CNamed>) -> List<&1, CH.CNamed> & List<&1, CH.CNamed>:
  match cols:
    case Nil{}:
      (Nil{}, Nil{})
    case CH.CNamed{+n, c} <> rest:
      CX.ccols.k(n, CX.cclone(c), CX.ccols(rest))

def CX.fclone2.k(+h: U32, r: List<&1, CH.CNamed> & List<&1, CH.CNamed>) -> CH.CFrame & CH.CFrame:
  (a, b) = r
  (CH.CFrame{h, a}, CH.CFrame{h, b})

# a chunked frame and its copy (every leaf cloned; a pre-chunked source read twice, a self join)
def CX.cfclone(f: CH.CFrame) -> CH.CFrame & CH.CFrame:
  match f:
    case CH.CFrame{+h, cols}:
      CX.fclone2.k(h, CX.ccols(cols))

# ---- aggregations inside row-wise expressions (16.4): evaluated ONCE over the whole column, then the
# expression runs per leaf with the value as a literal ----
# An aggregation Agg{op, e} (e row-local: a nested aggregation is a static error the ghost reported) is
# evaluated by the flat evaluator (V.Eval.expr) over a flat frame of the columns it reads: the frame
# itself when it is flat (borrowed), else a flattened COPY of those columns (CX.cpk clones them; the
# copy's bytes are counted as a conversion). Its 1-row answer becomes a literal (a typed null literal for
# null) and the top-level expression keeps its output name (Alias). A failing aggregation sends the
# operator to the flat path (the reference's error, as for a failing leaf).

# the maximal aggregations of e, in evaluation (postfix) order, prepended to acc
def CX.aggs(e: X.Expr, acc: List<&2, X.Expr>) -> List<&2, X.Expr>:
  match e:
    case X.Col{n}:
      acc
    case X.Lit{v}:
      acc
    case X.Alias{e2, n}:
      CX.aggs(e2, acc)
    case X.Cast{e2, t}:
      CX.aggs(e2, acc)
    case X.TryCast{e2, t}:
      CX.aggs(e2, acc)
    case X.Un{op, e2}:
      CX.aggs(e2, acc)
    case X.Bin{op, a, b}:
      CX.aggs(b, CX.aggs(a, acc))
    case X.FillNull{e2, v}:
      CX.aggs(v, CX.aggs(e2, acc))
    case X.Agg{op, e2}:
      X.Agg{op, e2} <> acc
    case X.When{c, a, b}:
      CX.aggs(b, CX.aggs(a, CX.aggs(c, acc)))
    case X.IsIn{e2, vs}:
      CX.aggs(e2, acc)
    case X.Clip{e2, lo, hi}:
      CX.aggs(e2, acc)
    case X.StrPred{op, e2, p}:
      CX.aggs(e2, acc)

def CX.aggsl(es: List<&2, X.Expr>, acc: List<&2, X.Expr>) -> List<&2, X.Expr>:
  match es:
    case Nil{}:
      acc
    case e <> t:
      CX.aggsl(t, CX.aggs(e, acc))

# how many maximal aggregations e holds
def CX.nagg(e: X.Expr) -> Nat:
  List.length(&2, X.Expr, CX.aggs(e, Nil{}))

def CX.dropn(n: Nat, xs: List<&2, X.Expr>) -> List<&2, X.Expr>:
  match n xs:
    case 0n _:
      xs
    case _ Nil{}:
      Nil{}
    case 1n+k x <> t:
      CX.dropn(k, t)

def CX.dropn2(+xs: List<&2, X.Expr>, n: Nat) -> List<&2, X.Expr>:
  CX.dropn(n, xs)

def CX.vhead(xs: List<&2, X.Expr>, +dflt: X.Expr) -> X.Expr:
  match xs:
    case Nil{}:
      dflt
    case x <> t:
      x

# e with its maximal aggregations replaced, in order, by the literals vs
def CX.sub(e: X.Expr, +vs: List<&2, X.Expr>) -> X.Expr:
  match e:
    case X.Col{n}:
      X.Col{n}
    case X.Lit{v}:
      X.Lit{v}
    case X.Alias{e2, n}:
      X.Alias{CX.sub(e2, vs), n}
    case X.Cast{e2, t}:
      X.Cast{CX.sub(e2, vs), t}
    case X.TryCast{e2, t}:
      X.TryCast{CX.sub(e2, vs), t}
    case X.Un{op, e2}:
      X.Un{op, CX.sub(e2, vs)}
    case X.Bin{op, +a, b}:
      X.Bin{op, CX.sub(a, vs), CX.sub(b, CX.dropn2(vs, CX.nagg(a)))}
    case X.FillNull{+e2, v}:
      X.FillNull{CX.sub(e2, vs), CX.sub(v, CX.dropn2(vs, CX.nagg(e2)))}
    case X.Agg{op, e2}:
      CX.vhead(vs, X.Agg{op, e2})
    case X.When{+c, +a, b}:
      X.When{CX.sub(c, vs), CX.sub(a, CX.dropn2(vs, CX.nagg(c))), CX.sub(b, CX.dropn2(vs, Nat.add(CX.nagg(c), CX.nagg(a))))}
    case X.IsIn{e2, xs}:
      X.IsIn{CX.sub(e2, vs), xs}
    case X.Clip{e2, lo, hi}:
      X.Clip{CX.sub(e2, vs), lo, hi}
    case X.StrPred{op, e2, p}:
      X.StrPred{op, CX.sub(e2, vs), p}

def CX.subt(+e: X.Expr, +vs: List<&2, X.Expr>, z: Bool) -> X.Expr:
  match z:
    case True{}:
      e
    case False{}:
      X.Alias{CX.sub(e, vs), X.Expr.name(e)}

def CX.subl(es: List<&2, X.Expr>, +vs: List<&2, X.Expr>) -> List<&2, X.Expr>:
  match es:
    case Nil{}:
      Nil{}
    case +e <> t:
      CX.subt(e, vs, Nat.is_eq(CX.nagg(e), 0n)) <> CX.subl(t, CX.dropn2(vs, CX.nagg(e)))

# a 1-row column's cell 0 as a literal of its dtype (null: the typed null literal)
def CX.lit.s(+t: D.DType, r: C.Column & D.Scalar) -> X.Expr:
  (c, v) = r
  match v:
    case D.SNull{}:
      X.Cast{X.Lit{D.SNull{}}, t}
    case other:
      X.Lit{other}

def CX.lit.t(r: C.Column & D.DType) -> X.Expr:
  (c, +t) = r
  CX.lit.s(t, C.Column.cell(c, 0))

def CX.lit(c: C.Column) -> X.Expr:
  CX.lit.t(C.Column.dtype(c))

type AV is Type:
  AV{f: C.Frame, vs: List<&2, X.Expr>, ok: Bool}

def CX.agv.k(vs: List<&2, X.Expr>, r: C.Frame & E.ResT(C.Column)) -> AV:
  (f, rc) = r
  match rc:
    case Fail{e}:
      AV{f, vs, False{}}
    case Done{c}:
      AV{f, CX.lit(c) <> vs, True{}}

def CX.agv.step(+a: X.Expr, st: AV) -> AV:
  match st:
    case AV{f, vs, ok}:
      match ok:
        case True{}:
          CX.agv.k(vs, V.Eval.expr(f, a))
        case False{}:
          AV{f, vs, False{}}

# every aggregation over the frame (borrowed), in order; the first failure stops (values newest first)
def CX.agv(as: List<&2, X.Expr>, st: AV) -> AV:
  match as:
    case Nil{}:
      st
    case a <> +t:
      CX.agv(t, CX.agv.step(a, st))

def CX.cpk.c(+n: String, cc: CH.CColumn & CH.CColumn, r: List<&1, CH.CNamed> & List<&1, CH.CNamed>) -> List<&1, CH.CNamed> & List<&1, CH.CNamed>:
  (a, b) = cc
  (ra, rb) = r
  (CH.CNamed{n, a} <> ra, CH.CNamed{n, b} <> rb)

def CX.cpk.k(hit: Bool, +n: String, c: CH.CColumn, r: List<&1, CH.CNamed> & List<&1, CH.CNamed>) -> List<&1, CH.CNamed> & List<&1, CH.CNamed>:
  match hit:
    case True{}:
      CX.cpk.c(n, CX.cclone(c), r)
    case False{}:
      (ra, rb) = r
      (CH.CNamed{n, c} <> ra, rb)

# the columns (back) and a copy of those named in refs
def CX.cpk(cols: List<&1, CH.CNamed>, +refs: List<&2, String>) -> List<&1, CH.CNamed> & List<&1, CH.CNamed>:
  match cols:
    case Nil{}:
      (Nil{}, Nil{})
    case CH.CNamed{+n, c} <> rest:
      CX.cpk.k(C.Names.has(refs, n), n, c, CX.cpk(rest, refs))

# ---- aggregations on the trees (16.4 D4): U32 / I32 sum, U32 min / max, count, len of a plain column ----
# Tree reductions with proven combines only (LAWS section 22: ck_sum, ck_min, ck_max; the count IS the
# popcount of the 0/1 mask tree): a U32 / I32 sum adds every row, null slots included (they hold the dtype
# default 0: Eval's dropnull-then-fold gives the same word); U32 min / max of an AllValid column (empty: the
# null rule, as Eval.nz); count = rows, or the mask's popcount; len = rows. F32 sums and I32 / F32 min / max
# stay sequential (D4): such an aggregation goes to the flat hoisting path below. The tree is borrowed (each
# CK fold hands it back), so nothing is copied.

def CX.tnull() -> X.Expr:
  X.Cast{X.Lit{D.SNull{}}, D.TU32{}}

def CX.tmm.k(+len: U32, r: CH.CW & U32) -> CH.CW & Maybe<&2, X.Expr>:
  (x, +w) = r
  (x, Some{Bool.pick(X.Expr, U32.is_zero(len), CX.tnull(), X.Lit{D.SU32{w}})})

def CX.tsum.k(+t: D.DType, r: CH.CW & U32) -> CH.CW & Maybe<&2, X.Expr>:
  (x, +w) = r
  (x, Some{X.Lit{C.Column.cell.word(t, w)}})

def CX.tcnt.k(r: CH.CW & U32) -> CH.CValid & Maybe<&2, X.Expr>:
  (m, +k) = r
  (CH.CMask{m}, Some{X.Lit{D.SU32{k}}})

# the valid-row count of a column: its rows (AllValid) or its mask's popcount
def CX.tcnt(+len: U32, v: CH.CValid) -> CH.CValid & Maybe<&2, X.Expr>:
  match v:
    case CH.CAllValid{}:
      (CH.CAllValid{}, Some{X.Lit{D.SU32{len}}})
    case CH.CMask{m}:
      CX.tcnt.k(KC.CK.popcount.w(m))

def CX.twv.k(+t: D.DType, +len: U32, x: CH.CW, r: CH.CValid & Maybe<&2, X.Expr>) -> CH.CColumn & Maybe<&2, X.Expr>:
  (v, mv) = r
  (CH.CColumn.mk_w(t, len, v, x), mv)

def CX.twx.k(+t: D.DType, +len: U32, v: CH.CValid, r: CH.CW & Maybe<&2, X.Expr>) -> CH.CColumn & Maybe<&2, X.Expr>:
  (x, mv) = r
  (CH.CColumn.mk_w(t, len, v, x), mv)

def CX.tmm.c(+mx: Bool, +len: U32, x: CH.CW) -> CH.CW & Maybe<&2, X.Expr>:
  match mx:
    case True{}:
      CX.tmm.k(len, KC.CK.max.w(x))
    case False{}:
      CX.tmm.k(len, KC.CK.min.w(x))

def CX.tmm.b(r: CH.CW & Maybe<&2, X.Expr>) -> CH.CValid & CH.CW & Maybe<&2, X.Expr>:
  (x, mv) = r
  (CH.CAllValid{}, x, mv)

def CX.tmm(+mx: Bool, +len: U32, v: CH.CValid, x: CH.CW) -> CH.CValid & CH.CW & Maybe<&2, X.Expr>:
  match v:
    case CH.CAllValid{}:
      CX.tmm.b(CX.tmm.c(mx, len, x))
    case CH.CMask{m}:
      (CH.CMask{m}, x, None{})

def CX.tmm.r(+t: D.DType, +len: U32, r: CH.CValid & CH.CW & Maybe<&2, X.Expr>) -> CH.CColumn & Maybe<&2, X.Expr>:
  (v, x, mv) = r
  (CH.CColumn.mk_w(t, len, v, x), mv)

def CX.tw.mm(+mx: Bool, +t: D.DType, u32: Bool, +len: U32, v: CH.CValid, x: CH.CW) -> CH.CColumn & Maybe<&2, X.Expr>:
  match u32:
    case True{}:
      CX.tmm.r(t, len, CX.tmm(mx, len, v, x))
    case False{}:
      (CH.CColumn.mk_w(t, len, v, x), None{})

# a word column (U32 / I32; sum also over I32, min / max over U32 only)
def CX.tw(+op: X.AggOp, +t: D.DType, +u32: Bool, +len: U32, v: CH.CValid, x: CH.CW) -> CH.CColumn & Maybe<&2, X.Expr>:
  match op:
    case X.Sum{}:
      CX.twx.k(t, len, v, CX.tsum.k(t, KC.CK.sum.w(x)))
    case X.Min{}:
      CX.tw.mm(False{}, t, u32, len, v, x)
    case X.Max{}:
      CX.tw.mm(True{}, t, u32, len, v, x)
    case X.Count{}:
      CX.twv.k(t, len, x, CX.tcnt(len, v))
    case X.Len{}:
      (CH.CColumn.mk_w(t, len, v, x), Some{X.Lit{D.SU32{len}}})
    case _:
      (CH.CColumn.mk_w(t, len, v, x), None{})

def CX.tvo.k(c: CH.CColumn, r: CH.CValid & Maybe<&2, X.Expr>) -> CH.CColumn & Maybe<&2, X.Expr>:
  (v, mv) = r
  (CX.cset_v(c, v), mv)

def CX.tvo.a(+op: X.AggOp, +len: U32, r: CH.CColumn & CH.CValid) -> CH.CColumn & Maybe<&2, X.Expr>:
  match op:
    case X.Count{}:
      (c, v) = r
      CX.tvo.k(c, CX.tcnt(len, v))
    case X.Len{}:
      (c, v) = r
      (CX.cset_v(c, v), Some{X.Lit{D.SU32{len}}})
    case _:
      (c, v) = r
      (CX.cset_v(c, v), None{})

# an aggregation of a plain column on its trees, or None (not a tree reduction: the flat path)
def CX.cagg(+op: X.AggOp, c: CH.CColumn) -> CH.CColumn & Maybe<&2, X.Expr>:
  match c:
    case CH.CU32{+len, v, x}:
      CX.tw(op, D.TU32{}, True{}, len, v, x)
    case CH.CI32{+len, v, x}:
      CX.tw(op, D.TI32{}, False{}, len, v, x)
    case CH.CBool{+len, v, x}:
      CX.tvo.a(op, len, CX.ctake_v(CH.CBool{len, v, x}))
    case CH.CF32{+len, v, x}:
      CX.tvo.a(op, len, CX.ctake_v(CH.CF32{len, v, x}))
    case CH.CStr{+len, v, x}:
      CX.tvo.a(op, len, CX.ctake_v(CH.CStr{len, v, x}))

def CX.cw.p(+nm: String, rest: List<&1, CH.CNamed>, r: CH.CColumn & Maybe<&2, X.Expr>) -> List<&1, CH.CNamed> & Maybe<&2, X.Expr>:
  (c, mv) = r
  (CH.CNamed{nm, c} <> rest, mv)

def CX.cw.k(eq: Bool, +nm: String, c: CH.CColumn, +op: X.AggOp, r: List<&1, CH.CNamed> & Maybe<&2, X.Expr>) -> List<&1, CH.CNamed> & Maybe<&2, X.Expr>:
  match eq:
    case True{}:
      (rest, m) = r
      CX.cw.p(nm, rest, CX.cagg(op, c))
    case False{}:
      (rest, m) = r
      (CH.CNamed{nm, c} <> rest, m)

# op over the column named n, on its trees (the columns come back in place)
def CX.cw(cols: List<&1, CH.CNamed>, +n: String, +op: X.AggOp) -> List<&1, CH.CNamed> & Maybe<&2, X.Expr>:
  match cols:
    case Nil{}:
      (Nil{}, None{})
    case CH.CNamed{+nm, c} <> rest:
      CX.cw.k(String.eq(nm, n), nm, c, op, CX.cw(rest, n, op))

type TA is Type:
  TA{cols: List<&1, CH.CNamed>, vs: List<&2, X.Expr>, ok: Bool}

def CX.tagg.r(vs: List<&2, X.Expr>, r: List<&1, CH.CNamed> & Maybe<&2, X.Expr>) -> TA:
  (cols, mv) = r
  match mv:
    case None{}:
      TA{cols, vs, False{}}
    case Some{v}:
      TA{cols, v <> vs, True{}}

# Len of a literal counts the frame's rows; any other aggregation of a literal goes flat
def CX.tagg.l(+h: U32, op: X.AggOp, vs: List<&2, X.Expr>, cols: List<&1, CH.CNamed>) -> TA:
  match op:
    case X.Len{}:
      TA{cols, X.Lit{D.SU32{h}} <> vs, True{}}
    case _:
      TA{cols, vs, False{}}

def CX.tagg.e(+h: U32, a: X.Expr, vs: List<&2, X.Expr>, cols: List<&1, CH.CNamed>) -> TA:
  match a:
    case X.Agg{+op, e}:
      match e:
        case X.Col{+n}:
          CX.tagg.r(vs, CX.cw(cols, n, op))
        case X.Lit{v}:
          CX.tagg.l(h, op, vs, cols)
        case _:
          TA{cols, vs, False{}}
    case _:
      TA{cols, vs, False{}}

def CX.tagg.step(+h: U32, +a: X.Expr, st: TA) -> TA:
  match st:
    case TA{cols, vs, ok}:
      match ok:
        case True{}:
          CX.tagg.e(h, a, vs, cols)
        case False{}:
          TA{cols, vs, False{}}

# every aggregation on the trees, in order, while each is a tree reduction (values newest first)
def CX.tagg(as: List<&2, X.Expr>, +h: U32, st: TA) -> TA:
  match as:
    case Nil{}:
      st
    case a <> +t:
      CX.tagg(t, h, CX.tagg.step(h, a, st))

# the hoisted expressions (es with every aggregation a literal), or ok = False (an aggregation failed)
type HO is Type:
  HO{st: CStats, x: XF, es: List<&2, X.Expr>, ok: Bool}

def CX.hoist.e(+es: List<&2, X.Expr>, st: CStats, x: XF, av: AV) -> HO:
  match av:
    case AV{f, vs, ok}:
      match ok:
        case True{}:
          HO{st, x, CX.subl(es, List.reverse(&2, X.Expr, vs)), True{}}
        case False{}:
          HO{st, x, es, False{}}

def CX.hoist.ff(+es: List<&2, X.Expr>, st: CStats, av: AV) -> HO:
  match av:
    case AV{f, vs, ok}:
      CX.hoist.e(es, st, XFlat{f}, AV{C.Frame.empty(), vs, ok})

def CX.hoist.d(+es: List<&2, X.Expr>, +as: List<&2, X.Expr>, +h: U32, cols: List<&1, CH.CNamed>, r: CStats & C.Frame) -> HO:
  (st, f) = r
  CX.hoist.e(es, st, XChk{CH.CFrame{h, cols}}, CX.agv(as, AV{f, Nil{}, True{}}))

def CX.hoist.c(+es: List<&2, X.Expr>, +as: List<&2, X.Expr>, st: CStats, +h: U32, r: List<&1, CH.CNamed> & List<&1, CH.CNamed>) -> HO:
  (cols, sub) = r
  CX.hoist.d(es, as, h, cols, CX.to(st, CH.CFrame{h, sub}))

# on the trees when every aggregation is a tree reduction, else over a flattened copy of their columns
def CX.hoist.t(+es: List<&2, X.Expr>, +as: List<&2, X.Expr>, st: CStats, +h: U32, ta: TA) -> HO:
  match ta:
    case TA{cols, vs, ok}:
      match ok:
        case True{}:
          HO{st, XChk{CH.CFrame{h, cols}}, CX.subl(es, List.reverse(&2, X.Expr, vs)), True{}}
        case False{}:
          CX.hoist.c(es, as, st, h, CX.cpk(cols, V.Eval.refs(as)))

def CX.hoist.b(+es: List<&2, X.Expr>, +as: List<&2, X.Expr>, st: CStats, x: XF) -> HO:
  match x:
    case XFlat{f}:
      CX.hoist.ff(es, st, CX.agv(as, AV{f, Nil{}, True{}}))
    case XChk{f}:
      match f:
        case CH.CFrame{+h, cols}:
          CX.hoist.t(es, as, st, h, CX.tagg(as, h, TA{cols, Nil{}, True{}}))

def CX.hoist.a(+es: List<&2, X.Expr>, +as: List<&2, X.Expr>, st: CStats, x: XF) -> HO:
  match as:
    case Nil{}:
      HO{st, x, es, True{}}
    case a <> t:
      CX.hoist.b(es, a <> t, st, x)

# es over the frame x with every aggregation evaluated once (see above)
def CX.hoist(+es: List<&2, X.Expr>, st: CStats, x: XF) -> HO:
  CX.hoist.a(es, List.reverse(&2, X.Expr, CX.aggsl(es, Nil{})), st, x)

# ---- filter ----

def CX.filter.w2(+g: Nat, st: CStats, ds: List<&1, DN>, +sk: CH.Skel, w: W1) -> XR:
  match w:
    case W1{f, m, ok}:
      CX.pushc(CStats.walk(st, 2), CX.redictf(CX.p2(CX.ft(sk, CX.cut(f), (Nil{}, Nil{})), m), ds))

def CX.filter.w1(+g: Nat, +pred: X.Expr, st: CStats, ds: List<&1, DN>, +sk: CH.Skel, w: W1) -> XR:
  match w:
    case W1{f, m, ok}:
      match ok:
        case True{}:
          CX.filter.w2(g, st, ds, sk, W1{f, m, True{}})
        case False{}:
          CX.bail(FUn{Q.IFilter{pred}}, CStats.walk(st, 1), f, ds)

def CX.filter.wi(+g: Nat, +pred: X.Expr, +p2: X.Expr, w: WI) -> XR:
  match w:
    case WI{st, f, ds, rd, ok, +sk}:
      match ok:
        case True{}:
          CX.filter.w1(g, pred, st, ds, sk, CX.p1(p2, CX.ft(sk, CX.cut(f), CX.dclone(rd))))
        case False{}:
          CX.bail(FUn{Q.IFilter{pred}}, st, f, ds)

def CX.filter.h(+g: Nat, +pred: X.Expr, ho: HO) -> XR:
  match ho:
    case HO{st, x, es2, ok}:
      match ok:
        case True{}:
          CX.filter.wi(g, pred, CX.vhead(es2, pred), CX.wi(g, X.Expr.refs(pred), st, x))
        case False{}:
          CX.flat(FUn{Q.IFilter{pred}}, st, x)

def CX.filter.c(+g: Nat, +pred: X.Expr, st: CStats, ok: Bool, x: XF) -> XR:
  match ok:
    case True{}:
      CX.filter.h(g, pred, CX.hoist(pred <> Nil{}, st, x))
    case False{}:
      CX.flat(FUn{Q.IFilter{pred}}, st, x)

def CX.filter.r(+g: Nat, +pred: X.Expr, st: CStats, r: XF & XI) -> XR:
  (x, i) = r
  CX.filter.c(g, pred, st, CX.route(g, X.Expr.refs(pred), Nil{}, i), x)

def CX.filter.b(+g: Nat, +pred: X.Expr, st: CStats, x: XF, go: GO) -> XR:
  match go:
    case GFail{e}:
      CX.flat(FUn{Q.IFilter{pred}}, st, x)
    case GOk{s2}:
      CX.filter.r(g, pred, st, CX.xinfo(x))

def CX.filter.a(+g: Nat, +pred: X.Expr, st: CStats, r: XF & List<&2, S.Field>) -> XR:
  (x, s) = r
  CX.filter.b(g, pred, st, x, CX.gok(V.Eval.filter(CX.ghost(s), pred)))

# Eval.filter, chunked: the ghost (static errors), the mask walk, the compaction walk (the ragged result is
# rebalanced lazily, by the next walk that reads it: CX.wi)
def CX.filter(+g: Nat, +pred: X.Expr, st: CStats, x: XF) -> XR:
  CX.filter.a(g, pred, st, CX.xschema(x))

# ---- the Filter + plain Select root step (F8: only the selected columns are compacted) ----

def CX.fsel.w2(+g: Nat, +es: List<&2, X.Expr>, st: CStats, ds: List<&1, DN>, +sk: CH.Skel, w: W1) -> XR:
  match w:
    case W1{f, m, ok}:
      match f:
        case CH.CFrame{h, cols}:
          CX.pushc(CStats.walk(st, 2), CX.redictf(CX.p2(CX.ft(sk, CX.cut(CH.CFrame{h, CX.pick(cols, V.Eval.names(es))}), (Nil{}, Nil{})), m), ds))

def CX.fsel.w1(+g: Nat, +pred: X.Expr, +es: List<&2, X.Expr>, st: CStats, ds: List<&1, DN>, +sk: CH.Skel, w: W1) -> XR:
  match w:
    case W1{f, m, ok}:
      match ok:
        case True{}:
          CX.fsel.w2(g, es, st, ds, sk, W1{f, m, True{}})
        case False{}:
          CX.bail(FFs{pred, es}, CStats.walk(st, 1), f, ds)

def CX.fsel.wi(+g: Nat, +pred: X.Expr, +p2: X.Expr, +es: List<&2, X.Expr>, w: WI) -> XR:
  match w:
    case WI{st, f, ds, rd, ok, +sk}:
      match ok:
        case True{}:
          CX.fsel.w1(g, pred, es, st, ds, sk, CX.p1(p2, CX.ft(sk, CX.cut(f), CX.dclone(rd))))
        case False{}:
          CX.bail(FFs{pred, es}, st, f, ds)

def CX.fsel.h(+g: Nat, +pred: X.Expr, +es: List<&2, X.Expr>, ho: HO) -> XR:
  match ho:
    case HO{st, x, es2, ok}:
      match ok:
        case True{}:
          CX.fsel.wi(g, pred, CX.vhead(es2, pred), es, CX.wi(g, X.Expr.refs(pred), st, x))
        case False{}:
          CX.flat(FFs{pred, es}, st, x)

def CX.fsel.c(+g: Nat, +pred: X.Expr, +es: List<&2, X.Expr>, st: CStats, ok: Bool, x: XF) -> XR:
  match ok:
    case True{}:
      CX.fsel.h(g, pred, es, CX.hoist(pred <> Nil{}, st, x))
    case False{}:
      CX.flat(FFs{pred, es}, st, x)

def CX.fsel.r(+g: Nat, +pred: X.Expr, +es: List<&2, X.Expr>, st: CStats, r: XF & XI) -> XR:
  (x, i) = r
  CX.fsel.c(g, pred, es, st, CX.route(g, X.Expr.refs(pred), Nil{}, i), x)

def CX.fsel.b(+g: Nat, +pred: X.Expr, +es: List<&2, X.Expr>, st: CStats, x: XF, go: GO) -> XR:
  match go:
    case GFail{e}:
      CX.flat(FFs{pred, es}, st, x)
    case GOk{s2}:
      CX.fsel.r(g, pred, es, st, CX.xinfo(CX.xkeep(x, List.append(&2, String, V.Eval.names(es), X.Expr.refs(pred)))))

def CX.fsel.a(+g: Nat, +pred: X.Expr, +es: List<&2, X.Expr>, st: CStats, r: XF & List<&2, S.Field>) -> XR:
  (x, s) = r
  CX.fsel.b(g, pred, es, st, x, CX.gok(Q.Exec.fs(CX.ghost(s), pred, es)))

# Q.Exec.fs (Eval.filter then Frame.select_names, plain columns), chunked
def CX.fsel(+g: Nat, +pred: X.Expr, +es: List<&2, X.Expr>, st: CStats, x: XF) -> XR:
  CX.fsel.a(g, pred, es, st, CX.xschema(x))

# ---- with_columns / select of expressions: one walk, all k expressions per leaf ----

# what the answer of a successful walk is: with_columns puts the outputs into the input; select is the outputs
type WK is Data:
  KWith{}
  KSel{}

# with_columns: the outputs put into the input, whose Dictionary columns get their Dicts back (no output
# overwrites one: CX.route); select: the outputs alone, fresh columns, so NO Dict is put back (an output
# may carry the name of a Dictionary input, e.g. `cast(d, u32)` is named d)
def CX.ws.fin(k: WK, f: CH.CFrame, o: CH.CFrame, ds: List<&1, DN>) -> CH.CFrame:
  match k:
    case KWith{}:
      match f:
        case CH.CFrame{h, cols}:
          match o:
            case CH.CFrame{ho, ocols}:
              CX.redictf(CH.CFrame{h, CX.cputs(ocols, cols)}, ds)
    case KSel{}:
      o

def CX.ws.w(+k: WK, op: FOp, st: CStats, ds: List<&1, DN>, w: W2) -> XR:
  match w:
    case W2{f, o, ok}:
      match ok:
        case True{}:
          CX.pushc(CStats.walk(st, 1), CX.ws.fin(k, f, o, ds))
        case False{}:
          CX.bail(op, CStats.walk(st, 1), f, ds)

def CX.ws.wi(+k: WK, +es: List<&2, X.Expr>, op: FOp, w: WI) -> XR:
  match w:
    case WI{st, f, ds, rd, ok, sk}:
      match ok:
        case True{}:
          CX.ws.w(k, op, st, ds, CX.w2(es, CX.ft(sk, CX.cut(f), CX.dclone(rd))))
        case False{}:
          CX.bail(op, st, f, ds)

def CX.ws.h(+g: Nat, +k: WK, +es: List<&2, X.Expr>, op: FOp, ho: HO) -> XR:
  match ho:
    case HO{st, x, es2, ok}:
      match ok:
        case True{}:
          CX.ws.wi(k, es2, op, CX.wi(g, V.Eval.refs(es), st, x))
        case False{}:
          CX.flat(op, st, x)

# a select consumes its input and reads only its expressions' columns: a chunked input is pruned to
# them before the flatten boundary (the ghost reported the static errors; Len counts the height, kept)
def CX.prune(k: WK, +refs: List<&2, String>, x: XF) -> XF:
  match k:
    case KWith{}:
      x
    case KSel{}:
      match x:
        case XFlat{f}:
          XFlat{f}
        case XChk{f}:
          match f:
            case CH.CFrame{h, cols}:
              XChk{CH.CFrame{h, CX.keep(cols, refs)}}

def CX.ws.c(+g: Nat, +k: WK, +es: List<&2, X.Expr>, op: FOp, st: CStats, ok: Bool, x: XF) -> XR:
  match ok:
    case True{}:
      CX.ws.h(g, k, es, op, CX.hoist(es, st, x))
    case False{}:
      CX.flat(op, st, CX.prune(k, V.Eval.refs(es), x))

# the output names that could overwrite an input column (with_columns only)
def CX.outs(k: WK, +es: List<&2, X.Expr>) -> List<&2, String>:
  match k:
    case KWith{}:
      V.Eval.names(es)
    case KSel{}:
      Nil{}

def CX.ws.r(+g: Nat, +k: WK, +es: List<&2, X.Expr>, +ok0: Bool, op: FOp, st: CStats, r: XF & XI) -> XR:
  (x, i) = r
  CX.ws.c(g, k, es, op, st, Bool.and(ok0, CX.route(g, V.Eval.refs(es), CX.outs(k, es), i)), x)

def CX.wc.b(+g: Nat, +es: List<&2, X.Expr>, st: CStats, x: XF, go: GO) -> XR:
  match go:
    case GFail{e}:
      CX.flat(FUn{Q.IWith{es}}, st, x)
    case GOk{+s2}:
      CX.ws.r(g, KWith{}, es, True{}, FUn{Q.IWith{es}}, st, CX.xinfo(x))

def CX.wc.a(+g: Nat, +es: List<&2, X.Expr>, st: CStats, r: XF & List<&2, S.Field>) -> XR:
  (x, s) = r
  CX.wc.b(g, es, st, x, CX.gok(V.Eval.with_columns(CX.ghost(s), es)))

# Eval.with_columns, chunked
def CX.wc(+g: Nat, +es: List<&2, X.Expr>, st: CStats, x: XF) -> XR:
  CX.wc.a(g, es, st, CX.xschema(x))

# a select of one row (literals and aggregations only; Ana.rows is False) over a chunked frame: every
# aggregation hoisted (on the trees when it is a tree reduction), then the reference select over a frame
# of no columns evaluates the literals (one row, the dtypes and names of the original expressions)
def CX.sel1.h(+es: List<&2, X.Expr>, ho: HO) -> XR:
  match ho:
    case HO{st, x, es2, ok}:
      match ok:
        case True{}:
          CX.xr(st, V.Eval.select(C.Frame{0, Nil{}}, es2))
        case False{}:
          CX.flat(FUn{Q.ISelect{es}}, st, CX.xkeep(x, V.Eval.refs(es)))

def CX.sel.c(+g: Nat, rows: Bool, +es: List<&2, X.Expr>, st: CStats, x: XF) -> XR:
  match rows:
    case True{}:
      CX.ws.r(g, KSel{}, es, CX.nonempty(es), FUn{Q.ISelect{es}}, st, CX.xinfo(CX.xkeep(x, V.Eval.refs(es))))
    case False{}:
      match x:
        case XFlat{f}:
          CX.flat(FUn{Q.ISelect{es}}, st, XFlat{f})
        case XChk{f}:
          CX.sel1.h(es, CX.hoist(es, st, XChk{f}))

def CX.sel.b(+g: Nat, +es: List<&2, X.Expr>, +s: List<&2, S.Field>, st: CStats, x: XF, go: GO) -> XR:
  match go:
    case GFail{e}:
      CX.flat(FUn{Q.ISelect{es}}, st, x)
    case GOk{+s2}:
      CX.sel.c(g, A.Ana.rows(es, s), es, st, x)

# a plain select on the trees: the ghost checked the names, the columns are moved
def CX.selp.b(+es: List<&2, X.Expr>, st: CStats, go: GO, x: XF) -> XR:
  match go:
    case GFail{e}:
      CX.flat(FUn{Q.ISelect{es}}, st, x)
    case GOk{s2}:
      match x:
        case XFlat{f}:
          CX.flat(FUn{Q.ISelect{es}}, st, XFlat{f})
        case XChk{f}:
          match f:
            case CH.CFrame{h, cols}:
              CX.pushc(st, CH.CFrame{h, CX.pick(cols, V.Eval.names(es))})

def CX.sel.k(+g: Nat, plain: Bool, +es: List<&2, X.Expr>, st: CStats, r: XF & List<&2, S.Field>) -> XR:
  match plain:
    case True{}:
      (x, +s) = r
      CX.selp.b(es, st, CX.gok(Q.Exec.select(CX.ghost(s), es)), x)
    case False{}:
      (x, +s) = r
      CX.sel.b(g, es, s, st, x, CX.gok(V.Eval.select(CX.ghost(s), es)))

# Exec.select, chunked: plain columns move on the trees; expressions run in one walk (when every output is
# a row of the input: some KRow expression, Ana.rows; a literal-only or reduction select is one row: flat)
def CX.sel(+g: Nat, +es: List<&2, X.Expr>, st: CStats, x: XF) -> XR:
  CX.sel.k(g, Q.Exec.plain(es), es, st, CX.xschema(x))

# ---- head / slice / tail on the trees (no row copied but a slice's boundary leaf; rebalanced lazily) ----

def CX.slice.k(z: Bool, f: CH.CFrame, +start: U32, +cnt: U32) -> CH.CFrame:
  match z:
    case True{}:
      CH.CFrame.head(f, cnt)
    case False{}:
      CH.CFrame.slice(f, start, cnt)

# TV.Slice.at's rows [start, start + cnt) (clamped by the caller); start = 0 is a head
def CX.slice(f: CH.CFrame, +start: U32, +cnt: U32) -> CH.CFrame:
  CX.slice.k(U32.is_zero(start), f, start, cnt)

def CX.cut_rows.t(+g: Nat, op: Q.TOp, st: CStats, r: CH.CFrame & U32) -> XR:
  match op:
    case Q.TSlice{+off, +len}:
      (f, +h) = r
      CX.pushc(st, CX.slice(f, U32.min(off, h), U32.min(len, U32.sub(h, U32.min(off, h)))))
    case Q.TTail{+n}:
      (f, +h) = r
      CX.pushc(st, CX.slice(f, U32.sub(h, U32.min(n, h)), U32.min(n, h)))
    case other:
      (f, h) = r
      CX.flat(FUn{Q.ITable{other}}, st, XChk{f})

def CX.cut_rows.c(+g: Nat, i: Q.Instr, st: CStats, r: CH.CFrame & U32) -> XR:
  match i:
    case Q.IHead{n}:
      (f, +h) = r
      CX.pushc(st, CH.CFrame.head(f, n))
    case Q.ITable{op}:
      CX.cut_rows.t(g, op, st, r)
    case other:
      (f, h) = r
      CX.flat(FUn{other}, st, XChk{f})

def CX.cut_rows(+g: Nat, i: Q.Instr, st: CStats, x: XF) -> XR:
  match x:
    case XFlat{f}:
      CX.flat(FUn{i}, st, XFlat{f})
    case XChk{f}:
      CX.cut_rows.c(g, i, st, CH.CFrame.height(f))

# ---- drop / rename on the trees (the ghost gives the errors and the output names) ----

def CX.dr.c(op: Q.TOp, st: CStats, +h: U32, cols: List<&1, CH.CNamed>, +s2: List<&2, S.Field>) -> XR:
  match op:
    case Q.TDrop{ns}:
      CX.pushc(st, CH.CFrame{h, CX.keep(cols, CX.names(s2))})
    case Q.TRename{ps}:
      CX.pushc(st, CH.CFrame{h, CX.renm(cols, s2)})
    case other:
      CX.flat(FUn{Q.ITable{other}}, st, XChk{CH.CFrame{h, cols}})

def CX.dr.b(op: Q.TOp, st: CStats, go: GO, x: XF) -> XR:
  match go:
    case GFail{e}:
      CX.flat(FUn{Q.ITable{op}}, st, x)
    case GOk{+s2}:
      match x:
        case XFlat{f}:
          CX.flat(FUn{Q.ITable{op}}, st, XFlat{f})
        case XChk{f}:
          match f:
            case CH.CFrame{h, cols}:
              CX.dr.c(op, st, h, cols, s2)

def CX.dr.a(+op: Q.TOp, st: CStats, r: XF & List<&2, S.Field>) -> XR:
  (x, s) = r
  CX.dr.b(op, st, CX.gok(Q.Exec.table(op, CX.ghost(s))), x)

# ---- group_by: flat (the F32 scatters are serial, D4), over the columns it reads only ----

def CX.gb.b(i: Q.Instr, +refs: List<&2, String>, st: CStats, go: GO, x: XF) -> XR:
  match go:
    case GFail{e}:
      CX.flat(FUn{i}, st, x)
    case GOk{s2}:
      match x:
        case XFlat{f}:
          CX.flat(FUn{i}, st, XFlat{f})
        case XChk{f}:
          match f:
            case CH.CFrame{h, cols}:
              CX.flat(FUn{i}, st, XChk{CH.CFrame{h, CX.keep(cols, refs)}})

def CX.gb.a(+ks: List<&2, X.Expr>, +as: List<&2, X.Expr>, +mo: Bool, st: CStats, r: XF & List<&2, S.Field>) -> XR:
  (x, s) = r
  CX.gb.b(Q.IGroupBy{ks, as, mo}, List.append(&2, String, V.Eval.refs(ks), V.Eval.refs(as)), st, CX.gok(G.GroupBy.run(CX.ghost(s), ks, as, mo)), x)

# ---- one input ----

def CX.unary(+g: Nat, i: Q.Instr, st: CStats, x: XF) -> XR:
  match i:
    case Q.IFilter{+pred}:
      CX.filter(g, pred, st, x)
    case Q.IWith{+es}:
      CX.wc(g, es, st, x)
    case Q.ISelect{+es}:
      CX.sel(g, es, st, x)
    case Q.IHead{n}:
      CX.cut_rows(g, Q.IHead{n}, st, x)
    case Q.ITable{op}:
      match op:
        case Q.TSlice{o, l}:
          CX.cut_rows(g, Q.ITable{Q.TSlice{o, l}}, st, x)
        case Q.TTail{n}:
          CX.cut_rows(g, Q.ITable{Q.TTail{n}}, st, x)
        case Q.TDrop{ns}:
          CX.dr.a(Q.TDrop{ns}, st, CX.xschema(x))
        case Q.TRename{ps}:
          CX.dr.a(Q.TRename{ps}, st, CX.xschema(x))
        case other:
          CX.flat(FUn{Q.ITable{other}}, st, x)
    case Q.IGroupBy{+ks, +as, +mo}:
      CX.gb.a(ks, as, mo, st, CX.xschema(x))
    case other:
      CX.flat(FUn{other}, st, x)

# ==== two inputs ====

def CX.join.b(+how: J.JoinHow, +lo: List<&2, String>, +ro: List<&2, String>, l: C.Frame, r: CStats & C.Frame) -> XR:
  (st, rf) = r
  CX.xr(CStats.flat(st), J.Join.run(how, l, rf, lo, ro))

def CX.join.a(+how: J.JoinHow, +lo: List<&2, String>, +ro: List<&2, String>, xr: XF, r: CStats & C.Frame) -> XR:
  (st, l) = r
  CX.join.b(how, lo, ro, l, CX.xflat(st, xr))

# a join runs today's flat code (both inputs flattened, left first)
def CX.join(+how: J.JoinHow, +lo: List<&2, String>, +ro: List<&2, String>, st: CStats, xl: XF, xr: XF) -> XR:
  CX.join.a(how, lo, ro, xr, CX.xflat(st, xl))

def CX.cat.flat.b(+i: U32, l: C.Frame, r: CStats & C.Frame) -> XR:
  (st, rf) = r
  CX.xr(CStats.flat(st), TV.Concat.two(i, l, rf))

def CX.cat.flat.a(+i: U32, xr: XF, r: CStats & C.Frame) -> XR:
  (st, l) = r
  CX.cat.flat.b(i, l, CX.xflat(st, xr))

def CX.cat.flat(+i: U32, st: CStats, xl: XF, xr: XF) -> XR:
  CX.cat.flat.a(i, xr, CX.xflat(st, xl))

def CX.cat.res(+g: Nat, st: CStats, r: E.ResT(CH.CFrame)) -> XR:
  match r:
    case Fail{e}:
      XR{st, Fail{e}}
    case Done{f}:
      CX.pushc(st, f)

def CX.cat.c2(+g: Nat, l: CH.CFrame, r: CStats & CH.CFrame) -> XR:
  (st, rf) = r
  CX.cat.res(g, st, CH.CFrame.concat(l, rf))

def CX.cat.c1(+g: Nat, xr: XF, r: CStats & CH.CFrame) -> XR:
  (st, l) = r
  CX.cat.c2(g, l, CX.xchk(g, st, xr))

def CX.cat.go(+g: Nat, +i: U32, st: CStats, xl: XF, xr: XF, go: GO) -> XR:
  match go:
    case GFail{e}:
      CX.cat.flat(i, st, xl, xr)
    case GOk{s2}:
      CX.cat.c1(g, xr, CX.xchk(g, st, xl))

def CX.cat.s(+g: Nat, +i: U32, st: CStats, xl: XF, r: XF & List<&2, S.Field>, sl: List<&2, S.Field>) -> XR:
  (xr, sr) = r
  CX.cat.go(g, i, st, xl, xr, CX.gok(TV.Concat.two(i, CX.ghost(sl), CX.ghost(sr))))

def CX.cat.k(+g: Nat, +i: U32, st: CStats, r: XF & List<&2, S.Field>, xr: XF) -> XR:
  (xl, sl) = r
  CX.cat.s(g, i, st, xl, CX.xschema(xr), sl)

def CX.ischk(x: XF) -> XF & Bool:
  match x:
    case XFlat{f}:
      (XFlat{f}, False{})
    case XChk{f}:
      (XChk{f}, True{})

def CX.cat.q(+g: Nat, +i: U32, any: Bool, st: CStats, xl: XF, xr: XF) -> XR:
  match any:
    case True{}:
      CX.cat.k(g, i, st, CX.xschema(xl), xr)
    case False{}:
      CX.cat.flat(i, st, xl, xr)

def CX.cat.p(+g: Nat, +i: U32, st: CStats, a: XF & Bool, b: XF & Bool) -> XR:
  (xl, cl) = a
  (xr, cr) = b
  CX.cat.q(g, i, Bool.or(cl, cr), st, xl, xr)

# concat: two flat inputs run today's TV.Concat.two; otherwise the ghost checks the schemas (v0.1's error)
# and the frames become one node per tree (CH.CFrame.concat: the row cap with v0.1's text; rebalanced lazily)
def CX.cat(+g: Nat, +i: U32, st: CStats, xl: XF, xr: XF) -> XR:
  CX.cat.p(g, i, st, CX.ischk(xl), CX.ischk(xr))

# ==== the runner: Exec's postfix code over a stack of XF ====

# a pre-chunked source (the benchmark's chunked inputs; W6 hands the reader's leaves over this way)
type PNF is Type:
  PNF{name: String, f: CH.CFrame}

type CSt is Type:
  CSt{env: P.Env, pre: List<&1, PNF>, st: CStats, r: E.ResT(List<&1, XF>)}

def CX.push(env: P.Env, pre: List<&1, PNF>, x: XR, stack: List<&1, XF>) -> CSt:
  match x:
    case XR{st, r}:
      match r:
        case Fail{e}:
          CSt{env, pre, st, Fail{e}}
        case Done{f}:
          CSt{env, pre, st, Done{f <> stack}}

def CX.fail(env: P.Env, pre: List<&1, PNF>, st: CStats, e: E.Err) -> CSt:
  CSt{env, pre, st, Fail{e}}

# the schema of a source / scan frame must be the plan's (Exec.check's text)
def CX.chk.k(r: E.ResT(C.Frame)) -> Maybe<&2, E.Err>:
  match r:
    case Fail{e}:
      Some{e}
    case Done{f}:
      None{}

def CX.chk(+what: String, +s: List<&2, S.Field>, +fs: List<&2, S.Field>) -> Maybe<&2, E.Err>:
  CX.chk.k(Q.Exec.check.k(S.Schema.eq(fs, s), C.Frame.empty(), what, s, fs))

def CX.src.k(env: P.Env, pre: List<&1, PNF>, st: CStats, stack: List<&1, XF>, m: Maybe<&2, E.Err>, x: XF) -> CSt:
  match m:
    case Some{e}:
      CSt{env, pre, st, Fail{e}}
    case None{}:
      CSt{env, pre, st, Done{x <> stack}}

def CX.src.x(env: P.Env, pre: List<&1, PNF>, st: CStats, stack: List<&1, XF>, +what: String, +s: List<&2, S.Field>, r: XF & List<&2, S.Field>) -> CSt:
  (x, +fs) = r
  CX.src.k(env, pre, st, stack, CX.chk(what, s, fs), x)

# a frame of env (taken on its last use, cloned before), as Exec.source
def CX.src.e(+n: String, +s: List<&2, S.Field>, pre: List<&1, PNF>, st: CStats, stack: List<&1, XF>, r: P.Env & Maybe<&1, C.Frame>) -> CSt:
  (env, m) = r
  match m:
    case None{}:
      CSt{env, pre, st, Fail{E.InvalidOperation{"source not in env: " ++ n}}}
    case Some{f}:
      CX.src.x(env, pre, st, stack, "source " ++ n, s, CX.xschema(XFlat{f}))

# ---- pre-chunked sources: take on the last use, a clone of the trees before ----

def CX.pre.two(n: String, rest: List<&1, PNF>, r: CH.CFrame & CH.CFrame) -> List<&1, PNF> & Maybe<&1, CH.CFrame>:
  (a, b) = r
  (PNF{n, a} <> rest, Some{b})

def CX.pre.hit(last: Bool, n: String, f: CH.CFrame, rest: List<&1, PNF>) -> List<&1, PNF> & Maybe<&1, CH.CFrame>:
  match last:
    case True{}:
      (rest, Some{f})
    case False{}:
      CX.pre.two(n, rest, CX.cfclone(f))

def CX.pre.k(eq: Bool, last: Bool, n: String, f: CH.CFrame, r: List<&1, PNF> & Maybe<&1, CH.CFrame>) -> List<&1, PNF> & Maybe<&1, CH.CFrame>:
  match eq:
    case True{}:
      (rest, m) = r
      CX.pre.hit(last, n, f, rest)
    case False{}:
      (rest, m) = r
      (PNF{n, f} <> rest, m)

# the pre-chunked frame of a name: taken on its last use, cloned (CX.cfclone) before
def CX.pre.get(+last: Bool, pre: List<&1, PNF>, +name: String) -> List<&1, PNF> & Maybe<&1, CH.CFrame>:
  match pre:
    case Nil{}:
      (Nil{}, None{})
    case PNF{+n, f} <> rest:
      CX.pre.k(String.eq(n, name), last, n, f, CX.pre.get(last, rest, name))

def CX.src.p(+n: String, +s: List<&2, S.Field>, +last: Bool, env: P.Env, st: CStats, stack: List<&1, XF>, r: List<&1, PNF> & Maybe<&1, CH.CFrame>) -> CSt:
  (pre, m) = r
  match m:
    case Some{f}:
      CX.src.x(env, pre, st, stack, "source " ++ n, s, CX.xschema(XChk{f}))
    case None{}:
      CX.src.e(n, s, pre, st, stack, Q.Exec.source.get(last, env, n))

def CX.scan.k(+path: String, +s: List<&2, S.Field>, pre: List<&1, PNF>, st: CStats, stack: List<&1, XF>, r: P.Env & Maybe<&1, C.Frame>) -> CSt:
  (env, m) = r
  match m:
    case None{}:
      CSt{env, pre, st, Fail{E.InvalidOperation{"exec: scan_csv not materialised: " ++ path}}}
    case Some{f}:
      CX.src.x(env, pre, st, stack, "scan_csv " ++ path, s, CX.xschema(XFlat{f}))

def CX.un.pop(+g: Nat, i: Q.Instr, env: P.Env, pre: List<&1, PNF>, st: CStats, stack: List<&1, XF>) -> CSt:
  match stack:
    case Nil{}:
      CSt{env, pre, st, Fail{Q.Exec.underflow()}}
    case x <> t:
      CX.push(env, pre, CX.unary(g, i, st, x), t)

def CX.join.pop(+how: J.JoinHow, +lo: List<&2, String>, +ro: List<&2, String>, env: P.Env, pre: List<&1, PNF>, st: CStats, stack: List<&1, XF>) -> CSt:
  match stack:
    case xr <> xl <> t:
      CX.push(env, pre, CX.join(how, lo, ro, st, xl, xr), t)
    case other:
      CSt{env, pre, st, Fail{Q.Exec.underflow()}}

def CX.cat.pop(+g: Nat, +k: U32, env: P.Env, pre: List<&1, PNF>, st: CStats, stack: List<&1, XF>) -> CSt:
  match stack:
    case xr <> xl <> t:
      CX.push(env, pre, CX.cat(g, k, st, xl, xr), t)
    case other:
      CSt{env, pre, st, Fail{Q.Exec.underflow()}}

# one instruction (Exec.step.pure's dispatch over the XF stack)
def CX.step.pure(+g: Nat, i: Q.Instr, env: P.Env, pre: List<&1, PNF>, st: CStats, stack: List<&1, XF>) -> CSt:
  match i:
    case Q.IScan{+path, o, +s}:
      CX.scan.k(path, s, pre, st, stack, P.Env.scan_take(env))
    case Q.ISource{+n, +s, +last}:
      CX.src.p(n, s, last, env, st, stack, CX.pre.get(last, pre, n))
    case Q.IJoin{+how, +lo, +ro}:
      CX.join.pop(how, lo, ro, env, pre, st, stack)
    case Q.IConcat{+k}:
      CX.cat.pop(g, k, env, pre, st, stack)
    case other:
      CX.un.pop(g, other, env, pre, st, stack)

def CX.step(+g: Nat, i: Q.Instr, s: CSt) -> CSt:
  match s:
    case CSt{env, pre, st, r}:
      match r:
        case Fail{e}:
          CSt{env, pre, st, Fail{e}}
        case Done{stack}:
          CX.step.pure(g, i, env, pre, st, stack)

def CX.loop(+g: Nat, code: List<&2, Q.Instr>, s: CSt) -> CSt:
  match code:
    case Nil{}:
      s
    case i <> t:
      CX.loop(g, t, CX.step(g, i, s))

def CX.start(+g: Nat, +p: P.Plan, env: P.Env, pre: List<&1, PNF>) -> CSt:
  CX.loop(g, Q.Exec.mark(Q.Exec.compile(p, Nil{})), CSt{env, pre, CStats.zero(), Done{Nil{}}})

# ---- the root steps (Exec.run_phys's): Sort + Head, Filter + plain Select ----

type RootK is Data:
  RSortHead{ks: List<&2, O.SortKey>, n: U32}
  RFsel{pred: X.Expr, es: List<&2, X.Expr>}

def CX.top.sh(+ks: List<&2, O.SortKey>, +n: U32, r: CStats & C.Frame) -> XR:
  (st, f) = r
  CX.xr(CStats.flat(st), O.Sort.frame_head(f, ks, n))

def CX.top.k(+g: Nat, k: RootK, st: CStats, x: XF) -> XR:
  match k:
    case RSortHead{ks, n}:
      CX.top.sh(ks, n, CX.xflat(st, x))
    case RFsel{pred, es}:
      CX.fsel(g, pred, es, st, x)

def CX.top(+g: Nat, s: CSt, k: RootK) -> CSt:
  match s:
    case CSt{env, pre, st, r}:
      match r:
        case Fail{e}:
          CSt{env, pre, st, Fail{e}}
        case Done{stack}:
          match stack:
            case Nil{}:
              CSt{env, pre, st, Fail{Q.Exec.underflow()}}
            case x <> t:
              CX.push(env, pre, CX.top.k(g, k, st, x), t)

def CX.phys.h(+g: Nat, +n: U32, x: P.Plan, env: P.Env, pre: List<&1, PNF>) -> CSt:
  match x:
    case P.Sort{+ks, y}:
      CX.top(g, CX.start(g, y, env, pre), RSortHead{ks, n})
    case other:
      CX.start(g, P.Head{n, other}, env, pre)

def CX.phys.f(+g: Nat, plain: Bool, +es: List<&2, X.Expr>, +pred: X.Expr, +y: P.Plan, env: P.Env, pre: List<&1, PNF>) -> CSt:
  match plain:
    case True{}:
      CX.top(g, CX.start(g, y, env, pre), RFsel{pred, es})
    case False{}:
      CX.start(g, P.Select{es, P.Filter{pred, y}}, env, pre)

def CX.phys.s(+g: Nat, +es: List<&2, X.Expr>, x: P.Plan, env: P.Env, pre: List<&1, PNF>) -> CSt:
  match x:
    case P.Filter{+pred, +y}:
      CX.phys.f(g, Q.Exec.plain(es), es, pred, y, env, pre)
    case other:
      CX.start(g, P.Select{es, other}, env, pre)

# the code of p over the XF stack, with Exec.run_phys's root steps
def CX.phys(+g: Nat, +p: P.Plan, env: P.Env, pre: List<&1, PNF>) -> CSt:
  match p:
    case P.Head{+n, x}:
      CX.phys.h(g, n, x, env, pre)
    case P.Select{+es, x}:
      CX.phys.s(g, es, x, env, pre)
    case other:
      CX.start(g, other, env, pre)

# ---- the result ----

def CX.fin.x(s: CSt) -> CStats & E.ResT(XF):
  match s:
    case CSt{env, pre, st, r}:
      match r:
        case Fail{e}:
          (st, Fail{e})
        case Done{stack}:
          match stack:
            case x <> Nil{}:
              (st, Done{x})
            case _:
              (st, Fail{E.InvalidOperation{"exec: malformed plan (not one result)"}})

def CX.fin.f(r: CStats & C.Frame) -> CStats & E.ResT(C.Frame):
  (st, f) = r
  (st, Done{f})

# the result frame, flattened if it is chunked (the last conversion, counted)
def CX.fin.r(r: CStats & E.ResT(XF)) -> CStats & E.ResT(C.Frame):
  (st, rx) = r
  match rx:
    case Fail{e}:
      (st, Fail{e})
    case Done{x}:
      CX.fin.f(CX.xflat(st, x))

# the chunked physical runner (Exec.run_phys's counterpart): pure, no IO, no binding checks; pre holds
# frames already chunked (by name, before env)
def CX.run(+g: Nat, +p: P.Plan, env: P.Env, pre: List<&1, PNF>) -> CStats & E.ResT(C.Frame):
  CX.fin.r(CX.fin.x(CX.phys(g, p, env, pre)))

# the same, the result left as it is (the benchmark times the final flatten apart: G6)
def CX.run_x(+g: Nat, +p: P.Plan, env: P.Env, pre: List<&1, PNF>) -> CStats & E.ResT(XF):
  CX.fin.x(CX.phys(g, p, env, pre))

# a result left chunked, flattened (counted)
def CX.out(st: CStats, r: E.ResT(XF)) -> CStats & E.ResT(C.Frame):
  CX.fin.r((st, r))

def CX.snd(r: CStats & E.ResT(C.Frame)) -> E.ResT(C.Frame):
  (st, x) = r
  x

# ==== the selector (DESIGN.md 16.5 D7) ====

def Exec.run_with.k(+g: Nat, +p: P.Plan, r: E.ResT(P.Env)) -> E.ResT(C.Frame):
  match r:
    case Fail{e}:
      Fail{e}
    case Done{env}:
      CX.snd(CX.run(g, p, env, Nil{}))

def Exec.run_with.c(+g: Nat, +csv: R.CsvEngine, +p: P.Plan, env: P.Env) -> IO(E.ResT(C.Frame)):
  do IO<E.ResT(C.Frame)>:
    r : E.ResT(P.Env) <- Q.Exec.prep(csv, p, env)
    return Exec.run_with.k(g, p, r)

# Exec.run by the engine: Reference is Exec.run itself (Exec.run_rd with the CSV engine csv); Chunked{g}
# runs the same checks and scan reads (Exec.prep), then the chunked runner at grain 2^g
def Exec.run_with_rd(+csv: R.CsvEngine, +eng: Engine, +p: P.Plan, env: P.Env) -> IO(E.ResT(C.Frame)):
  match eng:
    case Reference{}:
      Q.Exec.run_rd(csv, p, env)
    case Chunked{g}:
      Exec.run_with.c(g, csv, p, env)

def Exec.run_with(+eng: Engine, +p: P.Plan, env: P.Env) -> IO(E.ResT(C.Frame)):
  Exec.run_with_rd(R.CsvV01{}, eng, p, env)

# Lazy.collect by the engine (the release optimizer, then Exec.run_with)
def Lazy.collect_with(+eng: Engine, +p: P.Plan, env: P.Env) -> IO(E.ResT(C.Frame)):
  Exec.run_with(eng, P.Optimize.release(p), env)

def Lazy.collect_with_rd(+csv: R.CsvEngine, +eng: Engine, +p: P.Plan, env: P.Env) -> IO(E.ResT(C.Frame)):
  Exec.run_with_rd(csv, eng, P.Optimize.release(p), env)

# the chunked engine at the default grain (CH.Ch.grain() = 14: leaves of 16384 rows)
def Engine.chunked() -> Engine:
  Chunked{CH.Ch.grain()}

def Engine.reference() -> Engine:
  Reference{}
