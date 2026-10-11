# group_by key encoding without copies (v0.2 T5.4b; DESIGN.md 14 T5.4b).
#
# Grp.encode_keep (the key column is kept for the output gather at `first`) used to CLONE the key column; it
# now reads the key's data buffer and mask in place (Grp.bw.go / Grp.bk: one borrowed pass writes the order
# words or codes and hands the buffers back), cloning only the validity mask of a key WITH nulls. A single
# Dictionary or Bool key goes further: Grp.kd.go densifies the codes `x + 1` (null 0) straight from the key's
# own buffers (no codes array). Pinned here:
#   part 1  (n = 3000) for every key dtype (u32 / i32 / f32 / bool / Raw str / Dictionary str with nulls, an
#           all-null key) group_by [key] (the one-pass path for Dictionary / Bool, the borrowed encoder for the
#           rest) gives the same frame (DF.dump: F32 bits, validity, key column) as group_by [key, lit 1], a
#           route through Grp.codes / Grp.compact with no one-pass shortcut, for 9 aggregates
#   part 2  hand-derived frames per key dtype (8 rows): groups in first-appearance order, the key column
#           (null, NaN, -0.0 = 0.0 merged and shown at its first row, negative i32) intact after the borrow
#   part 3  0, 1 and 2 rows, an all-null key, a Dictionary key whose mask is a real mask (nulls) and whose
#           dictionary has entries no row uses
# Part 2 frames (v = [1..8]; every group lists its rows):
#   kb  bool [true, null, false, true, null, false, true, false]: true (0 3 6) sum 12 len 3; null (1 4) 7, 2;
#       false (2 5 7) 17, 3
#   kd  str  [b, a, null, b, c, null, a, b] (Dictionary): b (0 3 7) 13, 3; a (1 6) 9, 2; null (2 5) 9, 2; c (4) 5, 1
#   ki  i32  [-1, 2, null, -1, 2, 0, null, -3]: -1 (0 3) 5, 2; 2 (1 4) 7, 2; null (2 6) 10, 2; 0 (5) 6, 1; -3 (7) 8, 1
#   kf  f32  [nan, -0.0, 0.0, nan, null, inf, -0.0, null]: nan (0 3) 5, 2; -0.0 (1 2 6) 12, 3 (the key shows
#       row 1's -0.0); null (4 7) 13, 2; inf (5) 6, 1
#   ku  u32  [4e9, 7, null, 4e9, 7, 0, null, 0] (range >= 2^20: rank codes): 4e9 (0 3) 5, 2; 7 (1 4) 7, 2;
#       null (2 6) 10, 2; 0 (5 7) 14, 2
import Base
import ./../frame.bend as DF
import ./../src/dtype.bend as D
import ./../src/err.bend as E
import ./../src/kernels.bend as K
import ./../src/column.bend as C
import ./../src/strs.bend as ST
import ./../src/expr.bend as X
import ./../src/groupby.bend as G

def nan() -> F32:
  F32.div(0.0, 0.0)

def inf() -> F32:
  F32.div(1.0, 0.0)

def d_of(+n: U32) -> Nat:
  K.Kernel.depth_for(n)

def imap(~U: Data, ~f: U32 -> U, +n: U32, +z: U) -> Array<U>:
  K.Kernel.map(~U32, ~U, ~f, n, d_of(n), K.Kernel.iota(n, d_of(n)), z)

def mask(~f: U32 -> U32, +n: U32) -> C.Valid:
  C.Mask{imap(~U32, ~f, n, 0)}

# ---- part 1 keys (row i) ----
def vn(+i: U32) -> U32:
  Bool.pick(U32, U32.is_eq(U32.mod(i, 7), 3), 0, 1)

def kn(+n: U32) -> C.Column:
  C.CU32{n, d_of(n), mask(~(i => vn(i)), n), imap(~U32, ~(i => U32.mod(i, 6)), n, 0)}

def vi(+i: U32) -> U32:
  Bool.pick(U32, U32.is_eq(U32.mod(i, 11), 4), 0, 1)

def ki(+n: U32) -> C.Column:
  C.CI32{n, d_of(n), mask(~(i => vi(i)), n), imap(~U32, ~(i => U32.add(U32.mod(i, 5), 4294967294)), n, 0)}

def fk.b(+r: U32) -> F32:
  match r:
    case 0:
      nan()
    case 1:
      F32.neg(0.0)
    case 2:
      0.0
    case 3:
      inf()
    case 4:
      1.5
    case _:
      F32.neg(inf())

def fk(+i: U32) -> F32:
  fk.b(U32.mod(i, 6))

def vk(+i: U32) -> U32:
  Bool.pick(U32, U32.is_eq(U32.mod(i, 13), 5), 0, 1)

def kf(+n: U32) -> C.Column:
  C.CF32{n, d_of(n), mask(~(i => vk(i)), n), imap(~F32, ~(i => fk(i)), n, 0.0)}

def vb(+i: U32) -> U32:
  Bool.pick(U32, U32.is_eq(U32.mod(i, 5), 1), 0, 1)

def kb(+n: U32) -> C.Column:
  C.CBool{n, d_of(n), mask(~(i => vb(i)), n), imap(~U32, ~(i => Bool.to_u32(U32.is_eq(U32.mod(i, 3), 0))), n, 0)}

def vs(+i: U32) -> U32:
  Bool.pick(U32, U32.is_eq(U32.mod(i, 9), 2), 0, 1)

def ks(+n: U32) -> C.Column:
  C.CStr{n, d_of(n), mask(~(i => vs(i)), n), ST.SRaw{imap(~String, ~(i => U32.show(U32.mod(i, 7))), n, "")}}

def kz(+n: U32) -> C.Column:
  C.CU32{n, d_of(n), C.Mask{K.Kernel.const(~U32, d_of(n), 0)}, imap(~U32, ~(i => U32.mod(i, 4)), n, 0)}

# ---- part 1 values ----
def word(+i: U32) -> U32:
  U32.mul(i, 2654435761)

def vy(+i: U32) -> U32:
  Bool.pick(U32, U32.is_eq(U32.mod(i, 5), 0), 0, 1)

def vf(+i: U32) -> U32:
  Bool.pick(U32, U32.is_eq(U32.mod(i, 4), 3), 0, 1)

def fv(+i: U32) -> F32:
  Bool.pick(F32, U32.is_eq(i, 25), inf(), Bool.pick(F32, U32.is_eq(U32.mod(i, 97), 5), nan(), Bool.pick(F32, U32.is_eq(U32.mod(i, 91), 3), F32.neg(0.0), F32.div(U32.to_f32(U32.mod(U32.mul(i, 37), 1009)), 8.0))))

# the frame; `dict` re-encodes every str column as a Dictionary column
def frame(+n: U32, +dict: Bool) -> C.Frame:
  C.Frame.encode(C.Frame{n, [C.Named{"kn", kn(n)}, C.Named{"ki", ki(n)}, C.Named{"kf", kf(n)}, C.Named{"kb", kb(n)}, C.Named{"ks", ks(n)}, C.Named{"kz", kz(n)}, C.Named{"x", C.CU32{n, d_of(n), C.AllValid{}, imap(~U32, ~(i => word(i)), n, 0)}}, C.Named{"y", C.CI32{n, d_of(n), mask(~(i => vy(i)), n), imap(~U32, ~(i => word(i)), n, 0)}}, C.Named{"f", C.CF32{n, d_of(n), mask(~(i => vf(i)), n), imap(~F32, ~(i => fv(i)), n, 0.0)}}, C.Named{"g", C.CF32{n, d_of(n), C.AllValid{}, imap(~F32, ~(i => F32.div(U32.to_f32(U32.mod(U32.mul(i, 13), 997)), 3.0)), n, 0.0)}}, C.Named{"s", ks(n)}]}, dict)

def col(n: String) -> X.Expr:
  X.Col{n}

def agg(+op: X.AggOp, +c: String) -> X.Expr:
  X.Alias{X.Agg{op, X.Col{c}}, c ++ "_" ++ X.AggOp.name(op)}

def len1() -> X.Expr:
  X.Alias{X.Agg{X.Len{}, X.Lit{D.SU32{1}}}, "len"}

def aggs() -> List<&2, X.Expr>:
  [len1(), agg(X.Sum{}, "x"), agg(X.Mean{}, "f"), agg(X.Max{}, "y"), agg(X.Count{}, "f"), agg(X.Min{}, "f"), agg(X.Last{}, "s"), agg(X.First{}, "g"), agg(X.Std{}, "g")]

def names(+key: String) -> List<&2, String>:
  [key, "len", "x_sum", "f_mean", "y_max", "f_count", "f_min", "s_last", "g_first", "g_std"]

def c1() -> X.Expr:
  X.Alias{X.Lit{D.SU32{1}}, "c1"}

def dumpk(+key: String, r: E.ResT(C.Frame)) -> String:
  match r:
    case Fail{e}:
      "error: " ++ E.Err.show(e)
    case Done{f}:
      DF.dump(C.Frame.select_names(f, names(key)))

def cmp(+key: String, a: E.ResT(C.Frame), b: E.ResT(C.Frame)) -> String:
  Bool.pick(String, String.eq(dumpk(key, a), dumpk(key, b)), "ok", "DIFF")

def one(+n: U32, +dict: Bool, +key: String) -> String:
  key ++ ": " ++ cmp(key, G.GroupBy.run(frame(n, dict), [col(key)], aggs(), True{}), G.GroupBy.run(frame(n, dict), [col(key), c1()], aggs(), True{}))

# ---- part 2 ----
def mk.k(name: String, r: E.ResT(C.Column)) -> C.Named:
  match r:
    case Fail{e}:
      C.Named{E.Err.show(e), C.CU32{0, 0n, C.AllValid{}, [0 : U32*1n]}}
    case Done{c}:
      C.Named{name, c}

def mk(name: String, xs: List<&2, D.Scalar>, +t: D.DType) -> C.Named:
  mk.k(name, C.Column.from_scalars(xs, t))

def u(v: U32) -> D.Scalar:
  D.SU32{v}

def i(v: U32) -> D.Scalar:
  D.SI32{D.I32{v}}

def b(v: Bool) -> D.Scalar:
  D.SBool{v}

def f(v: F32) -> D.Scalar:
  D.SF32{v}

def s(v: String) -> D.Scalar:
  D.SStr{v}

def nul() -> D.Scalar:
  D.SNull{}

def vcol() -> C.Named:
  mk("v", [u(1), u(2), u(3), u(4), u(5), u(6), u(7), u(8)], D.TU32{})

def t8(kc: C.Named) -> E.ResT(C.Frame):
  C.Frame.from_columns([kc, vcol()])

def dictd(+dict: Bool, r: E.ResT(C.Frame)) -> E.ResT(C.Frame):
  match r:
    case Fail{e}:
      Fail{e}
    case Done{f0}:
      Done{C.Frame.encode(f0, dict)}

def head4(r: E.ResT(C.Frame)) -> E.ResT(C.Frame):
  match r:
    case Fail{e}:
      Fail{e}
    case Done{f0}:
      Done{C.Frame.head(f0, 4)}

def sumlen() -> List<&2, X.Expr>:
  [agg(X.Sum{}, "v"), len1()]

def gb(+key: String, as: List<&2, X.Expr>, r: E.ResT(C.Frame)) -> String:
  match r:
    case Fail{e}:
      "error: " ++ E.Err.show(e)
    case Done{f0}:
      DF.dump(G.GroupBy.run(f0, [col(key)], as, True{}))

def main() -> IO(Unit):
  do IO<Unit>:
    IO.print(one(3000, False{}, "kn"))
    IO.print(one(3000, False{}, "ki"))
    IO.print(one(3000, False{}, "kf"))
    IO.print(one(3000, False{}, "kb"))
    IO.print(one(3000, False{}, "ks"))
    IO.print(one(3000, True{}, "ks"))
    IO.print(one(3000, False{}, "kz"))
    IO.print(one(1, False{}, "kn"))
    IO.print(one(2, True{}, "ks"))
    IO.print(one(1, False{}, "kb"))
    IO.print(gb("kb", sumlen(), t8(mk("kb", [b(True{}), nul(), b(False{}), b(True{}), nul(), b(False{}), b(True{}), b(False{})], D.TBool{}))))
    IO.print(gb("kd", sumlen(), dictd(True{}, t8(mk("kd", [s("b"), s("a"), nul(), s("b"), s("c"), nul(), s("a"), s("b")], D.TStr{})))))
    IO.print(gb("kd", sumlen(), dictd(False{}, t8(mk("kd", [s("b"), s("a"), nul(), s("b"), s("c"), nul(), s("a"), s("b")], D.TStr{})))))
    IO.print(gb("ki", sumlen(), t8(mk("ki", [i(4294967295), i(2), nul(), i(4294967295), i(2), i(0), nul(), i(4294967293)], D.TI32{}))))
    IO.print(gb("kf", sumlen(), t8(mk("kf", [f(nan()), f(F32.neg(0.0)), f(0.0), f(nan()), nul(), f(inf()), f(F32.neg(0.0)), nul()], D.TF32{}))))
    IO.print(gb("ku", sumlen(), t8(mk("ku", [u(4000000000), u(7), nul(), u(4000000000), u(7), u(0), nul(), u(0)], D.TU32{}))))
    # a Dictionary key whose dictionary (a, b, c) has an entry no row uses: the first 4 rows (b, a, null, b)
    IO.print(gb("kd", sumlen(), head4(dictd(True{}, t8(mk("kd", [s("b"), s("a"), nul(), s("b"), s("c"), nul(), s("a"), s("b")], D.TStr{}))))))
    # empty frames
    IO.print(gb("kd", sumlen(), C.Frame.from_columns([mk("kd", [], D.TStr{}), mk("v", [], D.TU32{})])))
    IO.print(gb("kb", sumlen(), C.Frame.from_columns([mk("kb", [], D.TBool{}), mk("v", [], D.TU32{})])))
#|kn: ok
#|ki: ok
#|kf: ok
#|kb: ok
#|ks: ok
#|ks: ok
#|kz: ok
#|kn: ok
#|ks: ok
#|kb: ok
#|frame
#|height	3
#|width	3
#|col	bool	"kb"
#|col	u32	"v_sum"
#|col	u32	"len"
#|row	true	12	3
#|row	null	7	2
#|row	false	17	3
#|
#|frame
#|height	4
#|width	3
#|col	str	"kd"
#|col	u32	"v_sum"
#|col	u32	"len"
#|row	"b"	13	3
#|row	"a"	9	2
#|row	null	9	2
#|row	"c"	5	1
#|
#|frame
#|height	4
#|width	3
#|col	str	"kd"
#|col	u32	"v_sum"
#|col	u32	"len"
#|row	"b"	13	3
#|row	"a"	9	2
#|row	null	9	2
#|row	"c"	5	1
#|
#|frame
#|height	5
#|width	3
#|col	i32	"ki"
#|col	u32	"v_sum"
#|col	u32	"len"
#|row	-1	5	2
#|row	2	7	2
#|row	null	10	2
#|row	0	6	1
#|row	-3	8	1
#|
#|frame
#|height	4
#|width	3
#|col	f32	"kf"
#|col	u32	"v_sum"
#|col	u32	"len"
#|row	0x7fc00000	5	2
#|row	0x80000000	12	3
#|row	null	13	2
#|row	0x7f800000	6	1
#|
#|frame
#|height	4
#|width	3
#|col	u32	"ku"
#|col	u32	"v_sum"
#|col	u32	"len"
#|row	4000000000	5	2
#|row	7	7	2
#|row	null	10	2
#|row	0	14	2
#|
#|frame
#|height	3
#|width	3
#|col	str	"kd"
#|col	u32	"v_sum"
#|col	u32	"len"
#|row	"b"	5	2
#|row	"a"	2	1
#|row	null	3	1
#|
#|frame
#|height	0
#|width	3
#|col	str	"kd"
#|col	u32	"v_sum"
#|col	u32	"len"
#|
#|frame
#|height	0
#|width	3
#|col	bool	"kb"
#|col	u32	"v_sum"
#|col	u32	"len"
#|
