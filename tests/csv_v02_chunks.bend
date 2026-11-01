# W6.6: the v0.2 reader's chunk hand-off (Csv.read_v02_mode CMChk{g}: the combine cuts the regions' parts
# into leaves of 2^g rows across region boundaries, DESIGN.md 17.5) against the v0.1 reader (Csv.read_full)
# on every adversarial file of tests/csvadv, at grains 2^2 and 2^4 and tiny pieces (many regions, region
# edges everywhere inside the leaves). Every run checks:
#   * the frame flattened (CFrame.to_frame) gives v0.1's DF.dump AND storage (Raw / Dictionary size / a hash
#     of the codes: the merge's codes and EncAuto's fall back, tests/lib/v02cmp.bend), or v0.1's error;
#   * the chunk decision: a chunk frame iff v0.1 answers a frame of more than 2^g rows (else the flat frame);
#   * a chunk frame is WFCFrame (CFrame.check: one shape for every data and validity tree, the height,
#     unique names) and its shape is CH.CW.of's at grain g for its height (the shape CFrame.of_frame gives).
# Configurations x grain x pieces (13 runs per file): explicit schema EncAuto g2 {7, 4096} and g4 {3, 64};
# EncRaw g2 13; EncDict g2 5; EncAutoAt{2, 4} g2 5 (the Raw fall back at a row); EncAutoAt{0, 1} g4 3;
# EncAutoAt{3, 2} g2 7; inferred (infer_rows 100) g2 7; inferred (infer_rows 0) g4 64; one dtype too many
# g2 64; row cap 3 g2 31. The line is `<case>: ok <runs>` or the first run that differs; the last line counts
# the runs that produced a chunk frame (each one checked against the reference's height above).
import Base
import ./../src/err.bend as E
import ./../src/kernels.bend as K
import ./../src/column.bend as C
import ./../src/strs.bend as ST
import ./../src/csv.bend as V
import ./../src/chunks.bend as CH
import ./../bench/w6/cases.bend as CS
import ./../bench/w6/cmp.bend as M
import ./lib/v02cmp.bend as T

# ---- the shape checks ----

def Ck.eq(a: CH.Skel, b: CH.Skel) -> Bool:
  match a b:
    case CH.KLeaf{+x} CH.KLeaf{+y}:
      U32.is_eq(x, y)
    case CH.KNode{+r1, +l1, a1, b1} CH.KNode{+r2, +l2, a2, b2}:
      Bool.and(Bool.and(U32.is_eq(r1, r2), U32.is_eq(l1, l2)), Bool.and(Ck.eq(a1, a2), Ck.eq(b1, b2)))
    case _ _:
      False{}

def Ck.snd(r: CH.CW & CH.Skel) -> CH.Skel:
  (t, s) = r
  s

# CW.of's shape for n rows at grain g (what CFrame.of_frame gives a flat column of n rows)
def Ck.want(+g: Nat, +n: U32) -> CH.Skel:
  Ck.snd(CH.CW.skel(CH.CW.of(n, K.Kernel.depth_for(U32.max(n, 1)), g, Array.new(U32, K.Kernel.depth_for(U32.max(n, 1)), 0))))

def Ck.skel1.k(+h: U32, nm: String, rest: List<&1, CH.CNamed>, r: CH.CColumn & CH.Skel) -> CH.CFrame & CH.Skel:
  (c, s) = r
  (CH.CFrame{h, CH.CNamed{nm, c} <> rest}, s)

# the first column's data shape (a chunk frame always has columns)
def Ck.skel1(f: CH.CFrame) -> CH.CFrame & CH.Skel:
  match f:
    case CH.CFrame{+h, cols}:
      match cols:
        case Nil{}:
          (CH.CFrame{h, Nil{}}, CH.KLeaf{4294967295})
        case CH.CNamed{nm, c} <> rest:
          Ck.skel1.k(h, nm, rest, CH.CColumn.skel(c))

# the candidate's text, whether it was a chunk frame, a shape complaint
type CR is Data:
  CR{text: String, chk: Bool, bad: String}

def Ck.c3(+g: Nat, ok: Bool, +h: U32, r: CH.CFrame & CH.Skel) -> CR:
  (f, s) = r
  CR{T.Sg.text(Done{CH.CFrame.to_frame(f)}), True{}, Bool.pick(String, Bool.and(ok, Ck.eq(s, Ck.want(g, h))), "", " (chunk shape: not WFCFrame or not CW.of's)")}

def Ck.c2(+g: Nat, ok: Bool, r: CH.CFrame & U32) -> CR:
  (f, +h) = r
  Ck.c3(g, ok, h, Ck.skel1(f))

def Ck.c1(+g: Nat, r: CH.CFrame & Bool) -> CR:
  (f, ok) = r
  Ck.c2(g, ok, CH.CFrame.height(f))

def Ck.out(+g: Nat, r: E.ResT(V.CsvOut)) -> CR:
  match r:
    case Fail{e}:
      CR{T.Sg.text(Fail{e}), False{}, ""}
    case Done{o}:
      match o:
        case V.CsvFlat{f}:
          CR{T.Sg.text(Done{f}), False{}, ""}
        case V.CsvChk{f}:
          Ck.c1(g, CH.CFrame.check(f))

# ---- one configuration ----

# the reference: its text and whether it is a frame of more than 2^g rows
type RF is Data:
  RF{text: String, big: Bool}

def Ck.rf.k(+g: Nat, r: E.ResT(C.Frame)) -> RF:
  match r:
    case Fail{e}:
      RF{T.Sg.text(Fail{e}), False{}}
    case Done{C.Frame{+h, cols}}:
      RF{T.Sg.text(Done{C.Frame{h, cols}}), U32.is_lt(U32.shln(1, g), h)}

def Ck.ref(c: T.Cf, +g: Nat, +path: String) -> IO(RF):
  match c:
    case T.Cf{l, +schema, +hdr, +sep, +inf, +enc, +cap}:
      do IO<RF>:
        r : E.ResT(C.Frame) <- V.Csv.read_full(path, V.CsvOpts{Chr{sep}, hdr, inf}, T.Sch.dts(schema), enc, 1048576, cap)
        return Ck.rf.k(g, r)

def Ck.cand(c: T.Cf, +g: Nat, +path: String, +piece: U32) -> IO(CR):
  match c:
    case T.Cf{l, +schema, +hdr, +sep, +inf, +enc, +cap}:
      do IO<CR>:
        r : E.ResT(V.CsvOut) <- V.Csv.read_v02_mode(V.CMChk{g}, path, V.CsvOpts{Chr{sep}, hdr, inf}, T.Sch.dts(schema), enc, piece, cap)
        return Ck.out(g, r)

def Ck.label(c: T.Cf) -> String:
  match c:
    case T.Cf{l, schema, hdr, sep, inf, enc, cap}:
      l

# the first difference ("" none), runs, chunk frames
type ST2 is Data:
  ST2{v: String, n: U32, k: U32}

def Ck.why(+lab: String, +d: String, +big: Bool, +chk: Bool, +bad: String) -> String:
  Bool.pick(String, String.is_empty(d), Bool.pick(String, Bool.and(Bool.or(big, chk), Bool.not(Bool.and(big, chk))), lab ++ ": chunk decision " ++ Bool.pick(String, chk, "chunked", "flat") ++ " for a frame " ++ Bool.pick(String, big, "over", "within") ++ " 2^g rows", Bool.pick(String, String.is_empty(bad), "", lab ++ ":" ++ bad)), lab ++ ": " ++ d)

# a run against the reference: the text, the chunk decision, the shape
def Ck.judge(+lab: String, +ref: RF, r: CR, st: ST2) -> ST2:
  match ref r st:
    case RF{+rt, +big} CR{+text, +chk, +bad} ST2{+v, +n, +k}:
      Bool.pick(ST2, String.is_empty(v), ST2{Ck.why(lab, M.Cmp.diff(rt, text), big, chk, bad), U32.inc(n), U32.add(k, Bool.to_u32(chk))}, ST2{v, n, k})

def Ck.run.k(+lab: String, +ref: RF, st: ST2, r: CR) -> ST2:
  Ck.judge(lab, ref, r, st)

# the runs of one configuration at one grain, piece by piece
def Ck.pieces(f: Nat, +c: T.Cf, +g: Nat, +path: String, +ref: RF, ps: List<&2, U32>, st: ST2) -> IO(ST2):
  match f ps:
    case 0n _:
      IO.pure(ST2, st)
    case _ Nil{}:
      IO.pure(ST2, st)
    case 1n+p +q <> t:
      do IO<ST2>:
        r : CR <- Ck.cand(c, g, path, q)
        Ck.pieces(p, c, g, path, ref, t, Ck.run.k(Ck.label(c) ++ " g" ++ Nat.show(g) ++ " piece " ++ U32.show(q), ref, st, r))

type GC is Data:
  GC{c: T.Cf, g: Nat, ps: List<&2, U32>}

def Ck.all(cs: List<&2, GC>, +path: String, st: ST2) -> IO(ST2):
  match cs:
    case Nil{}:
      IO.pure(ST2, st)
    case GC{+c, +g, ps} <> t:
      do IO<ST2>:
        +ref : RF <- Ck.ref(c, g, path)
        st2 : ST2 <- Ck.pieces(40n, c, g, path, ref, ps, st)
        Ck.all(t, path, st2)

def Ck.cfgs(+schema: String, +hdr: Bool, +sep: U32) -> List<&2, GC>:
  [GC{T.Cf{"auto", schema, hdr, sep, 100, ST.EncAuto{}, 8388608}, 2n, [7, 4096]},
   GC{T.Cf{"auto", schema, hdr, sep, 100, ST.EncAuto{}, 8388608}, 4n, [3, 64]},
   GC{T.Cf{"raw", schema, hdr, sep, 100, ST.EncRaw{}, 8388608}, 2n, [13]},
   GC{T.Cf{"dict", schema, hdr, sep, 100, ST.EncDict{}, 8388608}, 2n, [5]},
   GC{T.Cf{"autoat 2 4", schema, hdr, sep, 100, ST.EncAutoAt{2, 4}, 8388608}, 2n, [5]},
   GC{T.Cf{"autoat 0 1", schema, hdr, sep, 100, ST.EncAutoAt{0, 1}, 8388608}, 4n, [3]},
   GC{T.Cf{"autoat 3 2", schema, hdr, sep, 100, ST.EncAutoAt{3, 2}, 8388608}, 2n, [7]},
   GC{T.Cf{"infer 100", "", hdr, sep, 100, ST.EncAuto{}, 8388608}, 2n, [7]},
   GC{T.Cf{"infer 0", "", hdr, sep, 0, ST.EncAuto{}, 8388608}, 4n, [64]},
   GC{T.Cf{"extra dtype", schema ++ "U", hdr, sep, 100, ST.EncAuto{}, 8388608}, 2n, [64]},
   GC{T.Cf{"cap 3", schema, hdr, sep, 100, ST.EncAuto{}, 3}, 2n, [31]}]

def Ck.line(+name: String, r: ST2) -> String & U32:
  match r:
    case ST2{+v, +n, +k}:
      (Bool.pick(String, String.is_empty(v), name ++ ": ok " ++ U32.show(n), name ++ ": DIFF " ++ v), k)

def Ck.file(+name: String, +schema: String, +hdr: Bool, +sep: U32) -> IO(String & U32):
  do IO<String & U32>:
    r : ST2 <- Ck.all(Ck.cfgs(schema, hdr, sep), "tests/csvadv/" ++ name ++ ".csv", ST2{"", 0, 0})
    return Ck.line(name, r)

def Ck.one(+only: String, c: CS.Mf) -> IO(String & U32):
  match c:
    case CS.Mf{+name, +schema, +hdr, +sep}:
      Bool.pick(IO(String & U32), Bool.or(String.is_empty(only), String.eq(only, name)), Ck.file(name, schema, hdr, sep), IO.pure(String & U32, ("", 0)))

def Ck.print(+k: U32, r: String & U32) -> IO(U32):
  (s, +k2) = r
  do IO<U32>:
    T.Run.print(s)
    return U32.add(k, k2)

def Ck.loop(+only: String, cs: List<&2, CS.Mf>, +k: U32) -> IO(U32):
  match cs:
    case Nil{}:
      IO.pure(U32, k)
    case c <> t:
      do IO<U32>:
        r : String & U32 <- Ck.one(only, c)
        +k2 : U32 <- Ck.print(k, r)
        Ck.loop(only, t, k2)

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<String> <- IO.args()
    +k : U32 <- Ck.loop(T.Run.only(args), CS.Cases.all(), 0)
    IO.print("chunk frames: " ++ U32.show(k))
#|quoted_nl: ok 13
#|quoted_nl_crlf: ok 13
#|quoted_nl_nofinal: ok 13
#|cr_soup: ok 13
#|cr_only_data: ok 13
#|crlf_plain: ok 13
#|utf8_typed: ok 13
#|utf8_bare: ok 13
#|long_records: ok 13
#|huge_record: ok 13
#|blanks_w2: ok 13
#|blanks_w1: ok 13
#|blanks_w1_str: ok 13
#|blanks_only: ok 13
#|lead_blank: ok 13
#|lead_blank_nohdr: ok 13
#|empty: ok 13
#|header_only: ok 13
#|header_only_nonl: ok 13
#|no_final_nl: ok 13
#|final_sep: ok 13
#|headerless: ok 13
#|bad_utf8: ok 13
#|mal_bare_quote_late: ok 13
#|mal_after_close: ok 13
#|mal_unclosed: ok 13
#|mal_unclosed_eof_q: ok 13
#|mal_cr_quote: ok 13
#|mal_closing_cr_text: ok 13
#|mal_and_ragged: ok 13
#|mal_in_second_half: ok 13
#|ragged_short: ok 13
#|ragged_long_first: ok 13
#|ragged_after_bad: ok 13
#|ragged_w1: ok 13
#|ragged_blank_ok: ok 13
#|bad_cols: ok 13
#|bad_cols_later_row: ok 13
#|bad_cols_earlier_other: ok 13
#|bad_quoted_text: ok 13
#|bad_i32_text: ok 13
#|f32_edges: ok 13
#|f32_one0: ok 13
#|f32_one1: ok 13
#|f32_one2: ok 13
#|f32_one3: ok 13
#|f32_one4: ok 13
#|f32_one5: ok 13
#|f32_one6: ok 13
#|f32_one7: ok 13
#|f32_one8: ok 13
#|f32_one9: ok 13
#|f32_one10: ok 13
#|f32_one11: ok 13
#|f32_one12: ok 13
#|f32_one13: ok 13
#|f32_one14: ok 13
#|f32_one15: ok 13
#|f32_one16: ok 13
#|f32_one17: ok 13
#|f32_random_fast: ok 13
#|u32_ok: ok 13
#|u32_bad0: ok 13
#|u32_bad1: ok 13
#|u32_bad2: ok 13
#|u32_bad3: ok 13
#|u32_bad4: ok 13
#|u32_bad5: ok 13
#|u32_bad6: ok 13
#|u32_bad7: ok 13
#|i32_ok: ok 13
#|u32_overflow: ok 13
#|u32_plus: ok 13
#|u32_sign: ok 13
#|u32_unicode_digit: ok 13
#|i32_edges: ok 13
#|i32_bad0: ok 13
#|i32_bad1: ok 13
#|i32_bad2: ok 13
#|i32_bad3: ok 13
#|i32_bad4: ok 13
#|i32_bad5: ok 13
#|i32_bad6: ok 13
#|i32_bad7: ok 13
#|i32_bad8: ok 13
#|i32_bad9: ok 13
#|bool_edges: ok 13
#|bool_bad: ok 13
#|bool_bad2: ok 13
#|bool_bad3: ok 13
#|escaped_numeric: ok 13
#|escaped_f32_bad: ok 13
#|nulls_all_types: ok 13
#|quote_edges: ok 13
#|fnv_collide: ok 13
#|fnv_collide_q: ok 13
#|wide: ok 13
#|tab_sep: ok 13
#|semicolon: ok 13
#|sep_dot: ok 13
#|sep_minus: ok 13
#|sep_pipe: ok 13
#|v03_late_null: ok 13
#|v03_valid_masked_valid: ok 13
#|v03_quoted_empty_late: ok 13
#|v03_all_null_col: ok 13
#|chunk frames: 273
