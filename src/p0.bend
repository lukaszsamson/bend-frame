# src/p0.bend -- the null-slot invariant checker (post-review B1; DESIGN.md 4.4 invariants, section 14
# "v0.2 post-review: the null-slot invariant").
#
# The P0 invariants of a column (DESIGN.md 4.4, LAWS.bend section 9 WFMaskedW / WFMaskedT): every
# validity word is 0 or 1, every Bool data word is 0 or 1, and the slot of an INVALID row holds the
# dtype default: word 0 (Bool / U32 / I32), +0.0 by its bits (F32: -0.0 is a violation), "" (Raw
# Str) or code 0 (Dictionary Str, the entry ""). A dump never shows a null slot, so a producer that
# breaks P0 is invisible until an operation that relies on it (F4's fill side, the chunked U32 sum)
# reads the slot: v0.2's F32 neg wrote -0.0 under its nulls and fill_null(neg(x), 0.0) answered -0.0.
#
# P0.frame_k walks every column of a frame (rows < height) and answers the frame back with a report:
# "ok", or one clause per offending column. It is a checker, not a kernel: the differential driver
# (tests/diff/lib/dx.bend), the CSV fuzz runner (bench/diff/csvfuzz.bend) and the regressions
# (tests/regress/V02_*) print it after every result, and a report other than "ok" fails the case.
# One flat loop per column (no per-row allocation); the frame is handed back unchanged.
import Base
import ./dtype.bend as D
import ./err.bend as E
import ./column.bend as C
import ./strs.bend as ST
import ./dump.bend as Y

# the counts of one column: null slots not the default (nb; the first such row and its slot word),
# validity words not 0/1 (mb), Bool data words not 0/1 (bb)
type PS is Data:
  PS{nb: U32, first: U32, fw: U32, mb: U32, bb: U32}

def P0.ps0() -> PS:
  PS{0, 0, 0, 0, 0}

# one row: k the validity word, bad whether the slot is not the default, w the slot as a word (the
# report shows it), bw whether the slot is a Bool word other than 0/1
def P0.step(+i: U32, +k: U32, +bad: Bool, +w: U32, +bw: Bool, acc: PS) -> PS:
  match acc:
    case PS{+nb, +first, +fw, +mb, +bb}:
      +bn = Bool.and(U32.is_eq(k, 0), bad)
      +fst = Bool.and(bn, U32.is_zero(nb))
      PS{U32.add(nb, Bool.to_u32(bn)), Bool.pick(U32, fst, i, first), Bool.pick(U32, fst, w, fw), U32.add(mb, Bool.to_u32(U32.is_gt(k, 1))), U32.add(bb, Bool.to_u32(bw))}

# ---- the loops: rows i < n, the data and the validity read in lockstep ----------------------------

type WR is Type:
  WR{x: Array<U32>, m: Array<U32>, s: PS}

type FR is Type:
  FR{x: Array<F32>, m: Array<U32>, s: PS}

type SR is Type:
  SR{x: Array<String>, m: Array<U32>, s: PS}

# word slots (Bool / U32 / I32 data, Dictionary codes); isb: Bool data (its words must be 0/1)
def P0.w.go(n: Nat, +i: U32, +isb: Bool, acc: PS, rx: Array<U32> & U32, rm: Array<U32> & U32) -> WR:
  match n:
    case 0n:
      (x, w) = rx
      (m, k) = rm
      WR{x, m, acc}
    case 1n+p:
      (x, +w) = rx
      (m, +k) = rm
      +j = U32.inc(i)
      P0.w.go(p, j, isb, P0.step(i, k, U32.is_ne(w, 0), w, Bool.and(isb, U32.is_gt(w, 1)), acc), Array.get(U32, x, j), Array.get(U32, m, j))

# f32 slots: the default is +0.0 by its bits (any other bit pattern, -0.0 included, is a violation)
def P0.f.go(n: Nat, +i: U32, acc: PS, rx: Array<F32> & F32, rm: Array<U32> & U32) -> FR:
  match n:
    case 0n:
      (x, y) = rx
      (m, k) = rm
      FR{x, m, acc}
    case 1n+p:
      (x, y) = rx
      (m, +k) = rm
      +j = U32.inc(i)
      +w = F32.bits(y)
      P0.f.go(p, j, P0.step(i, k, U32.is_ne(w, 0), w, False{}, acc), Array.get(F32, x, j), Array.get(U32, m, j))

def P0.nonempty(s: String) -> Bool:
  match s:
    case SNil{}:
      False{}
    case SCon{c, t}:
      True{}

# Raw Str slots: the default is "" (the report shows 1 for a non-empty slot)
def P0.s.go(n: Nat, +i: U32, acc: PS, rx: Array<String> & String, rm: Array<U32> & U32) -> SR:
  match n:
    case 0n:
      (x, y) = rx
      (m, k) = rm
      SR{x, m, acc}
    case 1n+p:
      (x, y) = rx
      (m, +k) = rm
      +j = U32.inc(i)
      +bad = P0.nonempty(y)
      P0.s.go(p, j, P0.step(i, k, bad, Bool.to_u32(bad), False{}, acc), Array.get(String, x, j), Array.get(U32, m, j))

# ---- per column -------------------------------------------------------------------------------------

# the validity as the loops read it: a mask, or the 1-slot ones array of an AllValid column (indices
# wrap, so every row reads 1); `has` says which, to rebuild the column
def P0.vm(v: C.Valid) -> Bool & Array<U32>:
  match v:
    case C.AllValid{}:
      (False{}, Array.new(U32, 0n, 1))
    case C.Mask{m}:
      (True{}, m)

def P0.back(has: Bool, m: Array<U32>) -> C.Valid:
  match has:
    case True{}:
      C.Mask{m}
    case False{}:
      C.AllValid{}

def P0.w.k(t: D.DType, +n: U32, d: Nat, has: Bool, r: WR) -> C.Column & PS:
  match r:
    case WR{x, m, s}:
      (C.Column.mk_w(t, n, d, P0.back(has, m), x), s)

def P0.w(t: D.DType, +isb: Bool, +n: U32, d: Nat, x: Array<U32>, r: Bool & Array<U32>) -> C.Column & PS:
  (+has, m) = r
  P0.w.k(t, n, d, has, P0.w.go(U32.to_nat(n), 0, isb, P0.ps0(), Array.get(U32, x, 0), Array.get(U32, m, 0)))

def P0.f.k(+n: U32, d: Nat, has: Bool, r: FR) -> C.Column & PS:
  match r:
    case FR{x, m, s}:
      (C.CF32{n, d, P0.back(has, m), x}, s)

def P0.f(+n: U32, d: Nat, x: Array<F32>, r: Bool & Array<U32>) -> C.Column & PS:
  (+has, m) = r
  P0.f.k(n, d, has, P0.f.go(U32.to_nat(n), 0, P0.ps0(), Array.get(F32, x, 0), Array.get(U32, m, 0)))

def P0.sr.k(+n: U32, d: Nat, has: Bool, r: SR) -> C.Column & PS:
  match r:
    case SR{x, m, s}:
      (C.CStr{n, d, P0.back(has, m), ST.SRaw{x}}, s)

def P0.sd.k(+n: U32, d: Nat, has: Bool, dict: ST.Dict, r: WR) -> C.Column & PS:
  match r:
    case WR{x, m, s}:
      (C.CStr{n, d, P0.back(has, m), ST.SDict{x, dict}}, s)

def P0.s.k(x: ST.Strs, +n: U32, d: Nat, +has: Bool, m: Array<U32>) -> C.Column & PS:
  match x:
    case ST.SRaw{a}:
      P0.sr.k(n, d, has, P0.s.go(U32.to_nat(n), 0, P0.ps0(), Array.get(String, a, 0), Array.get(U32, m, 0)))
    case ST.SDict{c, dict}:
      P0.sd.k(n, d, has, dict, P0.w.go(U32.to_nat(n), 0, False{}, P0.ps0(), Array.get(U32, c, 0), Array.get(U32, m, 0)))

def P0.s(+n: U32, d: Nat, x: ST.Strs, r: Bool & Array<U32>) -> C.Column & PS:
  (+has, m) = r
  P0.s.k(x, n, d, has, m)

# the counts of one column; the column comes back
def P0.col(c: C.Column) -> C.Column & PS:
  match c:
    case C.CBool{+n, d, v, x}:
      P0.w(D.TBool{}, True{}, n, d, x, P0.vm(v))
    case C.CU32{+n, d, v, x}:
      P0.w(D.TU32{}, False{}, n, d, x, P0.vm(v))
    case C.CI32{+n, d, v, x}:
      P0.w(D.TI32{}, False{}, n, d, x, P0.vm(v))
    case C.CF32{+n, d, v, x}:
      P0.f(n, d, x, P0.vm(v))
    case C.CStr{+n, d, v, x}:
      P0.s(n, d, x, P0.vm(v))

# ---- the report -------------------------------------------------------------------------------------

def P0.clause.k(clean: Bool, +name: String, s: PS) -> String:
  match clean:
    case True{}:
      ""
    case False{}:
      match s:
        case PS{nb, first, fw, mb, bb}:
          " [col " ++ Y.Dump.quote(name) ++ ": " ++ U32.show(nb) ++ " null slot(s) not the default, first row " ++ U32.show(first) ++ " holds 0x" ++ Y.Dump.hex(8n, fw) ++ "; " ++ U32.show(mb) ++ " validity word(s) not 0/1; " ++ U32.show(bb) ++ " bool word(s) not 0/1]"

def P0.clause(+name: String, s: PS) -> String:
  match s:
    case PS{+nb, first, fw, +mb, +bb}:
      P0.clause.k(U32.is_zero(U32.add(nb, U32.add(mb, bb))), name, PS{nb, first, fw, mb, bb})

def P0.cols.k(+name: String, r: C.Column & PS, rest: List<&1, C.Named> & String) -> List<&1, C.Named> & String:
  (c, s) = r
  (cols, txt) = rest
  (C.Named{name, c} <> cols, P0.clause(name, s) ++ txt)

def P0.cols(cols: List<&1, C.Named>) -> List<&1, C.Named> & String:
  match cols:
    case Nil{}:
      (Nil{}, "")
    case C.Named{+name, c} <> rest:
      P0.cols.k(name, P0.col(c), P0.cols(rest))

def P0.fin(+h: U32, r: List<&1, C.Named> & String) -> C.Frame & String:
  (cols, +txt) = r
  (C.Frame{h, cols}, Bool.pick(String, String.eq(txt, ""), "ok", "BAD" ++ txt))

# "ok" when every column of the frame keeps the P0 invariants at its rows below the height, else
# "BAD" and one clause per offending column; the frame comes back
def P0.frame_k(f: C.Frame) -> C.Frame & String:
  match f:
    case C.Frame{+h, cols}:
      P0.fin(h, P0.cols(cols))

def P0.frame.s(r: C.Frame & String) -> String:
  (f, s) = r
  s

# the report of a frame (consumed)
def P0.frame(f: C.Frame) -> String:
  P0.frame.s(P0.frame_k(f))

# the report of a result: an error has no columns ("ok")
def P0.result(r: E.ResT(C.Frame)) -> String:
  match r:
    case Fail{e}:
      "ok"
    case Done{f}:
      P0.frame(f)

# the dump text of a result (DF.dump's) followed by the line "p0 <report>"; the differential driver's
# printing step
def P0.dump.k(r: C.Frame & String) -> String:
  (f, rep) = r
  Y.Dump.frame(f) ++ "p0 " ++ rep ++ "\n"

def P0.dump(r: E.ResT(C.Frame)) -> String:
  match r:
    case Fail{e}:
      Y.Dump.result(Fail{e}) ++ "p0 ok\n"
    case Done{f}:
      P0.dump.k(P0.frame_k(f))
