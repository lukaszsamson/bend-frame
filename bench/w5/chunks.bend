# T5.1 probe (provisional numbers; plans/M_02.txt W5, DESIGN.md 16.1): the cost of the chunk boundary of
# src/chunks.bend at 2^20 rows, grain 2^14 (64 leaves), on the real modules.
#
#   clone      Array.clone of one 1M-row U32 column (the baseline the build cells subtract)
#   build      clone, then CW.of (the binary-counter build: one Ch.rng range copy per leaf)
#   rt         CW.of then CW.flatten back (one Kernel.copy_into per leaf), no clone: build + flatten
#   build10    clone, then CW.of at grain 2^10 (1024 leaves of 1024 rows)
#   rechunk    build10, then CW.rechunk(14): 1024 -> 64 leaves (every row copied once, in Kernel.append,
#              forked over the tree)
#   fclone     C.Frame.clone of a 7-column frame (5 U32 + 2 F32, 1M rows)
#   fbuild     fclone, then CFrame.of_frame(14): one builder per column, FORKED ACROSS COLUMNS
#   frt        CFrame.of_frame then CFrame.to_frame: build + flatten of 7 columns, forked across columns
#
# The timed window runs `reps` repetitions; the result's row count is the data dependency. One untimed
# check after the clock prints the wrapping sum of the column's words (rt / frt: of the round-tripped
# column, which must equal the source's sum; the other cells: of the source).
#   ~/.bend/bin/bend bench/w5/chunks.bend -o build/w5/chunks && build/w5/chunks --threads 12 frt 10
#   python3 -I bench/w5/run.py build/w5/chunks bench/w5/results/t51.jsonl 5 10
import Base
import ./../../src/err.bend as E
import ./../../src/column.bend as C
import ./../../src/kernels.bend as K
import ./../../src/chunks.bend as CH

def D() -> Nat:
  20n

def N() -> U32:
  1048576

# u[i] = i * 2654435761 + 12345 (wrapping)
def gu.go(f: Nat, +i: U32, +s: U32, out: Array<U32>) -> Array<U32>:
  match f:
    case 0n:
      out
    case 1n+p:
      gu.go(p, U32.inc(i), s, Array.set(U32, out, i, U32.add(U32.mul(i, 2654435761), s)))

def gu(+s: U32) -> Array<U32>:
  gu.go(U32.to_nat(N()), 0, s, Array.new(U32, D(), 0))

def gf.go(f: Nat, +i: U32, out: Array<F32>) -> Array<F32>:
  match f:
    case 0n:
      out
    case 1n+p:
      gf.go(p, U32.inc(i), Array.set(F32, out, i, F32.div(U32.to_f32(i), 7.0)))

def gf() -> Array<F32>:
  gf.go(U32.to_nat(N()), 0, Array.new(F32, D(), 0.0))

def ucol(+s: U32) -> C.Column:
  C.CU32{N(), D(), C.AllValid{}, gu(s)}

def frame7() -> C.Frame:
  C.Frame{N(), [C.Named{"a", ucol(1)}, C.Named{"b", ucol(2)}, C.Named{"c", ucol(3)}, C.Named{"d", ucol(4)}, C.Named{"e", ucol(5)}, C.Named{"f", C.CF32{N(), D(), C.AllValid{}, gf()}}, C.Named{"g", C.CF32{N(), D(), C.AllValid{}, gf()}}]}

# the wrapping sum of the first n words (consumes)
def wsum.go(f: Nat, +i: U32, +acc: U32, r: Array<U32> & U32) -> U32:
  match f:
    case 0n:
      acc
    case 1n+p:
      (a, x) = r
      +j = U32.inc(i)
      wsum.go(p, j, U32.add(acc, x), Array.get(U32, a, j))

def wsum(a: Array<U32>) -> U32:
  wsum.go(U32.to_nat(N()), 0, 0, Array.get(U32, a, 0))

def rows.k(r: CH.CW & U32) -> U32:
  (t, +n) = r
  n

def trows(t: CH.CW) -> U32:
  rows.k(CH.CW.rows(t))

# ---- the per-rep steps (each hands the state back) -----------------------------------------------

type St is Type:
  St{a: Array<U32>, acc: U32}

def st.clone(r: Array<U32> & Array<U32>, +acc: U32) -> St:
  (a, b) = r
  St{a, U32.add(acc, Pair.snd(Array<U32>, U32, Array.get(U32, b, 0)))}

def st.build(+g: Nat, r: Array<U32> & Array<U32>, +acc: U32) -> St:
  (a, b) = r
  St{a, U32.add(acc, trows(CH.CW.of(N(), D(), g, b)))}

def st.rechunk(r: Array<U32> & Array<U32>, +acc: U32) -> St:
  (a, b) = r
  St{a, U32.add(acc, trows(CH.CW.rechunk(14n, CH.CW.of(N(), D(), 10n, b))))}

def rep.clone(f: Nat, st: St) -> St:
  match f st:
    case 0n St{a, acc}:
      St{a, acc}
    case 1n+p St{a, +acc}:
      rep.clone(p, st.clone(Array.clone(U32, a), acc))

def rep.build(f: Nat, +g: Nat, st: St) -> St:
  match f st:
    case 0n St{a, acc}:
      St{a, acc}
    case 1n+p St{a, +acc}:
      rep.build(p, g, st.build(g, Array.clone(U32, a), acc))

def rep.rt(f: Nat, st: St) -> St:
  match f st:
    case 0n St{a, acc}:
      St{a, acc}
    case 1n+p St{a, +acc}:
      rep.rt(p, St{CH.CW.flatten(D(), CH.CW.of(N(), D(), CH.Ch.grain(), a)), U32.inc(acc)})

def rep.rechunk(f: Nat, st: St) -> St:
  match f st:
    case 0n St{a, acc}:
      St{a, acc}
    case 1n+p St{a, +acc}:
      rep.rechunk(p, st.rechunk(Array.clone(U32, a), acc))

type FSt is Type:
  FSt{f: C.Frame, acc: U32}

def fh.k(r: CH.CFrame & U32) -> U32:
  (f, +h) = r
  h

def fhf.k(r: C.Frame & U32) -> U32:
  (f, +h) = r
  h

def fst.clone(r: C.Frame & C.Frame, +acc: U32) -> FSt:
  (a, b) = r
  FSt{a, U32.add(acc, fhf.k(C.Frame.height(b)))}

def fst.build(r: C.Frame & C.Frame, +acc: U32) -> FSt:
  (a, b) = r
  FSt{a, U32.add(acc, fh.k(CH.CFrame.height(CH.CFrame.of_frame(CH.Ch.grain(), b))))}

def rep.fclone(f: Nat, st: FSt) -> FSt:
  match f st:
    case 0n FSt{fr, acc}:
      FSt{fr, acc}
    case 1n+p FSt{fr, +acc}:
      rep.fclone(p, fst.clone(C.Frame.clone(fr), acc))

def rep.fbuild(f: Nat, st: FSt) -> FSt:
  match f st:
    case 0n FSt{fr, acc}:
      FSt{fr, acc}
    case 1n+p FSt{fr, +acc}:
      rep.fbuild(p, fst.build(C.Frame.clone(fr), acc))

def rep.frt(f: Nat, st: FSt) -> FSt:
  match f st:
    case 0n FSt{fr, acc}:
      FSt{fr, acc}
    case 1n+p FSt{fr, +acc}:
      rep.frt(p, FSt{CH.CFrame.to_frame(CH.CFrame.of_frame(CH.Ch.grain(), fr)), U32.inc(acc)})

# ---- checks after the clock ---------------------------------------------------------------------------

def check.u(st: St) -> U32:
  match st:
    case St{a, acc}:
      wsum(a)

def check.col(c: C.Column) -> U32:
  match c:
    case C.CU32{len, depth, valid, data}:
      wsum(data)
    case _:
      0

def check.f(st: FSt) -> U32:
  match st:
    case FSt{fr, acc}:
      match fr:
        case C.Frame{h, cols}:
          match cols:
            case C.Named{n, c} <> rest:
              check.col(c)
            case Nil{}:
              0

def show(+mode: String, +reps: U32, +ms: Nat, +check: U32) -> String:
  "{\"mode\":\"" ++ mode ++ "\",\"rows\":" ++ U32.show(N()) ++ ",\"grain_log2\":14,\"reps\":" ++ U32.show(reps) ++ ",\"ms_total\":" ++ Nat.show(ms) ++ ",\"check\":" ++ U32.show(check) ++ "}"

def ustep(+id: U32, f: Nat, st: St) -> St:
  match id:
    case 0:
      rep.clone(f, st)
    case 1:
      rep.build(f, CH.Ch.grain(), st)
    case 2:
      rep.rt(f, st)
    case 3:
      rep.build(f, 10n, st)
    case _:
      rep.rechunk(f, st)

def fstep(+id: U32, f: Nat, st: FSt) -> FSt:
  match id:
    case 5:
      rep.fclone(f, st)
    case 6:
      rep.fbuild(f, st)
    case _:
      rep.frt(f, st)

def run.u(+mode: String, +id: U32, +reps: U32, a: Array<U32>) -> IO(Unit):
  do IO<Unit>:
    t0 : Nat <- IO.now()
    st : St <- IO.pure(St, ustep(id, U32.to_nat(reps), St{a, 0}))
    t1 : Nat <- IO.now()
    IO.print(show(mode, reps, Nat.sub(t1, t0), check.u(st)))

def run.f(+mode: String, +id: U32, +reps: U32, fr: C.Frame) -> IO(Unit):
  do IO<Unit>:
    t0 : Nat <- IO.now()
    st : FSt <- IO.pure(FSt, fstep(id, U32.to_nat(reps), FSt{fr, 0}))
    t1 : Nat <- IO.now()
    IO.print(show(mode, reps, Nat.sub(t1, t0), check.f(st)))

def dispatch.k(uni: Bool, +mode: String, +id: U32, +reps: U32) -> IO(Unit):
  match uni:
    case True{}:
      run.u(mode, id, reps, gu(1))
    case False{}:
      run.f(mode, id, reps, frame7())

def mid.k(hit: Bool, +id: U32, +rest: U32) -> U32:
  match hit:
    case True{}:
      id
    case False{}:
      rest

def mode_id(+m: String) -> U32:
  mid.k(String.eq(m, "clone"), 0, mid.k(String.eq(m, "build"), 1, mid.k(String.eq(m, "rt"), 2, mid.k(String.eq(m, "build10"), 3, mid.k(String.eq(m, "rechunk"), 4, mid.k(String.eq(m, "fclone"), 5, mid.k(String.eq(m, "fbuild"), 6, 7)))))))

def dispatch(+mode: String, +id: U32, +reps: U32) -> IO(Unit):
  dispatch.k(U32.is_lt(id, 5), mode, id, reps)

def nat_of.k(m: Maybe<&2, Nat>, +d: Nat) -> Nat:
  match m:
    case Some{n}:
      n
    case None{}:
      d

def nat_of(s: String, +d: Nat) -> Nat:
  nat_of.k(Nat.read(s), d)

def go(args: List<String>) -> IO(Unit):
  match args:
    case exe <> +mode <> reps <> Nil{}:
      dispatch(mode, mode_id(mode), U32.from_nat(nat_of(reps, 10n)))
    case _:
      IO.print("usage: chunks <clone|build|rt|build10|rechunk|fclone|fbuild|frt> <reps>")

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<String> <- IO.args()
    go(args)
