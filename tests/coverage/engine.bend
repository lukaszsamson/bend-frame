# T6 coverage (v0.2 T5.3): the execution engine selector (DESIGN.md 16.5 D7): engine_reference,
# engine_chunked, engine_chunked_at, collect_with, collect_raw_with. Every plan is collected by the
# reference (DF.collect / DF.collect_raw) and by the engine; a line prints the reference's height (or
# error) and "[same]" when the two DF.dump texts are equal (the engine contract: the same frame or the
# same error). Frames: tests/lib/cxgen.bend t(n) (every dtype, nulls in five columns, Raw and Dictionary
# strings); t(0) (zero rows); a frame of no columns (drop of every column). Invalid: a missing column (the
# plan's static error), a missing source (a binding error), a failing strict cast (a data error, row 13).
#@ cover engine_reference,engine_chunked,engine_chunked_at,collect_with,collect_raw_with success null empty invalid lazy
#@ na engine_reference,engine_chunked,engine_chunked_at,collect_with,collect_raw_with eager -- an engine runs a plan: it is the lazy API itself; the eager verbs have no engine
import Base
import ./../../frame.bend as DF
import ./../../src/dtype.bend as D
import ./../../src/err.bend as E
import ./../../src/column.bend as C
import ./../../src/plan.bend as P
import ./../lib/cxgen.bend as T

def same(+tag: String, ra: E.ResT(C.Frame), rb: E.ResT(C.Frame)) -> String:
  T.cmp.c(tag, T.dclone(ra), DF.dump(rb), "")

def chain(+n: U32) -> P.Plan:
  DF.lazy_head(DF.lazy_with_columns(DF.lazy_filter(T.srct(n), DF.gt(DF.col("qty"), DF.lit_u32(20))), [DF.alias(DF.mul(DF.cast_f32(DF.col("qty")), DF.fill_null(DF.col("disc"), DF.col("price"))), "r"), DF.alias(DF.is_null(DF.col("ok")), "okn")]), 9)

def nocols(+n: U32) -> P.Plan:
  DF.lazy_drop(DF.lazy_filter(T.srct(n), DF.gt(DF.col("qty"), DF.lit_u32(20))), ["id", "qty", "price", "ok", "disc", "s", "d", "num", "n"])

def bad_cast() -> P.Plan:
  DF.lazy_with_columns(T.srct(37), [DF.alias(DF.cast(DF.col("num"), D.TU32{}), "a")])

def main() -> IO(Unit):
  do IO<Unit>:
    a1 : E.ResT(C.Frame) <- DF.collect(chain(37), T.envt(37))
    b1 : E.ResT(C.Frame) <- DF.collect_with(DF.engine_chunked_at(2n), chain(37), T.envt(37))
    IO.print(same("chunked 2^2, nulls", a1, b1))
    a2 : E.ResT(C.Frame) <- DF.collect_raw(chain(37), T.envt(37))
    b2 : E.ResT(C.Frame) <- DF.collect_raw_with(DF.engine_chunked(), chain(37), T.envt(37))
    IO.print(same("chunked default grain (one leaf), raw", a2, b2))
    a3 : E.ResT(C.Frame) <- DF.collect(chain(37), T.envt(37))
    b3 : E.ResT(C.Frame) <- DF.collect_with(DF.engine_reference(), chain(37), T.envt(37))
    IO.print(same("reference", a3, b3))
    a4 : E.ResT(C.Frame) <- DF.collect(chain(0), T.envt(0))
    b4 : E.ResT(C.Frame) <- DF.collect_with(DF.engine_chunked_at(1n), chain(0), T.envt(0))
    IO.print(same("empty frame", a4, b4))
    a5 : E.ResT(C.Frame) <- DF.collect_raw(nocols(37), T.envt(37))
    b5 : E.ResT(C.Frame) <- DF.collect_raw_with(DF.engine_chunked_at(2n), nocols(37), T.envt(37))
    IO.print(same("zero columns", a5, b5))
    a6 : E.ResT(C.Frame) <- DF.collect(DF.lazy_filter(T.srct(37), DF.col("nope")), T.envt(37))
    b6 : E.ResT(C.Frame) <- DF.collect_with(DF.engine_chunked_at(2n), DF.lazy_filter(T.srct(37), DF.col("nope")), T.envt(37))
    IO.print(same("invalid: missing column", a6, b6))
    a7 : E.ResT(C.Frame) <- DF.collect_raw(chain(37), DF.empty_env())
    b7 : E.ResT(C.Frame) <- DF.collect_raw_with(DF.engine_chunked_at(2n), chain(37), DF.empty_env())
    IO.print(same("invalid: missing source", a7, b7))
    a8 : E.ResT(C.Frame) <- DF.collect(bad_cast(), T.envt(37))
    b8 : E.ResT(C.Frame) <- DF.collect_with(DF.engine_chunked_at(2n), bad_cast(), T.envt(37))
    IO.print(same("invalid: failing cast", a8, b8))
#|chunked 2^2, nulls: h=9 [same]
#|chunked default grain (one leaf), raw: h=9 [same]
#|reference: h=9 [same]
#|empty frame: h=0 [same]
#|zero columns: h=30 [same]
#|invalid: missing column: error: ColumnNotFound: nope [same]
#|invalid: missing source: error: InvalidOperation: source not in env: t [same]
#|invalid: failing cast: error: InvalidOperation: cast str to u32: row 13 holds "bad" [same]
