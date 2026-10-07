# p04: the library's error type and Result plumbing: a Data error enum, a
# Result alias as a type-level def, a do-block over Result, and an IO main
# that reports a Fail as text.
#   ~/.bend/bin/bend probes/p04_result_err.bend
import Base

type Err is Data:
  ColumnNotFound{name: String}
  TypeMismatch{op: String, want: String, got: String}
  ShapeMismatch{want: U32, got: U32}
  ParseError{line: U32, text: String}

def Err.show(e: Err) -> String:
  match e:
    case ColumnNotFound{name}:
      "ColumnNotFound: " ++ name
    case TypeMismatch{op, want, got}:
      "TypeMismatch in " ++ op ++ ": expected " ++ want ++ ", got " ++ got
    case ShapeMismatch{want, got}:
      "ShapeMismatch: expected " ++ U32.show(want) ++ " rows, got " ++ U32.show(got)
    case ParseError{line, text}:
      "ParseError at line " ++ U32.show(line) ++ ": " ++ text

# Res(A): a Data-kinded result (A must be Data for the &2 instance)
def Res(-A: Data) -> Data:
  Result<&2, &2, Err, A>

# a Type-kinded result for payloads that hold Arrays
def ResT(-A: Type) -> Type:
  Result<&2, &1, Err, A>

def parse_two(+a: String, +b: String) -> Res(U32):
  do Result<&2, &2, Err, U32>:
    x : U32 <- Maybe.default(&2, Res(U32), Maybe.map(&2, U32, Res(U32), v => Done{v}, U32.read(a)), Fail{ParseError{1, a}})
    y : U32 <- Maybe.default(&2, Res(U32), Maybe.map(&2, U32, Res(U32), v => Done{v}, U32.read(b)), Fail{ParseError{2, b}})
    return (x + y : U32)

def report(r: Res(U32)) -> String:
  match r:
    case Fail{e}:
      "error: " ++ Err.show(e)
    case Done{v}:
      "ok: " ++ U32.show(v)

# a match on a computed value needs its own def: pass the Bool in
def arr_ok.if(z: Bool) -> ResT(Array<F32>):
  match z:
    case True{}:
      Fail{ShapeMismatch{1, 0}}
    case False{}:
      Done{[1.5 : F32*2n]}

def arr_ok(n: U32) -> ResT(Array<F32>):
  arr_ok.if(U32.is_zero(n))

def arr_report(r: ResT(Array<F32>)) -> String:
  match r:
    case Fail{e}:
      Err.show(e)
    case Done{a}:
      List.show(~&1, ~F32, ~(x => F32.show(x)), Array.to_list(~F32, a))

def main() -> IO(Unit):
  do IO<Unit>:
    IO.print(report(parse_two("40", "2")))
    IO.print(report(parse_two("40", "x")))
    IO.print(arr_report(arr_ok(0)))
    IO.print(arr_report(arr_ok(3)))

#|ok: 42
#|error: ParseError at line 2: x
#|ShapeMismatch: expected 1 rows, got 0
#|[1.5, 1.5]
