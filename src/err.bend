# src/err.bend -- Err, Res, ResT, Err.show. DESIGN.md section 4.2.
import Base

type Err is Data:
  ColumnNotFound{name: String}
  DuplicateColumn{name: String}
  TypeMismatch{op: String, want: String, got: String}
  ShapeMismatch{want: U32, got: U32}
  ParseError{line: U32, text: String}
  InvalidOperation{what: String}
  IoError{code: U32, text: String}

# Data-kinded results (scalars, schemas, plans) and Type-kinded ones (columns, frames)
def Res(-A: Data) -> Data:
  Result<&2, &2, Err, A>

def ResT(-A: Type) -> Type:
  Result<&2, &1, Err, A>

def Err.show(e: Err) -> String:
  match e:
    case ColumnNotFound{name}:
      "ColumnNotFound: " ++ name
    case DuplicateColumn{name}:
      "DuplicateColumn: " ++ name
    case TypeMismatch{op, want, got}:
      "TypeMismatch in " ++ op ++ ": expected " ++ want ++ ", got " ++ got
    case ShapeMismatch{want, got}:
      "ShapeMismatch: expected " ++ U32.show(want) ++ " rows, got " ++ U32.show(got)
    case ParseError{line, text}:
      "ParseError at line " ++ U32.show(line) ++ ": " ++ text
    case InvalidOperation{what}:
      "InvalidOperation: " ++ what
    case IoError{code, text}:
      "IoError " ++ U32.show(code) ++ ": " ++ text
