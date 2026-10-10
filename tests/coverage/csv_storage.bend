# T6 coverage: the string storages and their introspection: encode_strings (Dictionary <-> Raw) and
# dict_columns (which str columns a frame holds as a Dictionary), over frames read with read_csv_enc
# and str_raw / str_dict / str_auto: a repeated string column, nulls and a quoted empty string, no str
# column, zero rows, a ragged file (the error passes through the reader). The decoded cells of every
# storage are compared in csv_read.bend (decode equivalence against the Polars twin); this file pins
# which columns Auto, Raw and Dictionary hold as a Dictionary and what encode_strings does to that.
# Expectations: DESIGN.md 14 "M4 string experiment" (Auto: a Dictionary while distinct <= max(16384,
# rows / 64)), 15.2.7; reasoned from the contract, no Polars twin (Polars has no such storage).
#@ cover encode_strings,dict_columns success null empty eager
#@ cover str_raw,str_dict,str_auto success null empty invalid eager
#@ na encode_strings,dict_columns invalid -- both take a valid Frame (and a Bool) and cannot fail
#@ na encode_strings,dict_columns lazy -- eager frame functions: the scan / collect path picks its storage itself
#@ na str_raw,str_dict,str_auto lazy -- scan_csv always uses the default (Auto) storage: the readers' choice is eager-only
import Base
import ./../../frame.bend as DF
import ./../../src/err.bend as E
import ./../../src/column.bend as C

def d() -> String:
  "tests/coverage/data/"

# which str columns each storage holds as a Dictionary, and decode / encode round trips
def names(ns: List<&2, String>) -> String:
  match ns:
    case Nil{}:
      "-"
    case n <> Nil{}:
      n
    case n <> t:
      n ++ "," ++ names(t)

def dcols.k(x: C.Frame & List<&2, String>) -> String:
  (f, ns) = x
  names(ns)

def dcols(r: E.ResT(C.Frame)) -> String:
  match r:
    case Fail{e}:
      "error: " ++ DF.err_show(e)
    case Done{f}:
      dcols.k(DF.dict_columns(f))

def enc(r: E.ResT(C.Frame), b: Bool) -> E.ResT(C.Frame):
  match r:
    case Fail{e}:
      Fail{e}
    case Done{f}:
      Done{DF.encode_strings(f, b)}

def storage(+tag: String, +path: String) -> IO(Unit):
  do IO<Unit>:
    ra : E.ResT(C.Frame) <- DF.read_csv_enc(path, DF.csv_opts(',', True{}, 100), [], DF.str_auto())
    rb : E.ResT(C.Frame) <- DF.read_csv_enc(path, DF.csv_opts(',', True{}, 100), [], DF.str_raw())
    rc : E.ResT(C.Frame) <- DF.read_csv_enc(path, DF.csv_opts(',', True{}, 100), [], DF.str_dict())
    re : E.ResT(C.Frame) <- DF.read_csv_enc(path, DF.csv_opts(',', True{}, 100), [], DF.str_dict())
    rd : E.ResT(C.Frame) <- DF.read_csv_enc(path, DF.csv_opts(',', True{}, 100), [], DF.str_raw())
    IO.print("-- " ++ tag ++ "\ndict_columns auto: " ++ dcols(ra) ++ "\ndict_columns raw: " ++ dcols(rb) ++ "\ndict_columns dict: " ++ dcols(rc) ++ "\nencode(raw, True) dict_columns: " ++ dcols(enc(rd, True{})) ++ "\nencode(dict, False) dict_columns: " ++ dcols(enc(re, False{})) ++ "\n\n")

def main() -> IO(Unit):
  do IO<Unit>:
    storage("storage of a repeated string column", d() ++ "repeat.csv")
    storage("storage of nulls and a quoted empty string", d() ++ "basic.csv")
    storage("storage with no str column", d() ++ "floats.csv")
    storage("storage of zero rows", d() ++ "header_only.csv")
    storage("storage of an error", d() ++ "ragged.csv")
#|-- storage of a repeated string column
#|dict_columns auto: name
#|dict_columns raw: -
#|dict_columns dict: name
#|encode(raw, True) dict_columns: name
#|encode(dict, False) dict_columns: -
#|
#|
#|-- storage of nulls and a quoted empty string
#|dict_columns auto: name
#|dict_columns raw: -
#|dict_columns dict: name
#|encode(raw, True) dict_columns: name
#|encode(dict, False) dict_columns: -
#|
#|
#|-- storage with no str column
#|dict_columns auto: -
#|dict_columns raw: -
#|dict_columns dict: -
#|encode(raw, True) dict_columns: -
#|encode(dict, False) dict_columns: -
#|
#|
#|-- storage of zero rows
#|dict_columns auto: id,name,score
#|dict_columns raw: -
#|dict_columns dict: id,name,score
#|encode(raw, True) dict_columns: id,name,score
#|encode(dict, False) dict_columns: -
#|
#|
#|-- storage of an error
#|dict_columns auto: error: ParseError at line 3: expected 3 fields, got 2
#|dict_columns raw: error: ParseError at line 3: expected 3 fields, got 2
#|dict_columns dict: error: ParseError at line 3: expected 3 fields, got 2
#|encode(raw, True) dict_columns: error: ParseError at line 3: expected 3 fields, got 2
#|encode(dict, False) dict_columns: error: ParseError at line 3: expected 3 fields, got 2
#|
#|
