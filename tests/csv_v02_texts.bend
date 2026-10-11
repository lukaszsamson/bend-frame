# W6.3: the v0.2 reader against the v0.1 reader on the CSV scenarios of tests/csv_*.bend and the B02
# regressions (written to files under /tmp), plus header-step edges: CR / CR CR / CRLF lines before and
# in the header, a header spanning lines, a long header record and long runs of blank lines (the header
# step reads pieces of min(piece, 64 KiB): with tiny pieces it crosses pieces in every phase), the empty file, blank-only files with and without a header, a non-ASCII
# separator (the v0.1 fall back), a file of several regions. DF.dump and the Str storage are compared
# (tests/lib/v02cmp.bend), per text, configurations x piece sizes:
#   infer_rows 100 (pieces 1, 5, 245760); 0 (2, 4096); 1 (3); 3 (5); explicit schema (1, 7, 245760);
#   explicit, EncRaw (4); header flipped, infer_rows 100 (3); explicit, EncAutoAt{0, 1} (6);
#   infer_rows 100, EncDict (2)
# The line is `<name>: ok <runs> | <the v0.1 outcome of infer_rows 100>`, else the first run that differs.
import Base
import ./../src/strs.bend as ST
import ./../bench/w6/hx.bend as X
import ./lib/v02cmp.bend as T

# a text, its header flag, separator, schema letters
type Tx is Data:
  Tx{name: String, text: String, hdr: Bool, sep: U32, schema: String}

# n copies of the code point c in front of acc (a tail loop)
def Tx.rep(n: Nat, +c: U32, acc: String) -> String:
  match n:
    case 0n:
      acc
    case 1n+p:
      Tx.rep(p, c, SCon{Chr{c}, acc})

# rows i .. n-1 of "<i>,k<i mod 37>,<i mod 3 == 0 ? empty : i / 2>" in front of acc (built backwards)
def Tx.row(+i: U32) -> String:
  U32.show(i) ++ ",k" ++ U32.show(U32.mod(i, 37)) ++ "," ++ Bool.pick(String, U32.is_eq(U32.mod(i, 3), 0), "", U32.show(U32.div(i, 2))) ++ "\n"

def Tx.rows(f: Nat, +i: U32, acc: String) -> String:
  match f:
    case 0n:
      acc
    case 1n+p:
      Tx.rows(p, U32.sub(i, 1), Tx.row(U32.sub(i, 1)) ++ acc)

def Tx.all() -> List<&2, Tx>:
  [Tx{"basic", "id,name,score,flag\n1,ann,1.5,true\n2,\"b,\"\"ob\",,false\r\n3,,7,True\n", True{}, 44, "USFB"},
   Tx{"no_final_nl", "a,b\n1,2\n3,4", True{}, 44, "UU"},
   Tx{"header_only", "a,b\n", True{}, 44, "SS"},
   Tx{"header_only_crlf", "a,b\r\n", True{}, 44, "SS"},
   Tx{"empty", "", True{}, 44, "UU"},
   Tx{"headerless", "1,2\n3,\n", False{}, 44, "UU"},
   Tx{"semicolon", "a;b\n\"x;y\";-5\n;7\n", True{}, 59, "SI"},
   Tx{"wide_ints", "i,j,k\n-1,1e3,5000000000\n2,0.5,7\n", True{}, 44, "IFF"},
   Tx{"multiline_cell", "m\n\"line1\nline2\"\n", True{}, 44, "S"},
   Tx{"ragged", "a,b\n1,2\n3\n", True{}, 44, "UU"},
   Tx{"dup_names", "a,a\n1,2\n", True{}, 44, "UU"},
   Tx{"malformed", "a\n\"bad\"x\n", True{}, 44, "S"},
   Tx{"infer_prefix", "x\n1\n2\nfoo\n", True{}, 44, "U"},
   Tx{"infer_straddle", "x\n1\n2\n3\nfoo\n", True{}, 44, "U"},
   Tx{"trim_blank", "a,b\n 1 , x\n2,y\n\n3,z\n", True{}, 44, "US"},
   Tx{"quoted_empty_null", "a,b\n\"\",x\n,y\n\"\",\n", True{}, 44, "SS"},
   Tx{"cr_header", "\rabc,def\n1,2\n", True{}, 44, "UU"},
   Tx{"cr_cr_header", "\r\r\n1\n", True{}, 44, "S"},
   Tx{"crlf_blank_lead", "\r\nh1,h2\n1,2\n", True{}, 44, "UU"},
   Tx{"lead_blanks_w1", "\n\n\nh\n1\n\n2\n", True{}, 44, "U"},
   Tx{"multiline_header", "\"a\nb\",c\n1,2\n3,4\n", True{}, 44, "UU"},
   Tx{"multiline_header_ragged", "\"a\nb\",c\n1,2\n3\n", True{}, 44, "UU"},
   Tx{"multiline_header_bad", "\"a\r\nb\",c\n1,2\nx,4\n", True{}, 44, "UU"},
   Tx{"quoted_empty_name", "\"\",b\n1,2\n", True{}, 44, "UU"},
   Tx{"only_cr", "\r", True{}, 44, "S"},
   Tx{"blank_lines_only", "\n\n", True{}, 44, "S"},
   Tx{"unicode_names", "日本,é\n1,2\n", True{}, 44, "UU"},
   Tx{"section_sep", "a§b\n1§2\nx§\n", True{}, 167, "SS"},
   Tx{"tab_sep", "a\tb\n1\t2\n", True{}, 9, "UU"},
   Tx{"trailing_sep", "a,b,\n1,2,\n", True{}, 44, "UUS"},
   Tx{"null_column", "a,b\n,1\n,2\n", True{}, 44, "SU"},
   Tx{"bools_w1", "b\ntrue\nFalse\n\n", True{}, 44, "B"},
   Tx{"unclosed_eof", "a,b\n1,\"x", True{}, 44, "SS"},
   Tx{"malformed_header", "a\"b,c\n1,2\n", True{}, 44, "UU"},
   Tx{"unclosed_header", "\"a,b\n1,2\n", True{}, 44, "UU"},
   Tx{"bad_later", "a,b\n1,2\n3,x\n", True{}, 44, "UU"},
   Tx{"crlf_all", "a,b\r\n1,2\r\n3,4\r\n", True{}, 44, "UU"},
   Tx{"quoted_numbers", "a\n\"12\"\n\" 3 \"\n", True{}, 44, "U"},
   Tx{"i32_edges", "a\n-2147483648\n2147483647\n", True{}, 44, "I"},
   Tx{"f32_values", "f\n1.5\n-0\nnan\ninf\n1e-7\n0.1\n", True{}, 44, "F"},
   Tx{"long_header", "\"" ++ Tx.rep(3000n, 120, "\",b\n1,2\n"), True{}, 44, "UU"},
   Tx{"long_lead_blanks", Tx.rep(5000n, 10, "h,i\n1,2\n3\n"), True{}, 44, "UU"},
   Tx{"long_lead_blanks_nohdr", Tx.rep(5000n, 10, "1\n2\n"), False{}, 44, "U"},
   Tx{"regions", "i,k,v\n" ++ Tx.rows(3000n, 3000, ""), True{}, 44, "USU"},
   Tx{"regions_nohdr", Tx.rows(3000n, 3000, ""), False{}, 44, "USU"}]

def Tx.cfgs(+schema: String, +hdr: Bool, +sep: U32) -> List<&2, T.CP>:
  [T.CP{T.Cf{"infer 100", "", hdr, sep, 100, ST.EncAuto{}, 8388608}, [1, 5, 245760]},
   T.CP{T.Cf{"infer all", "", hdr, sep, 0, ST.EncAuto{}, 8388608}, [2, 4096]},
   T.CP{T.Cf{"infer 1", "", hdr, sep, 1, ST.EncAuto{}, 8388608}, [3]},
   T.CP{T.Cf{"infer 3", "", hdr, sep, 3, ST.EncAuto{}, 8388608}, [5]},
   T.CP{T.Cf{"schema", schema, hdr, sep, 100, ST.EncAuto{}, 8388608}, [1, 7, 245760]},
   T.CP{T.Cf{"schema raw", schema, hdr, sep, 100, ST.EncRaw{}, 8388608}, [4]},
   T.CP{T.Cf{"flipped header", "", Bool.not(hdr), sep, 100, ST.EncAuto{}, 8388608}, [3]},
   T.CP{T.Cf{"schema autoat 0 1", schema, hdr, sep, 100, ST.EncAutoAt{0, 1}, 8388608}, [6]},
   T.CP{T.Cf{"infer dict", "", hdr, sep, 100, ST.EncDict{}, 8388608}, [2]}]

def Tx.run(+name: String, text: String, +hdr: Bool, +sep: U32, +schema: String) -> IO(String):
  do IO<String>:
    +path : String = "/tmp/bend_frame_v02_" ++ name ++ ".csv"
    X.Hx.write(path, text)
    T.Run.file(name, path, T.Cf{"infer 100", "", hdr, sep, 100, ST.EncAuto{}, 8388608}, Tx.cfgs(schema, hdr, sep))

def Tx.one(+only: String, t: Tx) -> IO(String):
  match t:
    case Tx{+name, text, +hdr, +sep, +schema}:
      Bool.pick(IO(String), Bool.or(String.is_empty(only), String.eq(only, name)), Tx.run(name, text, hdr, sep, schema), IO.pure(String, ""))

def Tx.loop(+only: String, ts: List<&2, Tx>) -> IO(Unit):
  match ts:
    case Nil{}:
      IO.pure(Unit, Unit{})
    case t <> r:
      do IO<Unit>:
        s : String <- Tx.one(only, t)
        T.Run.print(s)
        Tx.loop(only, r)

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<String> <- IO.args()
    Tx.loop(T.Run.only(args), Tx.all())
#|basic: ok 14 | frame| height 3| width 4
#|no_final_nl: ok 14 | frame| height 2| width 2
#|header_only: ok 14 | frame| height 0| width 2
#|header_only_crlf: ok 14 | frame| height 0| width 2
#|empty: ok 14 | frame| height 0| width 0
#|headerless: ok 14 | frame| height 2| width 2
#|semicolon: ok 14 | frame| height 2| width 2
#|wide_ints: ok 14 | frame| height 2| width 3
#|multiline_cell: ok 14 | frame| height 1| width 1
#|ragged: ok 14 | error ParseError at line 3: expected 2 fields, got 1
#|dup_names: ok 14 | error DuplicateColumn: a
#|malformed: ok 14 | error ParseError at line 0: malformed csv
#|infer_prefix: ok 14 | frame| height 3| width 1
#|infer_straddle: ok 14 | frame| height 4| width 1
#|trim_blank: ok 14 | frame| height 3| width 2
#|quoted_empty_null: ok 14 | frame| height 3| width 2
#|cr_header: ok 14 | frame| height 1| width 2
#|cr_cr_header: ok 14 | frame| height 1| width 1
#|crlf_blank_lead: ok 14 | frame| height 1| width 2
#|lead_blanks_w1: ok 14 | frame| height 3| width 1
#|multiline_header: ok 14 | frame| height 2| width 2
#|multiline_header_ragged: ok 14 | error ParseError at line 4: expected 2 fields, got 1
#|multiline_header_bad: ok 14 | frame| height 2| width 2
#|quoted_empty_name: ok 14 | frame| height 1| width 2
#|only_cr: ok 14 | frame| height 0| width 0
#|blank_lines_only: ok 14 | frame| height 0| width 0
#|unicode_names: ok 14 | frame| height 1| width 2
#|section_sep: ok 14 | frame| height 2| width 2
#|tab_sep: ok 14 | frame| height 1| width 2
#|trailing_sep: ok 14 | frame| height 1| width 3
#|null_column: ok 14 | frame| height 2| width 2
#|bools_w1: ok 14 | frame| height 3| width 1
#|unclosed_eof: ok 14 | error ParseError at line 0: malformed csv
#|malformed_header: ok 14 | error ParseError at line 0: malformed csv
#|unclosed_header: ok 14 | error ParseError at line 0: malformed csv
#|bad_later: ok 14 | frame| height 2| width 2
#|crlf_all: ok 14 | frame| height 2| width 2
#|quoted_numbers: ok 14 | frame| height 2| width 1
#|i32_edges: ok 14 | frame| height 2| width 1
#|f32_values: ok 14 | frame| height 6| width 1
#|long_header: ok 14 | frame| height 1| width 2
#|long_lead_blanks: ok 14 | error ParseError at line 5003: expected 2 fields, got 1
#|long_lead_blanks_nohdr: ok 14 | frame| height 5002| width 1
#|regions: ok 14 | frame| height 3000| width 3
#|regions_nohdr: ok 14 | frame| height 3000| width 3
