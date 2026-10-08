# src/csvparse.bend -- CSV parser that keeps quotedness and physical line numbers.
# DESIGN.md 15.6.1 / 15.6.2.
#
# Forked from the hub package bend-csv-parser@0.1.0.1 (core.bend, hash
# 0x64aa7934c3659ee6a818595494b38921), MIT licensed:
#
#   SPDX-License-Identifier: MIT
#   Copyright (c) 2026 nohzafk
#
#   Permission is hereby granted, free of charge, to any person obtaining a copy
#   of this software and associated documentation files (the "Software"), to deal
#   in the Software without restriction, including without limitation the rights
#   to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
#   copies of the Software, and to permit persons to whom the Software is
#   furnished to do so, subject to the following conditions:
#
#   The above copyright notice and this permission notice shall be included in all
#   copies or substantial portions of the Software.
#
#   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
#   IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
#   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
#   AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
#   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
#   OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
#   SOFTWARE.
#
# What the fork changes (the walk itself is the hub parser's):
#  - a field is a `CsvCell{text, quoted}`: `quoted` is True when the field was written
#    in quotes (`""` is the valid empty string, an unquoted empty field is null);
#  - a record is a `CsvRec{line, cells}`: `line` is the 1-based PHYSICAL line the record
#    starts on (every LF counts, also inside a quoted field and a blank line);
#  - the original proofs (PROOF.bend of the hub package) do not apply to this file.
#
# Reading rules (the hub's). Every LF (or CRLF) ends a record, so a blank line is a record
# of one empty unquoted field. The end of input ends a record only if one is unfinished,
# so the empty input holds no record and a final terminator adds no extra row. A lone CR
# is content. A quote inside a bare field, or text after a closing quote, rejects the
# whole input.
#
# Shape. One walk over the string builds finished fields and records directly: no token
# list and no state record. Mode, line counters and accumulators are separate arguments of
# `go`; the walk is tail recursive over them, so it can be resumed on the next chunk of a
# file (M4: line-by-line parsing over 1 MB chunks) by threading the same arguments.

import Base

type CsvCell is Data:
  CsvCell{text: String, quoted: Bool}

type CsvRec is Data:
  CsvRec{line: U32, cells: List<&2, CsvCell>}

type Ans is Data:
  Parsed{rows: List<&2, CsvRec>}
  Rejected{}

# character class: all nullary, so a class is a shared constant, never allocated
type CK is Data:
  CLf{}
  CCr{}
  CSep{}
  CQuote{}
  CText{}

# mode: S = at field start, B = in bare field, E = in escaped field,
# Q = just after a quote in an escaped field; SC/BC/QC = the same with one CR
# held back (it is content only if the next char continues the record).
# MBad is never built by this file: the walk rejects a bad pair at once.
type FM is Data:
  MS{}
  MB{}
  ME{}
  MQ{}
  MSC{}
  MBC{}
  MQC{}
  MBad{}

def cls_go(+lf: Bool, +cr: Bool, +sep: Bool, +quote: Bool) -> CK:
  match lf:
    case True{}:
      CLf{}
    case False{}:
      match cr:
        case True{}:
          CCr{}
        case False{}:
          match sep:
            case True{}:
              CSep{}
            case False{}:
              match quote:
                case True{}:
                  CQuote{}
                case False{}:
                  CText{}

def cls_u(+sep: U32, +u: U32) -> CK:
  cls_go(U32.is_eq(u, 10), U32.is_eq(u, 13), U32.is_eq(sep, u), U32.is_eq(u, 34))

def cls(+sep: U32, +c: Char) -> CK:
  cls_u(sep, Char.to_u32(c))

# the record that ends here (rl: its first line); rows are newest first, cells oldest first
def row(+txt: String, +q: Bool, +flds: List<&2, CsvCell>, +rows: List<&2, CsvRec>, +rl: U32) -> List<&2, CsvRec>:
  Con{CsvRec{rl, List.reverse(&2, CsvCell, Con{CsvCell{txt, q}, flds})}, rows}

# the end of input at a field start: an unfinished record ends with one more empty field
def close_empty(+flds: List<&2, CsvCell>, +rows: List<&2, CsvRec>, +rl: U32) -> List<&2, CsvRec>:
  match flds:
    case Nil{}:
      rows
    case Con{_, _}:
      row(SNil{}, False{}, flds, rows, rl)

def one(+c: Char) -> String:
  SCon{c, SNil{}}

def fin(+m: FM, +txt: String, +flds: List<&2, CsvCell>, +rows: List<&2, CsvRec>, +rl: U32) -> Ans:
  match m:
    case MS{}:
      Parsed{List.reverse(&2, CsvRec, close_empty(flds, rows, rl))}
    case MSC{}:
      Parsed{List.reverse(&2, CsvRec, row(SNil{}, False{}, flds, rows, rl))}
    case MB{}:
      Parsed{List.reverse(&2, CsvRec, row(txt, False{}, flds, rows, rl))}
    case MBC{}:
      Parsed{List.reverse(&2, CsvRec, row(txt, False{}, flds, rows, rl))}
    case MQ{}:
      Parsed{List.reverse(&2, CsvRec, row(txt, True{}, flds, rows, rl))}
    case MQC{}:
      Parsed{List.reverse(&2, CsvRec, row(txt, True{}, flds, rows, rl))}
    case ME{}:
      Rejected{}
    case MBad{}:
      Rejected{}

# class of the first character of a string (CText for the empty string: unused)
def cls_of(+sep: U32, +s: String) -> CK:
  match s:
    case SNil{}:
      CText{}
    case SCon{c, _}:
      cls(sep, c)

# the one walk: input first (it shrinks), then mode, then the class of the head
# character (computed once, by the caller), then everything else. ONE match on
# (input, mode, class) per character; a rejecting pair returns at once.
# ln: LFs seen so far (the physical line of the next character is ln + 1... counted from
# `ln0`, the first line, 1); rl: the line the current record started on.
def go(+s: String, +m: FM, +k: CK, +sep: U32, +txt: String, +flds: List<&2, CsvCell>, +rows: List<&2, CsvRec>, +ln: U32, +rl: U32) -> Ans:
  match s m k:
    case SNil{} _ _:
      fin(m, txt, flds, rows, rl)
    case SCon{c, t} MS{} CLf{}:
      go(t, MS{}, cls_of(sep, t), sep, SNil{}, Nil{}, row(SNil{}, False{}, flds, rows, rl), U32.add(ln, 1), U32.add(ln, 1))
    case SCon{c, t} MS{} CCr{}:
      go(t, MSC{}, cls_of(sep, t), sep, SNil{}, flds, rows, ln, rl)
    case SCon{c, t} MS{} CSep{}:
      go(t, MS{}, cls_of(sep, t), sep, SNil{}, Con{CsvCell{SNil{}, False{}}, flds}, rows, ln, rl)
    case SCon{c, t} MS{} CQuote{}:
      go(t, ME{}, cls_of(sep, t), sep, SNil{}, flds, rows, ln, rl)
    case SCon{c, t} MS{} CText{}:
      go(t, MB{}, cls_of(sep, t), sep, one(c), flds, rows, ln, rl)
    case SCon{c, t} MB{} CLf{}:
      go(t, MS{}, cls_of(sep, t), sep, SNil{}, Nil{}, row(txt, False{}, flds, rows, rl), U32.add(ln, 1), U32.add(ln, 1))
    case SCon{c, t} MB{} CCr{}:
      go(t, MBC{}, cls_of(sep, t), sep, txt, flds, rows, ln, rl)
    case SCon{c, t} MB{} CSep{}:
      go(t, MS{}, cls_of(sep, t), sep, SNil{}, Con{CsvCell{txt, False{}}, flds}, rows, ln, rl)
    case SCon{_, _} MB{} CQuote{}:
      Rejected{}
    case SCon{c, t} MB{} CText{}:
      go(t, MB{}, cls_of(sep, t), sep, String.append(txt, one(c)), flds, rows, ln, rl)
    case SCon{c, t} ME{} CQuote{}:
      go(t, MQ{}, cls_of(sep, t), sep, txt, flds, rows, ln, rl)
    case SCon{c, t} ME{} CLf{}:
      go(t, ME{}, cls_of(sep, t), sep, String.append(txt, one(Chr{10})), flds, rows, U32.add(ln, 1), rl)
    case SCon{c, t} ME{} CCr{}:
      go(t, ME{}, cls_of(sep, t), sep, String.append(txt, one(Chr{13})), flds, rows, ln, rl)
    case SCon{c, t} ME{} _:
      go(t, ME{}, cls_of(sep, t), sep, String.append(txt, one(c)), flds, rows, ln, rl)
    case SCon{c, t} MQ{} CLf{}:
      go(t, MS{}, cls_of(sep, t), sep, SNil{}, Nil{}, row(txt, True{}, flds, rows, rl), U32.add(ln, 1), U32.add(ln, 1))
    case SCon{c, t} MQ{} CCr{}:
      go(t, MQC{}, cls_of(sep, t), sep, txt, flds, rows, ln, rl)
    case SCon{c, t} MQ{} CSep{}:
      go(t, MS{}, cls_of(sep, t), sep, SNil{}, Con{CsvCell{txt, True{}}, flds}, rows, ln, rl)
    case SCon{c, t} MQ{} CQuote{}:
      go(t, ME{}, cls_of(sep, t), sep, String.append(txt, one(Chr{34})), flds, rows, ln, rl)
    case SCon{_, _} MQ{} CText{}:
      Rejected{}
    case SCon{c, t} MSC{} CLf{}:
      go(t, MS{}, cls_of(sep, t), sep, SNil{}, Nil{}, row(SNil{}, False{}, flds, rows, rl), U32.add(ln, 1), U32.add(ln, 1))
    case SCon{c, t} MSC{} CCr{}:
      go(t, MBC{}, cls_of(sep, t), sep, one(Chr{13}), flds, rows, ln, rl)
    case SCon{c, t} MSC{} CSep{}:
      go(t, MS{}, cls_of(sep, t), sep, SNil{}, Con{CsvCell{one(Chr{13}), False{}}, flds}, rows, ln, rl)
    case SCon{_, _} MSC{} CQuote{}:
      Rejected{}
    case SCon{c, t} MSC{} CText{}:
      go(t, MB{}, cls_of(sep, t), sep, SCon{Chr{13}, one(c)}, flds, rows, ln, rl)
    case SCon{c, t} MBC{} CLf{}:
      go(t, MS{}, cls_of(sep, t), sep, SNil{}, Nil{}, row(txt, False{}, flds, rows, rl), U32.add(ln, 1), U32.add(ln, 1))
    case SCon{c, t} MBC{} CCr{}:
      go(t, MBC{}, cls_of(sep, t), sep, String.append(txt, one(Chr{13})), flds, rows, ln, rl)
    case SCon{c, t} MBC{} CSep{}:
      go(t, MS{}, cls_of(sep, t), sep, SNil{}, Con{CsvCell{String.append(txt, one(Chr{13})), False{}}, flds}, rows, ln, rl)
    case SCon{_, _} MBC{} CQuote{}:
      Rejected{}
    case SCon{c, t} MBC{} CText{}:
      go(t, MB{}, cls_of(sep, t), sep, String.append(String.append(txt, one(Chr{13})), one(c)), flds, rows, ln, rl)
    case SCon{c, t} MQC{} CLf{}:
      go(t, MS{}, cls_of(sep, t), sep, SNil{}, Nil{}, row(txt, True{}, flds, rows, rl), U32.add(ln, 1), U32.add(ln, 1))
    case SCon{_, _} MQC{} _:
      Rejected{}
    case SCon{_, _} MBad{} _:
      Rejected{}

def parse_sep(+sep: U32, +s: String) -> Ans:
  go(s, MS{}, cls_of(sep, s), sep, SNil{}, Nil{}, Nil{}, 1, 1)

def parse(+s: String) -> Ans:
  parse_sep(44, s)
