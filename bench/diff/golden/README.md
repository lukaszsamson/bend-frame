# CSV fuzz goldens

`seed<S>.json` maps each case id of `make csv-fuzz-smoke`'s seed S (1,500 cases) to the hash of its reference
text (`tests/lib/v02cmp.bend` `Sg.hash` of the DF.dump + P0 line + Str storage of the read), as printed by the
runner's `ok <runs> ref <hash>` line. `csvfuzz.py --golden` fails any case whose reference text hashes otherwise.

How they were made (2026-11-01, DESIGN.md 14 "Pre-release"): `csvfuzz.py --write-golden` with a runner built from
the tree before the v0.1 reader's removal, whose reference read was the v0.1 reader (`Csv.read_full` at 1 MiB
chunks); a second run with that runner reproduced every hash. Then two decisions changed answers on purpose, and
only those entries were rewritten with the reader's hash after an independent check:

- a file starting with a UTF-8 byte order mark (D2: the mark is dropped): 6 cases of seed 20261004 and 9 of
  20261005, each checked equal to the v0.1 reader's text for the same file without its first three bytes;
- a separator above U+007F (now `InvalidOperation: csv: separator must be a single-byte (ASCII) character`): 117
  and 102 cases, each checked to answer exactly that error.

Every other entry (1,377 and 1,389) is the v0.1 reader's, and the reader matches it.
