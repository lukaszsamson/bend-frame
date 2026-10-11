#!/usr/bin/env python3
"""bench/w5/scale/instrument.py -- a DIAGNOSTIC build of an emitted Bend C file with scheduler counters.

  ~/.bend/bin/bend x.bend -o x.c
  python3 -I bench/w5/scale/instrument.py x.c x_dbg.c && clang -O2 -w -o x_dbg x_dbg.c -lpthread

The patched runtime counts, per process (printed to stderr at exit as one JSON line):
  iters         scheduler iterations (cube_run loop passes: one grow turn + one drain turn each)
  turns         pool turns
  grow_ns / drain_ns   wall time inside the grow / drain turns (the main thread's view)
  wake_ns       time the main thread spent in pool_turn's final wait (the join barrier)
  units[w]      drain units (ring groups) run by thread w (0 = the main thread)
  gunits[w]     grow units (rows grown) by thread w
  frontier[k]   histogram of the frontier size f at each iteration (1, 2, 3-4, 5-8, 9-16, 17-32, 33-64, 65-128, >128)
  nofk_skips    tasks the grow pass refused to run because their def is fork-free (monk_step's skip)
  deferred      forks dealt from inside a drain (task_deal with stride 0 outside the root deal): a fork
                that lands in the NEXT iteration
Nothing else changes: the program's results and its timing structure are those of the normal build (the
counters are relaxed atomics on separate cache lines).
"""
import re
import sys


def patch(src):
    # counters
    decl = r'''
// ---- diagnostic counters (bench/w5/scale/instrument.py) ----
static _Atomic unsigned long long dbg_iters, dbg_turns, dbg_grow_ns, dbg_drain_ns, dbg_wake_ns, dbg_nofk_skips, dbg_deferred;
static _Atomic unsigned long long dbg_units[256] __attribute__((aligned(128)));
static _Atomic unsigned long long dbg_gunits[256] __attribute__((aligned(128)));
static _Atomic unsigned long long dbg_frontier[9];
static _Atomic unsigned long long dbg_unit_ns[256] __attribute__((aligned(128)));
static _Atomic unsigned long long dbg_unit_max[256] __attribute__((aligned(128)));
static _Atomic unsigned long long dbg_steps[256] __attribute__((aligned(128)));
static unsigned long long dbg_now(void) { struct timespec ts; clock_gettime(CLOCK_MONOTONIC, &ts); return (unsigned long long)ts.tv_sec * 1000000000ull + ts.tv_nsec; }
static void dbg_report(void) {
  fprintf(stderr, "{\"iters\": %llu, \"turns\": %llu, \"grow_ms\": %.3f, \"drain_ms\": %.3f, \"wake_ms\": %.3f, \"nofk_skips\": %llu, \"deferred\": %llu, \"frontier\": [",
    (unsigned long long)dbg_iters, (unsigned long long)dbg_turns, dbg_grow_ns / 1e6, dbg_drain_ns / 1e6, dbg_wake_ns / 1e6, (unsigned long long)dbg_nofk_skips, (unsigned long long)dbg_deferred);
  for (int i = 0; i < 9; i++) fprintf(stderr, "%s%llu", i ? ", " : "", (unsigned long long)dbg_frontier[i]);
  fprintf(stderr, "], \"units\": [");
  int last = 0; for (int i = 0; i < 256; i++) if (dbg_units[i] || dbg_gunits[i]) last = i;
  for (int i = 0; i <= last; i++) fprintf(stderr, "%s%llu", i ? ", " : "", (unsigned long long)dbg_units[i]);
  fprintf(stderr, "], \"gunits\": [");
  for (int i = 0; i <= last; i++) fprintf(stderr, "%s%llu", i ? ", " : "", (unsigned long long)dbg_gunits[i]);
  fprintf(stderr, "], \"unit_ms\": [");
  for (int i = 0; i <= last; i++) fprintf(stderr, "%s%.2f", i ? ", " : "", dbg_unit_ns[i] / 1e6);
  fprintf(stderr, "], \"unit_max_ms\": [");
  for (int i = 0; i <= last; i++) fprintf(stderr, "%s%.2f", i ? ", " : "", dbg_unit_max[i] / 1e6);
  fprintf(stderr, "], \"steps\": [");
  for (int i = 0; i <= last; i++) fprintf(stderr, "%s%llu", i ? ", " : "", (unsigned long long)dbg_steps[i]);
  fprintf(stderr, "]}\n");
}
static int dbg_lane(Env e) { return (int)(((u64*)e.alc - &ALC[0][0]) / (3 * NCLS_ALL)); }
'''
    # insert after the pool globals
    anchor = "static pthread_cond_t  pool_join = PTHREAD_COND_INITIALIZER;\n"
    assert anchor in src
    src = src.replace(anchor, anchor + decl, 1)

    # cube_run: count iterations, frontier, time turns
    old = '''      if (f < CUBE) {
        pool_turn(true, rows);
      }
      f = a32_load(a32_at(H, H_CURSOR));
      pool_turn(false, f > rows ? f : rows);'''
    new = '''      { dbg_iters++; u32 ff = f; int b = ff <= 1 ? 0 : ff == 2 ? 1 : ff <= 4 ? 2 : ff <= 8 ? 3 : ff <= 16 ? 4 : ff <= 32 ? 5 : ff <= 64 ? 6 : ff <= 128 ? 7 : 8; dbg_frontier[b]++; }
      if (f < CUBE) {
        unsigned long long t0 = dbg_now();
        pool_turn(true, rows);
        dbg_grow_ns += dbg_now() - t0;
      }
      f = a32_load(a32_at(H, H_CURSOR));
      { unsigned long long t1 = dbg_now();
      pool_turn(false, f > rows ? f : rows);
      dbg_drain_ns += dbg_now() - t1; }'''
    assert old in src
    src = src.replace(old, new, 1)

    # pool_turn: count turns, time the final wait
    old = '''  pool_rows((Env){ CORPUS, ALC[0] }, io_stk);
  POOL_WAIT(a32_load_acq(&pool_done) != 0, pool_join)
}'''
    new = '''  dbg_turns++;
  pool_rows((Env){ CORPUS, ALC[0] }, io_stk);
  { unsigned long long tw = dbg_now();
  POOL_WAIT(a32_load_acq(&pool_done) != 0, pool_join)
  dbg_wake_ns += dbg_now() - tw; }
}'''
    assert old in src
    src = src.replace(old, new, 1)

    # pool_rows: units per thread
    old = '''    a32_acq(&pool_row);
    if (c >> 23 & 1) {
      row_grow(e, stk, r * CUBE_T, 1, CUBE_T);
    } else {'''
    new = '''    a32_acq(&pool_row);
    if (c >> 23 & 1) {
      dbg_gunits[dbg_lane(e)]++;
      row_grow(e, stk, r * CUBE_T, 1, CUBE_T);
    } else {
      dbg_units[dbg_lane(e)]++;
      unsigned long long tu = dbg_now();'''
    assert old in src
    src = src.replace(old, new, 1)
    old = '''        while (*ring_get(e.mem, rg) != put0 && !err_seen(e.mem)) {
          monk_step(e, stk, rg, put0, rg, 0, NULL);
        }
      }
    }
    n += 1;'''
    new = '''        while (*ring_get(e.mem, rg) != put0 && !err_seen(e.mem)) {
          dbg_steps[dbg_lane(e)]++;
          monk_step(e, stk, rg, put0, rg, 0, NULL);
        }
      }
      { unsigned long long du = dbg_now() - tu; int ln = dbg_lane(e); dbg_unit_ns[ln] += du; if (du > dbg_unit_max[ln]) dbg_unit_max[ln] = du; }
    }
    n += 1;'''
    assert old in src
    src = src.replace(old, new, 1)

    # monk_step: nofk skip in grow mode, deferred forks
    old = '''  if ((hi >> 31) != ring_lap(*get) || (!seq && fid_nofk((u32)term_aux(t)))) {
    return 0;
  }'''
    new = '''  if ((hi >> 31) != ring_lap(*get) || (!seq && fid_nofk((u32)term_aux(t)))) {
    if ((hi >> 31) == ring_lap(*get)) dbg_nofk_skips++;
    return 0;
  }'''
    assert old in src
    src = src.replace(old, new, 1)
    old = '''    task_deal(H, r, base, stride, cur);
    return 1;
  }
}'''
    new = '''    if (stride == 0) dbg_deferred++;
    task_deal(H, r, base, stride, cur);
    return 1;
  }
}'''
    assert old in src
    src = src.replace(old, new, 1)

    # report at exit: register in main
    m = re.search(r"\nint main\(int argc, char\*\* argv\) \{\n", src)
    assert m, "main not found"
    src = src[: m.end()] + "  atexit(dbg_report);\n" + src[m.end():]
    return src


def main():
    inp, out = sys.argv[1], sys.argv[2]
    open(out, "w").write(patch(open(inp).read()))


if __name__ == "__main__":
    main()
