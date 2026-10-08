#!/usr/bin/env bash
# Baseline of the native Bend engine: q1..q6 at 1k, 100k and 1M rows, plus the 1M CSV parse.
#   scripts/baseline.sh            rebuild build/bench from the working tree, measure, write bench/results/baseline.json
#   BUILD=0 scripts/baseline.sh    reuse the existing build/bench
#   THREADS=12 PROCS=5             the defaults: 12 threads only, 5 processes per cell
# Each cell is PROCS separate processes, one measurement each. A process reports the mean of `batch`
# collects, with the same batch rule as scripts/bench.sh (IO.now has 1 ms resolution). A cell's seconds
# is the median over its processes. Peak RSS comes from /usr/bin/time (macOS -l: "maximum resident set
# size"; GNU -v elsewhere). Commit, dirty paths, machine, toolchain, input hashes and load averages go
# into the JSON. Takes about 5-10 minutes; the load of other programs on the machine is recorded per process.
set -euo pipefail
cd "$(dirname "$0")/.."
ROOT=$PWD

BEND=${BEND:-$HOME/.bend/bin/bend}
THREADS=${THREADS:-12}
PROCS=${PROCS:-5}
BUILD=${BUILD:-1}
SIZES=${SIZES:-"1000 100000 1000000"}
QUERIES=${QUERIES:-"q1 q2 q3 q4 q5 q6"}
RAW=build/baseline.jsonl
OUT=bench/results/baseline.json

if [ "$(uname -s)" = Darwin ]; then TIME_FLAG=-l; else TIME_FLAG=-v; fi

# the same batch rule as scripts/bench.sh
batch_for() { # n query
  case "$1" in
    1000) if [ "$2" = q1 ] || [ "$2" = q2 ]; then echo 500; else echo 40; fi;;
    100000) if [ "$2" = q2 ]; then echo 8; else echo 1; fi;;
    *) if [ "$2" = q2 ]; then echo 3; else echo 1; fi;;
  esac
}

mkdir -p build bench/results
if ! ls bench/data/sales_*.csv >/dev/null 2>&1; then
  uv run --project bench python bench/gen.py
fi
if [ "$BUILD" = 1 ]; then
  "$BEND" bench/main.bend -o build/bench
fi
test -x build/bench || { echo "no build/bench: run with BUILD=1" >&2; exit 1; }

# measure CSV QUERY BATCH N PROC: one process; appends its JSON record (bench's line plus metadata) to $RAW
measure() {
  local csv=$1 q=$2 batch=$3 n=$4 proc=$5 line rss load
  if [ -r /proc/loadavg ]; then load=$(cut -d' ' -f1 /proc/loadavg)
  else load=$(sysctl -n vm.loadavg | awk '{print $2}'); fi
  line=$(/usr/bin/time "$TIME_FLAG" ./build/bench --threads "$THREADS" "$csv" "$q" 1 "$batch" "$THREADS" 2>build/time.err | tail -1)
  case "$line" in
    '{'*'}') ;;
    *) echo "unexpected output from build/bench ($q n=$n): $line" >&2; exit 1 ;;
  esac
  if [ "$TIME_FLAG" = -l ]; then
    rss=$(awk '/maximum resident set size/ {print $1}' build/time.err)
  else
    rss=$(awk -F': ' '/Maximum resident set size/ {print $2 * 1024}' build/time.err)
  fi
  case "$rss" in ''|*[!0-9]*) echo "no peak RSS in build/time.err ($q n=$n)" >&2; exit 1 ;; esac
  printf '%s,"size":%s,"proc":%s,"batch":%s,"peak_rss_bytes":%s,"load1":%s}\n' "${line%\}}" "$n" "$proc" "$batch" "$rss" "$load" >> "$RAW"
}

: > "$RAW"
for n in $SIZES; do
  for q in $QUERIES; do
    b=$(batch_for "$n" "$q")
    echo "== $q n=$n: $PROCS processes, batch $b, $THREADS threads" >&2
    for p in $(seq "$PROCS"); do
      measure "bench/data/sales_$n.csv" "$q" "$b" "$n" "$p"
    done
  done
done
echo "== CSV parse n=1000000: $PROCS processes" >&2
for p in $(seq "$PROCS"); do
  measure "bench/data/sales_1000000.csv" parse 1 1000000 "$p"
done

# aggregate: medians per cell, metadata, and the table on stdout
uv run --project bench python - "$RAW" "$OUT" "$BEND" "$THREADS" "$PROCS" "$ROOT" <<'PY'
import datetime, glob, hashlib, json, os, statistics, subprocess, sys

raw, out, bend, threads, procs, root = sys.argv[1:7]
threads, procs = int(threads), int(procs)
os.chdir(root)

def sh(*cmd):
    try:
        return subprocess.run(cmd, capture_output=True, text=True, check=True).stdout.strip()
    except (OSError, subprocess.CalledProcessError):
        return None

def sha256(path):
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for chunk in iter(lambda: f.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()

recs = [json.loads(line) for line in open(raw) if line.strip()]
cells = {}
for r in recs:
    cells.setdefault((r["query"], r["size"]), []).append(r)

order = {f"q{i}": i for i in range(1, 7)}
results, parse = [], None
for (q, n), rs in sorted(cells.items(), key=lambda kv: (kv[0][1], order.get(kv[0][0], 99), kv[0][0])):
    rss = [r["peak_rss_bytes"] for r in rs]
    loads = [r["load1"] for r in rs]
    if q == "parse":
        read = [r["read_ms"] for r in rs]
        walk = [r["first_walk_ms"] for r in rs]
        parse = {
            "query": "parse", "n": n, "processes": len(rs),
            "read_ms_median": statistics.median(read), "read_ms_all": read,
            "first_walk_ms_median": statistics.median(walk), "first_walk_ms_all": walk,
            "peak_rss_mb_median": statistics.median(rss) / 2**20, "peak_rss_bytes_all": rss,
            "load1_before_all": loads,
        }
        continue
    secs = [r["seconds"] for r in rs]
    results.append({
        "query": q, "n": n, "batch": rs[0]["batch"], "processes": len(rs),
        "seconds_median": statistics.median(secs), "seconds_min": min(secs), "seconds_max": max(secs),
        "seconds_all": secs,
        "peak_rss_mb_median": statistics.median(rss) / 2**20, "peak_rss_bytes_all": rss,
        "load1_before_all": loads,
    })

def machine():
    if sh("uname", "-s") == "Darwin":
        return {
            "os": f"macOS {sh('sw_vers', '-productVersion')} ({sh('sw_vers', '-buildVersion')})",
            "cpu": sh("sysctl", "-n", "machdep.cpu.brand_string"),
            "logical_cpus": int(sh("sysctl", "-n", "hw.ncpu")),
            "performance_cores": int(sh("sysctl", "-n", "hw.perflevel0.physicalcpu")),
            "efficiency_cores": int(sh("sysctl", "-n", "hw.perflevel1.physicalcpu")),
            "memory_bytes": int(sh("sysctl", "-n", "hw.memsize")),
            "arch": sh("uname", "-m"),
        }
    return {"os": sh("uname", "-sr"), "arch": sh("uname", "-m"), "logical_cpus": os.cpu_count()}

status = sh("git", "status", "--porcelain") or ""
doc = {
    "measured_at": datetime.datetime.now().astimezone().isoformat(timespec="seconds"),
    "script": "scripts/baseline.sh",
    "commit": sh("git", "rev-parse", "HEAD"),
    "working_tree": {"clean": status == "", "changed_paths": status.splitlines()},
    "machine": machine(),
    "toolchain": {
        "bend": (sh(bend, "version") or "").replace("bend ", ""),
        "bend_binary": "build/bench",
        "bend_bench_sha256": sha256("build/bench"),
        "lean": (sh("lean", "--version") or "").split(",")[0].replace("Lean (version ", ""),
        "uv": (sh("uv", "--version") or "").split()[1],
        "python": sys.version.split()[0],
        "polars": __import__("polars").__version__,
        "numpy": __import__("numpy").__version__,
    },
    "inputs": {
        os.path.basename(p): {"bytes": os.path.getsize(p), "sha256": sha256(p)}
        for p in sorted(glob.glob("bench/data/*.csv"))
    },
    "method": {
        "threads": threads, "processes_per_cell": procs,
        "statistic": "median over processes of the per-collect seconds (each process: mean of `batch` collects)",
        "peak_rss": "/usr/bin/time -l, maximum resident set size, median over processes",
        "load1_before_all": "1-minute load average read just before each process starts",
    },
    "results": results,
    "parse_1m": parse,
}
with open(out, "w") as f:
    json.dump(doc, f, indent=2)
    f.write("\n")

print(f"{'query':<6}{'n':>10}{'batch':>7}{'median s':>12}{'min s':>11}{'max s':>11}{'RSS MB':>10}")
for r in results:
    print(f"{r['query']:<6}{r['n']:>10,}{r['batch']:>7}{r['seconds_median']:>12.6f}{r['seconds_min']:>11.6f}"
          f"{r['seconds_max']:>11.6f}{r['peak_rss_mb_median']:>10.1f}")
if parse:
    print(f"parse  {parse['n']:>10,}  read {parse['read_ms_median']:.0f} ms (median), "
          f"first walk {parse['first_walk_ms_median']:.0f} ms, RSS {parse['peak_rss_mb_median']:.0f} MB")
print(f"wrote {out}")
PY
