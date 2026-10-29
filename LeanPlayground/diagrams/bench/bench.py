#!/usr/bin/env python3
"""Benchmark the diagrams framework's decision procedures and chase search.

Each workload is a statement about a grid with k squares on a side, defined in
grid.lean and proved by `decide`. For each workload the script tries growing
sizes, runs each case several times under Lean's profiler, and records the
median time spent in tactics (the elaborator's evaluation) and in type checking
(the kernel). A workload stops growing at its first timeout.

Usage, from the repository root:

    python3 LeanPlayground/diagrams/bench/bench.py --label baseline
    python3 LeanPlayground/diagrams/bench/bench.py --label after --compare \
        LeanPlayground/diagrams/bench/results/baseline.json

Results are written to LeanPlayground/diagrams/bench/results/<label>.json.
"""

import argparse
import datetime
import json
import os
import re
import resource
import signal
import statistics
import subprocess
import sys
import tempfile
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
RESULTS = Path(__file__).resolve().parent / "results"
MODULE = "LeanPlayground.diagrams.bench.grid"
IMPORTS = [MODULE, "LeanPlayground.diagrams.tactics"]

# Workload name -> Lean statement for size k. The tactic is appended.
WORKLOADS = {
    "reach": "example : reachBench {k} := by",
    "acyclic": "example : acyclicBench {k} := by",
    "minObligation": "example : minObligationBench {k} := by",
    "chain": "example : chainBench {k} := by",
    "search": "example : searchBench {k} = true := by",
    "unreach": "example : unreachBench {k} := by",
}

# Workloads proved by a certificate-finding tactic instead of the `--tactic`.
CERT_WORKLOADS = {
    "acyclic.cert": "example : acyclicBench {k} := by diagram_acyclic",
    "unreach.cert": "example : unreachBench {k} := by diagram_unreachable",
    "search.cert": ("example : Nonempty (Chase square (walkPath (origin {k}) (topDirs {k})).2 "
                    "(walkPath (origin {k}) (leftDirs {k})).2) := by "
                    "find_chase (cells ({k} + 1) ({k} + 1)) 10000000"),
}

DEFAULT_SIZES = [1, 2, 3, 4, 5, 6, 8, 10, 12, 16, 20, 24, 32]

PROFILE_LINE = re.compile(r"^\t(tactic execution|type checking) ([0-9.]+)(ms|s|us|μs)$")
UNIT = {"s": 1000.0, "ms": 1.0, "us": 0.001, "μs": 0.001}


def statement(workload: str, k: int, tactic: str) -> str:
    if workload in CERT_WORKLOADS:
        return CERT_WORKLOADS[workload].format(k=k, fuel=k * k + 1)
    return f"{WORKLOADS[workload].format(k=k)} {tactic}"


def lean_source(workload: str, k: int, tactic: str) -> str:
    return "\n".join([
        *[f"import {m}" for m in IMPORTS],
        "open Diagrams Diagrams.Bench",
        "set_option profiler true",
        "set_option maxRecDepth 100000",
        "set_option maxHeartbeats 0",
        statement(workload, k, tactic),
        "",
    ])


def lean_env() -> tuple[str, dict]:
    """The `lean` binary and environment that `lake env` would use."""
    def query(var: str) -> str:
        return subprocess.run(["lake", "env", "printenv", var], cwd=ROOT,
                              capture_output=True, text=True, check=True).stdout.strip()
    env = dict(os.environ, LEAN_PATH=query("LEAN_PATH"))
    lean = str(Path(query("LEAN_SYSROOT")) / "bin" / "lean")
    return lean, env


def cpu_limit(cpu_s: float):
    """A CPU-time limit for a child, as a backstop to the wall-clock timeout."""
    def apply():
        cpu = int(cpu_s) + 1
        resource.setrlimit(resource.RLIMIT_CPU, (cpu, cpu + 5))
    return apply


def rss_mb(pid: int) -> float:
    """Resident memory of a process, in MB. Lean memory-maps its imports, so the
    address space is large even for small runs; resident memory is what matters."""
    try:
        for line in Path(f"/proc/{pid}/status").read_text().splitlines():
            if line.startswith("VmRSS:"):
                return int(line.split()[1]) / 1024
    except OSError:
        pass
    return 0.0


def run_once(source: str, lean: str, env: dict, timeout: float, mem_mb: int) -> dict:
    with tempfile.TemporaryDirectory() as tmp:
        path = Path(tmp) / "Bench.lean"
        path.write_text(source)
        start = time.monotonic()
        log = Path(tmp) / "out.txt"
        with log.open("w") as sink:
            proc = subprocess.Popen(
                [lean, str(path)], cwd=ROOT, env=env, stdout=sink, stderr=subprocess.STDOUT,
                start_new_session=True, preexec_fn=cpu_limit(timeout),
            )
            peak, verdict = 0.0, None
            while proc.poll() is None:
                elapsed = time.monotonic() - start
                peak = max(peak, rss_mb(proc.pid))
                if elapsed > timeout:
                    verdict = {"status": "timeout"}
                elif peak > mem_mb:
                    verdict = {"status": "memory", "message": f"over {mem_mb} MB resident"}
                if verdict:
                    os.killpg(proc.pid, signal.SIGKILL)
                    proc.wait()
                    return {**verdict, "peak_mb": round(peak)}
                time.sleep(0.05)
        wall = time.monotonic() - start
        out = log.read_text()
    if proc.returncode < 0:
        sig = signal.Signals(-proc.returncode).name
        return {"status": "killed", "message": f"{sig}", "peak_mb": round(peak)}
    if proc.returncode != 0 or "error" in out:
        lines = out.splitlines()
        i = next((i for i, line in enumerate(lines) if "error" in line), max(len(lines) - 3, 0))
        return {"status": "error", "message": " ".join(lines[i:i + 3]).strip()[:300]}
    times = {"tactic execution": 0.0, "type checking": 0.0}
    for line in out.splitlines():
        m = PROFILE_LINE.match(line)
        if m:
            times[m.group(1)] = float(m.group(2)) * UNIT[m.group(3)]
    return {
        "status": "ok",
        "elab_ms": times["tactic execution"],
        "kernel_ms": times["type checking"],
        "wall_s": wall,
        "peak_mb": peak,
    }


def run_case(workload: str, k: int, tactic: str, repeats: int, timeout: float,
             lean: str, env: dict, mem_mb: int) -> dict:
    runs = []
    for _ in range(repeats):
        r = run_once(lean_source(workload, k, tactic), lean, env, timeout, mem_mb)
        if r["status"] != "ok":
            return {"workload": workload, "k": k, **r}
        runs.append(r)
    med = lambda key: statistics.median(r[key] for r in runs)
    elab, kernel = med("elab_ms"), med("kernel_ms")
    return {
        "workload": workload, "k": k, "status": "ok",
        "elab_ms": round(elab, 1), "kernel_ms": round(kernel, 1),
        "total_ms": round(elab + kernel, 1), "wall_s": round(med("wall_s"), 2),
        "peak_mb": round(max(r["peak_mb"] for r in runs)),
    }


def git_rev() -> str:
    try:
        return subprocess.run(["git", "rev-parse", "--short", "HEAD"], cwd=ROOT,
                              capture_output=True, text=True).stdout.strip()
    except OSError:
        return "unknown"


def load_baseline(path: str | None) -> dict:
    if not path:
        return {}
    data = json.loads(Path(path).read_text())
    return {(r["workload"], r["k"]): r for r in data["results"] if r["status"] == "ok"}


def fmt_row(r: dict, base: dict) -> str:
    if r["status"] != "ok":
        return f"| {r['workload']} | {r['k']} | {r['status']} | | | {r.get('peak_mb', '')} | |"
    ratio = ""
    b = base.get((r["workload"], r["k"]))
    if b and r["total_ms"] > 0:
        ratio = f"{b['total_ms'] / r['total_ms']:.1f}×"
    return (f"| {r['workload']} | {r['k']} | {r['elab_ms']:.0f} | {r['kernel_ms']:.0f} | "
            f"{r['total_ms']:.0f} | {r['peak_mb']} | {ratio} |")


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawTextHelpFormatter)
    ap.add_argument("--label", required=True, help="name for the results file")
    ap.add_argument("--only", nargs="*", choices=sorted({**WORKLOADS, **CERT_WORKLOADS}),
                    help="workloads to run")
    ap.add_argument("--sizes", nargs="*", type=int, default=DEFAULT_SIZES)
    ap.add_argument("--tactic", default="decide", help="tactic that proves each statement")
    ap.add_argument("--repeats", type=int, default=3)
    ap.add_argument("--timeout", type=float, default=60.0, help="seconds per run")
    ap.add_argument("--mem", type=int, default=3000, help="resident memory limit per run, in MB")
    ap.add_argument("--compare", help="earlier results file to compare against")
    args = ap.parse_args()

    build = subprocess.run(["lake", "build", *IMPORTS], cwd=ROOT, capture_output=True, text=True)
    if build.returncode != 0:
        print(build.stdout + build.stderr, file=sys.stderr)
        return 1

    lean, env = lean_env()
    base = load_baseline(args.compare)
    results = []
    RESULTS.mkdir(exist_ok=True)
    out = RESULTS / f"{args.label}.json"

    def save():
        out.write_text(json.dumps({
            "label": args.label, "git": git_rev(), "tactic": args.tactic,
            "date": datetime.datetime.now().isoformat(timespec="seconds"),
            "timeout_s": args.timeout, "mem_mb": args.mem, "repeats": args.repeats,
            "results": results,
        }, indent=2) + "\n")

    print("| workload | k | elaborator ms | kernel ms | total ms | peak MB | speedup |")
    print("|---|---|---|---|---|---|---|")
    for workload in args.only or [*WORKLOADS, *CERT_WORKLOADS]:
        for k in args.sizes:
            r = run_case(workload, k, args.tactic, args.repeats, args.timeout,
                         lean, env, args.mem)
            results.append(r)
            save()
            print(fmt_row(r, base), flush=True)
            if r["status"] != "ok":
                if "message" in r:
                    print(f"|   | | {r['message'][:120]} | | | | |", flush=True)
                break

    print(f"\nWrote {out.relative_to(ROOT)}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
