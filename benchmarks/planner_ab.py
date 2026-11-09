"""Source-pinned before/after performance audit of the pure scope planner.

Run on a dedicated CI host with git history available. Both arms run with
identical Python and dependencies; reports are measurements, not theorems.
This script intentionally lives outside the per-commit checkpoint gate.
"""
from __future__ import annotations

import json
import os
from pathlib import Path
import platform
import subprocess
import sys
from tempfile import TemporaryDirectory
from statistics import median

BASE = "b82c5d0a2bbada23320c936e58b6b551388209f2"
POST = "e39cd4c2dc28b5c6ae626ba9fb252f2f7ccc7f52"
ROOT = Path(__file__).resolve().parents[1]

MICRO = r"""
import json
from statistics import median
from time import perf_counter_ns
from non_exponential_sudoku.core.network import compile_leaf_plan
# Cycle / ladder, bounded treewidth with enough variables to expose
# planning cost. No coefficient tables or work accounting are involved.
n = 28
scopes = tuple((i, i+1) for i in range(n-1)) + tuple(
    (i, i+1, i+2) for i in range(n-2)
)
samples = []
for repeat in range(8):
    start = perf_counter_ns()
    for _ in range(120):
        plan = compile_leaf_plan(n, scopes, max_width=8, lookup_budget=0)
        if plan is None or len(plan.steps) != n:
            raise AssertionError("Unexpected structural refusal")
    samples.append((perf_counter_ns()-start)/120)
print(json.dumps({"median_ns_per_plan": median(samples),
                  "samples_ns_per_plan": samples,
                  "steps": len(plan.steps)}))
"""


def execute(root: Path, command: list[str], timeout: int = 300) -> str:
    env = os.environ.copy()
    env["PYTHONPATH"] = os.pathsep.join([str(root / "src"), str(root)])
    result = subprocess.run(command, cwd=root, env=env, check=False,
                            capture_output=True, text=True, timeout=timeout)
    if result.returncode:
        raise RuntimeError(
            f"{root.name}: {command}: exit={result.returncode}\n"
            + (result.stdout + result.stderr)[-5000:]
        )
    return result.stdout


def bench(root: Path, dest: Path) -> dict[str, object]:
    micro = json.loads(execute(root, [sys.executable, "-c", MICRO], 120))
    evidence_path = dest / "unified.json"
    execute(root, [
        sys.executable, "-m", "benchmarks.unified_cost",
        "--cases", "parity-2wire", "sudoku-4wire", "nested-2wire",
        "--variants", "reference", "plans",
        "--repeats", "3", "--timeout", "60",
        "--output", str(evidence_path)
    ], 450)
    evidence = json.loads(evidence_path.read_text())
    if evidence.get("status") != "complete":
        raise RuntimeError(f"{root.name}: unified experiment incomplete")
    summaries = {}
    for row in evidence["measured"]:
        summary = row["summary"]
        key = summary["case"] + "/" + summary["variant"]
        summaries[key] = {
            "count": summary["exact_count"],
            "ns": summary["baseline"]["median_duration_ns"],
            "samples_ns": summary["baseline"]["duration_ns"],
            "rss_bytes": summary["baseline"]["peak_process_rss_bytes"],
        }
    # Sparse ETH path is meaningful because it executes the shared
    # min-domain planning repeatedly. We compare the same exact counts.
    chain_code = (
        "import json;"
        "from benchmarks.eth.factorized_taylor_probe import _case;"
        "print(json.dumps([_case(n) for n in (12,32,64)]))"
    )
    chain = json.loads(execute(root, [sys.executable, "-c", chain_code], 300))
    return {"micro": micro, "contractions": summaries, "taylor_chains": chain}


def main() -> None:
    with TemporaryDirectory(prefix="planner-ab-") as tmp:
        root = Path(tmp)
        names = {"pre": BASE, "post": POST}
        checkouts = {}
        for name, ref in names.items():
            checkout = root / name
            execute(ROOT, ["git", "worktree", "add", "--detach", str(checkout), ref], 120)
            head = execute(checkout, ["git", "rev-parse", "HEAD"]).strip()
            if head != ref:
                raise AssertionError(f"Wrong source head: {head}")
            checkouts[name] = checkout
        # Alternate the arms to limit systematic thermal/cache differences.
        observed: dict[str, list[dict[str, object]]] = {"pre": [], "post": []}
        for name in ("pre", "post", "post", "pre"):
            observed[name].append(bench(checkouts[name], root / name))
        keys = set(observed["pre"][0]["contractions"])
        if any(set(run["contractions"]) != keys for runs in observed.values()
               for run in runs):
            raise AssertionError("Workload mismatch across arms")
        comparisons = []
        for key in sorted(keys):
            before = [int(run["contractions"][key]["ns"])
                      for run in observed["pre"]]
            after = [int(run["contractions"][key]["ns"])
                     for run in observed["post"]]
            counts = [run["contractions"][key]["count"]
                      for runs in observed.values() for run in runs]
            if len(set(counts)) != 1:
                raise AssertionError(f"Exact count changed: {key}")
            comparisons.append({
                "case": key, "count": counts[0],
                "pre_ns": before, "post_ns": after,
                "ratio_post_pre": median(after)/median(before),
            })
        micro_pre = [float(x["micro"]["median_ns_per_plan"])
                     for x in observed["pre"]]
        micro_post = [float(x["micro"]["median_ns_per_plan"])
                      for x in observed["post"]]
        chain = []
        for pos, n in enumerate((12, 32, 64)):
            pre = [r["taylor_chains"][pos] for r in observed["pre"]]
            post = [r["taylor_chains"][pos] for r in observed["post"]]
            if any(int(r["variables"]) != n for r in pre+post):
                raise AssertionError("Taylor family mismatch")
            if len({r["count"] for r in pre+post}) != 1:
                raise AssertionError("Taylor exact count mismatch")
            if len({(r["factor_assignments_tested"],
                     r["factor_scope_peak"], r["factor_entries_peak"])
                    for r in pre+post}) != 1:
                raise AssertionError("Taylor structural work changed")
            chain.append({
                "variables": n, "count": pre[0]["count"],
                "pre_seconds": [r["factorized_seconds"] for r in pre],
                "post_seconds": [r["factorized_seconds"] for r in post],
                "ratio_post_pre": median(r["factorized_seconds"] for r in post) /
                                  median(r["factorized_seconds"] for r in pre),
                "factor_assignments_tested": pre[0]["factor_assignments_tested"]
            })
        report = {
            "reference_source": {"pre": BASE, "post": POST},
            "python": platform.python_version(),
            "host": platform.platform(),
            "micro_ns_per_plan": {
                "pre": micro_pre, "post": micro_post,
                "ratio_post_pre": median(micro_post)/median(micro_pre),
            },
            "contractions": comparisons,
            "taylor_chains": chain,
            "interpretation": "ABBA independent runs; exact answers verified; CI noise possible",
        }
        output = ROOT / "artifacts" / "planner-ab.json"
        output.parent.mkdir(exist_ok=True, parents=True)
        output.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")
        print("Planner AB: source-pinned results")
        print(json.dumps(report, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
