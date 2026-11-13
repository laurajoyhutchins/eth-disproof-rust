#!/usr/bin/env python3
"""Source-elaborated, phase-by-phase original counting graph coverage.

This intentionally never substitutes a semantic SAT oracle for an opaque
BitProgram leaf. All probes are source-derived wrappers around pinned original
definitions, not independent original declarations. This is a diagnostic gate,
not a proof that the final counting machine runs.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import tempfile

from bounded_process import run_bounded
from export_compiled_batch import atomic_write, ensure_pinned
from extract_compiled_catalog import blob_hash
from run_source_graph_batch import LEAN
from compile_native_count import large_only_wrapper, LARGE_FQN, LARGE_IDENTITY
from verify_source_graph import (
    MAX_NODES, MAX_SOURCE_LABELS, SOURCE_SHA, closed_keys, insist, number,
    parse_node, parse_source_graph_json,
)

PREFIX = "OAI.Algorithms.SubexponentialSAT.SqrtLogSpace"
WRAPPER_NAME = PREFIX + ".CountingProbe.program"
MODULE_OUTER = PREFIX + ".NativeOuter"
MODULE_LEAF = PREFIX + ".NativeLeafProgram"
PHASES = {
    # Stage/port definitions are from the pinned original Lean source.
    "marked-query": (f"HighQueryProgram.marked {{k}}", 40, 896, 321, 323,
                     PREFIX + ".HighQueryProgram"),
    "accepted-query": (f"HighQueryProgram.accepted {{k}}", 40, 896, 700, 788,
                       PREFIX + ".HighQueryProgram"),
    "local-leaf": (f"NativeLeafProgram.localCommand {{k}}", 40, 896, 784, 788,
                   MODULE_LEAF),
    "leaf": (f"NativeLeafProgram.command {{k}}", 80, 1220, 265, 263,
             MODULE_LEAF),
    "dfs": (f"DisjointReuse.DFSCountProgram.command {{k}} (NativeLeafProgram.command {{k}})",
            80, 1220, 256, 256,
            PREFIX + ".DisjointReuse.DFSCountProgram"),
    "outer": (f"Native.outerCommand {{k}} (NativeLeafProgram.command {{k}})",
              80, 1220, 256, 1216, MODULE_OUTER),
    # The original finite fallback remains in this source expression, even
    # when it refuses to reduce to a supported finite source graph.
    "complete": (
        f"Native.entryCommand {{cutoff}} (Native.outerCommand {{k}} "
        f"(NativeLeafProgram.command {{k}}))",
        80, 1220, 256, 1216, MODULE_OUTER),
    "large-domain": ("source-refined-original-large-domain",
                     80, 1220, 256, 1216, MODULE_OUTER),
}


def phase_imports(phase: str) -> str:
    """Import only the compiled module closure required for the selected stage.

    Importing NativeOuter for a query-only probe would require building the
    entire later DFS closure and can falsely report a missing .olean as a
    failure of the marked-query command itself.
    """
    if phase not in PHASES:
        raise ValueError(f"unknown source counting phase: {phase}")
    module = PHASES[phase][-1]
    modules = [module]
    if phase in {"dfs", "outer", "complete", "large-domain"}:
        modules.append(MODULE_LEAF)
    return "".join(f"import {m}\n" for m in dict.fromkeys(modules))


def wrapper_for(phase: str, width: int, cutoff: int) -> tuple[str, tuple[int, ...]]:
    if phase not in PHASES:
        raise ValueError(f"unknown source counting phase: {phase}")
    if not (2 <= width <= 8 and 0 <= cutoff <= 128):
        raise ValueError("unsupported source counting parameter")
    if phase == "large-domain":
        return large_only_wrapper(width, cutoff), (80, 1220, 256, 1216)
    expression, r, s, inp, out, _module = PHASES[phase]
    expression = expression.format(k=width, cutoff=cutoff)
    wrapper = (
        phase_imports(phase)
        + f"namespace {PREFIX}.CountingProbe\n"
        f"open {PREFIX}\n"
        "open BitProgram StructuredCalls\n"
        "-- Source-derived diagnostic, NOT a new counting implementation.\n"
        "noncomputable def program :=\n"
        f"  compiled ({expression}) {inp} {out}\n"
        f"end {PREFIX}.CountingProbe\n"
    )
    return wrapper, (r, s, inp, out)


def inspect(phase: str, raw: bytes, blob: str, width: int, cutoff: int) -> dict:
    graph = parse_source_graph_json(raw)
    closed_keys(graph, {"kind", "source_commit", "source_blob", "declaration",
                        "id", "abi", "command"})
    insist(graph["kind"] == "original-structured-source-v1", "wrong graph protocol")
    expected_name = LARGE_FQN if phase == "large-domain" else WRAPPER_NAME
    expected_id = LARGE_IDENTITY if phase == "large-domain" else phase
    insist(graph["source_commit"] == SOURCE_SHA and
           graph["source_blob"] == blob and
           graph["declaration"] == expected_name and graph["id"] == expected_id,
           "source graph identity mismatch")
    _, expected = wrapper_for(phase, width, cutoff)
    abi = graph["abi"]
    closed_keys(abi, {"r", "s", "labels", "input", "output"})
    r = number(abi["r"], 256, "registers")
    s = number(abi["s"], 4096, "stacks")
    labels = number(abi["labels"], MAX_SOURCE_LABELS, "physical labels")
    inp = number(abi["input"], s, "input")
    out = number(abi["output"], s, "output")
    insist((r, s, inp, out) == expected, "original source stage ABI mismatch")
    root = parse_node(graph["command"], r, s, [MAX_NODES])
    insist(root.size + 1 == labels and 0 <= root.entry(1, 0) < labels,
           "source stage labels/entry inconsistent")
    # Static counts are instrumentation only; no claim of runtime execution.
    counts: dict[str, int] = {}
    def walk(node):
        counts[node.kind] = counts.get(node.kind, 0) + 1
        for child in node.children:
            walk(child)
    walk(root)
    return {
        "phase": phase,
        "status": "SOURCE_GRAPH_STRUCTURAL_ACCEPTED_UNCERTIFIED",
        "labels": labels, "entry": root.entry(1, 0),
        "abi": abi, "command_nodes": counts,
        "graph_sha256": hashlib.sha256(raw).hexdigest(),
    }


def source_for(wrapper: str, phase: str, source_blob: str, max_labels: int) -> str:
    # One graph exporter and one source-derived program wrapper for each stage.
    namespace = (PREFIX + ".CountingExecutable" if phase == "large-domain"
                 else PREFIX + ".CountingProbe")
    fqn = LARGE_FQN if phase == "large-domain" else WRAPPER_NAME
    identity = LARGE_IDENTITY if phase == "large-domain" else phase
    definitions = wrapper.split("namespace " + namespace, 1)[1]
    return (
        phase_imports(phase)
        + LEAN.read_text()
        + "\nnamespace " + namespace + definitions
        + "\nset_option maxHeartbeats 2000000\n"
        + f'#export_original_source_graph {fqn} "{identity}" "{source_blob}"\n'
    )


def run(a) -> dict:
    upstream, lake_root = a.upstream.resolve(), a.lake_root.resolve()
    pins = ensure_pinned(upstream, lake_root)
    insist(a.max_labels >= 1 and a.max_labels <= 8192, "invalid finite callee limit")
    requested = a.phase if isinstance(a.phase, list) else [a.phase]
    phases = list(PHASES) if "all" in requested else requested
    insist(len(phases) == len(set(phases)) and all(x in PHASES for x in phases),
           "duplicate or unknown counting phases")
    a.output_dir.mkdir(parents=True, exist_ok=True)
    report_path = a.output_dir / "counting-closure-report.json"
    report_path.unlink(missing_ok=True)
    accepted: list[dict] = []
    refused: list[dict] = []
    def checkpoint() -> None:
        atomic_write(report_path, json.dumps({
            "kind": "source-derived-counting-closure-diagnostic",
            "source_commit": SOURCE_SHA, "pins": pins,
            "width": a.width, "cutoff": a.cutoff,
            "accepted": accepted, "refused": refused, "requested": phases,
            "attempted": len(accepted) + len(refused),
            "not_attempted": phases[len(accepted) + len(refused):],
            "complete_counting_verified": False,
        }, sort_keys=True, indent=2) + "\n")

    checkpoint()
    prepared_modules: set[str] = set()
    failed_modules: dict[str, str] = {}
    build_blocked = False
    for phase in phases:
        if build_blocked:
            break
        _expr, _r, _s, _in, _out, module = PHASES[phase]
        source_relative = "lean/" + module.replace(".", "/") + ".lean"
        source_file = upstream / source_relative
        try:
            insist(source_file.is_file(), "original source module not checked out")
            blob = blob_hash(source_file.read_bytes())
            wrapper, _ = wrapper_for(phase, a.width, a.cutoff)
            with tempfile.TemporaryDirectory(prefix="source-counting-", dir=lake_root) as tmp:
                probe = Path(tmp) / "CountingProbe.lean"
                probe.write_text(source_for(wrapper, phase, blob, a.max_labels),
                                 encoding="utf-8")
                # A single invocation shares successful module builds and
                # remembers unsuccessful ones: a timed-out dependency must not
                # be rebuilt independently for every counting stage.
                modules = list(dict.fromkeys([module] +
                    ([MODULE_LEAF] if phase in {"dfs", "outer", "complete", "large-domain"} else [])))
                for dependency in modules:
                    if dependency in failed_modules:
                        raise RuntimeError(
                            f"DEPENDENCY_NOT_READY {dependency}: {failed_modules[dependency]}")
                    if dependency in prepared_modules:
                        continue
                    # Explicit --no-build separates source export from the
                    # expensive original .olean prerequisite. No guessed graph
                    # status may be reported when the import was not built.
                    if getattr(a, "no_build", False):
                        artifact = lake_root / ".lake/build/lib/lean" / (
                            dependency.replace(".", "/") + ".olean")
                        if not artifact.is_file():
                            failed_modules[dependency] = "original .olean missing (no-build)"
                            raise RuntimeError(
                                f"DEPENDENCY_NOT_READY {dependency}: original .olean missing")
                    else:
                        argv = ["lake", "-K", "maxJobs=2", "build", dependency]
                        try:
                            build = run_bounded(
                                argv, cwd=lake_root,
                                timeout=getattr(a, "build_timeout_seconds", a.timeout_seconds),
                            )
                        except subprocess.TimeoutExpired as exc:
                            # subprocess.TimeoutExpired may retain bytes even
                            # with text=True. Preserve the last actual Lean
                            # diagnostics instead of the Python exception alone.
                            def tail(value) -> str:
                                if isinstance(value, bytes):
                                    return value[-6000:].decode("utf-8", errors="replace")
                                return str(value or "")[-6000:]
                            summary = tail(exc.stdout) + "\n" + tail(exc.stderr)
                            failed_modules[dependency] = "build timeout"
                            atomic_write(a.output_dir / (phase + ".build.log"),
                                         summary + "\n")
                            raise RuntimeError(
                                f"DEPENDENCY_BUILD_TIMEOUT {dependency}: {summary[-1000:]}")
                        summary = build.stdout[-6000:] + "\n" + build.stderr[-6000:]
                        atomic_write(a.output_dir / (phase + ".build.log"),
                                     summary + "\n")
                        if build.returncode:
                            failed_modules[dependency] = "build failed"
                            raise RuntimeError(
                                f"DEPENDENCY_BUILD_FAILED {dependency}: {summary[-2500:]}")
                    prepared_modules.add(dependency)
                result = run_bounded(
                    ["lake", "env", "lean", str(probe)],
                    cwd=lake_root,
                    env={**os.environ, "ORIGINAL_MAX_LABELS": str(a.max_labels)},
                    timeout=a.timeout_seconds,
                )
                if result.returncode:
                    raise RuntimeError("Lean original graph export: " +
                                       (result.stdout + result.stderr)[-3000:])
                raw = result.stdout.encode("ascii")
                accepted_phase = inspect(phase, raw, blob, a.width, a.cutoff)
                accepted_phase["source_blob"] = blob
                accepted_phase["original_module"] = module
                accepted_phase["wrapper_sha256"] = hashlib.sha256(wrapper.encode()).hexdigest()
                atomic_write(a.output_dir / f"{phase}.graph.json", result.stdout)
                accepted.append(accepted_phase)
                print("SOURCE_COUNTING_PHASE_ACCEPTED", phase,
                      accepted_phase["labels"], flush=True)
        except (ValueError, RuntimeError, OSError, subprocess.TimeoutExpired,
                UnicodeError) as exc:
            refused.append({
                "phase": phase, "status": "REFUSED",
                "reason": type(exc).__name__,
                "detail": str(exc)[-3000:],
                "original_module": module,
            })
            print("SOURCE_COUNTING_PHASE_REFUSED", phase,
                  type(exc).__name__, str(exc)[-300:], flush=True)
            # A dependent phase cannot be distinguished from this failed
            # prerequisite until the source module is built. Do not burn
            # the runner budget trying the same unfinished closure again.
            if str(exc).startswith(("DEPENDENCY_BUILD_", "DEPENDENCY_NOT_READY")):
                build_blocked = True
        checkpoint()
    if refused:
        raise SystemExit(f"counting closure incomplete: {len(accepted)} accepted,"
                         f" {len(refused)} refused; inspect {report_path}")
    return {"accepted": accepted, "refused": refused}


def main():
    p = argparse.ArgumentParser(description=__doc__)
    for key in ("upstream", "lake-root", "output-dir"):
        p.add_argument("--" + key, type=Path, required=True)
    p.add_argument("--phase", choices=["all", *PHASES], action="append",
                   default=None, help="repeat to probe ordered stages in one shared build")
    p.add_argument("--width", type=int, default=3)
    p.add_argument("--cutoff", type=int, default=20)
    p.add_argument("--max-labels", type=int, default=4096)
    p.add_argument("--timeout-seconds", type=int, default=240,
                   help="per-stage Lean graph export budget")
    p.add_argument("--build-timeout-seconds", type=int, default=900,
                   help="one-time budget per required original Lean module")
    p.add_argument("--no-build", action="store_true",
                   help="probe only when original module .olean prerequisites exist")
    a = p.parse_args()
    a.phase = a.phase or ["all"]
    if not (10 <= a.timeout_seconds <= 1200 and
            10 <= a.build_timeout_seconds <= 1800):
        p.error("invalid Lean compilation budget")
    run(a)


if __name__ == "__main__":
    main()
