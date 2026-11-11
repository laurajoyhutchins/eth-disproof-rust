#!/usr/bin/env python3
"""Source-pinned, resumable capture of imported OpenAI Lean executable seams.

This runner never fabricates Lean outputs and never edits the upstream submodule.
The only successful records are produced by a zero-exit `lake env lean --run`
with exact pinned sources, inspected for complete case coverage and hashed.
"""
from __future__ import annotations

import argparse
from dataclasses import dataclass
import gzip
import hashlib
import json
import os
from pathlib import Path
import resource
import subprocess
import sys
import tempfile
import time
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
UPSTREAM = ROOT / "upstream/openai-math"
LEAN_ROOT = Path(os.environ.get("LEAN_CAPTURE_PROJECT", str(UPSTREAM / "lean"))).resolve()
PIN = "4eaee87548250b2682affda7d05d947c05554bae"
VERSION = "leanprover/lean4:v4.34.1"
SCHEMA = 1


@dataclass(frozen=True)
class Stage:
    file: str
    kind: str
    cases: tuple[str, ...]
    args: tuple[str, ...] = ()


HIGH_CASES = ("empty", "zero", "one", "mixed", "alternate", "all")
TUPLE_ODO = ("empty", "width0", "one", "two", "split", "three", "carry", "overflow")
TUPLE_ENUM = ("empty", "width0", "one", "two", "split", "three")
STAGES: dict[str, Stage] = {
    "native-high": Stage("native_high_trace.lean", "legacy", tuple(
        f"{k}/{c}" for k in ("branch", "initialize") for c in HIGH_CASES)),
    "native-tuple": Stage("native_tuple_trace.lean", "legacy", tuple(
        [f"odometer/{c}" for c in TUPLE_ODO] +
        [f"enumerate/{c}" for c in TUPLE_ENUM])),
    "native-query-prefix": Stage("native_query_prefix_trace.lean", "legacy",
        tuple(f"prepare/{c}" for c in ("empty", "none", "first", "middle", "separated", "all"))),
    "native-nodes": Stage("native_nodes_trace.lean", "legacy",
        tuple(f"nodes/{c}" for c in ("empty", "zero", "one", "two", "third", "mixed"))),
    "native-layout-pair": Stage("native_layout_pair_trace.lean", "legacy",
        tuple(f"{k}/{n}" for k in ("layout", "pair") for n in range(4))),
    "machine-branch": Stage("machine_dump.lean", "machine", HIGH_CASES, ("branch",)),
    "machine-initialize": Stage("machine_dump.lean", "machine", HIGH_CASES, ("initialize",)),
    "machine-odometer": Stage("machine_dump.lean", "machine", TUPLE_ODO, ("odometer",)),
    "machine-enumerate": Stage("machine_dump.lean", "machine", TUPLE_ENUM, ("enumerate",)),
}


def digest(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def canonical(obj: Any) -> bytes:
    return (json.dumps(obj, sort_keys=True, separators=(",", ":")) + "\n").encode()


def process(args: list[str], cwd: Path) -> subprocess.CompletedProcess[bytes]:
    return subprocess.run(args, cwd=cwd, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                          check=False)


def checked_process(args: list[str], cwd: Path) -> str:
    p = process(args, cwd)
    if p.returncode:
        raise RuntimeError(f"{' '.join(args)} failed ({p.returncode}): {p.stderr.decode(errors='replace')}")
    return p.stdout.decode(errors="strict").strip()


def source_environment() -> dict[str, str]:
    if not (UPSTREAM / ".git").exists():
        raise RuntimeError("Upstream submodule not initialized. Run git submodule update --init upstream/openai-math")
    # An alternate Lake workspace is useful for building only the imported
    # source closure. It must import the original checked-out OAI tree, not a
    # copied or modified implementation.
    if LEAN_ROOT != (UPSTREAM / "lean").resolve():
        if (LEAN_ROOT / "OAI").resolve() != (UPSTREAM / "lean" / "OAI").resolve():
            raise RuntimeError("Alternate Lean workspace must link the pinned original OAI source")
    if not (LEAN_ROOT / "lakefile.lean").is_file():
        raise RuntimeError(f"No Lake project at {LEAN_ROOT}")
    mathlib = LEAN_ROOT / ".lake/packages/mathlib"
    if mathlib.exists():
        revision = checked_process(["git", "rev-parse", "HEAD"], mathlib)
        if revision != "d13f23b723b8a846827a245b89c10fc7d3f11612":
            raise RuntimeError(f"Unpinned Mathlib dependency: {revision}")
    head = checked_process(["git", "rev-parse", "HEAD"], UPSTREAM)
    if head != PIN:
        raise RuntimeError(f"Wrong original Lean source: expected {PIN}, got {head}")
    toolchain = (LEAN_ROOT / "lean-toolchain").read_text().strip()
    if toolchain != VERSION:
        raise RuntimeError(f"Wrong Lean toolchain pin: expected {VERSION}, got {toolchain}")
    # `git status` may include .lake/ which is ignored; tracked changes to source are forbidden.
    if checked_process(["git", "status", "--porcelain", "--untracked-files=normal"], UPSTREAM):
        raise RuntimeError("Upstream source has modifications; refusing capture")
    lean_version = checked_process(["lake", "env", "lean", "--version"], LEAN_ROOT)
    if "4.34.1" not in lean_version:
        raise RuntimeError(f"Unexpected executable Lean version: {lean_version}")
    return {"original_repo": "openai/math", "original_commit": head,
            "source_tree": checked_process(["git", "rev-parse", "HEAD^{tree}"], UPSTREAM),
            "toolchain_pin": toolchain, "lean_version": lean_version,
            "lake_manifest_sha256": digest((LEAN_ROOT / "lake-manifest.json").read_bytes())}


def validate(stage: Stage, raw: bytes) -> dict[str, Any]:
    """Reject partial, duplicated, malformed, or deceptively successful traces."""
    lines = raw.decode("utf-8", errors="strict").splitlines()
    if not lines or any(not s.strip() for s in lines):
        raise ValueError("No lines, or a blank trace line")
    wanted = set(stage.cases)
    seen: set[str] = set()
    if stage.kind == "legacy":
        for line in lines:
            fields = line.split("|")
            if len(fields) < 3 or not fields[2].isdecimal():
                raise ValueError(f"Invalid legacy line: {line[:160]}")
            name = f"{fields[0]}/{fields[1]}"
            if name not in wanted or name in seen:
                raise ValueError(f"Unexpected/duplicate case: {name}")
            seen.add(name)
    else:
        begun: set[str] = set()
        ended: set[str] = set()
        code: dict[str, set[int]] = {}
        sizes: dict[str, int] = {}
        next_step: dict[str, int] = {}
        initialized: set[str] = set()
        for line in lines:
            fields = line.split("|")
            if len(fields) < 3:
                raise ValueError(f"Malformed machine line: {line[:160]}")
            kind, case = fields[:2]
            if case not in wanted:
                raise ValueError(f"Unexpected case: {case}")
            if kind == "PROGRAM":
                if case in begun or len(fields) != 8 or not all(x.isdecimal() for x in fields[2:]):
                    raise ValueError(f"Bad/duplicate program header: {case}")
                begun.add(case)
                sizes[case] = int(fields[4])
                code[case] = set()
                next_step[case] = 0
            elif kind == "CODE":
                if case not in begun or case in ended or len(fields) != 4 or not fields[2].isdecimal():
                    raise ValueError(f"Bad code entry: {case}")
                idx = int(fields[2])
                if idx >= sizes[case] or idx in code[case]:
                    raise ValueError(f"Bad/duplicate instruction label {case}:{idx}")
                code[case].add(idx)
            elif kind == "INITIAL":
                if case not in begun or case in initialized or case in ended or len(fields) != 5 or next_step[case] != 0:
                    raise ValueError(f"Bad/duplicate initial state: {case}")
                initialized.add(case)
            elif kind == "STEP":
                if case not in initialized or case in ended or len(fields) != 8:
                    raise ValueError(f"Bad step record: {case}")
                if not fields[2].isdecimal() or int(fields[2]) != next_step[case]:
                    raise ValueError(f"Nonconsecutive step index in {case}")
                next_step[case] += 1
            elif kind == "END":
                if case not in initialized or case in ended or len(fields) != 7:
                    raise ValueError(f"Bad/duplicate termination: {case}")
                if fields[2] != "halted" or not fields[3].isdecimal() or int(fields[3]) != next_step[case]:
                    raise ValueError(f"Not halted / inconsistent step count: {case}")
                if len(code[case]) != sizes[case]:
                    raise ValueError(f"Incomplete instruction table: {case}")
                ended.add(case)
            else:
                raise ValueError(f"Unrecognized machine record {kind}")
        seen = ended
        if begun != ended:
            raise ValueError(f"Unterminated cases: {begun - ended}")
    if seen != wanted:
        raise ValueError(f"Incomplete cases: missing={sorted(wanted-seen)} extra={sorted(seen-wanted)}")
    return {"lines": len(lines), "cases": sorted(seen)}



def machine_metrics(raw: bytes) -> dict[str, Any]:
    """Derived source-instruction metrics; never confuse them with TM2 cost."""
    results: dict[str, dict[str, Any]] = {}
    for line in raw.decode("utf-8").splitlines():
        fields = line.split("|")
        kind, case = fields[:2]
        if kind == "PROGRAM":
            results[case] = {"register_ports": int(fields[2]), "stack_ports": int(fields[3]),
                             "instruction_labels": int(fields[4]), "instructions_executed": 0,
                             "visited_labels": [], "opcode_counts": {},
                             "peak_live_stack_bits": 0, "peak_nonempty_stacks": 0,
                             "peak_stack_word_bits": 0, "final_registers": "", "final_stacks": ""}
        elif kind in ("INITIAL", "STEP", "END"):
            row = results[case]
            stack_image = fields[-1]
            words = [w.split(":", 1)[1] for w in stack_image.split(";") if w]
            row["peak_live_stack_bits"] = max(row["peak_live_stack_bits"], sum(map(len, words)))
            row["peak_nonempty_stacks"] = max(row["peak_nonempty_stacks"], len(words))
            row["peak_stack_word_bits"] = max(row["peak_stack_word_bits"], max(map(len, words), default=0))
            if kind == "STEP":
                row["instructions_executed"] += 1
                label = int(fields[3])
                if label not in row["visited_labels"]:
                    row["visited_labels"].append(label)
                opname = fields[4].split(":", 1)[0]
                row["opcode_counts"][opname] = row["opcode_counts"].get(opname, 0) + 1
            if kind == "END":
                row["final_registers"] = fields[-2]
                row["final_stacks"] = fields[-1]
    return results


def atomic_write(path: Path, payload: bytes) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.NamedTemporaryFile(dir=path.parent, prefix=".tmp-", delete=False) as f:
        tmp = Path(f.name)
        try:
            f.write(payload)
            f.flush()
            os.fsync(f.fileno())
        finally:
            pass
    os.replace(tmp, path)


def stage_fingerprint(name: str, environment: dict[str, str], fuel: int) -> str:
    stage = STAGES[name]
    source = (ROOT / "instrumentation/probes" / stage.file).read_bytes()
    return digest(canonical({"schema": SCHEMA, "stage": name, "runner_sha256": digest(source),
        "environment": environment, "args": stage.args, "fuel": fuel if stage.kind == "machine" else None}))


def stage_paths(out: Path, name: str) -> tuple[Path, Path, Path]:
    return (out / "runs" / f"{name}.json", out / "runs" / f"{name}.stdout.gz",
            out / "runs" / f"{name}.stderr")


def check_record(out: Path, name: str, expected_fingerprint: str) -> dict[str, Any] | None:
    meta, stdout, stderr = stage_paths(out, name)
    if not any(p.exists() for p in (meta, stdout, stderr)):
        return None
    if not all(p.exists() for p in (meta, stdout, stderr)):
        raise ValueError(f"{name}: partial prior capture; manual removal required")
    record = json.loads(meta.read_text())
    if record.get("fingerprint") != expected_fingerprint:
        raise ValueError(f"{name}: stale capture fingerprint; use --replace to explicitly discard it")
    compressed = stdout.read_bytes()
    try:
        payload = gzip.decompress(compressed)
    except (OSError, EOFError) as exc:
        raise ValueError(f"{name}: corrupted gzip trace") from exc
    if record["stdout_sha256"] != digest(payload) or record["stdout_gzip_sha256"] != digest(compressed):
        raise ValueError(f"{name}: stdout integrity failure")
    if record["stderr_sha256"] != digest(stderr.read_bytes()):
        raise ValueError(f"{name}: stderr integrity failure")
    if record["coverage"] != validate(STAGES[name], payload):
        raise ValueError(f"{name}: changed/incomplete coverage")
    derived = machine_metrics(payload) if STAGES[name].kind == "machine" else None
    if record.get("machine_metrics") != derived:
        raise ValueError(f"{name}: derived machine metrics do not match")
    return record


def save_index(out: Path, environment: dict[str, str], fuel: int) -> None:
    rows = {}
    for name in STAGES:
        meta = out / "runs" / f"{name}.json"
        if meta.exists():
            rows[name] = json.loads(meta.read_text())
    atomic_write(out / "index.json", canonical({"schema": SCHEMA, "environment": environment,
        "fuel": fuel, "completed": rows}))


def capture(out: Path, names: list[str], environment: dict[str, str], fuel: int,
            replace: bool) -> None:
    out.mkdir(parents=True, exist_ok=True)
    for name in names:
        stage = STAGES[name]
        fingerprint = stage_fingerprint(name, environment, fuel)
        paths = stage_paths(out, name)
        if replace:
            for p in paths:
                p.unlink(missing_ok=True)
        previous = check_record(out, name, fingerprint)
        if previous is not None:
            print(f"SKIP {name}: complete verified capture ({previous['coverage']['lines']} lines)")
            continue
        args = ["lake", "env", "lean", "--run", str(ROOT / "instrumentation/probes" / stage.file)]
        if stage.kind == "machine":
            args += [*stage.args, "all", str(fuel)]
        print(f"RUN  {name}", flush=True)
        started = time.perf_counter_ns()
        p = process(args, LEAN_ROOT)
        nanos = time.perf_counter_ns() - started
        # Store failed process diagnostics, never a successful checkpoint.
        if p.returncode:
            atomic_write(out / "runs" / f"{name}.failed.stderr", p.stderr)
            raise RuntimeError(f"{name}: Lean exited {p.returncode}; diagnostics in runs/{name}.failed.stderr")
        try:
            coverage = validate(stage, p.stdout)
        except Exception as exc:
            atomic_write(out / "runs" / f"{name}.failed.stdout", p.stdout)
            atomic_write(out / "runs" / f"{name}.failed.stderr", p.stderr)
            raise RuntimeError(f"{name}: Lean trace incomplete or malformed: {exc}") from exc
        compressed = gzip.compress(p.stdout, mtime=0)
        record = {"schema": SCHEMA, "name": name, "fingerprint": fingerprint,
                  "args": args, "cwd": "upstream/openai-math/lean",
                  "stdout_sha256": digest(p.stdout), "stdout_gzip_sha256": digest(compressed),
                  "stderr_sha256": digest(p.stderr), "coverage": coverage,
                  "machine_metrics": machine_metrics(p.stdout) if stage.kind == "machine" else None,
                  "wall_nanoseconds": nanos, "exit_code": p.returncode,
                  "max_rss_kb_children_peak": resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss}
        # Checkpoint is written LAST, once both streams have been durably written.
        atomic_write(paths[1], compressed)
        atomic_write(paths[2], p.stderr)
        atomic_write(paths[0], canonical(record))
        save_index(out, environment, fuel)
        print(f"DONE {name}: {len(coverage['cases'])} cases, {coverage['lines']} lines")
    save_index(out, environment, fuel)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("action", choices=("plan", "capture", "verify", "status"))
    parser.add_argument("--out", type=Path, default=ROOT / "lean-captures")
    parser.add_argument("--stage", action="append", choices=sorted(STAGES), dest="stages")
    parser.add_argument("--fuel", type=int, default=100000)
    parser.add_argument("--replace", action="store_true", help="explicitly replace previously recorded stages")
    args = parser.parse_args()
    names = list(dict.fromkeys(args.stages or list(STAGES)))
    if args.fuel <= 0:
        parser.error("--fuel must be positive")
    if args.action == "plan":
        for name in names:
            st = STAGES[name]
            print(f"{name:22} {st.file:36} {len(st.cases)} cases")
        return 0
    if args.action == "status":
        for name in names:
            print(f"{name:22} {'record present (unverified)' if stage_paths(args.out, name)[0].exists() else 'missing'}")
        return 0
    environment = source_environment()  # all nontrivial actions fail closed on source/runtime mismatch
    if args.action == "capture":
        capture(args.out, names, environment, args.fuel, args.replace)
    else:
        for name in names:
            data = check_record(args.out, name, stage_fingerprint(name, environment, args.fuel))
            if data is None:
                raise ValueError(f"{name}: no capture")
            print(f"VERIFIED {name}: {len(data['coverage']['cases'])} cases")
    return 0


if __name__ == "__main__":
    try:
        sys.exit(main())
    except (ValueError, RuntimeError, OSError) as exc:
        print(f"ERROR: {exc}", file=sys.stderr)
        sys.exit(1)
