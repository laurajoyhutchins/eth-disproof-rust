#!/usr/bin/env python3
"""Probe original QueryStream dependencies in separate pinned Lean processes.

Uses the existing original-source exporter and kernel certificate generator.
Each named stage imports its *own* original module, not QueryStreamProgram.
A graph without a successful exact Lean certificate is NOT an executable or
a source-refinement result. No SAT oracle or replacement command is supplied.
"""
from __future__ import annotations

import argparse
from dataclasses import dataclass
import hashlib
import json
import os
from pathlib import Path
import re
import signal
import subprocess
import tempfile
import time

from export_compiled_batch import atomic_write, ensure_pinned
from extract_compiled_catalog import SOURCE_SHA, blob_hash
from run_source_graph_batch import source
from source_graph_kernel_certificate import certificate_source, read_source_graph

SOURCE_ROOT = Path("lean/OAI/Algorithms/SubexponentialSAT")
MAX_OUTPUT_BYTES = 4 * 1024 * 1024
MAX_PEAK_RSS_BYTES = 12 * 1024 * 1024 * 1024
MAX_CERTIFICATE_LABELS = 4096


@dataclass(frozen=True)
class Stage:
    id: str
    module_suffix: str
    declaration_suffix: str
    registers: int
    stacks: int
    input: int
    output: int

    @property
    def module(self) -> str:
        return "OAI.Algorithms.SubexponentialSAT." + self.module_suffix

    @property
    def declaration(self) -> str:
        return "OAI.Algorithms.SubexponentialSAT." + self.declaration_suffix + ".program"

    @property
    def relative_path(self) -> Path:
        return SOURCE_ROOT / (self.module_suffix.replace(".", "/") + ".lean")


# Ordered from the local numerical readout outward. No synthetically
# reconstructed full QueryStream root is admitted by this stage list.
STAGES = (
    Stage("moments_readout", "SqrtLog.MomentsReadoutProgramNative",
          "SqrtLog.MomentsReadoutProgram", 8, 40, 15, 0),
    Stage("node_readout", "SqrtLogSpace.NodeReadoutSpace",
          "SqrtLogSpace.NodeReadoutSpace", 40, 896, 850, 862),
    Stage("node_append", "SqrtLogSpace.NodeAppendSpace",
          "SqrtLogSpace.NodeAppendSpace", 40, 896, 850, 863),
    Stage("node_finish", "SqrtLogSpace.QueryNodeFinish",
          "SqrtLogSpace.QueryNodeFinish", 40, 896, 850, 863),
    Stage("reconstruction", "SqrtLogSpace.QueryReconstruction",
          "SqrtLogSpace.QueryReconstruction", 40, 896, 863, 323),
)
STAGE_BY_ID = {stage.id: stage for stage in STAGES}


def pinned_record(stage: Stage, upstream: Path) -> dict[str, str]:
    """Bind module and symbol to actual source bytes, not a hand-entered hash."""
    path = upstream / stage.relative_path
    raw = path.read_bytes()
    # A lexical sanity check, not proof of the declaration's elaboration.
    if not re.search(rb"(?m)^def program\s*:=\s*compiled\b", raw):
        raise ValueError(f"missing expected source compiled program in {stage.relative_path}")
    return {
        "id": "query_module_" + stage.id,
        "module": stage.module,
        "fqn": stage.declaration,
        "git_blob": blob_hash(raw),
    }


def validate_stage_graph(path: Path, stage: Stage, record: dict[str, str]) -> tuple[int, str]:
    """Reuse the canonical strict graph parser and source-bound ABI verifier."""
    raw, _parsed, _root, (r, s, labels, _entry, inp, out) = read_source_graph(
        path, record
    )
    if (r, s, inp, out) != (stage.registers, stage.stacks, stage.input, stage.output):
        raise ValueError(
            f"{stage.id} original ABI mismatch: {(r, s, inp, out)}"
        )
    return labels, hashlib.sha256(raw).hexdigest()


def rss_bytes(pgid: int) -> int:
    """Account for the whole supervised Linux process group, including Lake."""
    if not Path("/proc").is_dir():
        raise RuntimeError("RSS-supervised original extraction requires Linux /proc")
    total = 0
    for proc in Path("/proc").iterdir():
        if not proc.name.isdecimal():
            continue
        try:
            fields = (proc / "stat").read_text().rsplit(") ", 1)[1].split()
            if int(fields[2]) != pgid:
                continue
            for line in (proc / "status").read_text().splitlines():
                if line.startswith("VmRSS:"):
                    total += int(line.split()[1]) * 1024
                    break
        except (OSError, IndexError, ValueError):
            continue
    return total


class Refusal(RuntimeError):
    pass


def run_stage_process(argv: list[str], cwd: Path, log: Path, timeout: int,
                      rss_limit: int = MAX_PEAK_RSS_BYTES,
                      env: dict[str, str] | None = None) -> dict[str, int]:
    """Bound wall time, output and process-group RSS, including child cleanup."""
    stdout = log.with_suffix(".stdout.log")
    stderr = log.with_suffix(".stderr.log")
    log.parent.mkdir(parents=True, exist_ok=True)
    with stdout.open("wb") as out, stderr.open("wb") as err:
        child = subprocess.Popen(argv, cwd=cwd, stdin=subprocess.DEVNULL,
                                 stdout=out, stderr=err, start_new_session=True, env=env)
        start = time.monotonic()
        peak = 0
        try:
            while child.poll() is None:
                peak = max(peak, rss_bytes(child.pid))
                if os.fstat(out.fileno()).st_size > MAX_OUTPUT_BYTES or
                    os.fstat(err.fileno()).st_size > MAX_OUTPUT_BYTES:
                    raise Refusal("original Lean output exceeds bounded log budget")
                if peak > rss_limit:
                    raise Refusal(f"original Lean process group exceeded {rss_limit} RSS bytes")
                if time.monotonic() - start >= timeout:
                    raise Refusal(f"original Lean wall timeout {timeout}s")
                time.sleep(0.2)
            if child.returncode != 0:
                raise Refusal(f"original Lean exit {child.returncode}")
            if os.fstat(out.fileno()).st_size > MAX_OUTPUT_BYTES or
                    os.fstat(err.fileno()).st_size > MAX_OUTPUT_BYTES:
                raise Refusal("original Lean output exceeds bounded log budget")
        except BaseException:
            if child.poll() is None:
                try:
                    os.killpg(child.pid, signal.SIGKILL)
                except ProcessLookupError:
                    pass
                try:
                    child.wait(timeout=3)
                except subprocess.TimeoutExpired:
                    child.kill()
                    child.wait(timeout=1)
            raise
    return {"peak_rss_bytes": peak, "elapsed_ms": int((time.monotonic() - start)*1000)}


def phase_from_log(path: Path) -> str:
    phase = "import-or-initialization"
    if path.is_file():
        for line in path.read_text(errors="replace").splitlines():
            if line.startswith("SOURCE_GRAPH_PHASE="):
                phase = line.removeprefix("SOURCE_GRAPH_PHASE=").strip()[:160]
    return phase


def probe_one(stage: Stage, upstream: Path, lake: Path, output: Path,
              build_timeout: int, export_timeout: int, cert_timeout: int,
              max_labels: int, rss_limit: int) -> dict:
    directory = output / stage.id
    directory.mkdir(parents=True, exist_ok=True)
    # Never accidentally inherit a previous successful receipt.
    for name in ("source.json", "kernel-certificate.lean", "receipt.json",
                 "report.json", "build.stdout.log", "build.stderr.log",
                 "graph.stdout.log", "graph.stderr.log",
                 "certificate.stdout.log", "certificate.stderr.log"):
        (directory / name).unlink(missing_ok=True)
    result = {"stage": stage.id, "module": stage.module,
              "declaration": stage.declaration, "source_commit": SOURCE_SHA,
              "status": "REFUSED", "lean_rust_refinement": "unassessed",
              "native_executable": False, "full_query": False}
    try:
        record = pinned_record(stage, upstream)
        result["source_blob"] = record["git_blob"]
        # Each stage gets fresh subprocesses. None imports QueryStreamProgram.
        result["build"] = run_stage_process(
            ["lake", "-K", "maxJobs=2", "build", stage.module],
            lake, directory / "build", build_timeout, rss_limit
        )
        with tempfile.TemporaryDirectory(prefix="query-module-") as tmp:
            probe = Path(tmp) / "Inspect.lean"
            probe.write_text(source(record), encoding="utf-8")
            result["export"] = run_stage_process(
                ["lake", "env", "lean", "-j", "1", "-M", "9216", str(probe)],
                lake, directory / "graph", export_timeout, rss_limit,
                env={**os.environ, "ORIGINAL_MAX_LABELS": str(max_labels),
                     "ORIGINAL_SOURCE_GRAPH_TRACE": "1"},
            )
            raw = (directory / "graph.stdout.log").read_bytes()
            graph = Path(tmp) / "source.json"
            graph.write_bytes(raw)
            labels, graph_sha = validate_stage_graph(graph, stage, record)
            result["physical_labels"] = labels
            result["source_graph_sha256"] = graph_sha
            if labels > MAX_CERTIFICATE_LABELS:
                result["status"] = "GRAPH_ONLY_UNCERTIFIED"
                (directory / "source.json").write_bytes(raw)
            else:
                cert, receipt = certificate_source(graph, record)
                certificate = Path(tmp) / "Certificate.lean"
                certificate.write_text(cert, encoding="utf-8")
                result["certificate"] = run_stage_process(
                    ["lake", "env", "lean", "-j", "1", "-M", "9216",
                     str(certificate)], lake, directory / "certificate",
                    cert_timeout, rss_limit
                )
                if (directory / "certificate.stdout.log").read_bytes().strip():
                    raise Refusal("Lean certificate emitted unexpected stdout")
                receipt.update({
                    "status": "ORIGINAL_MODULE_GRAPH_KERNEL_CERTIFIED",
                    "stage": stage.id,
                    "lean_rust_refinement": "unassessed",
                    "native_executable": False,
                    "full_query": False,
                })
                (directory / "source.json").write_bytes(raw)
                atomic_write(directory / "kernel-certificate.lean", cert)
                atomic_write(directory / "receipt.json",
                             json.dumps(receipt, sort_keys=True, indent=2) + "\n")
                result["status"] = "ORIGINAL_MODULE_GRAPH_KERNEL_CERTIFIED"
                result["certificate_sha256"] = receipt["certificate_sha256"]
    except (Refusal, ValueError, OSError, subprocess.SubprocessError) as error:
        result["status"] = "REFUSED"
        result["reason"] = str(error)[-1000:]
        for name in ("source.json", "kernel-certificate.lean", "receipt.json"):
            (directory / name).unlink(missing_ok=True)
    result["last_graph_phase"] = phase_from_log(directory / "graph.stderr.log")
    atomic_write(directory / "report.json", json.dumps(result, sort_keys=True, indent=2)+"\n")
    return result


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--upstream", type=Path, required=True)
    parser.add_argument("--lake-root", type=Path, required=True)
    parser.add_argument("--output-dir", type=Path, required=True)
    parser.add_argument("--stages", nargs="+", choices=sorted(STAGE_BY_ID),
                        default=["moments_readout"])
    parser.add_argument("--build-timeout", type=int, default=900)
    parser.add_argument("--export-timeout", type=int, default=300)
    parser.add_argument("--cert-timeout", type=int, default=300)
    parser.add_argument("--max-source-labels", type=int, default=4096)
    parser.add_argument("--rss-limit-gib", type=int, default=12)
    args = parser.parse_args()
    if not (60 <= args.build_timeout <= 3600 and 30 <= args.export_timeout <= 1800
            and 30 <= args.cert_timeout <= 1800 and
            1 <= args.max_source_labels <= 1_000_000_000 and
            1 <= args.rss_limit_gib <= 12):
        parser.error("invalid bounded extraction parameters")
    upstream, lake = args.upstream.resolve(), args.lake_root.resolve()
    output = args.output_dir.resolve()
    output.mkdir(parents=True, exist_ok=True)
    pin = ensure_pinned(upstream, lake)
    results = []
    for stage_id in dict.fromkeys(args.stages):
        stage = STAGE_BY_ID[stage_id]
        result = probe_one(stage, upstream, lake, output,
                           args.build_timeout, args.export_timeout,
                           args.cert_timeout, args.max_source_labels,
                           args.rss_limit_gib * 1024**3)
        results.append(result)
        print(f"QUERY_MODULE_STAGE={stage.id} status={result['status']} "
              f"phase={result['last_graph_phase']}", flush=True)
    report = {"kind": "original-query-module-extraction-v1", "pin": pin,
              "stages": results, "complete_query_executable": False,
              "rust_correspondence": "unassessed"}
    atomic_write(output / "report.json", json.dumps(report, sort_keys=True, indent=2)+"\n")
    if any(stage["status"] == "REFUSED" for stage in results):
        raise SystemExit(2)


if __name__ == "__main__":
    main()
