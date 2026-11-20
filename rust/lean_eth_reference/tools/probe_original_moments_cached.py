#!/usr/bin/env python3
"""One pinned original readout graph probe using the existing trusted OAI cache.

This is deliberately run against the long-lived original-query import branch,
whose built .olean files are branch-scoped. No ad-hoc rebuild is allowed: a
missing cached module is an explicit refusal. The only translation is the
existing OriginalSourceGraphExporter and its existing strict Lean certificate.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import tempfile

from export_compiled_batch import ensure_pinned, atomic_write
from extract_compiled_catalog import blob_hash
from source_graph_kernel_certificate import read_source_graph, certificate_source
from query_stream_aot import (
    MAX_EXPORT_RSS_BYTES, SOURCE_GRAPH_EXPORTER, run_bounded,
    source_export_phase, original_graph_export_argv, ResourceLimitError
)

SOURCE = Path("lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/MomentsReadoutProgramNative.lean")
MODULE = "OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsReadoutProgramNative"
DECLARATION = "OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsReadoutProgram.program"
ID = "query_module_moments_readout"


def execute(lake: Path, upstream: Path, output: Path, timeout: int) -> dict:
    output.mkdir(parents=True, exist_ok=True)
    for stale in ("source.json", "kernel-certificate.lean", "receipt.json",
                  "report.json", "readout.stdout.log", "readout.stderr.log"):
        (output / stale).unlink(missing_ok=True)
    report = {
        "status": "REFUSED",
        "source_commit": "4eaee87548250b2682affda7d05d947c05554bae",
        "module": MODULE, "declaration": DECLARATION,
        "physical_rust_correspondence": False,
        "complete_query_executable": False
    }
    try:
        pin = ensure_pinned(upstream, lake)
        blob = blob_hash((upstream / SOURCE).read_bytes())
        record = {"id": ID, "fqn": DECLARATION, "module": MODULE, "git_blob": blob}
        report["source_blob"] = blob
        olean = lake / ".lake/build/lib/lean" / (MODULE.replace(".", "/") + ".olean")
        if not olean.is_file() or olean.is_symlink():
            raise ValueError("cached original moments readout .olean missing; refuse to rebuild")
        report["restored_olean_sha256"] = hashlib.sha256(olean.read_bytes()).hexdigest()
        with tempfile.TemporaryDirectory(prefix="query-readout-pinned-") as scratch:
            tmp = Path(scratch)
            # A fresh Lean process imports exactly the real pinned original module.
            check = tmp / "CheckReadout.lean"
            check.write_text(f"import {MODULE}\n", encoding="utf-8")
            imported = run_bounded(
                ["lake", "env", "lean", "-j", "1", "-M", "8192", str(check)],
                lake, timeout, log_base=output / "fresh-import",
                rss_limit_bytes=MAX_EXPORT_RSS_BYTES)
            if imported.returncode != 0:
                raise ValueError("fresh original module import failed: " +
                                 (imported.stdout + imported.stderr)[-1600:])
            # Compile canonical Meta exporter without importing the OAI closure.
            module_name = "OriginalSourceGraphExporter"
            exporter_olean = lake / ".lake/build/lib/lean" / (module_name + ".olean")
            exporter_olean.parent.mkdir(parents=True, exist_ok=True)
            src = tmp / (module_name + ".lean")
            src.write_bytes(SOURCE_GRAPH_EXPORTER.read_bytes())
            compiled = run_bounded(
                ["lake", "env", "lean", "-o", str(exporter_olean), str(src)],
                lake, timeout, log_base=output / "exporter-compile",
                rss_limit_bytes=MAX_EXPORT_RSS_BYTES)
            if compiled.returncode != 0:
                raise ValueError("source graph exporter compilation failed: " +
                                 (compiled.stdout + compiled.stderr)[-1600:])
            probe = tmp / "Probe.lean"
            probe.write_text(
                f"import {module_name}\nimport {MODULE}\n"
                "set_option maxHeartbeats 8000000\nset_option maxRecDepth 8192\n"
                f'#export_original_source_graph {DECLARATION} "{ID}" "{blob}"\n',
                encoding="utf-8")
            exported = run_bounded(
                original_graph_export_argv(probe), lake, timeout,
                {**os.environ, "ORIGINAL_MAX_LABELS": "1000000000",
                 "ORIGINAL_SOURCE_GRAPH_TRACE": "1"},
                log_base=output / "readout",
                rss_limit_bytes=MAX_EXPORT_RSS_BYTES)
            report["last_graph_phase"] = source_export_phase(output / "readout.stderr.log")
            if exported.returncode != 0:
                raise ValueError("original readout source graph refused: " +
                                 (exported.stdout + exported.stderr)[-2000:])
            graph = output / "source.json"
            graph.write_bytes(exported.stdout.encode("utf-8"))
            raw, parsed, _root, abi = read_source_graph(graph, record)
            r, s, labels, entry, inp, out = abi
            if (r, s, inp, out) != (8, 40, 15, 0):
                raise ValueError(f"original readout port mismatch: {(r,s,inp,out)}")
            report["graph_sha256"] = hashlib.sha256(raw).hexdigest()
            report["physical_labels"] = labels
            report["entry"] = entry
            if labels > 4096:
                report["status"] = "GRAPH_ONLY_UNCERTIFIED"
            else:
                cert, receipt = certificate_source(graph, record)
                proof = tmp / "Certificate.lean"
                proof.write_text(cert, encoding="utf-8")
                verdict = run_bounded(
                    ["lake", "env", "lean", "-j", "1", "-M", "9216", str(proof)],
                    lake, timeout, log_base=output / "kernel-certificate",
                    rss_limit_bytes=MAX_EXPORT_RSS_BYTES)
                if verdict.returncode != 0 or verdict.stdout.strip():
                    raise ValueError("kernel proof failed: " +
                                     (verdict.stdout + verdict.stderr)[-2000:])
                receipt.update({
                    "status": "LEAN_KERNEL_CERTIFIED_PHYSICAL_PROGRAM",
                    "lean_version": pin["lean"],
                    "physical_rust_correspondence": False,
                    "complete_query_executable": False,
                })
                atomic_write(output / "kernel-certificate.lean", cert)
                atomic_write(output / "receipt.json", json.dumps(receipt, sort_keys=True, indent=2)+"\n")
                report["status"] = "ORIGINAL_MODULE_GRAPH_KERNEL_CERTIFIED"
    except (OSError, ValueError, TimeoutError, ResourceLimitError, RuntimeError) as error:
        report["status"] = "REFUSED"
        report["reason"] = str(error)[-2400:]
        report["last_graph_phase"] = source_export_phase(output / "readout.stderr.log")
        for name in ("source.json", "kernel-certificate.lean", "receipt.json"):
            (output / name).unlink(missing_ok=True)
    atomic_write(output / "report.json", json.dumps(report, sort_keys=True, indent=2)+"\n")
    return report


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--upstream", required=True, type=Path)
    parser.add_argument("--lake-root", required=True, type=Path)
    parser.add_argument("--output-dir", required=True, type=Path)
    parser.add_argument("--timeout", type=int, default=180)
    args = parser.parse_args()
    if not 30 <= args.timeout <= 300:
        parser.error("one original module phase must have a 30-300s budget")
    report = execute(args.lake_root.resolve(), args.upstream.resolve(),
                     args.output_dir.resolve(), args.timeout)
    print("ORIGINAL_MOMENTS_CACHED_PROBE=" + json.dumps(report, sort_keys=True), flush=True)
    if report["status"] != "ORIGINAL_MODULE_GRAPH_KERNEL_CERTIFIED":
        raise SystemExit(2)


if __name__ == "__main__":
    main()
