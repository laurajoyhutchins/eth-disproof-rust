#!/usr/bin/env python3
"""Original-Lean-core finite-table experiment, not a substitute compiler.

The original Lean #eval produces every physical instruction, with source-pinned
module and ABI. The *existing canonical* physical-program Lean serializer then
builds a candidate, and a fresh Lean kernel check must prove equality against
the independently imported original declaration at every address. This is a
bounded experimental receipt; Rust implementation refinement is separate.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import re
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
sys.path.insert(0, str(ROOT / "eth" / "tools"))

from query_stream_aot import MAX_EXPORT_RSS_BYTES, run_bounded
from source_graph_kernel_certificate import certificate_source, read_source_graph

SOURCE_SHA = "4eaee87548250b2682affda7d05d947c05554bae"
SOURCE_BLOB = "3e1664be261748c6e12a2d1cafb033dc26131bf9"
MODULE = "OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsReadoutProgramAccumulate"
DECL = "OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsReadoutProgram.accumulateProgram"
LEAN_SOURCE = HERE / "query_accumulate_core_index.lean"
MAX_LABELS = 4096

RECORD = {
    "id": "query_module_moments_accumulate",
    "module": MODULE, "fqn": DECL, "git_blob": SOURCE_BLOB,
}
CODE_KEY = re.compile(r"ORIGINAL_ACCUMULATE_CODE_AT\[([0-9]+)\]")
HEADER = {
    "ORIGINAL_ACCUMULATE_LABELS": "labels",
    "ORIGINAL_ACCUMULATE_INPUT": "input",
    "ORIGINAL_ACCUMULATE_OUTPUT": "output",
    "ORIGINAL_ACCUMULATE_ENTRY": "entry",
    "ORIGINAL_ACCUMULATE_EXIT": "exit",
}


def parse_observation(stdout: str) -> tuple[dict[str, int], list[str]]:
    """Require an exact complete source table, with no duplicates or omissions."""
    observed: dict[str, int] = {}
    rows: dict[int, str] = {}
    lines = stdout.splitlines()
    if not lines or len(lines) > MAX_LABELS + len(HEADER):
        raise ValueError("missing or oversized original Lean output")
    for line in lines:
        if not line.isascii() or len(line) > 140 or "=" not in line:
            raise ValueError("noncanonical Lean instruction line")
        key, value = line.split("=", 1)
        if key in HEADER:
            name = HEADER[key]
            if name in observed or not value.isdecimal():
                raise ValueError("duplicate or nondecimal source field: " + key)
            observed[name] = int(value)
        else:
            m = CODE_KEY.fullmatch(key)
            if m is None:
                raise ValueError("unexpected original Lean output: " + key)
            idx = int(m[1])
            if idx in rows or not value or len(value) > 80:
                raise ValueError("duplicate or invalid original code at: " + str(idx))
            rows[idx] = value
    if set(observed) != set(HEADER.values()):
        raise ValueError("missing original source ABI fields")
    count = observed["labels"]
    if not (0 < count <= MAX_LABELS and observed["input"] == 15
            and observed["output"] == 17
            and 0 <= observed["entry"] < count
            and 0 <= observed["exit"] < count):
        raise ValueError("source label count or ABI refused")
    if set(rows) != set(range(count)):
        raise ValueError("incomplete or out-of-range source instruction table")
    if rows[observed["exit"]] != "halt":
        raise ValueError("original source exit instruction is not halt")
    return observed, [rows[i] for i in range(count)]


def atomic_json(path: Path, payload: dict) -> None:
    tmp = path.with_suffix(path.suffix + ".tmp")
    tmp.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")
    tmp.replace(path)


def accept(lake: Path, output: Path, timeout: int) -> dict:
    output.mkdir(parents=True, exist_ok=True)
    for name in ("source.json", "kernel-certificate.lean", "receipt.json", "report.json"):
        (output / name).unlink(missing_ok=True)
    result = {
        "status": "REFUSED", "source_commit": SOURCE_SHA,
        "source_blob": SOURCE_BLOB, "declaration": DECL,
        "full_table_observed": False, "native_rust_correspondence": False,
        "counting_correctness": False, "uniform_cost_bound": False,
    }
    try:
        olean = lake / ".lake" / "build" / "lib" / "lean" / (
            MODULE.replace(".", "/") + ".olean"
        )
        if not olean.is_file() or olean.is_symlink():
            raise ValueError("cached original accumulate .olean missing; no build permitted")
        result["original_olean_sha256"] = hashlib.sha256(olean.read_bytes()).hexdigest()
        result["source_probe_sha256"] = hashlib.sha256(LEAN_SOURCE.read_bytes()).hexdigest()
        checked = run_bounded(
            ["lake", "env", "lean", "-j", "1", "-M", "9216", str(LEAN_SOURCE)],
            lake, timeout, log_base=output / "core-index",
            rss_limit_bytes=MAX_EXPORT_RSS_BYTES,
        )
        if checked.returncode:
            raise ValueError("original Lean core full-table observation failed: " +
                             str(checked.returncode) + "; " +
                             checked.stdout[-1200:] + checked.stderr[-1500:])
        if checked.stderr.strip():
            raise ValueError("original Lean observation unexpected stderr: " +
                             checked.stderr[-1500:])
        fields, rows = parse_observation(checked.stdout)
        graph = {
            "kind": "original-linked-source-v1",
            "source_commit": SOURCE_SHA, "source_blob": SOURCE_BLOB,
            "declaration": DECL, "id": RECORD["id"],
            "abi": {
                "r": 8, "s": 27, "labels": fields["labels"],
                "input": fields["input"], "output": fields["output"],
            },
            "program": {
                "r": 8, "s": 27, "labels": fields["labels"],
                "entry": fields["entry"],
                "input": fields["input"], "output": fields["output"],
                "code": rows,
            },
        }
        graph_path = output / "source.json"
        graph_path.write_text(
            json.dumps(graph, sort_keys=True, separators=(",", ":"), ensure_ascii=True)
            + "\n"
        )
        # Canonical source-graph decoder checks opcode/operand types and ABI.
        _raw, _parsed, _program, abi = read_source_graph(graph_path, RECORD)
        if abi != (8, 27, fields["labels"], fields["entry"], 15, 17):
            raise ValueError("source table disagrees with canonical graph decoder")
        result.update({
            "full_table_observed": True,
            "physical_labels": fields["labels"],
            "original_entry": fields["entry"],
            "original_exit": fields["exit"],
            "graph_sha256": hashlib.sha256(graph_path.read_bytes()).hexdigest(),
            "status": "ORIGINAL_LEAN_CORE_TABLE_OBSERVED_UNCERTIFIED",
        })
        atomic_json(output / "report.json", result)

        # This serializer is the *existing* canonical one, not a second
        # handwritten instruction semantics. Lean reimports the original module
        # and proves candidate/source code equality at EVERY address.
        certificate, cert = certificate_source(graph_path, RECORD)
        # The existing generic serializer uses `fin_cases` for every label.
        # On this 309-site original OAI module that expansion exhausted the
        # 12 GiB process limit. Retain the exact SAME equality theorem, but
        # prove its finite universal proposition by kernel reduction of
        # `decide`, rather than creating 309 elaborator tactic branches.
        # This is not an axiom, admission bypass, or replacement semantics.
        old = "  fin_cases pc <;> rfl"
        if certificate.count(old) != 1:
            raise ValueError("canonical source theorem layout changed")
        assertion = (
            f"  have h : ∀ q : Fin {fields['labels']}, candidate.code q = "
            f"{DECL}.code q := of_decide_true rfl\n"
            "  exact h pc"
        )
        certificate = certificate.replace(old, assertion)
        cert["certificate_sha256"] = hashlib.sha256(certificate.encode()).hexdigest()
        cert_path = output / "kernel-certificate.lean"
        cert_path.write_text(certificate)
        result["certificate_sha256"] = cert["certificate_sha256"]
        checked = run_bounded(
            ["lake", "env", "lean", "-j", "1", "-M", "9216", str(cert_path)],
            lake, timeout, log_base=output / "kernel-proof",
            rss_limit_bytes=MAX_EXPORT_RSS_BYTES,
        )
        if checked.returncode or checked.stdout.strip() or checked.stderr.strip():
            raise ValueError("original-source whole-table Lean certificate refused: " +
                             str(checked.returncode) + "; " +
                             checked.stdout[-1800:] + checked.stderr[-1800:])
        result["status"] = "ORIGINAL_ACCUMULATOR_FULL_TABLE_LEAN_KERNEL_CERTIFIED"
        result["kernel_certificate_status"] = "LEAN_KERNEL_CERTIFIED_PHYSICAL_PROGRAM"
        final_receipt = {**cert, **result}
        atomic_json(output / "receipt.json", final_receipt)
    except (ValueError, RuntimeError, TimeoutError, OSError, KeyError) as error:
        result["status"] = "REFUSED"
        result["reason"] = str(error)[-4000:]
        (output / "receipt.json").unlink(missing_ok=True)
    atomic_json(output / "report.json", result)
    return result


def main() -> None:
    p = argparse.ArgumentParser()
    p.add_argument("--lake-root", required=True, type=Path)
    p.add_argument("--output-dir", required=True, type=Path)
    p.add_argument("--timeout", type=int, default=300)
    args = p.parse_args()
    if not 30 <= args.timeout <= 360:
        p.error("bounded timeout must be 30..360 seconds")
    result = accept(args.lake_root.resolve(), args.output_dir.resolve(), args.timeout)
    print("ORIGINAL_ACCUMULATOR_CORE_TABLE=" +
          json.dumps(result, sort_keys=True), flush=True)
    if result["status"] != "ORIGINAL_ACCUMULATOR_FULL_TABLE_LEAN_KERNEL_CERTIFIED":
        raise SystemExit(2)


if __name__ == "__main__":
    main()
