#!/usr/bin/env python3
"""Observed source-machine costs, distinct from theorem TM2 bounds.

This parses fresh independent Lean/Rust traces. With --rust-metrics it also
checks the source transition totals against a separately run Rust step
profiler. It NEVER imputes unobserved Lean allocations or instruction time.
"""
from __future__ import annotations

import argparse
import csv
import importlib.util
import json
from pathlib import Path

REFERENCE = Path(__file__).with_name("compare-full-machine-trace.py")
spec = importlib.util.spec_from_file_location("full_trace_comparator", REFERENCE)
assert spec and spec.loader
comparator = importlib.util.module_from_spec(spec)
spec.loader.exec_module(comparator)

def logical_transition(a: tuple[str, ...], b: tuple[str, ...]) -> bool:
    """Any BitProgram instruction may change at most one stack at its head."""
    differing = 0
    for old, new in zip(a[3:], b[3:]):
        if old == new:
            continue
        differing += 1
        if not (new[1:] == old or old[1:] == new):
            return False
    return differing <= 1

def profile(path: Path) -> dict[str, dict[str, object]]:
    result = {}
    for case, states in comparator.parse(path).items():
        for before, after in zip(states, states[1:]):
            if not logical_transition(before, after):
                raise ValueError(f"{path}: physically impossible stack transition: {case} step {before[0]}")
        result[case] = {
            "source_transitions": len(states) - 1,
            "states_observed": len(states),
            "halted": states[-1][1] == "H",
            "peak_live_stack_bits": max(len(state[3]) + len(state[4]) for state in states),
            "final_regs": states[-1][2],
            "final_output_stack": states[-1][4],
        }
    return result

def read_native_metrics(path: Path, traces: dict[str, dict[str, object]]) -> dict[str, object]:
    rows_by_case: dict[str, dict[str, object]] = {}
    allowed = {
        "halt", "goto", "set", "copy", "not", "and", "or", "xor",
        "branch", "push", "peek", "pop",
    }
    with path.open(newline="", encoding="utf8") as handle:
        reader = csv.DictReader(handle)
        expected_columns = {
            "case", "opcode", "transitions", "elapsed_ns", "allocation_calls",
            "reallocation_calls", "requested_bytes", "peak_stack_bits",
            "peak_stack_capacity_bits", "max_integer_bits",
        }
        if set(reader.fieldnames or []) != expected_columns:
            raise ValueError("native profiler CSV has wrong field names")
        for row in reader:
            case, op = row["case"], row["opcode"]
            if case not in traces or op not in allowed:
                raise ValueError(f"unknown profiler case/opcode: {case}/{op}")
            target = rows_by_case.setdefault(case, {"transitions": 0, "elapsed_ns": 0,
                "allocation_calls": 0, "reallocation_calls": 0, "requested_bytes": 0,
                "by_opcode": {}})
            if op in target["by_opcode"]:
                raise ValueError(f"duplicate {case}/{op}")
            for field in ("transitions", "elapsed_ns", "allocation_calls", "reallocation_calls", "requested_bytes"):
                value = row[field]
                if not value.isascii() or not value.isdecimal():
                    raise ValueError(f"invalid {field} for {case}/{op}")
                target[field] += int(value)
            if int(row["transitions"]) < 1:
                raise ValueError(f"zero transitions in {case}/{op}")
            if row["max_integer_bits"] != "NA":
                raise ValueError("source bit-machine has no host integer-size measurement")
            if int(row["peak_stack_bits"]) != traces[case]["peak_live_stack_bits"]:
                raise ValueError(f"peak stack bit mismatch for {case}/{op}")
            if int(row["peak_stack_capacity_bits"]) < int(row["peak_stack_bits"]):
                raise ValueError(f"stack capacity less than live data: {case}/{op}")
            target["by_opcode"][op] = {
                field: int(row[field]) for field in (
                    "transitions", "elapsed_ns", "allocation_calls",
                    "reallocation_calls", "requested_bytes",
                )
            }
    if set(rows_by_case) != set(traces):
        raise ValueError("native profiler case coverage is incomplete")
    for case, data in rows_by_case.items():
        if data["transitions"] != traces[case]["source_transitions"]:
            raise ValueError(f"transition accounting mismatch: {case}")
    return rows_by_case

def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--rust", type=Path, required=True)
    parser.add_argument("--lean", type=Path)
    parser.add_argument("--rust-metrics", type=Path)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    rust = profile(args.rust)
    lean = profile(args.lean) if args.lean else None
    if lean is not None:
        comparator.compare(args.lean, args.rust)
        # The full-state comparator already checks all states, including halt.
        assert rust == lean
    native = read_native_metrics(args.rust_metrics, rust) if args.rust_metrics else None
    report = {
        "status": "INDEPENDENT_LEAN_RUST_MATCH" if lean is not None else "RUST_ONLY_NOT_DIFFERENTIAL",
        "measurement_scope": "BitProgram source instructions, not primitive TM2 steps",
        "theorem_tm2_resource_bound_verified": False,
        "timing_note": "instrumented Rust elapsed_ns includes observer overhead; Lean per-op timing is unobserved",
        "allocation_note": "Rust allocations are alloc/realloc requests made during step(); not net heap bytes or Lean allocations",
        "integer_note": "No host big integers exist in this Boolean source machine; max integer bits not applicable",
        "rust_source_states": rust,
        "lean_source_states": lean,
        "rust_native_op_metrics": native,
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n", encoding="utf8")
    print(f"{report['status']}: {len(rust)} cases; report={args.output}")

if __name__ == "__main__":
    main()
