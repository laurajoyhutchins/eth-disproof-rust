#!/usr/bin/env python3
"""Source-bound finite lowering of original Count.Prepare stack clears.

Use the exact pinned OAI Lean definitions. This is a bounded compiler slice,
not a proof that the full QueryStream algorithm executes or that Python is
definitionally equal to Lean. A balanced adjacent Seq tree preserves command
order and avoids deep recursive traversals; regrouping is not independently
kernel certified yet. No external source or user-supplied port list is trusted.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import re
import subprocess
from pathlib import Path
from typing import Any

from prepare_ports_compositional import (
    PORT_DECL, PREFIX, SOURCE_COMMIT, generate, normalized,
)

CLEAR = "OAI.Algorithms.SubexponentialSAT.StackRoutines.clearProgram"
BANK = "OAI.Algorithms.SubexponentialSAT.BankRoutines.clearCmd"
CLEAR_SOURCE = PREFIX + "StackRoutines.lean"
BANK_SOURCE = PREFIX + "BankRoutines.lean"
SOURCE_LIMIT = 2_000_000
MAX_PORTS = 768


def original_file(root: Path, path: str) -> tuple[str, str]:
    data = (root / path).read_bytes()
    if len(data) > SOURCE_LIMIT:
        raise ValueError(f"pinned source file too large: {path}")
    ref = subprocess.run(
        ["git", "-C", str(root), "show", f"{SOURCE_COMMIT}:{path}"],
        check=True, capture_output=True, timeout=15,
    ).stdout
    if data != ref:
        raise ValueError(f"pinned original source file changed: {path}")
    return data.decode("utf-8"), hashlib.sha256(data).hexdigest()


def require_original_clear_program(text: str) -> None:
    pattern = re.compile(
        r"(?m)^abbrev clearProgram \{r s : ℕ\} "
        r"\(src : Fin s\) \(value present : Fin r\) "
        r": Program r s 3 where\s*"
        r"inputStack := src\s*outputStack := src\s*entry := 0\s*"
        r"code := !\[\.pop src value present 1, "
        r"\.branch present 0 2, \.halt\]"
    )
    if len(pattern.findall(text)) != 1:
        raise ValueError("original clearProgram table or ABI no longer matches")


def require_original_bank_recursion(text: str) -> None:
    pattern = re.compile(
        r"(?m)^def clearCmd \{r s : ℕ\} \(tmp : Fin s\) "
        r"\(value present : Fin r\) :\s*"
        r"List \(Fin s\) → Cmd r s\s*"
        r"\| \[\] => \.call \(clearProgram tmp value present\)\s*"
        r"\| dst :: ports => \.seq "
        r"\(\.call \(clearProgram dst value present\)\)\s*"
        r"\(clearCmd tmp value present ports\)"
    )
    if len(pattern.findall(text)) != 1:
        raise ValueError("original clearCmd recursion/termination/order changed")


def clear_call(src: int) -> dict[str, Any]:
    if type(src) is not int or not 0 <= src < 768:
        raise ValueError("clear call source stack outside original Fin 768")
    return {
        "kind": "call",
        "program": {
            "r": 40, "s": 768, "labels": 3, "entry": 0,
            "input": src, "output": src,
            "code": [
                f"pop:{src}:0:1:1",
                "branch:1:0:2",
                "halt",
            ],
        },
    }


def adjacent_seq(leaves: list[dict[str, Any]]) -> dict[str, Any]:
    if not leaves:
        raise ValueError("empty finite program cannot silently become skip")
    # Adjacent, order-preserving association only. Each subtree has bounded
    # logarithmic depth even for the 121-source-port fixed bank.
    level = list(leaves)
    while len(level) > 1:
        level = [
            {"kind": "seq", "first": level[i], "second": level[i+1]}
            if i + 1 < len(level) else level[i]
            for i in range(0, len(level), 2)
        ]
    return level[0]


def leaf_ports(node: dict[str, Any]) -> list[int]:
    if node.get("kind") == "seq" and set(node) == {"kind", "first", "second"}:
        return leaf_ports(node["first"]) + leaf_ports(node["second"])
    if node.get("kind") == "call" and set(node) == {"kind", "program"}:
        table = node["program"]
        if set(table) != {"r", "s", "labels", "entry", "input", "output", "code"}:
            raise ValueError("source clear table has noncanonical fields")
        src = table["input"]
        if node != clear_call(src):
            raise ValueError("source clear table or arguments mutated")
        return [src]
    raise ValueError("unsupported command in finite original bank")


def source_bound_expansion(root: Path, kernel: dict, ports_receipt: dict) -> dict:
    # Refuse a receipt that doesn't match the original source-observed program.
    expected = generate(root, kernel)
    if ports_receipt != expected:
        raise ValueError("source port receipt differs from the exact pinned composition")
    evidence = kernel["source_prepare_obligation"]
    if (kernel["format"] != "original-query-kernel-root-v11" or
            kernel["rust_executable"] is not False or
            evidence["bank_port_values_resolved"] is not False or
            evidence["program_dimensions"] != [40, 768] or
            evidence["bank_dimensions"] != [40, 768] or
            evidence["program_indices"] != [699, 0, 1] or
            evidence["bank_indices"] != [699, 0, 1] or
            evidence["bank_port_declaration"] != PORT_DECL):
        raise ValueError("original Lean preparation source contract changed")
    first, first_hash = original_file(root, CLEAR_SOURCE)
    second, second_hash = original_file(root, BANK_SOURCE)
    require_original_clear_program(first)
    require_original_bank_recursion(second)
    ports = expected["ports"]
    if len(ports) != 121 or 699 in ports or len(set(ports)) != len(ports):
        raise ValueError("original source-composed finite bank is no longer the checked bank")
    # Exactly the Lean cons case calls in order, then the Lean nil case.
    bank_call_ports = ports + [699]
    bank = adjacent_seq([clear_call(p) for p in bank_call_ports])
    prefix_call_ports = [699] + bank_call_ports
    prepare = adjacent_seq([clear_call(p) for p in prefix_call_ports])
    if leaf_ports(bank) != bank_call_ports:
        raise ValueError("source bank call order changed")
    if leaf_ports(prepare) != prefix_call_ports:
        raise ValueError("source preparation call order changed")
    if len(prefix_call_ports) * 3 != 369:
        raise ValueError("original source preparation label count changed")
    return {
        "format": "original-query-prepare-clear-expansion-v1",
        "status": "SOURCE_BOUND_FINITE_CLEAR_SLICE_UNCERTIFIED",
        "source_commit": SOURCE_COMMIT,
        "source_git_blob": kernel["source_git_blob"],
        "original_olean_sha256": kernel["original_olean_sha256"],
        "port_source_sha256": expected["source_file_sha256"],
        "clear_source_sha256": {
            CLEAR_SOURCE: first_hash, BANK_SOURCE: second_hash,
        },
        "port_count": len(ports),
        "ordered_ports": ports,
        "scratch": 699,
        "read_registers": [0, 1],
        "bank_clear_calls": len(bank_call_ports),
        "bank_labels": 3 * len(bank_call_ports),
        "prepare_clear_calls": len(prefix_call_ports),
        "prepare_labels": 3 * len(prefix_call_ports),
        "bank_ir": bank,
        "prepare_ir": prepare,
        "seq_regrouping": "adjacent_order_preserving_balanced",
        "kernel_source_graph_patched": False,
        "complete_query_executable": False,
        "lean_rust_semantic_certificate": False,
        "independent_lean_trace_parity": False,
    }


def main() -> None:
    p = argparse.ArgumentParser()
    p.add_argument("--upstream", type=Path, required=True)
    p.add_argument("--source-receipt", type=Path, required=True)
    p.add_argument("--ports-receipt", type=Path, required=True)
    p.add_argument("--output", type=Path, required=True)
    args = p.parse_args()
    result = source_bound_expansion(
        args.upstream.resolve(),
        json.loads(args.source_receipt.read_text()),
        json.loads(args.ports_receipt.read_text()),
    )
    args.output.write_text(json.dumps(result, sort_keys=True) + "\n")
    print(
        f"PINNED_PREPARE_CLEAR_IR ports={result['port_count']} "
        f"bank_calls={result['bank_clear_calls']} "
        f"prepare_labels={result['prepare_labels']} "
        "source_verified=true executable_query=false parity_certificate=false"
    )


if __name__ == "__main__":
    main()
