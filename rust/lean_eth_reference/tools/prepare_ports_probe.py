"""Strictly validate the independent original Lean Count.Prepare.ports evaluation.

This is a runtime observation of the pinned original, not a kernel certificate.
Do not silently treat these values as compiled Rust instructions.
"""
import argparse
import json
from pathlib import Path

PREFIX = "ORIGINAL_PREPARE_PORTS_JSON="
PORT_NAME = "OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Count.Prepare.ports"


def validate(original_stdout: str, source_receipt: dict) -> dict:
    lines = [line[len(PREFIX):] for line in original_stdout.splitlines()
             if line.startswith(PREFIX)]
    if len(lines) != 1:
        raise ValueError("exactly one original compiled Lean port-list output required")
    values = json.loads(lines[0])
    if (not isinstance(values, list) or not 7 <= len(values) <= 768 or
            # The pinned original proves all Count.Prepare.ports are < 330.
            # Fin.castAdd 448 widens the type but preserves each port value.
            any(type(n) is not int or not 0 <= n < 330 for n in values) or
            len(set(values)) != len(values) or
            not set(range(323, 330)).issubset(values) or 699 in values):
        raise ValueError("original prepared finite port list violates source constraints")
    prep = source_receipt.get("source_prepare_obligation")
    if (source_receipt.get("format") != "original-query-kernel-root-v11" or
            source_receipt.get("status") != "SOURCE_ROOT_INVENTORIED_UNVERIFIED" or
            not isinstance(prep, dict) or
            prep.get("bank_port_declaration") != PORT_NAME or
            prep.get("bank_port_values_resolved") is not False or
            source_receipt.get("rust_executable") is not False or
            source_receipt.get("receipt_is_kernel_certificate") is not False):
        raise ValueError("original source receipt does not bind this observed port list")
    source_hash = source_receipt.get("original_olean_sha256")
    git_blob = source_receipt.get("source_git_blob")
    if (type(source_hash) is not str or len(source_hash) != 64 or
            type(git_blob) is not str or len(git_blob) != 40):
        raise ValueError("original Lean provenance digest missing")
    return {
        "format": "original-query-prepare-ports-evaluation-v1",
        "status": "ORIGINAL_LEAN_PORT_LIST_OBSERVED_UNCERTIFIED",
        "source_commit": source_receipt["source_commit"],
        "source_git_blob": git_blob,
        "original_olean_sha256": source_hash,
        "declaration": PORT_NAME,
        "ports": values,
        "port_count": len(values),
        "port_list_is_Lean_runtime_observation": True,
        "rust_executable": False,
        "receipt_is_kernel_certificate": False,
    }


def main() -> None:
    p = argparse.ArgumentParser()
    p.add_argument("--lean-stdout", type=Path, required=True)
    p.add_argument("--source-receipt", type=Path, required=True)
    p.add_argument("--output", type=Path, required=True)
    args = p.parse_args()
    result = validate(args.lean_stdout.read_text(),
                      json.loads(args.source_receipt.read_text()))
    args.output.write_text(json.dumps(result, sort_keys=True, indent=2) + "\n")
    print(f"ORIGINAL_PREPARE_PORT_LIST_OBSERVED count={result['port_count']} "
          "execution=false certificate=false")


if __name__ == "__main__":
    main()
