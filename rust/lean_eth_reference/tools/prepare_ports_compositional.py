#!/usr/bin/env python3
"""Bounded, source-compositional evaluation of original Count.Prepare.ports.

This is NOT a general Lean parser, kernel certificate, or runnable QueryStream.
It implements exactly the closed list-expression fragment in pinned OpenAI Lean
source, checking each syntactic constructor and Fin.castAdd embedding. Unknown
forms fail closed instead of falling back to interpreted Lean or guessed ports.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import re
import subprocess
from pathlib import Path

SOURCE_COMMIT = "4eaee87548250b2682affda7d05d947c05554bae"
PREFIX = "lean/OAI/Algorithms/SubexponentialSAT/"
SOURCES = {
    "prepare": "SqrtLog/LeafProgramCountPrepare.lean",
    "state": "SqrtLog/ReconstructionProgramState.lean",
    "middle": "SqrtLog/ReconstructionProgramMiddle.lean",
    "cofactor": "SqrtLog/ReconstructionProgramCofactorOuter.lean",
    "scalar": "SqrtLog/ReconstructionProgramScalar.lean",
    "horner": "SqrtLog/ReconstructionProgramHorner.lean",
    "initial": "SubexpCRTOuterFinish.lean",
    "local_work": "SqrtLog/CRTLocalProgramExecution.lean",
    "local_ports": "SubexpCRTOuterControl.lean",
    "buffer_ports": "SubexpConvolutionStore.lean",
    "ready": "SqrtLog/ReconstructionProgramReady.lean",
    "crt_stacks": "SqrtLog/LeafProgramCount.lean",
}
PORT_DECL = (
    "OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Count.Prepare.ports"
)
MAX_FILE_BYTES = 2_000_000


def normalized(value: str) -> str:
    return " ".join(value.split())


def declaration(text: str, name: str, typ: str) -> str:
    # These original declarations are all closed, block-separated definitions.
    signature = (f"{name} {typ}" if typ.startswith("(")
                 else f"{name} : {typ}")
    marker = re.compile(rf"(?m)^def\s+{re.escape(signature)}\s*:=\s*")
    matches = list(marker.finditer(text))
    if len(matches) != 1:
        raise ValueError(f"source declaration {name}:{typ} absent or ambiguous")
    start = matches[0].end()
    end = text.find("\n\n", start)
    if end < 0:
        raise ValueError(f"source definition {name} has no block boundary")
    body = normalized(text[start:end])
    if not body or len(body) > 2048:
        raise ValueError(f"source definition {name} exceeded bounded fragment")
    return body


def expect(body: str, expected: str, label: str) -> None:
    if normalized(body) != normalized(expected):
        raise ValueError(f"unsupported or changed original {label} expression")


def literal(expr: str, bound: int) -> list[int]:
    if not re.fullmatch(r"\[\s*\d+(?:\s*,\s*\d+)*\s*\]", expr):
        raise ValueError("source list is not a closed numeric literal")
    nums = [int(n.strip()) for n in expr[1:-1].split(",")]
    if len(nums) > 768 or any(n >= bound for n in nums):
        raise ValueError("source Fin list contains out-of-range values")
    return nums


def def_list(sources: dict[str, str], file: str, name: str, bound: int) -> list[int]:
    return literal(declaration(sources[file], name, f"List (Fin {bound})"), bound)


def evaluate(s: dict[str, str]) -> tuple[list[int], dict[str, int]]:
    if set(s) != set(SOURCES):
        raise ValueError("original preparation dependency file set incomplete")
    expect(
        declaration(s["prepare"], "ports", "List (Fin 768)"),
        "(((ReconstructionProgram.NativeState.cleanPorts ++ "
        "ReconstructionProgram.InputReady.emptyPorts).map crtStacks) ++ "
        "[323,324,325,326,327,328,329]).dedup",
        "Count.Prepare.ports",
    )
    expect(
        declaration(s["state"], "workingClean", "List (Fin 320)"),
        "Middle.cleanPorts ++ CRTLocalProgram.localWork.map localPorts ++ "
        "(List.ofFn fun i => localPorts (SubexpConvolutionControl.bufferPorts i))",
        "NativeState.workingClean",
    )
    expect(
        declaration(s["state"], "cleanPorts", "List (Fin 320)"),
        "initialCleanPorts ++ workingClean ++ [5,10]",
        "NativeState.cleanPorts",
    )
    expect(
        declaration(s["middle"], "cleanPorts", "List (Fin 320)"),
        "CofactorOuter.cleanPorts ++ Scalar.cleanPorts ++ Horner.cleanPorts ++ "
        "[192,193,262,263,264]",
        "Middle.cleanPorts",
    )
    expect(
        declaration(s["crt_stacks"], "crtStacks", "(i : Fin 320) : Fin 768"),
        "i.castAdd 448",
        "crtStacks embedding",
    )
    expect(
        declaration(s["local_ports"], "localPorts", "Fin 256 ↪ Fin 320"),
        "⟨Fin.castAdd 64, Fin.castAdd_injective 256 64⟩",
        "localPorts embedding",
    )
    expect(
        declaration(s["buffer_ports"], "bufferPorts", "Fin 11 ↪ Fin 256"),
        "⟨![100, 101, 102, 103, 105, 106, 108, 109, 110, 198, 199], by decide⟩",
        "bufferPorts closed vector",
    )
    initial = declaration(s["initial"], "initialCleanPorts", "List (Fin 320)")
    parts = initial.split(" ++ ")
    if len(parts) != 2:
        raise ValueError("initialCleanPorts must have exactly two literal operands")
    initial_values = literal(parts[0], 320) + literal(parts[1], 320)
    cofactor = def_list(s, "cofactor", "cleanPorts", 320)
    scalar = def_list(s, "scalar", "cleanPorts", 320)
    horner = def_list(s, "horner", "cleanPorts", 320)
    middle = cofactor + scalar + horner + [192, 193, 262, 263, 264]
    local_work = def_list(s, "local_work", "localWork", 256)
    # Fin.castAdd preserves the numeric value; it merely widens the bound.
    mapped_local_work = list(local_work)
    buffer_vector = [100, 101, 102, 103, 105, 106, 108, 109, 110, 198, 199]
    working = middle + mapped_local_work + buffer_vector
    clean = initial_values + working + [5, 10]
    ready = def_list(s, "ready", "emptyPorts", 320)
    mapped = clean + ready
    # crtStacks is also Fin.castAdd: 320 -> 768 without offset.
    full = mapped + [323, 324, 325, 326, 327, 328, 329]
    # Pinned Mathlib's List.dedup retains the *rightmost* occurrence.
    # Thus dedup([1, 2, 1]) = [2, 1], not [1, 2].
    seen: set[int] = set()
    reversed_result: list[int] = []
    for n in reversed(full):
        if n not in seen:
            seen.add(n)
            reversed_result.append(n)
    ports = list(reversed(reversed_result))
    if (not 7 <= len(ports) <= 330 or
            len(ports) != len(set(ports)) or
            any(n < 0 or n >= 330 for n in ports) or
            not set(range(323, 330)).issubset(ports) or 699 in ports):
        raise ValueError("source-compositional ports violate proven source bounds")
    trace = {
        "initial": len(initial_values),
        "cofactor": len(cofactor),
        "scalar": len(scalar),
        "horner": len(horner),
        "middle": len(middle),
        "local_work": len(local_work),
        "buffer_vector": len(buffer_vector),
        "native_clean": len(clean),
        "input_ready": len(ready),
        "pre_dedup": len(full),
        "result": len(ports),
    }
    return ports, trace


def read_pinned(upstream: Path) -> tuple[dict[str, str], dict[str, str]]:
    head = subprocess.run(
        ["git", "-C", str(upstream), "rev-parse", "HEAD"],
        check=True, text=True, capture_output=True, timeout=10,
    ).stdout.strip()
    if head != SOURCE_COMMIT:
        raise ValueError("source tree is not the exact pinned original OAI commit")
    result = {}
    hashes = {}
    for key, relative in SOURCES.items():
        path = PREFIX + relative
        actual = (upstream / path).read_bytes()
        if len(actual) > MAX_FILE_BYTES:
            raise ValueError(f"source file {path} exceeds explicit byte bound")
        original = subprocess.run(
            ["git", "-C", str(upstream), "show", f"{SOURCE_COMMIT}:{path}"],
            check=True, capture_output=True, timeout=15,
        ).stdout
        if actual != original:
            raise ValueError(f"original source {path} differs from pinned Git blob")
        result[key] = actual.decode("utf-8")
        hashes[path] = hashlib.sha256(actual).hexdigest()
    return result, hashes


def validate_receipt(receipt: dict) -> None:
    prep = receipt.get("source_prepare_obligation", {})
    if (receipt.get("format") != "original-query-kernel-root-v11" or
            receipt.get("status") != "SOURCE_ROOT_INVENTORIED_UNVERIFIED" or
            receipt.get("source_commit") != SOURCE_COMMIT or
            receipt.get("rust_executable") is not False or
            receipt.get("receipt_is_kernel_certificate") is not False or
            receipt.get("source_command_ir_resolved") is not False or
            prep.get("bank_port_declaration") != PORT_DECL or
            prep.get("bank_port_values_resolved") is not False):
        raise ValueError("pinned kernel receipt does not bind unresolved source ports")


def generate(upstream: Path, receipt: dict) -> dict:
    validate_receipt(receipt)
    sources, hashes = read_pinned(upstream)
    ports, trace = evaluate(sources)
    return {
        "format": "original-query-prepare-ports-compositional-v1",
        "status": "PINNED_SOURCE_EXPRESSION_EVALUATED_UNCERTIFIED",
        "source_commit": SOURCE_COMMIT,
        "source_git_blob": receipt["source_git_blob"],
        "original_olean_sha256": receipt["original_olean_sha256"],
        "declaration": PORT_DECL,
        "source_file_sha256": hashes,
        "source_constructor_counts": trace,
        "ports": ports,
        "port_count": len(ports),
        "method": "bounded-pinned-source-composition",
        "lean_kernel_certificate": False,
        "rust_executable": False,
        "independent_lean_runtime_parity": False,
    }


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--upstream", type=Path, required=True)
    ap.add_argument("--source-receipt", type=Path, required=True)
    ap.add_argument("--output", type=Path, required=True)
    args = ap.parse_args()
    result = generate(args.upstream.resolve(),
                      json.loads(args.source_receipt.read_text()))
    args.output.write_text(json.dumps(result, sort_keys=True, indent=2) + "\n")
    print(f"PINNED_PREPARE_PORTS_COMPOSED count={result['port_count']} "
          "lean_certificate=false rust_executable=false")


if __name__ == "__main__":
    main()
