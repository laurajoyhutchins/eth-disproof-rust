#!/usr/bin/env python3
"""Fail-closed, source-pinned actual Lean native-query table capture.

No pasted table, fake stdout or Cloud/Drive-specific path is accepted as evidence.
This requires a genuinely importable Lean 4.34.1 and pinned Mathlib checkout.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]
UPSTREAM = ROOT / "upstream" / "openai-math"
LAKE = UPSTREAM / "lean"
SOURCE = "4eaee87548250b2682affda7d05d947c05554bae"
MATHLIB_SHA = "d13f23b723b8a846827a245b89c10fc7d3f11612"
BLOB = "c2fb29983bb33229d5cf60729cd3d1e37b9b00ca"
SOURCE_PATH = "lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/QueryStreamProgram.lean"
PROBE = ROOT / "instrumentation" / "probes" / "query_program_dump.lean"


def command(*args: str, cwd: Path) -> str:
    result = subprocess.run(args, cwd=cwd, text=True, capture_output=True, check=True)
    return result.stdout.strip()


def verified_identity(lake_root: Path = LAKE) -> dict[str, str]:
    lake_root = lake_root.resolve()
    # For reproducible public CI, allow a minimal Lake project that imports
    # the pinned original OAI source without fetching unrelated OAI packages.
    # Refuse substituting a different source tree at that import boundary.
    if lake_root != LAKE.resolve():
        source_link = lake_root / "OAI"
        if source_link.resolve() != (UPSTREAM / "lean" / "OAI").resolve():
            raise RuntimeError("Lean project does not import the pinned original OAI source")
    mathlib = lake_root / ".lake" / "packages" / "mathlib"
    if command("git", "rev-parse", "HEAD", cwd=UPSTREAM) != SOURCE:
        raise RuntimeError("unpinned original OpenAI math checkout")
    if command("git", "status", "--porcelain", "--untracked-files=no", cwd=UPSTREAM):
        raise RuntimeError("modified tracked OpenAI source")
    if command("git", "rev-parse", f"HEAD:{SOURCE_PATH}", cwd=UPSTREAM) != BLOB:
        raise RuntimeError("QueryStreamProgram source blob mismatch")
    if command("git", "rev-parse", "HEAD", cwd=mathlib) != MATHLIB_SHA:
        raise RuntimeError("unpinned Mathlib checkout")
    if command("git", "status", "--porcelain", "--untracked-files=no", cwd=mathlib):
        raise RuntimeError("modified tracked Mathlib source")
    version = command("lake", "env", "lean", "--version", cwd=lake_root)
    if not version.startswith("Lean (version 4.34.1"):
        raise RuntimeError(f"unexpected Lean toolchain: {version}")
    return {
        "openai_commit": SOURCE,
        "source_blob": BLOB,
        "mathlib_commit": MATHLIB_SHA,
        "lean_version": version,
        "probe_sha256": hashlib.sha256(PROBE.read_bytes()).hexdigest(),
    }


def verify_stream(path: Path, max_labels: int) -> int:
    with path.open("rb") as stream:
        pin = f"PIN|query|{SOURCE}|{BLOB}\n".encode()
        if stream.readline() != pin:
            raise RuntimeError("invalid source identity in exporter output")
        fields = stream.readline().decode("ascii").rstrip("\n").split("|")
        if len(fields) != 8 or fields[:4] != ["PROGRAM", "query", "40", "896"]:
            raise RuntimeError("invalid source machine header")
        labels = int(fields[4])
        if not 0 < labels <= max_labels or fields[6:] != ["330", "323"]:
            raise RuntimeError("source table limits or port map mismatch")
        for i in range(labels):
            if not stream.readline().startswith(f"CODE|query|{i}|".encode()):
                raise RuntimeError(f"missing or out-of-order source label {i}")
        if stream.readline() != f"END|query|{labels}\n".encode() or stream.read(1):
            raise RuntimeError("missing end marker or extra data")
    return labels


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--max-labels", type=int, default=8192)
    parser.add_argument("--lake-root", type=Path, default=LAKE,
                        help="minimal pinned Lake project importing original OAI sources")
    args = parser.parse_args()
    if args.max_labels <= 0:
        parser.error("--max-labels must be positive")
    lake_root = args.lake_root.resolve()
    identity = verified_identity(lake_root)
    target = args.output.resolve()
    target.parent.mkdir(parents=True, exist_ok=True)
    temporary: Path | None = None
    try:
        with tempfile.NamedTemporaryFile(dir=target.parent, suffix=".partial", delete=False) as output:
            temporary = Path(output.name)
            environment = os.environ.copy()
            environment["M1_MAX_LABELS"] = str(args.max_labels)
            result = subprocess.run(
                ["lake", "env", "lean", str(PROBE)],
                cwd=lake_root, stdout=output, stderr=subprocess.PIPE, text=True,
                env=environment,
            )
        if result.returncode != 0:
            raise RuntimeError(f"actual Lean exporter failed (exit {result.returncode}): {result.stderr}")
        labels = verify_stream(temporary, args.max_labels)
        identity.update({
            "labels": labels,
            "output_sha256": hashlib.sha256(temporary.read_bytes()).hexdigest(),
            "output_bytes": temporary.stat().st_size,
            "source": "actual imported Lean QueryStreamProgram.program",
            "status": "EXPORTED_NOT_DIFFERENTIALLY_VERIFIED",
        })
        os.replace(temporary, target)
        target.with_suffix(target.suffix + ".receipt.json").write_text(
            json.dumps(identity, indent=2, sort_keys=True) + "\n", encoding="utf-8"
        )
        print(json.dumps({"output": str(target), **identity}, sort_keys=True))
    finally:
        if temporary is not None and temporary.exists():
            temporary.unlink()


if __name__ == "__main__":
    main()
