#!/usr/bin/env python3
"""Read a recorded Lean trace offline, without invoking Lean or Rust."""
from __future__ import annotations

import argparse
import gzip
from pathlib import Path
import sys

from capture import STAGES, stage_paths


def main() -> int:
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--out", type=Path, default=Path(__file__).resolve().parents[1] / "lean-captures")
    p.add_argument("--stage", required=True, choices=sorted(STAGES))
    p.add_argument("--case", help="one case name (e.g. mixed or initialize/mixed)")
    p.add_argument("--step", type=int, help="single physical machine step")
    p.add_argument("--code", action="store_true", help="include instruction table")
    args = p.parse_args()
    if args.step is not None and args.step < 0:
        p.error("--step must be nonnegative")
    meta, stream, _ = stage_paths(args.out, args.stage)
    if not meta.is_file() or not stream.is_file():
        p.error("capture not present; run capture.py capture for this stage")
    import json
    import hashlib
    record = json.loads(meta.read_text())
    compressed = stream.read_bytes()
    content = gzip.decompress(compressed)
    if hashlib.sha256(content).hexdigest() != record["stdout_sha256"] or \
       hashlib.sha256(compressed).hexdigest() != record["stdout_gzip_sha256"]:
        p.error("capture integrity failure")
    for line in content.decode().splitlines():
        parts = line.split("|")
        if STAGES[args.stage].kind == "legacy":
            if args.case is not None and f"{parts[0]}/{parts[1]}" != args.case:
                continue
            if args.step is not None:
                p.error("legacy aggregate trace has no individual machine steps")
        else:
            if args.case is not None and parts[1] != args.case:
                continue
            if parts[0] == "CODE" and not args.code:
                continue
            if args.step is not None and (parts[0] != "STEP" or int(parts[2]) != args.step):
                continue
        print(line)
    return 0


if __name__ == "__main__":
    sys.exit(main())
