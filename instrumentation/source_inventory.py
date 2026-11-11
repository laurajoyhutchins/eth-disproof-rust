#!/usr/bin/env python3
"""Index the exact pinned Lean source tree without loading Mathlib or running Lean.

Declaration locations are a conservative lexical index, not Lean elaboration.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
PIN = "4eaee87548250b2682affda7d05d947c05554bae"
SOURCE = ROOT / "upstream/openai-math/lean/OAI/Algorithms/SubexponentialSAT"
DECL = re.compile(
    r"^\s*(?:(?:private|protected|noncomputable|partial|unsafe|scoped|local)\s+)*"
    r"(def|abbrev|theorem|lemma|structure|inductive|class|instance|opaque|axiom|example|"
    r"mutual|section|namespace)\b(?:\s+([^\s(:{]+))?")
IMPORT = re.compile(r"^\s*import\s+(.+?)\s*$")


def digest(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def collect(source: Path = SOURCE) -> dict:
    if not source.is_dir():
        raise RuntimeError("Original Lean source missing; initialize the upstream submodule first")
    checkout = source.parents[3]  # .../lean/OAI/Algorithms/SubexponentialSAT -> openai-math
    p = subprocess.run(["git", "-C", str(checkout), "rev-parse", "HEAD"],
                       capture_output=True, text=True)
    if p.returncode or p.stdout.strip() != PIN:
        raise RuntimeError(f"Original Lean source is not pinned to {PIN}")
    dirty = subprocess.run(["git", "-C", str(checkout), "status", "--porcelain",
                            "--untracked-files=normal"], capture_output=True, text=True)
    if dirty.returncode or dirty.stdout.strip():
        raise RuntimeError("Original Lean source has modifications")
    files = []
    for path in sorted(source.rglob("*.lean")):
        raw = path.read_bytes()
        content = raw.decode("utf-8")
        imports = []
        declarations = []
        for lineno, line in enumerate(content.splitlines(), 1):
            im = IMPORT.match(line)
            if im:
                imports.extend(im.group(1).split())
            m = DECL.match(line)
            if m:
                declarations.append({"line": lineno, "kind": m.group(1),
                                     "name_token": m.group(2) or ""})
        files.append({"path": path.relative_to(checkout).as_posix(),
                      "sha256": digest(raw), "bytes": len(raw),
                      "line_count": len(content.splitlines()),
                      "imports": imports, "declarations_lexical": declarations})
    return {"schema": 1, "kind": "pinned-source-lexical-index", "source_commit": PIN,
            "limits": "Lexical index, not an elaborated symbol table or dependency proof",
            "files": files,
            "totals": {"modules": len(files),
                       "lexical_declarations": sum(len(f["declarations_lexical"]) for f in files),
                       "source_bytes": sum(f["bytes"] for f in files)}}


def main() -> int:
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--out", type=Path, default=ROOT / "lean-captures/source-inventory.json")
    args = p.parse_args()
    try:
        data = collect()
        args.out.parent.mkdir(parents=True, exist_ok=True)
        args.out.write_text(json.dumps(data, indent=2, sort_keys=True) + "\n")
        print(f"Indexed {data['totals']['modules']} Lean modules and "
              f"{data['totals']['lexical_declarations']} lexical declaration locations")
        return 0
    except (OSError, RuntimeError, UnicodeError) as exc:
        print(f"ERROR: {exc}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    sys.exit(main())
