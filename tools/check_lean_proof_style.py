#!/usr/bin/env python3
"""Small, dependency-free style check for repository-owned Lean proof modules.

This deliberately does not parse Lean or make claims about proof soundness.
"""
from __future__ import annotations

import argparse
from pathlib import Path
import re


ROOT = Path(__file__).resolve().parents[1]
PROOF_DIRECTORIES = (
    Path("eth/proofs"),
    Path("instrumentation/lean-env/ACC"),
)
DECLARATION = re.compile(
    r"^(?:@\\[[^\\]\\n]*\\]\\s*)*"
    r"(?:(?:private|protected|noncomputable|partial|unsafe)\s+)*"
    r"(?:def|theorem|lemma|structure|inductive|class|abbrev|instance|opaque)\b"
)


def discover_proof_modules(root: Path = ROOT) -> list[Path]:
    """Only repository-authored proofs; exclude pinned or generated upstream Lean."""
    return sorted(
        path
        for relative in PROOF_DIRECTORIES
        for path in (root / relative).glob("*.lean")
    )


def preceding_doc(lines: list[str], index: int) -> bool:
    """Require a declaration comment, not a module or ordinary block comment."""
    pos = index - 1
    while pos >= 0 and not lines[pos].strip():
        pos -= 1
    if pos < 0 or not lines[pos].rstrip().endswith("-/"):
        return False
    while pos >= 0:
        opening = lines[pos].lstrip()
        if opening.startswith("/--"):
            return True
        if opening.startswith("/-"):
            return False
        pos -= 1
    return False


def undocumented_declarations(source: str) -> list[str]:
    lines = source.splitlines()
    return [
        f"{i + 1}: top-level declaration needs /-- documentation"
        for i, line in enumerate(lines)
        if DECLARATION.match(line) and not preceding_doc(lines, i)
    ]


def check_text(source: str, *, strict_docs: bool = False) -> list[str]:
    errors: list[str] = []
    lines = source.splitlines()
    if not lines or not lines[0].startswith("import "):
        errors.append("1: begin with explicit imports")
    if not any(line.startswith("/-!") for line in lines[:30]):
        errors.append("1: add a module documentation comment (/-! ... -/)")
    if not source.endswith("\n") or source.endswith("\n\n"):
        errors.append("EOF: end with exactly one newline")
    for i, line in enumerate(lines):
        loc = f"{i + 1}:"
        if "\t" in line:
            errors.append(f"{loc} tabs are not allowed")
        if line != line.rstrip(" \t"):
            errors.append(f"{loc} trailing whitespace")
        if len(line) > 100:
            errors.append(f"{loc} line exceeds 100 characters ({len(line)})")
        if i > 1 and not line and not lines[i - 1] and not lines[i - 2]:
            errors.append(f"{loc} more than one blank line")
    if strict_docs:
        errors.extend(undocumented_declarations(source))
    return errors


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("paths", nargs="*", type=Path)
    parser.add_argument(
        "--strict-docs", action="store_true",
        help="also fail on undocumented top-level declarations",
    )
    args = parser.parse_args()
    paths = args.paths or discover_proof_modules()
    if not paths:
        parser.error("no Lean proof modules found")
    failed = False
    for path in paths:
        source = path.read_text(encoding="utf-8")
        errors = check_text(source, strict_docs=args.strict_docs)
        if not args.strict_docs:
            undocumented = undocumented_declarations(source)
            if undocumented:
                print(f"{path}: advisory: {len(undocumented)} undocumented declaration(s)")
        for error in errors:
            print(f"{path}: {error}")
        failed |= bool(errors)
    if not failed:
        print(f"Lean proof style: {len(paths)} module(s) clean")
    return int(failed)


if __name__ == "__main__":
    raise SystemExit(main())
