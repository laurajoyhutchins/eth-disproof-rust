#!/usr/bin/env python3
"""Conservative change-impact plan for the fast contract checkpoint.

Only specifically isolated research modules and documentation qualify for
reduced execution. Everything else fails closed to the full checkpoint.
This is test SELECTION, not proof reuse or a general dependency oracle.
"""
from __future__ import annotations

import argparse
from dataclasses import dataclass
import json
from pathlib import Path
import subprocess
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
RESEARCH_MODULES = {
    "benchmarks/eth/support_join_probe.py": "benchmarks.eth.support_join_probe",
    "benchmarks/eth/or_clique_cardinality.py": "benchmarks.eth.or_clique_cardinality",
}
PLAN_VERSION = 1


@dataclass(frozen=True)
class Selection:
    mode: str
    reason: str
    tests: tuple[str, ...] = ()


def _documentation(path: str) -> bool:
    return path in ("README.md", "CONTRIBUTING.md") or (
        path.startswith("docs/") and path.endswith(".md")
    )


def _test_path(path: str) -> bool:
    parts = Path(path).parts
    return len(parts) >= 3 and parts[0] == "tests" and parts[-1].startswith("test_") and parts[-1].endswith(".py")


def _consumers(root: Path, module: str) -> tuple[str, ...] | None:
    """Find lexical consumers; refuse partial verification for non-test consumers.

    The intentionally overinclusive match catches normal static imports and
    literal dynamic-import names. Unrecognized consumers trigger full checks.
    """
    leaf = module.rsplit(".", 1)[-1]
    consumers: list[str] = []
    for folder in ("src", "tests", "scripts", "benchmarks", "reference", "research"):
        base = root / folder
        if not base.is_dir():
            continue
        for file in base.rglob("*.py"):
            rel = file.relative_to(root).as_posix()
            if rel in RESEARCH_MODULES or rel == "scripts/change_impact.py":
                continue
            try:
                content = file.read_text(encoding="utf-8")
            except (UnicodeError, OSError):
                return None
            if leaf not in content:
                continue
            if not _test_path(rel):
                return None
            consumers.append(rel)
    return tuple(sorted(set(consumers)))


def classify(root: Path, changes: tuple[str, ...], *, deletions: frozenset[str] = frozenset()) -> Selection:
    """Classify changed paths without guessing unowned dependencies."""
    if not changes:
        return Selection("full", "No trustworthy changed-path boundary")
    if any(p in deletions or not (root / p).is_file() for p in changes):
        return Selection("full", "Deleted or unavailable changed file")
    runnable = [p for p in changes if not _documentation(p)]
    if not runnable:
        return Selection("none", "Documentation-only; no executable contracts changed")
    if any(p not in RESEARCH_MODULES and not _test_path(p) for p in runnable):
        return Selection("full", "Unowned source, fixture, configuration, or workflow change")
    chosen: set[str] = set()
    allowed_test_names: set[str] = set()
    for path, module in RESEARCH_MODULES.items():
        if path in runnable or any(p in runnable for p in (
            "tests/eth/test_support_join_probe.py", "tests/eth/test_or_clique_cardinality.py"
        )):
            readers = _consumers(root, module)
            if readers is None:
                return Selection("full", "Research code has an unowned consumer")
            allowed_test_names.update(readers)
            if path in runnable:
                if not readers:
                    return Selection("full", "No independently owned test for changed research code")
                chosen.update(readers)
    for p in runnable:
        if p in RESEARCH_MODULES:
            continue
        if p not in allowed_test_names:
            return Selection("full", "Test has no certified isolated research ownership")
        chosen.add(p)
    if not chosen or any(not (root / p).is_file() for p in chosen):
        return Selection("full", "Missing or unavailable owned test")
    return Selection("targeted", "Explicit isolated research-contract consumers", tuple(sorted(chosen)))


def _git(root: Path, *arguments: str) -> subprocess.CompletedProcess[bytes]:
    return subprocess.run(["git", *arguments], cwd=root, capture_output=True, check=False, timeout=12)


def changed_paths(root: Path, base: str | None) -> tuple[tuple[str, ...], frozenset[str], str]:
    if not base or not all(c in "0123456789abcdefABCDEF" for c in base) or len(base) < 7:
        return (), frozenset(), "No trustworthy base commit"
    try:
        merge_base = _git(root, "merge-base", base, "HEAD")
        if merge_base.returncode != 0:
            return (), frozenset(), "Base commit is unavailable or unrelated"
        diff = _git(root, "diff", "--no-renames", "--name-status", "-z", merge_base.stdout.decode().strip(), "HEAD")
        if diff.returncode != 0:
            return (), frozenset(), "Cannot calculate complete Git diff"
        parts = diff.stdout.decode("utf-8").split("\0")
        entries = [p for p in parts if p]
        if len(entries) % 2 != 0:
            return (), frozenset(), "Malformed Git name-status output"
        changed: set[str] = set()
        deleted: set[str] = set()
        for status, path in zip(entries[::2], entries[1::2]):
            if not status or status[0] not in "ACDMRTUXB":
                return (), frozenset(), "Unrecognized Git diff status"
            changed.add(path)
            if status[0] == "D":
                deleted.add(path)
        return tuple(sorted(changed)), frozenset(deleted), ""
    except (OSError, UnicodeError, subprocess.TimeoutExpired):
        return (), frozenset(), "Cannot read complete Git diff"


def plan(root: Path, base: str | None) -> dict[str, Any]:
    changes, deletions, error = changed_paths(root, base)
    selection = Selection("full", error) if error else classify(root, changes, deletions=deletions)
    head = _git(root, "rev-parse", "HEAD")
    revision = head.stdout.decode().strip() if head.returncode == 0 else None
    return {
        "schema_version": PLAN_VERSION, "base": base, "head": revision,
        "changed_paths": list(changes), "mode": selection.mode,
        "reason": selection.reason, "tests": list(selection.tests),
        "reused_evidence": False,
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--base", help="Commit to compare to HEAD; unknown base falls back to full")
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    result = plan(ROOT, args.base)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2) + "\n")
    print(f"change-impact: {result['mode']} ({result['reason']}); {len(result['tests'])} owned test files")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
