"""Cloud Build entry point for source-pinned remote verification.

The 30-second feedback budget belongs to agent-local checks, not hosted CI.
Cloud Build executes the complete two-shard test union before accepting a PR.
"""
from __future__ import annotations

import argparse
from pathlib import Path
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]


def require_checkout(expected: str) -> None:
    """Refuse builds without an exact trigger revision or with modified tracked files."""
    if re.fullmatch(r"[0-9a-f]{40}", expected) is None:
        raise ValueError("Cloud Build trigger did not supply a full commit SHA")
    actual = subprocess.run(
        ["git", "rev-parse", "HEAD"], cwd=ROOT, text=True,
        capture_output=True, check=True,
    ).stdout.strip()
    if actual != expected:
        raise ValueError(f"checkout {actual} differs from trigger revision {expected}")
    subprocess.run(["git", "diff", "--quiet", "HEAD", "--"], cwd=ROOT, check=True)


def _run(*args: str) -> None:
    subprocess.run([sys.executable, *args], cwd=ROOT, check=True)


def checkpoint(head: str) -> None:
    """Run full sharded checkpoint; never use inferred PR impact boundaries."""
    impact = ROOT / "artifacts" / "pure" / "impact.json"
    impact.parent.mkdir(parents=True, exist_ok=True)
    _run("scripts/change_impact.py", "--output", str(impact))
    root = ROOT / "artifacts" / "shards"
    # Separate processes, but sequential execution: shards share /workspace
    # in Cloud Build and must not race while creating temporary files.
    failures: list[int] = []
    for index in range(2):
        folder = root / f"checkpoint-shard-{index}"
        folder.mkdir(parents=True, exist_ok=True)
        result = subprocess.run(
            [sys.executable, "scripts/verify.py", "checkpoint",
             "--shard-count", "2", "--shard-index", str(index),
             "--impact-plan", str(impact), "--output", str(folder)],
            cwd=ROOT, check=False,
        )
        if result.returncode != 0:
            failures.append(index)
    if failures:
        raise RuntimeError(f"checkpoint shards failed: {failures}")
    _run("-m", "scripts.aggregate_checkpoint", "--root", str(root),
         "--head", head, "--count", "2")


def native() -> None:
    """Require the same native, independent-oracle and extended tiers as native.yml."""
    _run("build_native.py")
    _run("scripts/verify.py", "checkpoint", "--timeout", "120",
         "--require-native", "--require-native-attestation",
         "--require-backend", "flint", "--require-backend", "ganak",
         "--output", "artifacts/native")
    _run("scripts/verify.py", "integration", "--timeout", "600",
         "--require-native", "--output", "artifacts/native")
    _run("scripts/verify.py", "extended", "--timeout", "600",
         "--require-native", "--require-native-attestation",
         "--output", "artifacts/native")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("tier", choices=("validate", "checkpoint", "native"))
    parser.add_argument("--expected-sha", required=True)
    args = parser.parse_args()
    require_checkout(args.expected_sha)
    if args.tier == "checkpoint":
        checkpoint(args.expected_sha)
    elif args.tier == "native":
        native()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
