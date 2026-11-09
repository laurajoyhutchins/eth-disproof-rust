"""Parallel execution must preserve checkpoint collection and backend obligations."""
from __future__ import annotations

from pathlib import Path
import subprocess
import sys

import pytest

from scripts.verify import build_pytest_command

pytestmark = pytest.mark.checkpoint


def test_parallel_checkpoint_keeps_unmodified_test_selection() -> None:
    tests = ["tests/unit/test_change_impact.py", "tests/unit/test_evidence_provenance.py"]
    junit = Path("artifacts/pure/checkpoint.xml")
    actual = build_pytest_command("checkpoint", junit, tests, [], 4)
    assert actual == [
        sys.executable, "-m", "pytest", "-q", "-m", "checkpoint",
        "--durations=20", "--junitxml=artifacts/pure/checkpoint.xml",
        "-n", "4", "--dist=loadfile", *tests,
    ]


def test_sequential_backend_requirement_preserves_required_markers() -> None:
    cmd = build_pytest_command("checkpoint", Path("test.xml"), [],
                               ["flint", "ganak"], 1)
    assert "-n" not in cmd
    assert cmd[-4:] == ["--require-backend", "flint", "--require-backend", "ganak"]


@pytest.mark.parametrize("args", [
    ("checkpoint", "--workers", "0"),
    ("checkpoint", "--workers", "4", "--require-native"),
    ("checkpoint", "--workers", "4", "--require-backend", "flint"),
    ("integration", "--workers", "4"),
])
def test_parallel_mode_refuses_unsupported_backend_contracts(args: tuple[str, ...]) -> None:
    proc = subprocess.run(
        [sys.executable, "scripts/verify.py", *args],
        capture_output=True, text=True, check=False,
    )
    assert proc.returncode == 2
    assert "error:" in proc.stderr
