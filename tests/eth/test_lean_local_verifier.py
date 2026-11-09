"""Fast tests for fail-closed, runner-free local Lean verification."""
from pathlib import Path
import os
import subprocess

import pytest

ROOT = Path(__file__).resolve().parents[2]
SCRIPT = ROOT / "scripts" / "verify_lean_local.sh"


@pytest.mark.checkpoint
def test_local_lean_verifier_help() -> None:
    out = subprocess.run(
        ["bash", str(SCRIPT), "--help"], cwd=ROOT,
        text=True, capture_output=True, check=True, timeout=5,
    )
    assert "Lean 4.34.1" in out.stdout
    assert "LEAN_CACHE_ROOT" in out.stdout
    assert "No GitHub Actions runner" in out.stdout


@pytest.mark.integration
def test_local_lean_verifier_refuses_missing_compiler(tmp_path: Path) -> None:
    env = os.environ.copy()
    env["LEAN_BIN"] = str(tmp_path / "missing-lean")
    env["LEAN_UPSTREAM"] = str(tmp_path / "not-an-upstream")
    out = subprocess.run(
        ["bash", str(SCRIPT)], cwd=ROOT, env=env,
        text=True, capture_output=True, timeout=5,
    )
    assert out.returncode == 2
    assert "Missing" in out.stderr
