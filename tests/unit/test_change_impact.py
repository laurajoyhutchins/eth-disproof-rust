"""Fail-closed change selection: unknown inputs always run the full checkpoint."""
from __future__ import annotations

from pathlib import Path
import subprocess

import pytest

from scripts.change_impact import changed_paths, classify, plan

pytestmark = pytest.mark.checkpoint


def _files(root: Path) -> None:
    paths = {
        "benchmarks/eth/support_join_probe.py": "def support(): pass\n",
        "tests/eth/test_support_join_probe.py":
            "from benchmarks.eth.support_join_probe import support\n",
        "docs/probe.md": "# Result\n",
        "src/sudoku/core.py": "def solve(): pass\n",
        "tests/unit/test_core.py": "from sudoku.core import solve\n",
        "scripts/change_impact.py": "# self-owned selection policy\n",
    }
    for name, content in paths.items():
        file = root / name
        file.parent.mkdir(parents=True, exist_ok=True)
        file.write_text(content)


def test_only_nonexecutable_documentation_requires_no_pytest(tmp_path: Path) -> None:
    _files(tmp_path)
    result = classify(tmp_path, ("docs/probe.md",))
    assert result.mode == "none"
    assert result.tests == ()


def test_isolated_research_file_selects_all_lexical_test_consumers(tmp_path: Path) -> None:
    _files(tmp_path)
    other = tmp_path / "tests/eth/test_other.py"
    other.write_text("from benchmarks.eth.support_join_probe import support\n")
    result = classify(tmp_path, ("benchmarks/eth/support_join_probe.py", "docs/probe.md"))
    assert result.mode == "targeted"
    assert result.tests == ("tests/eth/test_other.py", "tests/eth/test_support_join_probe.py")


def test_unmapped_consumer_falls_back_to_complete_checkpoint(tmp_path: Path) -> None:
    _files(tmp_path)
    outside = tmp_path / "src/sudoku/uses_probe.py"
    outside.write_text("from benchmarks.eth.support_join_probe import support\n")
    result = classify(tmp_path, ("benchmarks/eth/support_join_probe.py",))
    assert result.mode == "full"
    assert "unowned" in result.reason


@pytest.mark.parametrize("changed", [
    ("src/sudoku/core.py",),
    ("tests/unit/test_core.py",),
    ("scripts/change_impact.py",),
    ("src/sudoku/core.py", "docs/probe.md"),
])
def test_nonowned_changes_run_full(tmp_path: Path, changed: tuple[str, ...]) -> None:
    _files(tmp_path)
    assert classify(tmp_path, changed).mode == "full"


def test_deleted_files_and_missing_owned_tests_run_full(tmp_path: Path) -> None:
    _files(tmp_path)
    assert classify(tmp_path, ("benchmarks/eth/support_join_probe.py",),
                    deletions=frozenset({"benchmarks/eth/support_join_probe.py"})).mode == "full"
    (tmp_path / "tests/eth/test_support_join_probe.py").unlink()
    assert classify(tmp_path, ("benchmarks/eth/support_join_probe.py",)).mode == "full"


def test_empty_diff_and_unavailable_base_fail_closed(tmp_path: Path) -> None:
    _files(tmp_path)
    assert classify(tmp_path, ()).mode == "full"
    result = plan(tmp_path, "0" * 40)
    assert result["mode"] == "full"
    assert result["reused_evidence"] is False


def test_git_diff_uses_merge_base_and_sees_deleted_files(tmp_path: Path) -> None:
    _files(tmp_path)

    def git(*args: str) -> str:
        completed = subprocess.run(["git", *args], cwd=tmp_path, text=True,
                                   check=True, capture_output=True)
        return completed.stdout.strip()

    git("init", "-q")
    git("config", "user.name", "Verifier Test")
    git("config", "user.email", "verifier@example.org")
    git("add", ".")
    git("commit", "-qm", "baseline")
    base = git("rev-parse", "HEAD")
    (tmp_path / "docs/probe.md").write_text("# Changed\n")
    (tmp_path / "src/sudoku/core.py").unlink()
    git("add", "-A")
    git("commit", "-qm", "changes")
    changed, deleted, error = changed_paths(tmp_path, base)
    assert not error
    assert changed == ("docs/probe.md", "src/sudoku/core.py")
    assert deleted == frozenset({"src/sudoku/core.py"})
    assert plan(tmp_path, base)["mode"] == "full"
