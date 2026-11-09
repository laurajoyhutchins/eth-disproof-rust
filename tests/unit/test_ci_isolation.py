"""Workflow trigger policies for expensive formal verification."""

from pathlib import Path

import pytest

from scripts.guard_proof_ci import declared_events, violations


@pytest.mark.checkpoint
def test_current_proof_workflows_are_manual_only() -> None:
    assert violations(Path(".github/workflows")) == []


@pytest.mark.checkpoint
@pytest.mark.parametrize(
    "trigger",
    [
        "on:\n  push:\n    branches:\n      - main\n",
        "on:\n  pull_request:\n",
        "on: [workflow_dispatch, pull_request]\n",
        "on:\n  workflow_call:\n",
    ],
)
def test_reject_automatic_proof_trigger(tmp_path: Path, trigger: str) -> None:
    workflow = tmp_path / "proof.yml"
    workflow.write_text(
        "name: Pinned Lean / Mathlib proof\n"
        + trigger
        + "jobs:\n  proof:\n    runs-on: ubuntu-latest\n"
        "    steps:\n      - run: lake build\n",
        encoding="utf-8",
    )
    assert violations(tmp_path)
    assert declared_events(workflow.read_text(encoding="utf-8")) != {
        "workflow_dispatch"
    }


@pytest.mark.checkpoint
def test_manual_proof_and_automatic_python_are_allowed(tmp_path: Path) -> None:
    (tmp_path / "proof.yml").write_text(
        "name: Lean proof\non:\n  workflow_dispatch:\n"
        "jobs:\n  proof:\n    steps:\n      - run: lake build\n",
        encoding="utf-8",
    )
    (tmp_path / "checks.yml").write_text(
        "name: Checkpoint\non:\n  push:\n  pull_request:\n"
        "jobs:\n  checkpoint:\n    steps:\n      - run: python -m pytest\n",
        encoding="utf-8",
    )
    assert violations(tmp_path) == []


@pytest.mark.checkpoint
def test_unknown_proof_trigger_fails_closed(tmp_path: Path) -> None:
    (tmp_path / "proof.yml").write_text(
        "name: Lean proof\non: {workflow_dispatch: null}\n",
        encoding="utf-8",
    )
    assert violations(tmp_path)
