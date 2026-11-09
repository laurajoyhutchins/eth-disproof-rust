"""Verify every selected checkpoint identity is executed exactly once."""
from __future__ import annotations

import json
from pathlib import Path

import pytest

from scripts.aggregate_checkpoint import validate
from scripts.shard_contract import owned_nodeids, shard_for, verify_partition

pytestmark = pytest.mark.checkpoint


def _manifests(nodeids: list[str]) -> list[dict[str, object]]:
    full = sorted(nodeids)
    return [{
        "schema_version": 1, "shard_index": index, "shard_count": 2,
        "all_nodeids": full, "selected_nodeids": owned_nodeids(full, index, 2),
    } for index in range(2)]


def test_partition_is_complete_and_order_independent() -> None:
    full = [f"tests/unit/test_math.py::test_case[{i}]" for i in range(129)]
    manifests = _manifests(full)
    assert verify_partition(manifests) == sorted(full)
    assert verify_partition(list(reversed(manifests))) == sorted(full)
    assert all(shard_for(name, 2) in (0, 1) for name in full)


def test_partition_refuses_missing_duplicate_and_moved_tests() -> None:
    manifests = _manifests([f"tests/unit/test_x.py::test_x[{i}]" for i in range(40)])
    with pytest.raises(ValueError):
        verify_partition(manifests[:1])
    manifests[1]["selected_nodeids"] = manifests[0]["selected_nodeids"]
    with pytest.raises(ValueError):
        verify_partition(manifests)


def _evidence(root: Path, head: str, manifest: dict[str, object]) -> None:
    index = manifest["shard_index"]
    assert isinstance(index, int)
    folder = root / f"checkpoint-shard-{index}"
    folder.mkdir(parents=True)
    selected = manifest["selected_nodeids"]
    assert isinstance(selected, list)
    (folder / f"checkpoint-shard-{index}.json").write_text(json.dumps(manifest))
    (folder / "checkpoint.xml").write_text(
        f"<testsuite tests='{len(selected)}' failures='0' errors='0' skipped='0'></testsuite>"
    )
    report = {
        "shard_index": index, "shard_count": 2,
        "shard_manifest_valid": True,
        "git": {"revision": head, "dirty": False},
        "impact_plan": {"mode": "full", "head": head, "base": head,
                        "reused_evidence": False, "changed_paths": ["scripts/verify.py"],
                        "tests": [], "reason": "full", "schema_version": 1},
        "source_sha256": "a" * 64,
        "verification_sources_sha256": "b" * 64,
        "passed": True, "verification_status": "passed",
        "tests_executed": True, "inputs_stable": True, "reused_evidence": False,
        "junit_counts": {"tests": len(selected), "failures": 0, "errors": 0, "skipped": 0},
    }
    (folder / "checkpoint.json").write_text(json.dumps(report))


def test_aggregate_accepts_exact_complete_partition(tmp_path: Path) -> None:
    head = "f" * 40
    full = [f"tests/unit/test_x.py::test_x[{i}]" for i in range(40)]
    for manifest in _manifests(full):
        _evidence(tmp_path, head, manifest)
    assert validate(tmp_path, head=head)["tests"] == len(full)


def test_aggregate_rejects_missing_junit_case_and_stale_head(tmp_path: Path) -> None:
    head = "f" * 40
    for manifest in _manifests([f"tests/unit/test_x.py::test_x[{i}]" for i in range(40)]):
        _evidence(tmp_path, head, manifest)
    with pytest.raises(ValueError, match="stale"):
        validate(tmp_path, head="0" * 40)
    xml = tmp_path / "checkpoint-shard-0" / "checkpoint.xml"
    xml.write_text("<testsuite tests='1' failures='0' errors='0' skipped='0'></testsuite>")
    with pytest.raises(ValueError, match="JUnit"):
        validate(tmp_path, head=head)
