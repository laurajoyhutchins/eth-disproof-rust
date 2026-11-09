"""A changed build/interface/fixture must invalidate its relevant evidence."""
from __future__ import annotations

from pathlib import Path

import pytest

from scripts.evidence import fingerprints, native_binaries

pytestmark = pytest.mark.checkpoint


def test_fingerprints_track_native_interfaces_scripts_and_fixtures(tmp_path: Path) -> None:
    root = tmp_path
    (root / "src" / "pkg").mkdir(parents=True)
    (root / "tests").mkdir()
    (root / "scripts").mkdir()
    (root / "research").mkdir()
    (root / "benchmarks").mkdir()
    (root / ".github" / "workflows").mkdir(parents=True)
    (root / "src" / "pkg" / "core.py").write_text("x = 3\n")
    (root / "native_ring.pyx").write_text("def add(a, b): return a + b\n")
    (root / "native_ring.pxd").write_text("cdef int a\n")
    (root / "native_ring.pyi").write_text("def add(a: int, b: int) -> int: ...\n")
    (root / "pyproject.toml").write_text("[build-system]\n")
    (root / "MANIFEST.in").write_text("include native_ring.pyx\n")
    (root / "tests" / "fixture.json").write_text('{"expected": 2}')
    (root / "scripts" / "measure.py").write_text("print(2)\n")
    (root / "benchmarks" / "case.py").write_text("N = 3\n")
    (root / "research" / "oracle.py").write_text("N = 4\n")
    (root / ".github" / "workflows" / "checks.yml").write_text("name: Check\n")
    original = fingerprints(root)
    for relative in (
        "native_ring.pxd", "native_ring.pyi", "native_ring.pyx",
        "src/pkg/core.py", "pyproject.toml", "MANIFEST.in",
    ):
        path = root / relative
        before = path.read_text()
        path.write_text(before + "# edited\n")
        changed = fingerprints(root)
        assert changed["source_sha256"] != original["source_sha256"], relative
        assert changed["verification_sources_sha256"] == original["verification_sources_sha256"]
        path.write_text(before)
    for relative in (
        "tests/fixture.json", "scripts/measure.py", "benchmarks/case.py",
        "research/oracle.py",
        ".github/workflows/checks.yml",
    ):
        path = root / relative
        before = path.read_text()
        path.write_text(before + "\n")
        changed = fingerprints(root)
        assert changed["source_sha256"] == original["source_sha256"]
        assert changed["verification_sources_sha256"] != original["verification_sources_sha256"]
        path.write_text(before)
    assert fingerprints(root) == original


def test_native_binary_manifest_is_explicit() -> None:
    result = native_binaries()
    assert set(result) == {"native_ring", "native_sparse", "native_recursive"}
    for item in result.values():
        assert item["importable"] is True or (item["filename"] is None
                                              and item["binary_sha256"] is None)
        if item["importable"]:
            assert len(item["binary_sha256"]) == 64


def test_verifier_rejects_missing_or_incomplete_junit(tmp_path: Path) -> None:
    from scripts.verify import summarize_junit

    path = tmp_path / "checkpoint.xml"
    assert summarize_junit(path) is None
    path.write_text("<testsuite tests='1'>")
    assert summarize_junit(path) is None
    path.write_text("<testsuite tests='1' failures='1' errors='0' skipped='0'></testsuite>")
    assert summarize_junit(path) == {"tests": 1, "failures": 1, "errors": 0, "skipped": 0}
