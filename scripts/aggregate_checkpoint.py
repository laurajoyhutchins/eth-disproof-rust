#!/usr/bin/env python3
"""Fail-closed aggregate gate for independently executed checkpoint shards."""
from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from scripts.shard_contract import verify_partition
from xml.etree import ElementTree as ET


def summarize_junit(path: Path) -> dict[str, int] | None:
    if not path.is_file():
        return None
    try:
        root = ET.parse(path).getroot()
        suites = [root] if root.tag == "testsuite" else list(root.findall("testsuite"))
        if not suites:
            return None
        return {name: sum(int(s.attrib.get(name, 0)) for s in suites)
                for name in ("tests", "failures", "errors", "skipped")}
    except (ET.ParseError, ValueError):
        return None


def _json(path: Path) -> dict[str, Any]:
    value = json.loads(path.read_text())
    if not isinstance(value, dict):
        raise ValueError(f"non-object evidence at {path}")
    return value


def validate(root: Path, *, head: str, count: int = 2) -> dict[str, object]:
    if type(count) is not int or count < 2 or not head:
        raise ValueError("invalid shard count or expected exact head")
    reports: list[dict[str, Any]] = []
    modes: list[str] = []
    fingerprints: list[tuple[str, str]] = []
    for index in range(count):
        folder = root / f"checkpoint-shard-{index}"
        if not folder.is_dir():
            raise ValueError(f"missing checkpoint shard artifact {index}")
        for name in ("checkpoint.json", "checkpoint-not-applicable.json",
                     "checkpoint-no-assignment.json"):
            path = folder / name
            if path.exists():
                report = _json(path)
                break
        else:
            raise ValueError(f"missing checkpoint outcome for shard {index}")
        git = report.get("git")
        impact = report.get("impact_plan")
        if (not isinstance(git, dict) or git.get("revision") != head
                or not isinstance(impact, dict) or impact.get("head") != head
                or impact.get("reused_evidence") is not False
                or report.get("shard_index") != index
                or report.get("shard_count") != count
                or report.get("reused_evidence") is not False):
            raise ValueError(f"stale, partial, or misidentified shard {index}")
        source = report.get("source_sha256")
        verification = report.get("verification_sources_sha256")
        mode_value = impact.get("mode")
        if (not isinstance(source, str) or len(source) != 64
                or not isinstance(verification, str) or len(verification) != 64):
            raise ValueError("missing fingerprint")
        if not isinstance(mode_value, str):
            raise ValueError("missing impact mode")
        fingerprints.append((source, verification))
        modes.append(mode_value)
        reports.append(report)
    if len(set(fingerprints)) != 1 or len(set(modes)) != 1:
        raise ValueError("shards disagree on source or impact mode")
    if any(report["impact_plan"] != reports[0]["impact_plan"] for report in reports):
        raise ValueError("shards disagree on changed-source boundary")
    mode = modes[0]
    if mode == "none":
        if any(r.get("verification_status") != "not_applicable" or
               r.get("tests_executed") is not False for r in reports):
            raise ValueError("documentation-only shard has an incorrect outcome")
        return {"mode": mode, "tests": 0, "skipped": 0, "shards": count}
    active: tuple[int, ...]
    if mode == "targeted":
        if any(r.get("verification_status") != "no_assignment" or
               r.get("tests_executed") is not False for r in reports[1:]):
            raise ValueError("targeted tests must run only on shard zero")
        active = (0,)
    elif mode == "full":
        active = tuple(range(count))
    else:
        raise ValueError("unknown impact mode")
    manifests: list[dict[str, object]] = []
    seen_tests = seen_skips = 0
    for index in active:
        folder = root / f"checkpoint-shard-{index}"
        report = reports[index]
        if (report.get("verification_status") != "passed"
                or report.get("passed") is not True
                or report.get("inputs_stable") is not True
                or report.get("tests_executed") is not True):
            raise ValueError(f"checkpoint verification failed on shard {index}")
        junit = summarize_junit(folder / "checkpoint.xml")
        if junit is None or junit != report.get("junit_counts"):
            raise ValueError(f"missing or inconsistent JUnit results on shard {index}")
        if junit["tests"] < 1 or junit["errors"] != 0 or junit["failures"] != 0:
            raise ValueError(f"invalid verification counts on shard {index}")
        seen_tests += junit["tests"]
        seen_skips += junit["skipped"]
        if mode == "full":
            if report.get("shard_manifest_valid") is not True:
                raise ValueError("per-shard collection attestation failed")
            manifest = _json(folder / f"checkpoint-shard-{index}.json")
            manifests.append(manifest)
            selected_files = manifest.get("selected_test_files")
            if not isinstance(selected_files, list) or len(selected_files) > junit["tests"]:
                raise ValueError("JUnit misses assigned test files")
    if mode == "full":
        verify_partition(manifests)
        # Every file is owned by exactly one runner, including modules whose
        # optional imports skip during collection (which have no test node ID).

    return {"mode": mode, "tests": seen_tests, "skipped": seen_skips, "shards": count}


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, required=True)
    parser.add_argument("--head", required=True)
    parser.add_argument("--count", type=int, default=2)
    args = parser.parse_args()
    result = validate(args.root, head=args.head, count=args.count)
    print("complete checkpoint:", json.dumps(result))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
