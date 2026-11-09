#!/usr/bin/env python3
"""Run a test tier and save JUnit plus a fail-closed, source-pinned report.

The checkpoint tier must work without optional native extensions. The native
requirement is explicit; no absent, truncated, or failed verification can be
reported as successful.
"""
from __future__ import annotations

import argparse
import importlib.util
import json
import os
from pathlib import Path
import platform
import subprocess
import sys
import time
import xml.etree.ElementTree as ET

ROOT = Path(__file__).resolve().parents[1]
sys.path[:0] = [str(ROOT), str(ROOT / "src")]

from scripts.evidence import (  # noqa: E402
    fingerprints, git_provenance, native_binaries, validate_attestation,
)

DEFAULT_TIMEOUTS = {"checkpoint": 30, "integration": 180, "extended": 600}
JUNIT_FIELDS = ("tests", "failures", "errors", "skipped")


def summarize_junit(path: Path) -> dict[str, int] | None:
    if not path.is_file():
        return None
    try:
        root = ET.parse(path).getroot()
        suites = [root] if root.tag == "testsuite" else list(root.findall("testsuite"))
        if not suites:
            return None
        return {key: sum(int(s.attrib.get(key, 0)) for s in suites)
                for key in JUNIT_FIELDS}
    except (ET.ParseError, ValueError):
        return None


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("tier", choices=sorted(DEFAULT_TIMEOUTS))
    parser.add_argument("--timeout", type=float)
    parser.add_argument("--require-native", action="store_true",
                        help="Fail unless all three optional native binaries load")
    parser.add_argument("--require-backend", action="append", default=[],
                        choices=("native", "flint", "ganak"),
                        help="Enforce marked optional tests, never accept their skips")
    parser.add_argument("--require-native-attestation", action="store_true",
                        help="Require matching native build-input and binary hashes")
    parser.add_argument("--output", type=Path, default=ROOT / "artifacts")
    args = parser.parse_args()
    if args.timeout is not None and args.timeout <= 0:
        parser.error("--timeout must be positive")
    if args.tier != "checkpoint" and args.require_backend:
        parser.error("--require-backend is only supported for checkpoint tests")

    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=True)
    junit = output / f"{args.tier}.xml"
    junit.unlink(missing_ok=True)
    required = sorted(set(args.require_backend))
    if args.require_native and args.tier == "checkpoint" and "native" not in required:
        required.append("native")
    command = [sys.executable, "-m", "pytest", "-q", "-m", args.tier,
               "--durations=20", "--junitxml=" + str(junit)]
    if args.tier == "checkpoint":
        # Report the active test before a hard timeout truncates JUnit output.
        command.append("-vv")
    for backend in required:
        command.extend(("--require-backend", backend))
    env = os.environ.copy()
    env["PYTHONPATH"] = os.pathsep.join(filter(None, (
        str(ROOT / "src"), str(ROOT), env.get("PYTHONPATH", ""))))
    before = fingerprints()
    before_git = git_provenance()
    before_native = native_binaries()
    start = time.perf_counter()
    timeout = args.timeout or DEFAULT_TIMEOUTS[args.tier]
    timed_out = False
    infrastructure_error: str | None = None
    try:
        completed = subprocess.run(command, cwd=ROOT, env=env,
                                   timeout=timeout, check=False)
        code = completed.returncode
    except subprocess.TimeoutExpired:
        code = 124
        timed_out = True
    except OSError as exc:
        code = 127
        infrastructure_error = f"{type(exc).__name__}: {exc}"

    counts = summarize_junit(junit)
    after = fingerprints()
    after_git = git_provenance()
    after_native = native_binaries()
    stable = (before == after and before_git == after_git and
              before_native == after_native)
    native_available = all(item["importable"] for item in before_native.values())
    dependencies = {"flint": "flint", "ganak": "pyganak"}
    backend_available = {name: (native_available if name == "native" else
                       importlib.util.find_spec(dependencies[name]) is not None)
                         for name in required}
    attestation = validate_attestation(ROOT, before, before_native)
    passed = (code == 0 and not timed_out and infrastructure_error is None and
              counts is not None and counts["tests"] > 0 and
              counts["failures"] == counts["errors"] == 0 and stable and
              (native_available or not args.require_native) and
              all(backend_available.values()) and
              (not args.require_native_attestation or attestation["valid"]))
    record = {
        "tier": args.tier,
        "passed": passed,
        "exit_code": code,
        "timeout": timed_out,
        "infrastructure_error": infrastructure_error,
        "duration_seconds": round(time.perf_counter() - start, 3),
        "timeout_seconds": timeout,
        "junit": junit.name if junit.exists() else None,
        "junit_counts": counts,
        "python": platform.python_version(),
        "native_extension_importable": native_available,
        "native_extensions": before_native,
        "require_native": args.require_native,
        "required_backends": required,
        "backend_available": backend_available,
        "native_build_attestation": attestation,
        "require_native_attestation": args.require_native_attestation,
        "git": before_git,
        **before,
        "inputs_stable": stable,
        "inputs_after": {"git": after_git, **after, "native_extensions": after_native}
                        if not stable else None,
        "command": command,
    }
    (output / f"{args.tier}.json").write_text(json.dumps(record, indent=2) + "\n")
    print(f"tier={args.tier} success={passed} inputs_stable={stable}"
          f" xml={record['junit']} summary={counts}", flush=True)
    return 0 if passed else (code if code else 1)


if __name__ == "__main__":
    raise SystemExit(main())
