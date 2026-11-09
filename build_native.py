"""Build optional Cython extensions and record source/binary identity.

The default is an incremental build (setuptools/Cython decide which extensions
need rebuilding). Use --force for a complete release rebuild. The manifest
records observed build inputs and loaded binary hashes, not an independent
proof of compiler provenance. It is checked by verify.py.
"""
from __future__ import annotations

import argparse
import json
import os
from pathlib import Path
import platform
import subprocess
import sys
import sysconfig
import time

ROOT = Path(__file__).resolve().parent
sys.path[:0] = [str(ROOT), str(ROOT / "src")]


def main() -> int:
    from scripts.evidence import fingerprints, git_provenance, native_binaries

    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--force", action="store_true", help="Recompile all three extensions")
    args = parser.parse_args()
    before = fingerprints()
    env = os.environ.copy()
    env["SUDOKU_BUILD_NATIVE"] = "1"
    command = [sys.executable, "setup.py", "build_ext", "--inplace"]
    if args.force:
        command.append("--force")
    try:
        from importlib.metadata import version
        cython_version = version("Cython")
    except ImportError:
        cython_version = None
    started = time.perf_counter()
    status = subprocess.call(command, cwd=ROOT, env=env)
    after = fingerprints()
    binaries = native_binaries()
    stable = before == after
    success = status == 0 and stable and all(v["importable"] for v in binaries.values())
    record = {
        "schema_version": 1,
        "build_succeeded": success,
        "exit_code": status,
        "source_inputs_stable": stable,
        "source_sha256": before["source_sha256"],
        "verification_sources_sha256": before["verification_sources_sha256"],
        "git": git_provenance(),
        "binaries": binaries,
        "build": {
            "command": command,
            "forced": args.force,
            "python": platform.python_version(),
            "cython_version": cython_version,
            "compiler": sysconfig.get_config_var("CC"),
            "cflags": os.environ.get("CFLAGS"),
            "ldflags": os.environ.get("LDFLAGS"),
            "platform": platform.platform(),
            "duration_seconds": round(time.perf_counter() - started, 3),
        },
    }
    path = ROOT / "artifacts" / "native-build.json"
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(record, indent=2, sort_keys=True) + "\n")
    if not success:
        print("native build not attested; inspect " + str(path), file=sys.stderr)
    return 0 if success else status or 1


if __name__ == "__main__":
    raise SystemExit(main())
