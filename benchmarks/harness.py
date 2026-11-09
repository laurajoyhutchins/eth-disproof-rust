"""Shared, workload-neutral benchmark evidence and process utilities.

The canonical contraction, exact-cover, structural-growth and recursive studies
remain separate because they measure different workloads and have distinct
failure semantics. This module owns only their reusable evidence mechanics.
"""
from __future__ import annotations

from datetime import datetime, timezone
import hashlib
import importlib.metadata
import json
import math
import os
from pathlib import Path
import subprocess
import sys
import xml.etree.ElementTree as ET
from collections.abc import Iterable, Sequence

ROOT = Path(__file__).resolve().parents[1]
THREAD_VARIABLES = (
    'OMP_NUM_THREADS', 'OPENBLAS_NUM_THREADS', 'MKL_NUM_THREADS',
    'NUMEXPR_NUM_THREADS', 'VECLIB_MAXIMUM_THREADS', 'BLIS_NUM_THREADS',
    'PYTHONHASHSEED', 'CFLAGS', 'CPPFLAGS', 'LDFLAGS', 'CC', 'CXX',
)


def iso_now() -> str:
    return datetime.now(timezone.utc).isoformat()


def command_output(args: Sequence[str]) -> str | None:
    try:
        result = subprocess.run(args, cwd=ROOT, capture_output=True, text=True, timeout=6)
        return result.stdout.strip() if result.returncode == 0 else None
    except (OSError, subprocess.TimeoutExpired):
        return None


def version_of(module: str) -> str | None:
    try:
        return importlib.metadata.version(module)
    except importlib.metadata.PackageNotFoundError:
        return None


def source_hash_files(paths: Iterable[Path], root: Path = ROOT) -> str:
    """Hash the *ordered* path set; callers choose the study's source scope."""
    digest = hashlib.sha256()
    for path in paths:
        digest.update(path.relative_to(root).as_posix().encode() + b'\0')
        digest.update(path.read_bytes())
    return digest.hexdigest()


def git_metadata() -> dict[str, str | bool | None]:
    rev = command_output(['git', 'rev-parse', 'HEAD'])
    if rev is None:
        return {'revision': None, 'dirty': None, 'status': 'not_a_git_checkout'}
    result = subprocess.run(['git', 'status', '--porcelain', '--untracked-files=normal'],
                            cwd=ROOT, capture_output=True, text=True, timeout=10)
    return {'revision': rev, 'dirty': bool(result.stdout.strip()) if result.returncode == 0 else None,
            'status': 'available' if result.returncode == 0 else 'unavailable'}


def cpu_model() -> str | None:
    try:
        for line in Path('/proc/cpuinfo').read_text().splitlines():
            if line.startswith('model name'):
                return line.split(':', 1)[1].strip()
    except OSError:
        pass
    return None


def junit_counts(path: Path) -> dict[str, int] | None:
    if not path.is_file():
        return None
    try:
        root = ET.parse(path).getroot()
        suites = [root] if root.tag == 'testsuite' else root.findall('testsuite')
        if not suites:
            return None
        return {name: sum(int(s.attrib.get(name, 0)) for s in suites)
                for name in ('tests', 'failures', 'errors', 'skipped')}
    except (ET.ParseError, ValueError):
        return None


def run_process(command: Sequence[str], env: dict[str, str], timeout: float,
                log_path: Path | None = None) -> dict[str, object]:
    try:
        result = subprocess.run(command, cwd=ROOT, env=env, capture_output=True,
                                text=True, timeout=timeout)
        output = (result.stdout or '') + '\n' + (result.stderr or '')
        if log_path is not None:
            log_path.write_text(output)
        return {'exit_code': result.returncode, 'stdout': result.stdout, 'timed_out': False,
                'error': output[-3000:] if result.returncode else None}
    except subprocess.TimeoutExpired:
        if log_path is not None:
            log_path.write_text(f'Exceeded timeout ({timeout} seconds)\n')
        return {'exit_code': 124, 'timed_out': True, 'error': f'Timeout after {timeout} s'}
    except OSError as err:
        return {'exit_code': 1, 'timed_out': False, 'error': f'{type(err).__name__}: {err}'}


def validate_native_timing(path: Path, expected: Iterable[tuple[str, ...]],
                           key_fields: tuple[str, ...], minimum_rounds: int) -> tuple[bool, str | None]:
    """Require exactly the requested case/variant rows and positive raw samples.

    Native pytest-benchmark JSON is validated, never rewritten or synthesized.
    """
    if not path.is_file():
        return False, 'Missing native pytest-benchmark JSON'
    try:
        rows = json.loads(path.read_text())['benchmarks']
        observed: set[tuple[str, ...]] = set()
        for row in rows:
            extra = row['extra_info']
            key = tuple(extra[field] for field in key_fields)
            if not all(isinstance(value, str) and value for value in key) or key in observed:
                return False, f'Missing or duplicated native case identifier: {key}'
            samples = row['stats']['data']
            if len(samples) < minimum_rounds or not all(
                isinstance(value, (int, float)) and not isinstance(value, bool)
                and math.isfinite(value) and value > 0 for value in samples
            ):
                return False, f'Invalid or incomplete native timing samples: {key}'
            observed.add(key)
        if observed != set(expected):
            return False, f'Case mismatch in native results: {sorted(observed)}'
        return True, None
    except (OSError, KeyError, TypeError, ValueError, AttributeError, IndexError) as exc:
        return False, f'Invalid native JSON: {type(exc).__name__}: {exc}'
