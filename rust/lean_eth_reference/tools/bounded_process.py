"""Bounded Linux child-process execution for expensive original Lean builds.

A timeout must stop the entire Lake/Lean process group before callers archive
partial .olean build outputs. subprocess.run(timeout=...) only kills Lake;
its descendant Lean processes may keep changing files during cache upload.
This helper captures actual diagnostics and never treats timeout as success.
"""
from __future__ import annotations

import os
from pathlib import Path
import signal
import subprocess


def run_bounded(
    argv: list[str],
    *,
    cwd: Path,
    timeout: float,
    env: dict[str, str] | None = None,
    grace_seconds: float = 3.0,
) -> subprocess.CompletedProcess[str]:
    """Run a command in its own POSIX session and reap its children on timeout.

    Preserves subprocess.run(text=True, capture_output=True)'s output contract.
    On timeout the exception still contains real stdout/stderr as bytes.
    """
    if os.name != "posix":
        raise RuntimeError("original Lean group-limited builds require POSIX")
    with subprocess.Popen(
        argv,
        cwd=cwd,
        env=env,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        start_new_session=True,
    ) as process:
        try:
            stdout, stderr = process.communicate(timeout=timeout)
        except subprocess.TimeoutExpired:
            # A completed Lake parent may still have children holding output
            # descriptors. Kill the session's entire process group, not merely
            # the parent, and wait before exposing the filesystem to caching.
            try:
                os.killpg(process.pid, signal.SIGTERM)
            except ProcessLookupError:
                pass
            try:
                stdout, stderr = process.communicate(timeout=grace_seconds)
            except subprocess.TimeoutExpired:
                try:
                    os.killpg(process.pid, signal.SIGKILL)
                except ProcessLookupError:
                    pass
                stdout, stderr = process.communicate()
            raise subprocess.TimeoutExpired(
                argv, timeout, output=stdout, stderr=stderr
            ) from None
        return subprocess.CompletedProcess(
            argv,
            process.returncode,
            stdout.decode("utf-8", errors="replace"),
            stderr.decode("utf-8", errors="replace"),
        )
