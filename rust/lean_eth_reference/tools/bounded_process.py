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
            # A failed or timed-out build is never accepted. Hard-stop the
            # whole process group, not just Lake's PID. A graceful-only signal
            # can leave detached-output children writing .olean files while
            # actions/cache reads the directory.
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
