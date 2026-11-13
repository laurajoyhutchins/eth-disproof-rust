#!/usr/bin/env python3
"""Explicit two-route Lean-to-Rust experiment; one fail-closed output contract.

No automatic fallback. Successful emission remains unverified, non-executable.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import tempfile

from lean_codegen_contract import Refusal, require, source_identity, validate_contract
from run_lean_ir_backend import main as run_ir


def toolchain(lake_root: Path, expected: str) -> None:
    pin = (lake_root / 'lean-toolchain').read_text(encoding='utf-8').strip()
    require(pin == expected, 'Lake toolchain differs from pinned source')


def symbolic(args: argparse.Namespace, temp: Path, source: dict[str, str]) -> bytes:
    require(len(args.root) == 1, 'symbolic path currently accepts exactly one root')
    require(args.producer is not None and args.producer.is_file(),
            'symbolic path requires a Lean core-Expr producer')
    toolchain(args.lake_root, source['lean_toolchain'])
    producer = args.producer.read_text(encoding='utf-8')
    # Insert the actual source import before declarations, not a host rewrite of the algorithm.
    require(producer.startswith('import Lean\n'), 'producer must begin with import Lean')
    body = ('import Lean\nimport ' + args.module + '\n' +
            producer.removeprefix('import Lean\n') + '\n' +
            '#export_residual_graph ' + args.root[0] + '\n')
    driver = temp / 'ResidueDriver.lean'
    driver.write_text(body, encoding='utf-8')
    try:
        out = subprocess.run(['lake', 'env', 'lean', str(driver)], cwd=args.lake_root,
                             capture_output=True, timeout=args.timeout_seconds, check=False)
    except (OSError, subprocess.TimeoutExpired) as exc:
        raise Refusal(f'Lean symbolic exporter unavailable: {exc}') from exc
    require(out.returncode == 0,
            f'Lean symbolic export refused: {out.stderr.decode("utf-8", "replace")[-1600:]}')
    return out.stdout


def run(args: argparse.Namespace) -> int:
    require(args.output.resolve() != args.receipt.resolve(), 'artifact and receipt paths collide')
    require(args.timeout_seconds in range(1, 3601), 'timeout must be 1..3600')
    source = source_identity(args.source_repo, args.source_path,
                             args.source_revision, args.source_toolchain_path)
    toolchain(args.lake_root, source['lean_toolchain'])
    # Generate and inspect entirely in a temporary location. Publish only after the
    # same contract accepts the exact artifact bytes and pinned Git source.
    args.output.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(prefix='lean-two-route-', dir=args.output.parent) as tmp:
        work = Path(tmp)
        if args.backend == 'compiler-ir':
            staged = work / 'generated.rs'
            internal = work / 'ir-report.json'
            command = ['--lake-root', str(args.lake_root), '--module', args.module,
                       '--output-rs', str(staged), '--report', str(internal),
                       '--timeout-seconds', str(args.timeout_seconds)]
            for root in args.root:
                command += ['--root', root]
            require(run_ir(command) == 0, 'compiler-IR generator refused; no symbolic fallback')
            artifact, report = staged.read_bytes(), internal.read_bytes()
        else:
            artifact, report = symbolic(args, work, source), None
        receipt = validate_contract(backend=args.backend, artifact=artifact,
                                    report=report, module=args.module,
                                    roots=args.root, source=source)
        if args.backend == 'residual-expr':
            receipt['producer_sha256'] = hashlib.sha256(args.producer.read_bytes()).hexdigest()
        candidate = work / 'accepted-artifact'
        candidate.write_bytes(artifact)
        candidate_receipt = work / 'accepted-receipt'
        candidate_receipt.write_text(json.dumps(receipt, sort_keys=True, indent=2) + '\n',
                                     encoding='utf-8')
        os.replace(candidate, args.output)
        os.replace(candidate_receipt, args.receipt)
    return 0


def main(argv: list[str] | None = None) -> int:
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--backend', choices=['compiler-ir', 'residual-expr'], required=True)
    p.add_argument('--module', required=True)
    p.add_argument('--root', action='append', required=True)
    p.add_argument('--lake-root', type=Path, required=True)
    p.add_argument('--source-repo', type=Path, required=True)
    p.add_argument('--source-path', required=True)
    p.add_argument('--source-revision', required=True)
    p.add_argument('--source-toolchain-path', default='lean-toolchain')
    p.add_argument('--producer', type=Path)
    p.add_argument('--output', type=Path, required=True)
    p.add_argument('--receipt', type=Path, required=True)
    p.add_argument('--timeout-seconds', type=int, default=300)
    args = p.parse_args(argv)
    try:
        require(args.output.resolve() != args.receipt.resolve(), 'output equals receipt')
        require(bool(re.fullmatch(r'[A-Za-z_]\w*(?:\.[A-Za-z_]\w*)*', args.module)),
                'invalid module')
        require(args.root and all(bool(re.fullmatch(r'[A-Za-z_]\w*(?:\.[A-Za-z_]\w*)*', r))
                                  for r in args.root), 'invalid root')
        code = run(args)
        print('Generated and contract-checked; execution and equivalence NOT established')
        return code
    except (OSError, ValueError, subprocess.TimeoutExpired) as exc:
        args.receipt.unlink(missing_ok=True)
        print(f'two-path compilation refused: {exc}', file=sys.stderr)
        return 2


if __name__ == '__main__':
    raise SystemExit(main())
