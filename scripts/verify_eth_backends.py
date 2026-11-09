#!/usr/bin/env python3
"""Require real installed backends and run their differential verification.

Defaults to both libraries. --ganak-only and --flint-only allow an available
backend to be verified independently without silently skipping its tests.
"""
from __future__ import annotations

from argparse import ArgumentParser
from importlib import import_module
from pathlib import Path
import subprocess
import sys


def main() -> int:
    parser = ArgumentParser(description=__doc__)
    selection = parser.add_mutually_exclusive_group()
    selection.add_argument('--ganak-only', action='store_true')
    selection.add_argument('--flint-only', action='store_true')
    args = parser.parse_args()
    selected = (
        [('pyganak', 'eth-ganak', 'ganak_external')] if args.ganak_only else
        [('flint', 'eth-flint', 'flint_external')] if args.flint_only else
        [('pyganak', 'eth-ganak', 'ganak_external'),
         ('flint', 'eth-flint', 'flint_external')]
    )
    for module, extra, _ in selected:
        try:
            import_module(module)
        except ImportError:
            print(f'MISSING: {module}; install .[{extra}] before verifying this backend',
                  file=sys.stderr)
            return 2
    root = Path(__file__).resolve().parents[1]
    return subprocess.call([
        sys.executable, '-m', 'pytest', '-q',
        'tests/eth/test_optional_backends.py',
        '-k', ' or '.join(expression for _, _, expression in selected), '-ra',
    ], cwd=root)


if __name__ == '__main__':
    sys.exit(main())
