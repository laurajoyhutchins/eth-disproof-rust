"""Run a bounded, auditable CNF-to-count reference, never an oracle fallback.

Usage:
  python -m scripts.eth_reference
  python -m scripts.eth_reference --dimacs example.cnf --output report.json
  python -m scripts.eth_reference --dimacs example.cnf --threshold 3

Exit 0: complete exact count. Exit 2: capacity refusal with JSON evidence.
Other errors are left visible, not disguised as ordinary resource refusal.
"""
from __future__ import annotations

import argparse
from dataclasses import asdict, replace
import json
from pathlib import Path
from typing import Any

from non_exponential_sudoku.eth.cnf import CNFFormula
from non_exponential_sudoku.eth.pipeline import (
    ReferencePipelineConfig, count_cnf_reference,
)
from non_exponential_sudoku.eth.sparsification import reference_sparsification_parameters
from non_exponential_sudoku.runtime.budget import CapacityError


def _emit(report: dict[str, Any], output: Path | None) -> None:
    payload = json.dumps(report, indent=2, sort_keys=True) + '\n'
    if output is not None:
        output.parent.mkdir(parents=True, exist_ok=True)
        output.write_text(payload)
    print(payload, end='')


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--dimacs', type=Path, help='DIMACS input; default is a tiny example')
    parser.add_argument('--output', type=Path, help='JSON evidence destination')
    parser.add_argument('--threshold', type=int, default=2,
                        help='experimental disjoint-sparsification threshold (NOT theorem M)')
    parser.add_argument('--max-leaves', type=int, default=64)
    parser.add_argument('--backend', choices=('python', 'flint'), default='python')
    args = parser.parse_args()
    formula = (CNFFormula.from_dimacs(args.dimacs.read_text())
               if args.dimacs is not None else CNFFormula(2, ((1, 2),)))
    config = replace(
        ReferencePipelineConfig(),
        sparsification=reference_sparsification_parameters(3, args.threshold),
        max_leaves=args.max_leaves,
        backend=args.backend,
    )
    try:
        result = count_cnf_reference(formula, config=config)
    except CapacityError as exc:
        _emit({
            'status': 'capacity_refusal',
            'error': str(exc),
            'source_variables': formula.nvars,
            'source_clauses': len(formula.clauses),
            'reference_threshold': args.threshold,
            'count': None,
        }, args.output)
        return 2
    _emit({
        'status': 'completed',
        'reference_threshold': args.threshold,
        **asdict(result),
    }, args.output)
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
