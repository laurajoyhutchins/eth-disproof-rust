"""Exact bond-rank obstruction under a fixed group ordering.

Formula F_k = AND_i (x_i OR y_i) has count 3**k. At the cut with all
x variables left and all y variables right, its truth tensor is the
Kronecker power of [[0,1],[1,1]], an invertible rank-2 matrix. Thus the
exact tensor-train bond is 2**k. Interleaving the paired variables makes
maximum bond <=2. This is an order-sensitive tensor representation
lower bound, NOT an arbitrary-order #SAT hardness lower bound.

Run: PYTHONPATH=src:. python -m benchmarks.eth.tensor_bond_obstruction
"""
from __future__ import annotations

import json
import time
from fractions import Fraction

from non_exponential_sudoku.eth.cnf import CNFFormula
from non_exponential_sudoku.eth.design import MeasurementDesign
from non_exponential_sudoku.eth.tensor_train import (
    TensorLimits, contract_certified_order_zero,
)


def matching_case(k: int, *, interleaved: bool) -> tuple[CNFFormula, MeasurementDesign]:
    if type(k) is not int or k < 1:
        raise ValueError('k must be a positive integer')
    formula = CNFFormula(2 * k, tuple((i + 1, k + i + 1) for i in range(k)))
    order = (
        tuple(v for i in range(k) for v in (i, k + i))
        if interleaved else tuple(range(2 * k))
    )
    owners = {variable: position for position, variable in enumerate(order)}
    design = MeasurementDesign(
        groups=tuple((variable,) for variable in order),
        clause_groups=tuple(owners[i] for i in range(k)),
        matrices=tuple(((1,),) for _ in order),
        tau=Fraction(1, 2), D=1,
    )
    return formula, design


def probe(max_k: int = 4) -> dict[str, object]:
    rows: list[dict[str, object]] = []
    for k in range(1, max_k + 1):
        for interleaved in (False, True):
            formula, design = matching_case(k, interleaved=interleaved)
            start = time.perf_counter()
            result = contract_certified_order_zero(
                formula, design, at=1,
                limits=TensorLimits(max_bond=512, max_rational_operations=6_000_000),
            )
            duration = time.perf_counter() - start
            expected_rank = 2 if interleaved else 1 << k
            expected_count = 3 ** k
            if (result.value != expected_count or
                    max(result.stats.final_bonds, default=1) != expected_rank):
                raise ArithmeticError('matching exact bond-rank identity failed')
            rows.append({
                'k': k,
                'variables': 2 * k,
                'group_order': 'paired' if interleaved else 'x-first-y-last',
                'exact_cut_rank': expected_rank,
                'final_bonds': result.stats.final_bonds,
                'maximum_final_bond': max(result.stats.final_bonds, default=1),
                'clause_automaton_bond_bound': result.stats.theoretical_clause_bond_bound,
                'exact_count': str(result.value),
                'seconds': duration,
                'rational_operations': result.stats.rational_operations,
            })
    return {'status': 'exact-order-sensitive-bond-lower-bound-not-SAT-hardness',
            'cases': rows}


def main() -> None:
    print(json.dumps(probe(), indent=2, sort_keys=True))


if __name__ == '__main__':
    main()
