"""Measured exact rational tensor rank against certified spectral group graphs.

Run: PYTHONPATH=src:. python -m benchmarks.eth.tensor_rank_probe

All spectral replacements and measurement witnesses are constructed, not
selected by hand. The numerical r,Q,R are *finite research parameters*;
none of these CNFs meets the manuscript's literal n-derived admission.
The observed rank of a full clause product is NOT bounded by the
per-clause 2**w+1-state automaton bound.
"""
from __future__ import annotations

import json
import time
import tracemalloc
from fractions import Fraction
from typing import Literal

from non_exponential_sudoku.eth import (
    BalanceLimits, CNFFormula, ConstructionLimits,
    construct_bounded_designs, taylor_coefficients_separated,
)
from non_exponential_sudoku.eth.design import certify_measurements
from non_exponential_sudoku.eth.factor_width import audit_factor_width
from non_exponential_sudoku.eth.tensor_train import (
    TensorLimits, contract_certified_order_zero,
)
from benchmarks.eth.spectral_factor_width_probe import ring_formula


def _case(
    name: str, n: int, width: Literal[2, 3], r: int, Q: int, R: int,
) -> dict[str, object]:
    formula = ring_formula(n, width=width)
    construction = construct_bounded_designs(
        formula, r=r, Q=Q, R=R, schedule='conditional',
        measurement_basis='projector',
        limits=ConstructionLimits(
            max_variables=32, max_clauses=64,
            max_occurrences=64, max_measurement_rows=128,
        ),
        balance_limits=BalanceLimits(
            max_domain_size=32, max_indicator_work=2_000_000,
        ),
    )
    centers: list[dict[str, object]] = []
    for center, design in construction.centers:
        cert = certify_measurements(
            formula, construction.replacements, design, at=center)
        graph = audit_factor_width(cert)
        tracemalloc.start()
        start = time.perf_counter()
        tensor = contract_certified_order_zero(
            formula, design, construction.replacements, at=center,
            limits=TensorLimits(max_rational_operations=4_000_000),
        )
        runtime = time.perf_counter() - start
        _, peak = tracemalloc.get_traced_memory()
        tracemalloc.stop()
        tracemalloc.start()
        reference_start = time.perf_counter()
        independent = taylor_coefficients_separated(
            formula, design, construction.replacements, at=center,
            order=0, summation='eliminate',
        )
        reference_seconds = time.perf_counter() - reference_start
        _, reference_peak = tracemalloc.get_traced_memory()
        tracemalloc.stop()
        if tensor.value != independent.coefficients[0]:
            raise ArithmeticError('spectral tensor differs from independent exact Taylor oracle')
        stats = tensor.stats
        centers.append({
            'center': center,
            'value': str(tensor.value),
            'complete_group_graph': graph.complete_graph,
            'graph_edges': len(graph.interaction_edges),
            'induced_scope_groups': graph.max_scope_groups,
            'potential_dense_domain_bits': graph.max_domain_bits,
            'theoretical_single_clause_bond_bound': stats.theoretical_clause_bond_bound,
            'final_bonds': stats.final_bonds,
            'maximum_final_bond': max(stats.final_bonds, default=1),
            'maximum_intermediate_bond': max(
                (max(bonds, default=1) for bonds in stats.clause_bond_history),
                default=1,
            ),
            'peak_precompression_bond': stats.peak_bond_before_compression,
            'peak_postcompression_bond': stats.peak_bond_after_compression,
            'peak_core_entries': stats.peak_core_entries,
            'rational_operations': stats.rational_operations,
            'max_coefficient_bits': stats.maximum_coefficient_bits,
            'measured_seconds': runtime,
            'peak_traced_bytes': peak,
            'separated_reference_seconds': reference_seconds,
            'separated_reference_peak_traced_bytes': reference_peak,
            'bond_history': stats.clause_bond_history,
            'independent_separated_agreement': True,
        })
    return {
        'name': name, 'nvars': n, 'r': r, 'Q': Q, 'R': R,
        'clauses': len(formula.clauses),
        'center_measurements': centers,
        'literal_paper_parameters_admitted': False,
    }


def probe() -> dict[str, object]:
    return {
        'status': 'finite-spectral-exact-tensor-rank-not-ETH-worst-case-bound',
        'cases': [
            _case('ring6-K2', 6, 2, 2, 2, 2),
            _case('ring6-K3', 6, 2, 3, 2, 2),
            _case('ring8-K4', 8, 2, 4, 2, 2),
            _case('ring9-K3', 9, 3, 3, 3, 2),
        ],
    }


def main() -> None:
    print(json.dumps(probe(), sort_keys=True, indent=2))


if __name__ == '__main__':
    main()
