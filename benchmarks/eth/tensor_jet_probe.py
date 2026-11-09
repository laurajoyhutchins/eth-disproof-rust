"""Exact higher-order tensor Taylor jet benchmark and independent oracle.

Reproduce: PYTHONPATH=src:. python -m benchmarks.eth.tensor_jet_probe

Each measured arm includes center-specific certification. The exact
tensor evaluator directly shifts the replacement polynomials; the
independent separated evaluator uses the manuscript's Boolean
differences. They agree coefficientwise but follow different paths.
The local-mask domain and tensor bonds can remain exponential. The
small manual and spectral cases do not establish the literal paper
parameter schedule or an asymptotic runtime guarantee.
"""
from __future__ import annotations

import json
import time
import tracemalloc
from fractions import Fraction
from typing import Any

from non_exponential_sudoku.eth import (
    BalanceLimits, CNFFormula, MeasurementDesign, Polynomial,
    ReplacementForm, ReplacementSystem, construct_bounded_designs,
    deformation_polynomial, taylor_coefficients_separated,
)
from non_exponential_sudoku.eth.tensor_jet import contract_certified_taylor


def _manual() -> tuple[CNFFormula, MeasurementDesign, ReplacementSystem]:
    formula = CNFFormula(4, ((1, -3), (2, 4), (-1, 2, -4)))
    groups = ((0, 1), (2, 3))
    design = MeasurementDesign(
        groups=groups,
        clause_groups=(0, 0, 0),
        matrices=(((1, 0), (0, 1)), ((1, 0), (0, 1))),
        tau=Fraction(1, 2), D=1,
    )
    identity = ReplacementSystem.identity(formula)
    replacement = ReplacementSystem(tuple(
        tuple(ReplacementForm(tuple(
            poly + Polynomial((0, Fraction((e + 1) * (i % 3 - 1), 7),
                               Fraction((e + 2) * (i + 1), 19)))
            for i, poly in enumerate(form.coefficients)))
            for form in forms)
        for e, forms in enumerate(identity.clauses)
    ))
    return formula, design, replacement


def _measure(
    name: str, formula: CNFFormula, design: MeasurementDesign,
    replacement: ReplacementSystem, center: Fraction, order: int,
    *, symbolic_oracle: bool,
) -> dict[str, Any]:
    tracemalloc.start()
    start = time.perf_counter()
    tensor = contract_certified_taylor(
        formula, design, replacement, at=center, order=order)
    tensor_seconds = time.perf_counter() - start
    _, tensor_memory = tracemalloc.get_traced_memory()
    tracemalloc.stop()

    tracemalloc.start()
    start = time.perf_counter()
    reference = taylor_coefficients_separated(
        formula, design, replacement, at=center, order=order,
        summation='eliminate')
    reference_seconds = time.perf_counter() - start
    _, reference_memory = tracemalloc.get_traced_memory()
    tracemalloc.stop()
    if tensor.coefficients != reference.coefficients:
        raise ArithmeticError('tensor jet differs from independent exact separated Taylor')
    if symbolic_oracle:
        polynomial = deformation_polynomial(formula, replacement)
        oracle = polynomial.taylor(center, order)
        if tensor.coefficients != oracle.coefficients + (
            Fraction(0),
        ) * (order + 1 - len(oracle.coefficients)):
            raise ArithmeticError('tensor jet differs from Boolean cube polynomial oracle')
    return {
        'name': name,
        'nvars': formula.nvars,
        'groups': len(design.groups),
        'clauses': len(formula.clauses),
        'order': order,
        'center': str(center),
        'coefficients': [str(c) for c in tensor.coefficients],
        'tensor_seconds': tensor_seconds,
        'separated_seconds': reference_seconds,
        'tensor_peak_traced_bytes': tensor_memory,
        'separated_peak_traced_bytes': reference_memory,
        'tensor_rational_operations': tensor.stats.rational_operations,
        'tensor_max_coefficient_bits': tensor.stats.maximum_coefficient_bits,
        'tensor_peak_bond_before_compression': tensor.stats.peak_bond_before_compression,
        'tensor_peak_bond_after_compression': tensor.stats.peak_bond_after_compression,
        'tensor_final_bonds': tensor.stats.final_bonds,
        'tensor_clause_bond_history': tensor.stats.clause_bond_history,
        'reference_pairs': reference.stats.taylor_pairs,
        'exact_reference_agreement': True,
        'symbolic_cube_agreement': symbolic_oracle,
    }


def probe() -> dict[str, Any]:
    formula, design, replacement = _manual()
    rows = [
        _measure('manual-degree-two', formula, design, replacement,
                 Fraction(2, 3), order, symbolic_oracle=True)
        for order in (0, 1, 2, 3)
    ]
    from benchmarks.eth.spectral_factor_width_probe import ring_formula

    spectral_formula = ring_formula(6, width=2)
    constructed = construct_bounded_designs(
        spectral_formula, r=3, Q=2, R=2, schedule='conditional',
        measurement_basis='projector',
        balance_limits=BalanceLimits(
            max_domain_size=32, max_indicator_work=2_000_000,
        ),
    )
    center, spectral_design = constructed.centers[0]
    rows.extend(
        _measure('constructed-spectral', spectral_formula, spectral_design,
                 constructed.replacements, center, order,
                 symbolic_oracle=False)
        for order in (0, 1, 2)
    )
    return {
        'status': 'measured-exact-Taylor-jet-not-general-ETH-bound',
        'cases': rows,
        'paper_parameter_schedule_admitted': False,
    }


def main() -> None:
    print(json.dumps(probe(), sort_keys=True, indent=2))


if __name__ == '__main__':
    main()
