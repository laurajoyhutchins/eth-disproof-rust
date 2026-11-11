"""One actual source path across transfer, witnesses, Taylor and Hermite.

A small *non-paper-admitted* instance is used to test source correspondence.
The virtual asymptotic Step-5 family remains separate and unmaterialized.
"""
from __future__ import annotations

from fractions import Fraction

import pytest

from non_exponential_sudoku.eth import (
    CNFFormula, certify_measurements, construct_bounded_designs,
    count_bruteforce,
)
from non_exponential_sudoku.eth.interpolation import (
    HermiteDatum, interpolate_origin_hermite,
)
from non_exponential_sudoku.eth.taylor import (
    TaylorLimits, taylor_coefficients_separated,
)
from reference.eth_hermite_origin_budget import hermite_origin_budget
from reference.eth_measurement_witness_budget import (
    traced_row_combination, witness_bit_budget,
)
from reference.eth_separated_center_budget import (
    certified_separated_center_envelope,
)
from reference.eth_spectral_transfer_height import (
    ceil_log2, spectral_transfer_height_budget,
)


@pytest.mark.integration
def test_source_composition_exact_end_to_end_vs_independent_boolean_oracle() -> None:
    formula = CNFFormula(3, ((1, -2), (-1, 3)))
    construction = construct_bounded_designs(
        formula, r=2, Q=2, R=2, schedule="conditional",
        representation="implicit", measurement_basis="selectors",
    )
    assert construction.paper_admission is not None
    assert not construction.paper_admission.admitted
    occurrences = sum(map(len, formula.clauses))
    transfer_budget = spectral_transfer_height_budget(
        r=2, Q=2, R=2,
        incidence_log2_upper=ceil_log2(occurrences + 1),
    )
    degree = sum(
        sum(max(coefficient.degree for coefficient in form.coefficients)
            for form in row)
        for row in construction.replacements.clauses
    )
    order = degree // len(construction.centers)
    assert len(construction.centers) * (order + 1) > degree

    data: list[HermiteDatum] = []
    for center, design in construction.centers:
        certificate = certify_measurements(
            formula, construction.replacements, design, at=center,
        )
        for e, (forms, witnesses) in enumerate(zip(
            construction.replacements.clauses, certificate.occurrences,
        )):
            for form, occurrence in zip(forms, witnesses):
                for coefficient in form.coefficients:
                    for scalar in coefficient.coefficients:
                        assert max(
                            abs(scalar.numerator).bit_length(),
                            scalar.denominator.bit_length(),
                        ) <= transfer_budget.transferred_polynomial_fraction_bits_upper
                for g, (group, rows) in enumerate(zip(
                    design.groups, design.matrices,
                )):
                    if g == design.clause_groups[e]:
                        continue
                    target = tuple(
                        form.coefficients[v].evaluate(center) for v in group
                    )
                    witness_budget = witness_bit_budget(rows, target)
                    trace = traced_row_combination(rows, target)
                    assert trace.coefficients == occurrence.lambda_by_group[g]
                    assert trace.measured_fraction_bits <= (
                        witness_budget.intermediate_fraction_bits_upper
                    )
        center_budget = certified_separated_center_envelope(
            formula, construction.replacements, certificate, order=order,
        )
        result = taylor_coefficients_separated(
            formula, design, construction.replacements,
            at=center, order=order, summation="tuples",
            limits=TaylorLimits(
                max_taylor_pairs=20_000,
                max_measurement_tuples=2_000_000,
                max_group_assignments=20_000_000,
                max_jet_operations=40_000_000,
            ),
        )
        assert result.stats.max_coefficient_bits <= (
            center_budget.every_intermediate_fraction_bits_upper
        )
        assert result.stats.group_assignments_tried <= (
            center_budget.loop_assignment_slots
        )
        data.append(HermiteDatum(
            Fraction(center), result.coefficients
        ))

    conditions = tuple(len(datum.coefficients) for datum in data)
    input_bits = max(
        max(abs(scalar.numerator).bit_length(), scalar.denominator.bit_length())
        for datum in data for scalar in datum.coefficients
    )
    origin_budget = hermite_origin_budget(
        tuple(int(datum.center) for datum in data),
        conditions, input_fraction_bits=max(1, input_bits),
    )
    reconstructed = interpolate_origin_hermite(
        data, degree_bound=degree,
    )
    assert reconstructed.value.denominator == 1
    assert reconstructed.value == count_bruteforce(formula)
    assert reconstructed.stats.max_coefficient_bits <= (
        origin_budget.intermediate_fraction_bits_upper
    )
    assert reconstructed.stats.rational_operations <= (
        origin_budget.rational_operations_upper
    )
