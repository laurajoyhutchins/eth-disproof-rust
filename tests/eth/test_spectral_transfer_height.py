"""Conditional spectral-transfer heights checked against real source objects."""
from __future__ import annotations

from fractions import Fraction
from itertools import product

import pytest

from non_exponential_sudoku.eth import CNFFormula, construct_bounded_designs
from non_exponential_sudoku.eth.construction import (
    _interpolation_polynomial, _walsh_by_weight, construct_implicit_auxiliary,
)
from non_exponential_sudoku.eth.paper_admitted_witness import (
    virtual_coupled_3cnf_step5,
)
from reference.eth_spectral_transfer_height import (
    ceil_log2, spectral_transfer_height_budget,
)


def _fraction_bits(value: Fraction) -> int:
    return max(1, abs(value.numerator).bit_length(), value.denominator.bit_length())


@pytest.mark.checkpoint
@pytest.mark.parametrize(("r", "Q", "R"), [
    (2, 1, 1), (2, 2, 1), (2, 2, 2), (2, 2, 3),
    (2, 3, 2), (2, 3, 3), (3, 1, 2), (3, 2, 2),
])
def test_source_spectral_kernel_polynomial_and_integer_interpolation_heights(
    r: int, Q: int, R: int,
) -> None:
    # Use projector representation to avoid eagerly enumerating huge
    # selector sets. This exercises the SAME implicit row_at spectral
    # coefficients used by the enumerated selector path.
    budget = spectral_transfer_height_budget(
        r=r, Q=Q, R=R, incidence_log2_upper=0,
    )
    aux = construct_implicit_auxiliary(
        r=r, Q=Q, R=R, measurement_basis="projector",
    )
    interpolation = _interpolation_polynomial(aux.interval)
    for j in range(Q + 1):
        actual = interpolation.evaluate(j)
        assert actual.denominator == 1
        assert abs(actual) <= R * (2 * Q) ** R
    for coefficient in interpolation.coefficients:
        assert _fraction_bits(coefficient) <= (
            budget.interpolation_and_walsh_bits_upper
        )
    for coefficient in _walsh_by_weight(interpolation, Q):
        assert _fraction_bits(coefficient) <= (
            budget.interpolation_and_walsh_bits_upper
        )
        assert (coefficient * (1 << Q)).denominator == 1
    for row in aux.kernel:
        for coefficient in row:
            assert _fraction_bits(coefficient) <= budget.kernel_fraction_bits_upper
            assert (coefficient * (1 << Q)).denominator == 1
    labels = tuple(product(range(r), repeat=2 * Q))
    coordinates = tuple(
        tuple((x[2 * i], x[2 * i + 1]) for i in range(Q))
        for x in labels
    )
    for source in coordinates:
        for destination in coordinates:
            transferred = aux.row_at(source, destination)
            for coefficient in transferred.coefficients:
                assert _fraction_bits(coefficient) <= (
                    budget.transferred_polynomial_fraction_bits_upper
                )
                from math import factorial
                assert (coefficient * (1 << Q) * factorial(Q)).denominator == 1
            for center in range(1, Q + 1):
                assert _fraction_bits(transferred.evaluate(center)) <= (
                    budget.centered_occurrence_fraction_bits_upper
                )


@pytest.mark.integration
def test_real_conditional_transfer_coefficients_and_certification_fit_height() -> None:
    # Real balanced incidence schedules and occurrence transfer, rather
    # than just constructing a small auxiliary without a CNF.
    formula = CNFFormula(4, ((1, -2), (-2, 3), (3, -4), (-4, 1)))
    result = construct_bounded_designs(
        formula, r=2, Q=2, R=2, schedule="conditional",
        representation="implicit", measurement_basis="projector",
    )
    occurrences = sum(map(len, formula.clauses))
    bounds = spectral_transfer_height_budget(
        r=2, Q=2, R=2, incidence_log2_upper=ceil_log2(occurrences + 1),
    )
    seen = 0
    for rows in result.replacements.clauses:
        for form in rows:
            for polynomial in form.coefficients:
                for coefficient in polynomial.coefficients:
                    assert _fraction_bits(coefficient) <= (
                        bounds.transferred_polynomial_fraction_bits_upper
                    )
                for center, _ in result.centers:
                    assert _fraction_bits(polynomial.evaluate(center)) <= (
                        bounds.centered_occurrence_fraction_bits_upper
                    )
                    seen += 1
    assert seen > 0


@pytest.mark.checkpoint
def test_coupled_virtual_step5_height_is_linear_in_lambda_without_n_or_D() -> None:
    for lam in (1 << 34, 1 << 40):
        witness = virtual_coupled_3cnf_step5(lam)
        assert witness.admitted_by_sufficient_conditions
        # For n=2**lam and M<=3n, ceil(log2(M+1))<=lam+2.
        budget = spectral_transfer_height_budget(
            r=witness.r, Q=witness.Q, R=witness.R,
            incidence_log2_upper=lam + 2,
        )
        assert budget.selector_dimension_log2_upper <= lam
        assert budget.transferred_polynomial_fraction_bits_upper <= 10 * lam
        assert budget.centered_occurrence_fraction_bits_upper <= 10 * lam


@pytest.mark.checkpoint
def test_transfer_contract_rejects_unjustified_inputs() -> None:
    for values in (
        (1, 2, 2, 0),
        (2, 0, 1, 0),
        (2, 2, 4, 0),
        (2, 2, 2, -1),
        (True, 2, 2, 0),
    ):
        with pytest.raises(ValueError):
            spectral_transfer_height_budget(
                r=values[0], Q=values[1], R=values[2],
                incidence_log2_upper=values[3],
            )
