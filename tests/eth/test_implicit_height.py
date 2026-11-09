"""Source-correspondent exact tests of implicit spectral coefficient heights.

Checks actual _walsh_by_weight kernel, implicit swap row_at and
exceptional_projector_at, transferred occurrence-specific coefficients,
and the final Boolean-cube deformation at ALL generated centers.
Numerical parameter choices are explicitly not literal paper admission.
"""
from __future__ import annotations

from fractions import Fraction
from itertools import product
from random import Random

import pytest

from non_exponential_sudoku.eth import (
    CNFFormula, construct_bounded_designs, construct_implicit_auxiliary,
)
from non_exponential_sudoku.eth.construction import construct_auxiliary
from non_exponential_sudoku.eth.polynomial import deformation_polynomial
from reference.eth_implicit_height import (
    implicit_deformation_output_height, implicit_spectral_height,
)
from reference.eth_output_height import universal_deformation_output_height


def _covered(value: Fraction, numerator_bits: int,
             denominator_bits: int) -> bool:
    return (
        max(1, abs(value.numerator).bit_length()) <= numerator_bits
        and max(1, value.denominator.bit_length()) <= denominator_bits
    )


@pytest.mark.integration
@pytest.mark.parametrize("r,Q,R", [
    (2, 1, 1), (2, 2, 2), (2, 3, 3), (3, 3, 2),
])
def test_source_implicit_kernel_rows_and_projector_have_proved_bit_heights(
    r: int, Q: int, R: int,
) -> None:
    auxiliary = construct_implicit_auxiliary(
        r=r, Q=Q, R=R, measurement_basis="projector",
    )
    height = implicit_spectral_height(r, Q, R)
    assert auxiliary.dimension.bit_length() <= height.virtual_dimension_bits_upper
    assert auxiliary.max_polynomial_degree == height.replacement_degree_upper
    for row in auxiliary.kernel:
        for value in row:
            assert _covered(
                value, height.kernel_numerator_bits_upper,
                height.kernel_denominator_bits_upper,
            )

    rng = Random(r * 1000 + Q * 100 + R)
    labels = [
        tuple((0, 0) for _ in range(Q)),
        tuple((0, 1) for _ in range(Q)),
        tuple((1, 0) for _ in range(Q)),
        tuple((j % r, (j + 1) % r) for j in range(Q)),
    ]
    labels.extend(
        tuple((rng.randrange(r), rng.randrange(r)) for _ in range(Q))
        for _ in range(8)
    )
    for source, target in product(labels, repeat=2):
        polynomial = auxiliary.row_at(source, target)
        assert polynomial.degree <= height.replacement_degree_upper
        assert all(
            _covered(value, height.row_numerator_bits_upper,
                     height.row_denominator_bits_upper)
            for value in polynomial.coefficients
        )
        projection = auxiliary.exceptional_projector_at(source, target)
        assert _covered(
            projection, height.projector_numerator_bits_upper,
            height.projector_denominator_bits_upper,
        )


@pytest.mark.integration
def test_implicit_coefficients_match_dense_auxiliary_with_proved_height() -> None:
    r, Q, R = 2, 2, 2
    implicit = construct_implicit_auxiliary(
        r=r, Q=Q, R=R, measurement_basis="projector")
    dense = construct_auxiliary(r=r, Q=Q, R=R)
    height = implicit_spectral_height(r, Q, R)
    for i, source in enumerate(dense.labels):
        for j, target in enumerate(dense.labels):
            polynomial = implicit.row_at(source, target)
            assert polynomial == dense.rows[i][j]
            assert all(
                _covered(value, height.row_numerator_bits_upper,
                         height.row_denominator_bits_upper)
                for value in polynomial.coefficients
            )


@pytest.mark.integration
@pytest.mark.parametrize("r,Q,R,n", [
    (2, 2, 2, 6), (3, 2, 2, 6),
])
def test_real_transferred_replacements_and_all_center_outputs_are_bounded(
    r: int, Q: int, R: int, n: int,
) -> None:
    from benchmarks.eth.spectral_factor_width_probe import ring_formula

    formula = ring_formula(n, width=2)
    built = construct_bounded_designs(
        formula, r=r, Q=Q, R=R, schedule="conditional",
        representation="implicit", measurement_basis="projector")
    assert built.paper_admission is not None
    assert not built.paper_admission.admitted
    assert built.auxiliary.r == r
    ell = sum(map(len, formula.clauses))
    spectral = implicit_spectral_height(r, Q, R)
    overall = implicit_deformation_output_height(
        n, len(formula.clauses), ell, r=r, Q=Q, R=R)
    for forms in built.replacements.clauses:
        for form in forms:
            for polynomial in form.coefficients:
                assert polynomial.degree <= R - 1
                for coefficient in polynomial.coefficients:
                    assert _covered(
                        coefficient,
                        spectral.transferred_numerator_bits_upper(ell),
                        spectral.row_denominator_bits_upper,
                    )
    whole = deformation_polynomial(formula, built.replacements)
    for center, _design in built.centers:
        assert 1 <= center <= Q
        actual = universal_deformation_output_height(
            formula, built.replacements, center)
        assert actual.numerator_bits_upper <= overall.numerator_bits_upper
        assert actual.denominator_bits_upper <= overall.denominator_bits_upper
        polynomial = whole.taylor(center, overall.output_degree_upper)
        for coefficient in polynomial.coefficients:
            assert _covered(coefficient, overall.numerator_bits_upper,
                            overall.denominator_bits_upper)


@pytest.mark.integration
def test_symbolic_giant_virtual_operator_never_allocates_its_dimension() -> None:
    # The formula uses ONLY small integers Q,R; it never computes r**(2Q).
    r, Q, R = 31, 20_000, 4_000
    height = implicit_spectral_height(r, Q, R)
    assert height.virtual_dimension_bits_upper > 100_000
    assert height.row_numerator_bits_upper < 5_000_000
    assert height.row_denominator_bits_upper < 1_000_000
    whole = implicit_deformation_output_height(
        100_000, 120_000, 250_000, r=r, Q=Q, R=R)
    assert whole.output_degree_upper == 250_000 * (R - 1)
    assert whole.numerator_bits_upper > whole.denominator_bits_upper
    assert whole.replacement_coefficient_count_upper == 100_000 * 250_000 * R


@pytest.mark.checkpoint
def test_nonpaper_and_invalid_parameter_shapes_fail_explicitly() -> None:
    for r, Q, R in ((1, 3, 2), (2, 0, 1), (2, 3, 5), (2, 3, 0)):
        with pytest.raises(ValueError):
            implicit_spectral_height(r, Q, R)
    with pytest.raises(ValueError):
        implicit_spectral_height(2.0, 3, 2)  # type: ignore[arg-type]
    with pytest.raises(ValueError):
        implicit_spectral_height(2, 2, 2).transferred_numerator_bits_upper(-1)
    with pytest.raises(ValueError):
        implicit_deformation_output_height(
            -1, 2, 3, r=2, Q=2, R=2,
        )


@pytest.mark.integration
def test_real_implicit_query_has_huge_virtual_dimension_and_small_coefficients() -> None:
    """Run SOURCE row_at/projector_at, not merely a symbolic formula."""
    r, Q, R = 17, 12, 3
    auxiliary = construct_implicit_auxiliary(
        r=r, Q=Q, R=R, measurement_basis="projector",
    )
    height = implicit_spectral_height(r, Q, R)
    assert auxiliary.dimension > 10 ** 25
    assert len(auxiliary.kernel) == Q + 1
    assert height.row_numerator_bits_upper < 300
    left = tuple((0, 1) if s % 2 == 0 else (3, 7) for s in range(Q))
    targets = (
        left,
        tuple((b, a) for a, b in left),
        tuple((0, 0) for _ in range(Q)),
        tuple((a, b) if s < R - 1 else (b, a)
              for s, (a, b) in enumerate(left)),
    )
    for right in targets:
        row = auxiliary.row_at(left, right)
        assert row.degree <= R - 1
        assert all(_covered(value, height.row_numerator_bits_upper,
                            height.row_denominator_bits_upper)
                   for value in row.coefficients)
        projector = auxiliary.exceptional_projector_at(left, right)
        assert _covered(
            projector, height.projector_numerator_bits_upper,
            height.projector_denominator_bits_upper,
        )
