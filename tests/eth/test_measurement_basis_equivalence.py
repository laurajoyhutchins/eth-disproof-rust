"""Actual ETH spectral selector versus projected basis equivalence.

The two measurement representations have the exact same row space.
They need NOT have the same matrix shape, integer L1 norm, or
(tau,D) admission parameters. All count/oracle comparisons remain
independent of the tested reduction.
"""
from __future__ import annotations

from fractions import Fraction
from itertools import product
from random import Random

import pytest

from non_exponential_sudoku.eth import (
    CNFFormula, ConstructionLimits, certify_measurements,
    construct_bounded_designs, construct_from_schedules,
    count_bruteforce, count_from_constructed,
    deformation_polynomial, deterministic_schedules,
    taylor_coefficients_separated,
)
from non_exponential_sudoku.eth.construction import (
    ImplicitAuxiliaryDesign, construct_implicit_auxiliary,
    construct_paper_bounded_designs,
)
from non_exponential_sudoku.eth.parameters import PaperParametersUnavailable
from non_exponential_sudoku.runtime.budget import CapacityError
from reference.eth_measurement_basis_equivalence import (
    compare_transferred_rowspaces, projector_from_selectors,
)


@pytest.mark.integration
@pytest.mark.parametrize(("r", "Q", "R"), [
    (2, 1, 1),
    (2, 2, 1),
    (2, 2, 2),
    (2, 2, 3),
    (2, 3, 2),
    (3, 1, 1),
    (3, 1, 2),
])
def test_actual_projector_equals_orthogonal_normalized_selector_sum(
    r: int, Q: int, R: int,
) -> None:
    aux = construct_implicit_auxiliary(
        r=r, Q=Q, R=R, measurement_basis="selectors",
        limits=ConstructionLimits(max_measurement_rows=10_000),
    )
    rng = Random(7189 + r * 100 + Q * 10 + R)
    labels = tuple(
        tuple((coords[2 * s], coords[2 * s + 1]) for s in range(Q))
        for coords in product(range(r), repeat=2 * Q)
    )
    sample = labels if len(labels) <= 16 else tuple(
        labels[i] for i in sorted(set(
            [0, len(labels) - 1, *(
                rng.randrange(len(labels)) for _ in range(12)
            )]
        ))
    )
    for left in sample:
        for right in sample:
            actual = aux.exceptional_projector_at(left, right)
            reference = projector_from_selectors(aux, left, right)
            assert actual == reference


@pytest.mark.integration
@pytest.mark.parametrize(("n", "clauses", "Q", "R"), [
    (3, ((1, -2), (-1, 3), (2, 3)), 2, 2),
    (4, ((1, 2), (-1, 3), (2, -4)), 2, 2),
    (4, ((1, 2), (3, 4)), 3, 2),
    (4, (), 2, 1),
    (4, ((),), 2, 2),
])
def test_both_transfers_same_exact_rowspace_and_count(
    n: int, clauses: tuple[tuple[int, ...], ...], Q: int, R: int,
) -> None:
    formula = CNFFormula(n, clauses)
    selectors = construct_implicit_auxiliary(
        r=2, Q=Q, R=R, measurement_basis="selectors",
        limits=ConstructionLimits(max_measurement_rows=1000),
    )
    projected = construct_implicit_auxiliary(
        r=2, Q=Q, R=R, measurement_basis="projector",
    )
    a, d = deterministic_schedules(formula, r=2, Q=Q)
    limits = ConstructionLimits(max_measurement_rows=1000)
    original = construct_from_schedules(
        formula, selectors, a, d, limits=limits)
    compact = construct_from_schedules(
        formula, projected, a, d, limits=limits)
    assert original.replacements == compact.replacements
    assert original.variable_schedules == compact.variable_schedules
    assert original.clause_schedules == compact.clause_schedules
    witness = compare_transferred_rowspaces(original.centers, compact.centers)
    assert witness.compared_centers == Q
    assert witness.groups == 2 * Q
    assert witness.projector_row_count <= witness.selector_row_count
    for (center, old), (other_center, new) in zip(
        original.centers, compact.centers
    ):
        assert center == other_center
        old_certificate = certify_measurements(
            formula, original.replacements, old, at=center)
        new_certificate = certify_measurements(
            formula, compact.replacements, new, at=center)
        assert old_certificate.total_measurements == sum(map(len, old.matrices))
        assert new_certificate.total_measurements == sum(map(len, new.matrices))
        reference = deformation_polynomial(
            formula, original.replacements).evaluate(Fraction(center))
        assert taylor_coefficients_separated(
            formula, old, original.replacements, at=center,
            order=0, summation="fused",
        ).coefficients == (reference,)
        assert taylor_coefficients_separated(
            formula, new, compact.replacements, at=center,
            order=0, summation="fused",
        ).coefficients == (reference,)
    expected = count_bruteforce(formula)
    # The original literal tuple evaluator can refuse on a large
    # redundant selector row count. The fused exact evaluator avoids
    # that representational explosion, without substituting brute force.
    assert count_from_constructed(
        formula, compact, summation="fused",
    ) == expected
    assert count_from_constructed(
        formula, original, summation="fused",
    ) == expected


@pytest.mark.integration
def test_conditional_schedule_projected_and_selector_certify_same_space() -> None:
    formula = CNFFormula(4, ((1, -2), (2, 3), (-3, 4)))
    limits = ConstructionLimits(max_measurement_rows=1000)
    selector = construct_bounded_designs(
        formula, r=2, Q=2, R=2, schedule="conditional",
        measurement_basis="selectors", limits=limits)
    projected = construct_bounded_designs(
        formula, r=2, Q=2, R=2, schedule="conditional",
        measurement_basis="projector", limits=limits)
    assert selector.replacements == projected.replacements
    assert selector.variable_schedules == projected.variable_schedules
    assert selector.clause_schedules == projected.clause_schedules
    certificate = compare_transferred_rowspaces(
        selector.centers, projected.centers)
    assert certificate.exact_rowspace_inclusions_checked > 0
    assert certificate.projector_row_count <= certificate.selector_row_count


@pytest.mark.integration
def test_projector_avoids_global_exception_selector_enumeration_but_not_design_caps() -> None:
    low = ConstructionLimits(max_measurement_rows=4)
    with pytest.raises(CapacityError, match="exceptional direction"):
        construct_implicit_auxiliary(
            r=2, Q=5, R=2, limits=low, measurement_basis="selectors")
    projected = construct_implicit_auxiliary(
        r=2, Q=5, R=2, limits=low, measurement_basis="projector")
    assert projected.measurement_selectors == ()
    assert projected.exceptional_count > low.max_measurement_rows
    # No claim that its transferred row count and L1 conditions hold:
    # those checks are still enforced at each actual center.


@pytest.mark.checkpoint
def test_strict_entrypoint_opt_in_retains_literal_admission_and_invalid_mode_policy() -> None:
    formula = CNFFormula(3, ((1, 2), (-2, 3)))
    for mode in ("selectors", "projector"):
        with pytest.raises(PaperParametersUnavailable):
            construct_paper_bounded_designs(formula, measurement_basis=mode)
    # Admission is checked before auxiliary construction on this tiny
    # nonadmitted input: no alternative toy schedule is substituted.
    with pytest.raises(PaperParametersUnavailable):
        construct_paper_bounded_designs(
            formula, measurement_basis="invalid",  # type: ignore[arg-type]
        )
