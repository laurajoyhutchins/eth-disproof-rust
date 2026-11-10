"""Conditional source-level separated Taylor cost and bit-height contracts.

These tests verify a bounded, *already certified* center, not the
manuscript's giant input admission, full CNF construction, or Lean machine.
"""
from __future__ import annotations

from fractions import Fraction

import pytest

from benchmarks.eth.spectral_factor_width_probe import ring_formula
from non_exponential_sudoku.eth import construct_bounded_designs
from non_exponential_sudoku.eth.design import certify_measurements
from non_exponential_sudoku.eth.polynomial import (
    ReferenceLimits, deformation_polynomial,
)
from non_exponential_sudoku.eth.taylor import (
    TaylorLimits, taylor_coefficients_separated,
)
from non_exponential_sudoku.runtime.budget import CapacityError
from reference.eth_separated_center_budget import (
    ceil_log2_ratio, certified_separated_center_envelope,
    paper_separated_rate,
)


@pytest.mark.checkpoint
def test_log_ratio_ceiling_is_exact_and_never_uses_floating_point() -> None:
    for numerator, denominator, expected in (
        (1, 1, 0), (2, 1, 1), (3, 2, 1), (9, 2, 3),
        (17, 16, 1), (31, 2, 4), (1025, 1024, 1),
    ):
        actual = ceil_log2_ratio(numerator, denominator)
        assert actual == expected
        assert denominator * (1 << actual) >= numerator
        if actual:
            assert denominator * (1 << (actual - 1)) < numerator
    for a, b in ((1, 0), (0, 1), (1, 2), (True, 1)):
        with pytest.raises(ValueError):
            ceil_log2_ratio(a, b)


@pytest.mark.checkpoint
def test_symbolic_admitted_coupled_paper_center_has_subexp_limit_not_finite_win() -> None:
    first = paper_separated_rate(1 << 34)
    assert (first.r, first.Q, first.R) == (113, 3947580, 524288)
    assert first.order_fraction_upper == Fraction(3 * 524288, 3947580)
    assert first.order_fraction_upper < Fraction(1, 2)
    assert first.total_rate_upper_without_additive_over_n > 1
    # This is a coarse UPPER bound, not a lower bound on execution.
    later = paper_separated_rate(1 << 50)
    assert later.total_rate_upper_without_additive_over_n < Fraction(1, 10)
    assert later.total_rate_upper_without_additive_over_n < first.total_rate_upper_without_additive_over_n
    assert later.additive_exponent_upper == (1 << 50) + 1 + (
        later.r - 1
    ).bit_length()


@pytest.mark.checkpoint
def test_paper_rate_fail_closed_when_full_source_admission_absent() -> None:
    for lam in (1, 10, 1 << 20, 1 << 33):
        with pytest.raises(ValueError, match="Step-5"):
            paper_separated_rate(lam)


@pytest.mark.integration
def test_real_spectral_projected_centers_fit_separated_loop_and_bit_envelope() -> None:
    # Real conditional-expectations schedules, actual spectral transfer,
    # restricted projector and re-certified measurement witnesses.
    # n=6 is not Step-5 admitted, but does exercise the actual source
    # construction. Independent full-cube oracle evaluates H(T).
    formula = ring_formula(6, width=2)
    constructed = construct_bounded_designs(
        formula, r=2, Q=2, R=2, schedule="conditional",
        representation="implicit", measurement_basis="projector",
    )
    assert constructed.paper_admission is not None
    assert not constructed.paper_admission.admitted
    independent = deformation_polynomial(
        formula, constructed.replacements,
        limits=ReferenceLimits(
            max_variables=6, max_assignments=64,
            max_degree=64, max_operations=4_000_000,
            max_coefficient_bits=4096,
        ),
    )
    for center, design in constructed.centers:
        cert = certify_measurements(
            formula, constructed.replacements, design,
            at=Fraction(center),
        )
        for order in (0, 1):
            envelope = certified_separated_center_envelope(
                formula, constructed.replacements, cert, order=order,
            )
            observed = taylor_coefficients_separated(
                formula, design, constructed.replacements,
                at=Fraction(center), order=order,
                summation="tuples",
                limits=TaylorLimits(
                    max_taylor_pairs=10_000,
                    max_measurement_tuples=2_000_000,
                    max_group_assignments=20_000_000,
                    max_jet_operations=40_000_000,
                    max_coefficient_bits=4096,
                ),
            )
            expected = independent.taylor(Fraction(center), order)
            padded = expected.coefficients + (Fraction(0),) * (
                order + 1 - len(expected.coefficients)
            )
            assert observed.coefficients == padded
            assert observed.stats.taylor_pairs == envelope.taylor_pairs
            assert observed.stats.measurement_tuples == (
                envelope.taylor_pairs * envelope.tuples_per_pair
            )
            assert observed.stats.group_assignments_tried <= envelope.loop_assignment_slots
            assert observed.stats.clause_evaluations <= envelope.clause_evaluations_upper
            assert observed.stats.jet_operations <= envelope.rational_jet_operation_upper
            assert (observed.stats.max_coefficient_bits
                    <= envelope.every_intermediate_fraction_bits_upper)
            assert envelope.abstract_schoolbook_bit_work_upper > envelope.rational_jet_operation_upper
            assert envelope.retained_rational_slots_upper > envelope.input_rational_count


@pytest.mark.integration
def test_bounded_source_refusal_does_not_invalidate_uncapped_mathematical_budget() -> None:
    formula = ring_formula(6, width=2)
    constructed = construct_bounded_designs(
        formula, r=2, Q=2, R=2, schedule="conditional",
        representation="implicit", measurement_basis="projector",
    )
    center, design = constructed.centers[0]
    cert = certify_measurements(
        formula, constructed.replacements, design, at=Fraction(center)
    )
    envelope = certified_separated_center_envelope(
        formula, constructed.replacements, cert, order=1,
    )
    assert envelope.taylor_pairs == 13
    assert envelope.tuples_per_pair >= 1
    with pytest.raises(CapacityError, match="measurement tuple limit"):
        taylor_coefficients_separated(
            formula, design, constructed.replacements,
            at=Fraction(center), order=1, summation="tuples",
            limits=TaylorLimits(
                max_measurement_tuples=max(
                    1, envelope.taylor_pairs * envelope.tuples_per_pair - 1
                ),
                max_taylor_pairs=10_000,
            ),
        )
