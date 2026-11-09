"""Independent RED/green boundary tests for depth-wise paper support summation.

No finite test certifies the asymptotic theorem; these tests guard the exact
implemented schedule/formulas and prevent accidental solver-time promotion.
"""
from __future__ import annotations

from fractions import Fraction
from math import isqrt

import pytest

from non_exponential_sudoku.contraction.engine import paper_schedule_parameters
from reference.global_mode_support import uniform_support_ratio_square_bound
from reference.paper_depth_sum import (
    ROOT_SUM_SQRT_RATIO_CONSTANT,
    paper_depth_ratios,
    summed_paper_support_exponent,
)

pytestmark = pytest.mark.checkpoint


def _ceil_sqrt(value: int) -> int:
    r = isqrt(value)
    return r + int(r * r != value)


def test_no_paper_depth_before_activation() -> None:
    assert paper_depth_ratios(131071) == ()
    result = summed_paper_support_exponent(1 << 120)
    assert result.active_depths == 0
    assert result.log2_support_exponent_sum_ceiling == 0


@pytest.mark.parametrize('u0', (1, 2, 3, 4, 16, 100, 4096))
def test_ratio_formula_agrees_with_literal_schedule(u0: int) -> None:
    lam = 131072 * u0
    terms = paper_depth_ratios(lam)
    assert len(terms) == u0.bit_length()
    rho = Fraction(1)
    for d, frame in enumerate(terms):
        _, a, u, _ = paper_schedule_parameters(2, lam, d)
        assert (frame.active_coordinates, frame.accumulated_slot_exponent) == (u, a)
        capped = min(u, 2 * lam.bit_length())
        independent = (3 * rho * (37 + 8 * (a + 1)) / (1 << capped)
                       + 192 * rho * rho / u)
        assert frame.color_precision_ratio_ceiling == independent
        rho *= Fraction(3, 32)
    # The older, weaker proof took the maximum of these terms.
    assert max(t.color_precision_ratio_ceiling for t in terms) == (
        uniform_support_ratio_square_bound(lam)
    )


def test_first_active_ratio_is_not_small_at_threshold() -> None:
    term, = paper_depth_ratios(131072)
    assert term.color_precision_ratio_ceiling == Fraction(567, 2)
    assert term.color_precision_ratio_ceiling > 1


@pytest.mark.parametrize('u0', (1, 2, 4, 16))
def test_symbolic_depth_sum_majorizes_exact_ceiling_at_paper_scale(u0: int) -> None:
    # This constructs a ~lambda-bit *integer*, not a network or a factor
    # table of size 2**lambda. Explicit arithmetic checks the numeric
    # majorant for several finite parameter values, not the infinite proof.
    lam = 131072 * u0
    s = (1 << (lam - 1)) + 1
    budget = summed_paper_support_exponent(s)
    assert budget.active_depths == u0.bit_length()
    exact_upper = 0
    for term in paper_depth_ratios(lam):
        ratio = term.color_precision_ratio_ceiling
        numerator = ratio.numerator * s * s
        integral_upper = (numerator + ratio.denominator - 1) // ratio.denominator
        exact_upper += 4 * _ceil_sqrt(integral_upper)
    assert exact_upper <= budget.log2_support_exponent_sum_ceiling
    # A valid ceiling need not be useful at the finite activation threshold.
    assert budget.log2_support_exponent_sum_ceiling > 0


def test_sum_bound_improves_over_max_times_depth_as_lambda_grows() -> None:
    # The infinite proof sums dyadically. Check its claimed finite majorant
    # using rational-square-root integer upper bounds; do NOT allocate s.
    assert ROOT_SUM_SQRT_RATIO_CONSTANT == 256
    scale = 1 << 24
    for u0 in (16, 256, 4096, 65536):
        ratios = paper_depth_ratios(131072 * u0)
        upper = 0
        for t in ratios:
            r = t.color_precision_ratio_ceiling
            squared = (r.numerator * scale * scale + r.denominator - 1) // r.denominator
            upper += _ceil_sqrt(squared)
        # Rounding contributes at most one unit per active level.
        assert upper * isqrt(u0) <= (
            ROOT_SUM_SQRT_RATIO_CONSTANT * scale
            + len(ratios) * isqrt(u0)
        )


def test_enormous_symbolic_lambda_has_bounded_fraction_denominators() -> None:
    # The cap on 2**(-u) is a one-sided enlargement of the estimate.
    lam = 1 << 140
    terms = paper_depth_ratios(lam)
    assert terms
    assert terms[0].active_coordinates > 2 * lam.bit_length()
    assert all(t.color_precision_ratio_ceiling >= 0 for t in terms)
    assert len(terms) == (lam // 131072).bit_length()


@pytest.mark.parametrize('bad', (0, -1, 1.0, True))
def test_invalid_symbolic_inputs_are_refused(bad: object) -> None:
    with pytest.raises(ValueError):
        paper_depth_ratios(bad)  # type: ignore[arg-type]
    with pytest.raises(ValueError):
        summed_paper_support_exponent(bad)  # type: ignore[arg-type]
