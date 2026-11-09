"""Independent asymptotic boundary tests for the theorem acceptance gate."""
from __future__ import annotations

from fractions import Fraction

import pytest

from reference.cell_rate_transfer import (
    DIRECT_SUDOKU_EDGE_LOG_GROWTH, PAPER_CONDITIONAL_RATE, NetworkRate,
)

pytestmark = pytest.mark.checkpoint


def test_current_conditional_paper_rate_does_not_transfer_to_cells() -> None:
    assert PAPER_CONDITIONAL_RATE.alpha == Fraction(1, 2)
    assert PAPER_CONDITIONAL_RATE.beta == 0
    assert not PAPER_CONDITIONAL_RATE.suffices_for_cell_subexponential(
        edge_log_growth=DIRECT_SUDOKU_EDGE_LOG_GROWTH,
    )


@pytest.mark.parametrize('alpha,beta,growth,should_transfer', [
    (Fraction(2), 0, Fraction(1), True),
    (Fraction(1), -1, Fraction(1), True),
    (Fraction(1), 0, Fraction(1), False),
    (Fraction(1), 1, Fraction(1), False),
    (Fraction(1, 2), 0, Fraction(1), False),
    (Fraction(1, 2), 0, Fraction(0), True),
    (Fraction(1, 2), 0, Fraction(1, 2), False),
    (Fraction(1, 4), 1, Fraction(0), True),
    (Fraction(0), -1, Fraction(0), True),
])
def test_symbolic_rate_transfer_criterion(
    alpha: Fraction, beta: int, growth: Fraction, should_transfer: bool,
) -> None:
    assert NetworkRate(alpha, beta).suffices_for_cell_subexponential(
        edge_log_growth=growth) is should_transfer


def test_direct_sudoku_wire_ratio_obstruction_has_diverging_square() -> None:
    # For b=2**k, N=b**4, M=6*k*N, lambda=ceil(log2 M)<=10k.
    # (M/N/sqrt(lambda))**2 >= 36*k**2/(10*k) = (18/5)*k.
    # This is an obstruction for the DISPLAYED UPPER-BOUND EXPRESSION,
    # not a lower bound on the actual algorithm's running time.
    for k in (1, 2, 4, 8, 16, 32):
        N = 1 << (4 * k)
        M = 6 * k * N
        lam = (M - 1).bit_length()
        assert lam <= 10 * k
        assert Fraction((M // N)**2, lam) >= Fraction(18, 5) * k


@pytest.mark.parametrize('bad_alpha,bad_beta', [
    (Fraction(-1), 1), (Fraction(1, 4), 0.3),
])
def test_rate_rejects_invalid_parameters(bad_alpha: Fraction, bad_beta: object) -> None:
    with pytest.raises(ValueError):
        NetworkRate(bad_alpha, bad_beta)  # type: ignore[arg-type]


def test_rate_refuses_negative_encoding_growth() -> None:
    with pytest.raises(ValueError):
        NetworkRate(Fraction(2), 0).suffices_for_cell_subexponential(
            edge_log_growth=Fraction(-1),
        )
