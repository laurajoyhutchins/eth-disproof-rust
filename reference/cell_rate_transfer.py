"""Exact criterion for transferring an established network-time UPPER bound.

This is *not* evidence of a network-time bound or a lower bound on the
solver. It decides whether a stated symbolic rate ALONE suffices for a
subexponential theorem in the Sudoku-cell parameter under a stated encoding.
"""
from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction


@dataclass(frozen=True, slots=True)
class NetworkRate:
    """log2 T(s) = O(s (loglog s)^beta / (log s)^alpha)."""

    alpha: Fraction
    beta: int

    def __post_init__(self) -> None:
        if not isinstance(self.alpha, Fraction) or self.alpha < 0:
            raise ValueError('alpha must be a nonnegative exact fraction')
        if type(self.beta) is not int:
            raise ValueError('beta must be an integer')

    def suffices_for_cell_subexponential(
        self, *, edge_log_growth: Fraction,
    ) -> bool:
        """Sufficient transfer for s=O(N*(log N)**delta), log s=Theta(log N).

        The implied exponent/N is O((log N)**(delta-alpha)
        *(loglog N)**beta). This upper expression tends to zero precisely
        if alpha>delta, or alpha==delta and beta<0. Failure does not prove
        the algorithm is slow: only that this upper bound is too weak.
        """
        if not isinstance(edge_log_growth, Fraction) or edge_log_growth < 0:
            raise ValueError('edge growth exponent must be nonnegative exact fraction')
        return (self.alpha > edge_log_growth or
                self.alpha == edge_log_growth and self.beta < 0)


# Current conditional whole-frame paper statement, not an established
# theorem for the production solver: lambda=ceil(log2 s).
PAPER_CONDITIONAL_RATE = NetworkRate(Fraction(1, 4), 1)
# Direct generalized-Sudoku Boolean wires: s=Theta(N log N) in N cells.
DIRECT_SUDOKU_EDGE_LOG_GROWTH = Fraction(1)
