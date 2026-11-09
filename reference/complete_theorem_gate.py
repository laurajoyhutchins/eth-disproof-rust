"""Fail-closed current theorem status, not a self-certifying proof checker.

A complete numerical local-work dictionary is insufficient. This gate also
requires the source/totality obligations maintained by the composed recurrence,
and, for Sudoku-cell claims, a justified rate transfer through the encoding.
"""
from __future__ import annotations

from dataclasses import dataclass
from typing import Literal

from reference.cell_rate_transfer import (
    DIRECT_SUDOKU_EDGE_LOG_GROWTH, PAPER_CONDITIONAL_RATE,
)
from reference.whole_frame_recurrence import OPEN_PREMISES


class IncompleteTheorem(ValueError):
    """At least one independent universal claim remains uncertified."""


@dataclass(frozen=True, slots=True)
class CompleteTheoremStatus:
    target: Literal['network', 'sudoku_cells']
    local_bit_work_gap: str | None
    source_and_totality_gaps: tuple[str, ...]
    parameter_transfer_gap: str | None

    @property
    def outstanding(self) -> tuple[str, ...]:
        gaps: list[str] = []
        if self.local_bit_work_gap is not None:
            gaps.append('local_bit_work: ' + self.local_bit_work_gap)
        gaps.extend('source_or_totality: ' + term
                    for term in self.source_and_totality_gaps)
        if self.parameter_transfer_gap is not None:
            gaps.append('cell_parameter: ' + self.parameter_transfer_gap)
        return tuple(gaps)

    def require_complete(self) -> None:
        if self.outstanding:
            raise IncompleteTheorem('unproved: ' + '; '.join(self.outstanding))


def current_theorem_status(
    *, local_bit_work_gap: str | None,
    target: Literal['network', 'sudoku_cells'] = 'sudoku_cells',
) -> CompleteTheoremStatus:
    """Report all independent current blockers even if local fields are filled.

    OPEN_PREMISES belongs to the actual composed paper-source recurrence.
    The cell test checks only whether the *displayed network upper bound*
    suffices with the *direct* Sudoku reduction, not real runtime lower bounds.
    No caller-supplied boolean can suppress either source/totality or cell
    transfer obligations. Future positive proofs require changing their
    independently reviewed source implementations and this acceptance gate.
    """
    if target not in ('network', 'sudoku_cells'):
        raise ValueError('unsupported theorem parameter')
    gap: str | None = None
    if (target == 'sudoku_cells' and
            not PAPER_CONDITIONAL_RATE.suffices_for_cell_subexponential(
                edge_log_growth=DIRECT_SUDOKU_EDGE_LOG_GROWTH,
            )):
        gap = ('current O(s loglog(s) / log(s)^(1/4)) edge-time ceiling '
               'does not imply o(N) exponent through s=Theta(N log N)')
    return CompleteTheoremStatus(target, local_bit_work_gap, OPEN_PREMISES, gap)
