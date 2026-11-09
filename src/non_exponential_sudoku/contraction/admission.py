"""Conservative preflight of *mandatory first-factor* child evaluations.

All feasibility decisions use the same iterative assignment enumerator as
factor construction and explicit summation. A bounded scan returning unknown
must not reject; actual runtime resource guards remain authoritative.
"""
from __future__ import annotations

from dataclasses import dataclass
from typing import Literal, Sequence

from ..core.mode_assignments import iter_mode_assignments
from ..core.modes import Mode
from .planning import FactorizationPlan


@dataclass(frozen=True)
class AdmissionEstimate:
    outcome: Literal['within_first_factor_limit', 'refused', 'unknown']
    first_factor_assignments: int | None
    reason: str


class _PreflightWorkCap(RuntimeError):
    """Internal scan budget; never interpreted as mandatory excess work."""


def estimate_first_factor(
    plan: FactorizationPlan, modes: Sequence[Mode], precision: int,
    *, max_child_evaluations: int, max_transitions: int = 20_000,
    packet_row_caps: bool = False,
) -> AdmissionEstimate:
    """Count actual mandatory scoped tuples, stopping once refusal is proved.

    The initial factor is always materialized in full, even if zero. Later
    factors may never be constructed. The row cap is justified only for a
    genuine paper PacketEntry target, not arbitrary child oracles.
    """
    if (type(precision) is not int or precision < 1
            or type(max_child_evaluations) is not int or max_child_evaluations < 1
            or type(max_transitions) is not int or max_transitions < 1):
        raise ValueError('admission limits and precision must be positive integers')
    if not plan.factors:
        return AdmissionEstimate('within_first_factor_limit', 0, 'no factors')
    first = plan.factors[0]
    transitions = 0

    def work() -> None:
        nonlocal transitions
        transitions += 1
        if transitions > max_transitions:
            raise _PreflightWorkCap

    count = 0
    try:
        for _ in iter_mode_assignments(
                modes, precision, scope=first.mode_indices,
                target_groups=(first.group,) if packet_row_caps else (), work=work):
            count += 1
            if count > max_child_evaluations:
                return AdmissionEstimate(
                    'refused', count, 'first factor exceeds child-contraction limit')
    except _PreflightWorkCap:
        return AdmissionEstimate('unknown', None, 'preflight work cap reached')
    return AdmissionEstimate(
        'within_first_factor_limit', count, 'first factor fits child budget; remaining costs unknown')
