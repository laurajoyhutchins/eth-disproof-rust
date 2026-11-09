"""Cheap, conservative preflight of mandatory first-factor child evaluations.

Only the first local factor is guaranteed to be constructed: construction may
return early when a preceding factor is identically zero. Nonzero-table sizes,
work, peak memory, and all later recursive fanout are NOT bounded here.
Runtime resource guards remain authoritative. This check can refuse only when
the mandatory first factor alone provably exceeds its child-evaluation budget.
"""
from __future__ import annotations

from dataclasses import dataclass
from typing import Literal, Sequence

from ..core.modes import Mode
from .planning import FactorizationPlan


@dataclass(frozen=True)
class AdmissionEstimate:
    outcome: Literal["within_first_factor_limit", "refused", "unknown"]
    first_factor_assignments: int | None
    reason: str


def estimate_first_factor(
    plan: FactorizationPlan, modes: Sequence[Mode], precision: int,
    *, max_child_evaluations: int, max_transitions: int = 20_000,
) -> AdmissionEstimate:
    """Count first-factor weighted assignments, or return unknown within a work cap.

    Each partial assignment can extend by zeros; an intermediate count over
    budget is therefore a valid lower bound on final assignments. We never
    pre-refuse on possible sparse-table size or on conditional later factors.
    """
    if precision < 1 or max_child_evaluations < 1 or max_transitions < 1:
        raise ValueError("admission limits and precision must be positive")
    if not plan.factors:
        return AdmissionEstimate("within_first_factor_limit", 0, "no factors")
    degrees = {0: 1}
    transitions = 0
    for j in plan.factors[0].mode_indices:
        m = modes[j]
        if m.weight < 1:
            raise ValueError("mode weights must be positive")
        limit = min(len(m.rows), (precision - 1) // m.weight)
        next_degrees: dict[int, int] = {}
        for degree, count in degrees.items():
            for beta in range(min(limit, (precision - 1 - degree) // m.weight) + 1):
                transitions += 1
                if transitions > max_transitions:
                    return AdmissionEstimate("unknown", None, "preflight work cap reached")
                target = degree + beta * m.weight
                next_degrees[target] = min(max_child_evaluations + 1,
                                           next_degrees.get(target, 0) + count)
        degrees = next_degrees
        total = sum(degrees.values())
        if total > max_child_evaluations:
            return AdmissionEstimate("refused", total,
                                     "first factor exceeds child-contraction limit")
    return AdmissionEstimate("within_first_factor_limit", sum(degrees.values()),
                             "first factor fits child budget; remaining costs unknown")
