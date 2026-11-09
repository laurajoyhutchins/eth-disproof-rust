"""Opt-in RED acceptance tests for a complete worst-case bit-work theorem.

Run explicitly: PYTHONPATH=src:. python -m pytest -q research_acceptance/
Outside the default testpaths and verification tiers. A failing theorem claim
must not be disguised as an expected failure, skip, or a passed CI check.
"""
from __future__ import annotations

from dataclasses import dataclass
from typing import Callable

import pytest

from non_exponential_sudoku.runtime.config import ContractorConfig
from reference.precision_envelope import PaperFrameEnvelope, paper_frame_envelopes
from reference.recurrence_calls import recursive_call_bound
from reference.complete_theorem_gate import current_theorem_status, IncompleteTheorem


# A complete bit recurrence must bound *each* local operation, including the
# work of recursively generated oracles. These are named proof obligations,
# not stopwatch counters or guesses at small-instance asymptotic rates.
LOCAL_BIT_WORK_TERMS = (
    "network_validation_and_input_oracles",
    "irreducible_modulus_construction",
    "balanced_labels_and_packet_materialization",
    "mode_catalog_and_factor_construction",
    "mode_elimination_and_cache_materialization",
    "recursive_packet_entry_oracles",
    "nested_ring_arithmetic_and_coefficient_growth",
    "deformation_sampling_and_interpolation",
    "exact_rational_recovery_and_allocation",
    "terminal_leaf_oracle_and_arithmetic_work",
)


@dataclass(frozen=True)
class LocalBitBound:
    """Conditional numeric upper bounds for one frame, not proof certificates.

    The bounds must be derived and justified separately. Providing numbers is
    deliberately insufficient to establish the theorem's universal premise.
    """

    terms: dict[str, int]

    def require_complete(self) -> int:
        missing = sorted(set(LOCAL_BIT_WORK_TERMS) - set(self.terms))
        unexpected = sorted(set(self.terms) - set(LOCAL_BIT_WORK_TERMS))
        invalid = sorted(k for k, v in self.terms.items()
                         if type(v) is not int or v < 0)
        if missing or unexpected or invalid:
            raise IncompleteBitBound(
                f"missing={missing}; unexpected={unexpected}; invalid={invalid}"
            )
        return sum(self.terms.values())


class IncompleteBitBound(ValueError):
    """A missing term must never become a zero-cost term."""


def unfold_conditional_bit_recurrence(
    frames: tuple[PaperFrameEnvelope, ...],
    local: Callable[[PaperFrameEnvelope], LocalBitBound],
) -> int:
    """Unfold T_d <= U_d + K_d*T_(d+1), conditional on every given U_d.

    This is exact arithmetic on proposed upper bounds. It does not verify that
    the supplied U_d terms are valid upper bounds for the implementation.
    """
    if not frames or not frames[-1].terminal:
        raise IncompleteBitBound("missing terminal recurrence frame")
    total = 0
    for frame in reversed(frames):
        work = local(frame).require_complete()
        if frame.terminal:
            total = work
        else:
            branching = (frame.centers * frame.evaluations_per_center *
                         frame.children_per_evaluation)
            total = work + branching * total
    return total


def current_local_bit_evidence(frame: PaperFrameEnvelope) -> LocalBitBound:
    """State the *current* proved numeric local bounds, without extrapolation.

    The repo proves call-count, coordinate-size and some ring-operation
    envelopes, but not a complete per-frame BIT-work bound. Consequently no
    LOCAL_BIT_WORK_TERMS have universally proved numeric bounds yet.
    """
    return LocalBitBound({})


def _active_symbolic_frames() -> tuple[PaperFrameEnvelope, ...]:
    # A small constructible Sudoku board never enters the paper recursion.
    # Use an allocation-free symbolic paper schedule to exercise recurrence
    # closure without constructing an astronomically sized coefficient ring.
    s = (1 << 131071) + 1
    cfg = ContractorConfig(s=s, precision=3, schedule="paper")
    return paper_frame_envelopes(cfg, edges=s, vertices=40)


def test_missing_bit_cost_is_not_silently_charged_as_zero() -> None:
    frames = _active_symbolic_frames()
    assert len(frames) == 2 and not frames[0].terminal and frames[1].terminal
    with pytest.raises(IncompleteBitBound, match="recursive_packet_entry_oracles"):
        unfold_conditional_bit_recurrence(frames, current_local_bit_evidence)


def test_conditional_recurrence_accounts_for_both_levels() -> None:
    frames = _active_symbolic_frames()
    ones = {name: 1 for name in LOCAL_BIT_WORK_TERMS}
    estimated = unfold_conditional_bit_recurrence(frames, lambda _: LocalBitBound(ones))
    k = (frames[0].centers * frames[0].evaluations_per_center *
         frames[0].children_per_evaluation)
    assert estimated == len(ones) * (1 + k)
    # The independent existing call-count bound corresponds to U_d=1.
    cfg = ContractorConfig(s=(1 << 131071) + 1, precision=3, schedule="paper")
    assert recursive_call_bound(cfg, cfg.s) == 1 + k


def test_recurrence_refuses_invalid_or_fabricated_local_terms() -> None:
    frames = _active_symbolic_frames()
    complete = {name: 1 for name in LOCAL_BIT_WORK_TERMS}
    with pytest.raises(IncompleteBitBound, match="invalid="):
        unfold_conditional_bit_recurrence(
            frames, lambda _: LocalBitBound({**complete, "mode_elimination_and_cache_materialization": -1})
        )
    with pytest.raises(IncompleteBitBound, match="unexpected="):
        unfold_conditional_bit_recurrence(
            frames, lambda _: LocalBitBound({**complete, "measured_microseconds": 50})
        )



def test_observed_call_ledger_cannot_bound_opaque_oracle_work() -> None:
    """Equal observable events can hide arbitrarily different oracle work.

    A constant-one vertex oracle may perform additional integer operations
    before returning. The ledger counts calls to the oracle, not its body.
    Thus it cannot serve as the local bit bound U_d without an oracle-cost
    contract that is preserved across recursive packet construction.
    """
    from non_exponential_sudoku.core.algebra import Padic, modulus_polynomial
    from non_exponential_sudoku.core.network import Network, Vertex
    from non_exponential_sudoku.runtime.cost_ledger import CostLedger

    ring = Padic(3, modulus_polynomial(3), 8)
    records: list[tuple[dict[str, int], dict[str, int], int]] = []
    for body_iterations in (1, 1000):
        internal = [0]

        def oracle(bits: tuple[int, ...], r: Padic) -> tuple[int, ...]:
            for i in range(body_iterations):
                internal[0] += (i * i) & 7
            return r.one

        graph = Network([Vertex("opaque", (), oracle)], [], 0)
        ledger = CostLedger()
        with ledger.frame(depth=0, wires=0, precision=ring.p,
                          ring_depth=0, schedule="exhaustive"):
            assert graph.direct(ring, 0) == ring.one
        records.append((dict(ledger.total_work), dict(ledger.total_ring_calls), internal[0]))
    assert records[0][0] == records[1][0]
    assert records[0][1] == records[1][1]
    assert records[0][2] != records[1][2]


def test_fabricated_local_costs_cannot_satisfy_complete_theorem() -> None:
    """GREEN negative control: a numerical ledger cannot bypass totality/cell claims."""
    frames = _active_symbolic_frames()
    ones = {name: 1 for name in LOCAL_BIT_WORK_TERMS}
    assert unfold_conditional_bit_recurrence(
        frames, lambda _: LocalBitBound(ones),
    ) > 0
    with pytest.raises(IncompleteTheorem, match="source_or_totality"):
        current_theorem_status(local_bit_work_gap=None).require_complete()


def test_complete_bit_recurrence_for_current_paper_solver() -> None:
    """RED: all independent theorem obligations must be discharged.

    Numeric local terms, source/totality proofs and the Sudoku-cell
    exponent transfer are independently required. A partially filled
    ledger may not conceal non-refusal or the wrong input-size parameter.
    """
    frames = _active_symbolic_frames()
    local_gap: str | None = None
    try:
        unfold_conditional_bit_recurrence(frames, current_local_bit_evidence)
    except IncompleteBitBound as exc:
        local_gap = str(exc)
    current_theorem_status(local_bit_work_gap=local_gap).require_complete()
