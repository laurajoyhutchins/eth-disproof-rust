"""Reachability TDD against an independently enumerated row transition model.

This is a combinatorial theorem about *one* prepared packet's coefficient
update, including those from the literal paper schedule; it is not a proof
about global mode elimination or subexponential generalized Sudoku.
"""
from __future__ import annotations

from random import Random

import pytest

from non_exponential_sudoku.contraction.engine import paper_schedule_parameters
from non_exponential_sudoku.core.modes import Mode, mode_catalog, weighted_tuples
from non_exponential_sudoku.core.packing import pack
from reference.sudoku_network_oracle import port_graph_with_cross_mode
from non_exponential_sudoku.runtime.config import ContractorConfig
from reference.packet_oracle_work import packet_evaluation_envelope
from reference.paper_mode_reachability import (
    PAPER_EXPONENT_DENOMINATOR,
    paper_mode_count_ceiling, paper_packet_state_exponents,
    reachable_state_ceiling, reachable_transition_ceiling, uniform_paper_packet_bound,
)

pytestmark = pytest.mark.checkpoint


def independent_reachable(
    beta: tuple[int, ...], rows: tuple[tuple[int, ...], ...],
) -> tuple[set[tuple[int, ...]], ...]:
    """Literal row-by-row finite reference, without using binomial formula."""
    current = {(0,) * len(beta)}
    trace = [current]
    for choices in rows:
        nxt = set(current)
        for key in current:
            for target in choices:
                if key[target] < beta[target]:
                    raised = list(key)
                    raised[target] += 1
                    nxt.add(tuple(raised))
        current = nxt
        trace.append(current)
    return tuple(trace)


def test_reachable_state_bound_against_independent_exhaustion() -> None:
    rng = Random(73281)
    for k in range(5):
        for rows_count in range(7):
            for _ in range(15):
                beta = tuple(rng.randrange(4) for _ in range(k))
                rows = tuple(tuple(i for i in range(k) if rng.randrange(2))
                             for _ in range(rows_count))
                trace = independent_reachable(beta, rows)
                for j, states in enumerate(trace):
                    assert len(states) <= reachable_state_ceiling(beta, j)
                    assert all(sum(a) <= j for a in states)
                    assert all(all(0 <= a <= b for a, b in zip(key, beta))
                               for key in states)
                actual_transitions = sum(
                    len(trace[j]) * (1 + len(rows[j])) for j in range(rows_count)
                )
                ceiling = reachable_transition_ceiling(beta, tuple(map(len, rows)))
                assert actual_transitions <= ceiling


def test_one_row_defeats_cartesian_multiplicity_count() -> None:
    beta = (1,) * 60
    assert reachable_state_ceiling(beta, 0) == 1
    assert reachable_state_ceiling(beta, 1) == 61
    assert reachable_state_ceiling(beta, 2) == 1891
    assert reachable_transition_ceiling(beta, (60,)) == 61
    assert independent_reachable(beta, (tuple(range(60)),))[-1] == (
        {(0,) * 60} | {
            tuple(int(j == i) for j in range(60)) for i in range(60)
        }
    )


def test_orthogonal_modes_still_have_exponential_local_states_in_rows() -> None:
    for k in (1, 2, 5, 9):
        beta = (1,) * k
        rows = tuple((i,) for i in range(k))
        assert len(independent_reachable(beta, rows)[-1]) == 2 ** k
        assert reachable_state_ceiling(beta, k) == 2 ** k
    # The theorem bounds k by a sublinear L in *network input size*,
    # not by log(L); 2**L is not polynomial in L.


def test_prepared_one_row_packet_uses_reachable_not_cartesian_transition_bound() -> None:
    """Tie many multiplicity-one modes to a single row in the actual evaluator."""
    from non_exponential_sudoku.contraction.packets import PacketEntry, PacketGeometry, PacketModeTerms
    from non_exponential_sudoku.core.algebra import Padic, modulus_polynomial

    ring = Padic(3, modulus_polynomial(3), 8)
    k = 12
    target = tuple((Mode(0, 0, 0, 0, 1, 1, (), (0,)), 1) for _ in range(k))
    entry = object.__new__(PacketEntry)
    entry.R = ring
    entry.work_ring = ring
    entry.native = None
    entry.geometry = PacketGeometry({}, (0,), (), (), ((0, 0, ((1, 0),)),), {})
    entry.terms = PacketModeTerms(
        active=target, target=target, source=(), desired=(1,) * k,
        contributions={0: tuple((i, ring.one) for i in range(k))},
        tile_slots=(), tile_bits=(),
    )
    entry.cauchy = {0: ring.one}
    envelope = packet_evaluation_envelope(entry)
    assert envelope.coefficient_states == (1 << k)
    assert envelope.table_transitions == k + 1  # versus naive (1+k)*2**k
    assert entry._evaluate_python((1, 1)) == ring.zero  # impossible all-target exponent


def test_weight_constraint_alone_does_not_bound_global_assignment_count() -> None:
    """This is a MODE-DOMAIN counterexample, not a paper-admitted packing.

    A putative global subexponential conclusion cannot follow solely from
    positive weights and each mode's own row-cap. Factor graph constraints
    must be used in a separate elimination-width or support argument.
    """
    for k in (1, 4, 8, 11):
        modes = [Mode(i, 0, 0, 0, 1, 1, (), (0,)) for i in range(k)]
        assert sum(1 for _ in weighted_tuples(modes, k + 1)) == 2 ** k


def test_actual_catalog_modes_respect_one_packet_precision_and_slot_bound() -> None:
    net = port_graph_with_cross_mode()
    packing = pack(net, 2, 1, (((0,),), ((1,),)))
    for precision in (3, 9, 17):
        for center in (-1, 1):  # eligible center valuations are strictly below a
            modes = mode_catalog(net, packing, center, precision)
            for packet_id in range(len(packing.packets)):
                for target in range(2):
                    k = sum(m.packet == packet_id and m.target == target for m in modes)
                    assert k <= paper_mode_count_ceiling(precision, 1 << packing.a)
                    assert all(0 <= m.y0 < (1 << packing.a) for m in modes)
                    assert all(len(m.rows) <= (1 << packing.a) for m in modes)


def test_negative_packet_endpoint_is_excluded_before_mode_catalog() -> None:
    """At t=-L the valuation exceeds the number of group-label digits.

    The engine must never ask mode_catalog to read groups[g][a]; its
    order=q=ceil(3M/u)*max(0,u-v2(t)) is already zero at that center.
    """
    from non_exponential_sudoku.core.algebra import v2
    for lam in (131072, 262144, 524288, 1_048_576):
        s = (1 << (lam - 1)) + 1
        for depth in range(5):
            _, a, u, _ = paper_schedule_parameters(s, lam, depth)
            if u:
                assert a >= 2 * u
                L = 1 << a
                assert v2(-L) == a >= u
                assert max(0, u - v2(-L)) == 0  # no mode catalog for -L
                for t in (-L + 1, -1, 1, L - 1):
                    if t and v2(t) < u:
                        assert v2(t) < a  # valid group-label digit index


def test_paper_schedule_slot_exponent_is_uniformly_sublinear() -> None:
    # The proof is a finite-geometric-series argument; the symbolic tests
    # ensure implementation schedule and claimed constants agree even for
    # sizes that cannot be constructed as physical Sudoku boards.
    for lam in (131071, 131072, 131073, 262144, 524288, 1_048_576, 2_097_152):
        s = (1 << (lam - 1)) + 1
        for d in range(7):
            _, a, u, _ = paper_schedule_parameters(s, lam, d)
            if u:
                assert PAPER_EXPONENT_DENOMINATOR * a < lam
                assert a >= 2
                assert (1 << a) <= (1 << ((lam - 1) // PAPER_EXPONENT_DENOMINATOR))


def test_symbolic_paper_path_has_subexponential_local_packet_state_exponent() -> None:
    # Conditional on input edges<=s and precision<=s. Existing paper
    # precision-envelope proof bounds every paper-generated child precision.
    for lam in (131072, 262144, 524288):
        s = (1 << (lam - 1)) + 1
        cfg = ContractorConfig(s=s, precision=33, schedule='paper')
        frames = paper_packet_state_exponents(cfg, edges=s, vertices=s)
        assert frames
        for frame in frames:
            assert frame.log2_reachable_states_ceiling >= 0
            assert frame.target_modes_ceiling == (frame.precision - 1) * frame.slots
            # Very loose finite-size comparison, not an experimental limit
            # proof. The mathematical exponent gap is 1 - 1/32768.
            assert frame.log2_reachable_states_ceiling < s


def test_uniform_paper_state_proof_encloses_actual_symbolic_frames() -> None:
    for lam in (131072, 262144, 524288, 1_048_576):
        s = (1 << (lam - 1)) + 1
        overall = uniform_paper_packet_bound(s=s, initial_edges=s, initial_precision=33)
        assert overall.maximum_slots >= 4
        assert overall.log2_local_state_ceiling < s
        cfg = ContractorConfig(s=s, precision=33, schedule='paper')
        for frame in paper_packet_state_exponents(cfg, edges=s, vertices=s):
            assert frame.slots <= overall.maximum_slots
            assert frame.precision <= overall.maximum_precision
            assert frame.log2_reachable_states_ceiling <= overall.log2_local_state_ceiling


def test_uniform_packet_claim_rejects_unbounded_input_precision() -> None:
    with pytest.raises(ValueError, match='p0<=s'):
        uniform_paper_packet_bound(s=10, initial_edges=5, initial_precision=11)
    with pytest.raises(ValueError, match='M0<=s'):
        uniform_paper_packet_bound(s=10, initial_edges=11, initial_precision=5)
    with pytest.raises(ValueError, match='exact integers'):
        uniform_paper_packet_bound(s=10.0, initial_edges=2, initial_precision=1)  # type: ignore[arg-type]


def test_reachability_helper_refuses_invalid_proof_inputs() -> None:
    with pytest.raises(ValueError):
        reachable_state_ceiling((-1,), 2)
    with pytest.raises(ValueError):
        reachable_state_ceiling((1,), -1)
    with pytest.raises(ValueError):
        reachable_transition_ceiling((1,), (2,))
    with pytest.raises(ValueError):
        paper_mode_count_ceiling(0, 4)
    with pytest.raises(ValueError):
        paper_mode_count_ceiling(4, 3)
    with pytest.raises(ValueError):
        paper_packet_state_exponents(ContractorConfig(s=8, precision=3, schedule='micro'), edges=4, vertices=4)
