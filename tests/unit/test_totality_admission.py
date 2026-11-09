"""TDD for conditional totality versus configured finite resource admission.

No test claims to execute astronomical instances or certify a Python callback.
"""
from __future__ import annotations

from itertools import product
from typing import Literal

import pytest

from non_exponential_sudoku.core.algebra import Padic, modulus_polynomial
from non_exponential_sudoku.core.modes import Mode
from non_exponential_sudoku.core.network import Network, simple_network, estimated_coefficient_bytes
from non_exponential_sudoku.elimination.engine import ModeEliminator
from non_exponential_sudoku.runtime.budget import CapacityError
from non_exponential_sudoku.runtime.config import ContractorConfig, LeafConfig, ModeLimits
from non_exponential_sudoku.runtime.statistics import Counters
from non_exponential_sudoku.contraction.engine import ContractionEngine
from reference.totality_admission import (
    BudgetNotMaterializable, exact_weighted_support, finite_mode_budget,
    terminal_budget, symbolic_terminal_budget, symbolic_mode_budget,
)

pytestmark = pytest.mark.checkpoint


def _independent_net(edges: int) -> Network:
    one: dict[tuple[int, ...], int] = {(0,): 1, (1,): 1}
    return simple_network(edges,
                          [((i,), one) for i in range(edges)],
                          [((i,), one) for i in range(edges)])


def _connected_cycle(n: int) -> Network:
    one: dict[tuple[int, ...], int] = {(0, 0): 1, (0, 1): 1, (1, 0): 1, (1, 1): 1}
    return simple_network(2*n,
        [((2*i, 2*i + 1), one) for i in range(n)],
        [((2*i + 1, 2*((i+1) % n)), one) for i in range(n)])


@pytest.mark.parametrize('edges', [0, 1, 6, 19])
def test_size_dependent_terminal_budget_guarantees_no_leaf_guard_refusal(edges: int) -> None:
    net = _independent_net(edges)
    template = ContractionEngine(ContractorConfig(s=max(edges, 2), precision=edges+2))
    ring = Padic(template.e, template.f, edges+2)
    witness = terminal_budget(net, ring)
    assert witness.max_width == max(edges, 1)
    assert witness.bytes_per_coefficient == estimated_coefficient_bytes(ring)
    leaf = witness.to_leaf_config()
    engine = ContractionEngine(ContractorConfig(
        s=max(edges, 2), precision=edges+2, schedule='paper', leaf=leaf))
    result = engine.contract(net)
    assert result == ring.scalar(1 << edges)
    assert leaf.max_factor_bytes >= (len(net.left)+len(net.right)+edges+2) * (1 << edges) * witness.bytes_per_coefficient
    if edges > 18:
        assert leaf.limit == edges


def test_terminal_budget_handles_connected_graph_and_reference() -> None:
    net = _connected_cycle(6)
    template = ContractionEngine(ContractorConfig(s=net.edges, precision=net.edges+2))
    ring = Padic(template.e, template.f, net.edges + 2)
    witness = terminal_budget(net, ring)
    leaf = witness.to_leaf_config()
    engine = ContractionEngine(ContractorConfig(
        s=net.edges, precision=ring.p, schedule='paper', leaf=leaf))
    assert engine.contract(net) == ring.scalar(1 << net.edges)
    # Exhaustive independent reference agrees, without relying on leaf width.
    assert net.direct(ring, net.edges) == ring.scalar(1 << net.edges)


def test_symbolic_terminal_budget_does_not_materialize_giant_table() -> None:
    net = _independent_net(100)
    ring = Padic(3, modulus_polynomial(3), 101)
    w = terminal_budget(net, ring)
    assert w.estimated_bytes_log2_ceiling > 100
    assert w.entries_log2_ceiling >= 100
    with pytest.raises(BudgetNotMaterializable):
        w.to_leaf_config()
    with pytest.raises(ValueError):
        w.to_leaf_config(max_exhaustive_bits=-1)


def _modes(weights: tuple[int, ...], rows: int = 1) -> list[Mode]:
    return [Mode(i, 0, 0, 0, 1, w, (), tuple(range(rows)))
            for i, w in enumerate(weights)]


@pytest.mark.parametrize('precision', [2, 4, 7])
@pytest.mark.parametrize('weights', [(1,), (1, 2), (1, 1, 2)])
def test_weighted_support_matches_independent_cartesian_count(
    precision: int, weights: tuple[int, ...],
) -> None:
    modes = _modes(weights, rows=2)
    actual = exact_weighted_support(modes, precision)
    brute = sum(
        sum(b*w for b, w in zip(beta, weights)) < precision
        for beta in product(*(range(min(2, (precision-1)//w)+1) for w in weights))
    )
    assert actual == brute


@pytest.mark.parametrize('join', ['sparse', 'enumerate'])
@pytest.mark.parametrize('weights', [(1,), (1, 2), (1, 1, 2), (1, 1, 1, 2)])
def test_sufficient_mode_limits_do_not_refuse_after_mode_catalog_exists(
    weights: tuple[int, ...], join: Literal["sparse", "enumerate"],
) -> None:
    precision = 4
    modes = _modes(weights)
    ring = Padic(3, modulus_polynomial(3), precision)
    bytes_per = max(64, (ring.e * ring.p + 7)//8 + 160)
    witness = finite_mode_budget(modes, factors=2, precision=precision,
                                 bytes_per_coefficient=bytes_per)
    assert witness.admissible_assignments == exact_weighted_support(modes, precision)
    assert witness.limits.max_child_contractions >= 2*witness.admissible_assignments
    stats = Counters()
    calls: list[tuple[int, ...]] = []

    def oracle(_group: int | tuple[int, int], _scope: tuple[int, ...], assignment: tuple[int, ...]) -> tuple[int, ...]:
        calls.append(assignment)
        return ring.one

    output = ModeEliminator(
        modes, {0, 1}, ring, oracle, stats, CapacityError,
        join_strategy=join, native_sparse=False, limits=witness.limits,
    ).run()
    assert output == ring.scalar(witness.admissible_assignments)
    assert len(calls) == 2*witness.admissible_assignments
    assert stats.mode_dp_local_child_evaluations == len(calls)
    assert stats.mode_dp_peak_factor_states <= witness.limits.max_live_terms
    assert stats.mode_dp_operations + stats.mode_dp_order_scans <= witness.limits.max_operations
    assert stats.mode_dp_peak_estimated_bytes <= witness.limits.max_estimated_bytes


def test_real_guard_refuses_when_one_required_child_exceeds_cap() -> None:
    modes = _modes((1, 1, 1, 1))
    ring = Padic(3, modulus_polynomial(3), 4)
    adequate = finite_mode_budget(modes, factors=2, precision=4,
                                 bytes_per_coefficient=192)
    stats = Counters()
    with pytest.raises(CapacityError, match='child-contraction limit'):
        ModeEliminator(
            modes, {0, 1}, ring, lambda *_: ring.one, stats, CapacityError,
            join_strategy='sparse', native_sparse=False,
            limits=ModeLimits(max_child_contractions=1),
        ).run()
    assert adequate.limits.max_child_contractions > 1


def test_budget_rejects_nonfinite_or_invalid_model_inputs() -> None:
    with pytest.raises(ValueError, match='positive integer precision'):
        exact_weighted_support([], 0)
    invalid = [Mode(0, 0, 0, 0, 1, 0, (), (0,))]
    with pytest.raises(ValueError, match='weights'):
        exact_weighted_support(invalid, 4)
    with pytest.raises(ValueError, match='positive factor'):
        finite_mode_budget(_modes((1,)), factors=0, precision=4,
                           bytes_per_coefficient=100)


@pytest.mark.parametrize('weights', [(1,), (1, 2), (1, 1, 2)])
def test_symbolic_mode_shape_dominates_finite_sufficient_limits(
    weights: tuple[int, ...],
) -> None:
    modes = _modes(weights, rows=2)
    exact = finite_mode_budget(modes, factors=3, precision=5,
                               bytes_per_coefficient=256)
    alpha = (exact.admissible_assignments - 1).bit_length()
    symbolic = symbolic_mode_budget(
        modes=len(modes), factors=3, precision=5,
        support_exponent=alpha, bytes_per_coefficient=256,
    )
    upper = symbolic.materialize()
    assert upper.max_factor_states >= exact.limits.max_factor_states
    assert upper.max_live_terms >= exact.limits.max_live_terms
    assert upper.max_operations >= exact.limits.max_operations
    assert upper.max_child_contractions >= exact.limits.max_child_contractions
    assert upper.max_estimated_bytes >= exact.limits.max_estimated_bytes
    assert (upper.max_factor_states - 1).bit_length() <= symbolic.max_factor_states_log2
    assert (upper.max_live_terms - 1).bit_length() <= symbolic.max_live_terms_log2
    assert (upper.max_operations - 1).bit_length() <= symbolic.max_operations_log2
    assert (upper.max_child_contractions - 1).bit_length() <= symbolic.max_child_contractions_log2
    assert (upper.max_estimated_bytes - 1).bit_length() <= symbolic.max_estimated_bytes_log2


def test_symbolic_paper_scale_requires_no_exponential_integer_allocation() -> None:
    # Here s has 131072 bits; a frame can require a genuinely enormous
    # terminal network. Compute log2 of sufficient factor storage without
    # constructing a Python integer with 2**s bits.
    s = (1 << 131071) + 1
    leaf_edges = s // 362
    terminal = symbolic_terminal_budget(
        edges=leaf_edges, vertices=s, bytes_per_coefficient=1024,
    )
    assert terminal.estimated_bytes_log2_ceiling > leaf_edges
    assert terminal.estimated_bytes_log2_ceiling < s
    with pytest.raises(BudgetNotMaterializable):
        terminal.to_leaf_config()
    alpha = s // 1000
    modes = s // 200
    symbolic = symbolic_mode_budget(
        modes=modes, factors=s, precision=s,
        support_exponent=alpha, bytes_per_coefficient=1024,
    )
    assert symbolic.max_operations_log2 >= 2*alpha
    assert symbolic.max_operations_log2 < s
    with pytest.raises(BudgetNotMaterializable):
        symbolic.materialize()


def test_symbolic_budget_rejects_invalid_shapes() -> None:
    with pytest.raises(ValueError):
        symbolic_terminal_budget(edges=-1, vertices=0, bytes_per_coefficient=1)
    with pytest.raises(ValueError):
        symbolic_mode_budget(modes=-1, factors=1, precision=4,
                             support_exponent=0, bytes_per_coefficient=64)
    with pytest.raises(ValueError):
        symbolic_mode_budget(modes=4, factors=1, precision=4,
                             support_exponent=-1, bytes_per_coefficient=64)


def test_explicit_exhaustive_reference_is_not_silent_fallback() -> None:
    net = _independent_net(5)
    engine = ContractionEngine(ContractorConfig(
        s=5, precision=7, schedule='paper',
        leaf=LeafConfig(strategy='enumerate', limit=2),
    ))
    with pytest.raises(CapacityError, match='Direct leaf'):
        engine.contract(net)
    result = engine.contract_complete(net)
    assert result == Padic(engine.e, engine.f, 7).scalar(32)


def test_finite_guard_budget_does_not_certify_arbitrary_oracle_body() -> None:
    from non_exponential_sudoku.core.network import Network, Vertex

    def broken(_bits: tuple[int, ...], _ring: object) -> tuple[int, ...]:
        raise RuntimeError('untrusted input oracle failed')

    net = Network([Vertex('broken', (), broken)], [], 0)
    engine = ContractionEngine(ContractorConfig(s=2, precision=3))
    ring = Padic(engine.e, engine.f, 3)
    budget = terminal_budget(net, ring).to_leaf_config()
    evaluator = ContractionEngine(ContractorConfig(s=2, precision=3, leaf=budget))
    with pytest.raises(RuntimeError, match='untrusted input oracle failed'):
        evaluator.contract(net)


def test_theorem_acceptance_remains_unproved_by_guard_budgets() -> None:
    from reference.whole_frame_recurrence import OPEN_PREMISES
    assert 'input_oracle_bit_contract_and_uniform_metadata' in OPEN_PREMISES
    assert 'resource_limits_do_not_refuse_valid_inputs' in OPEN_PREMISES
    assert 'working_set_and_allocation_bit_accounting' in OPEN_PREMISES


@pytest.mark.parametrize('join', ['sparse', 'enumerate'])
@pytest.mark.parametrize('precision', [2, 4, 6])
@pytest.mark.parametrize('count', [2, 4, 6])
def test_split_component_scopes_keep_global_budget_admissible(
    join: Literal['sparse', 'enumerate'], precision: int, count: int,
) -> None:
    """Overlapping factor scopes require joins, not independent factors."""
    ring = Padic(3, modulus_polynomial(3), precision)
    modes = _modes(tuple(1 + (j % 3) for j in range(count)))
    # Group 0 has one separate component per mode. Group 1 has one shared
    # factor involving all modes, so the global eliminator must join scopes.
    scopes: dict[tuple[int, int], tuple[int, ...]] = {(0, j): (j,) for j in range(count)}
    scopes[(1, 0)] = tuple(range(count))
    F = len(scopes)
    witness = finite_mode_budget(
        modes, factors=F, precision=precision,
        bytes_per_coefficient=max(64, (ring.e*ring.p + 7)//8 + 160),
    )
    stats = Counters()
    calls = 0

    def child(_group: int | tuple[int, int], _scope: tuple[int, ...],
              _assignment: tuple[int, ...]) -> tuple[int, ...]:
        nonlocal calls
        calls += 1
        return ring.one

    answer = ModeEliminator(
        modes, {0, 1}, ring, child, stats, CapacityError,
        factor_scopes=scopes, join_strategy=join, native_sparse=False,
        limits=witness.limits,
    ).run()
    assert answer == ring.scalar(witness.admissible_assignments)
    assert calls <= F*witness.admissible_assignments
    assert stats.mode_dp_peak_factor_states <= (F+count+1)*witness.admissible_assignments
    assert stats.mode_dp_operations + stats.mode_dp_order_scans <= witness.limits.max_operations
