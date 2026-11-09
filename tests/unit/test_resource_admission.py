"""Small local factorization witness and safe resource admission boundaries."""
from __future__ import annotations

import pytest

from non_exponential_sudoku import (
    ContractionEngine, ContractorConfig, LeafConfig, ModeConfig, ModeLimits,
    CapacityError, Padic,
)
from non_exponential_sudoku.contraction.admission import estimate_first_factor
from non_exponential_sudoku.contraction.planning import FactorSpec, FactorizationPlan
from non_exponential_sudoku.core.modes import Mode, mode_catalog
from non_exponential_sudoku.core.network import simple_network
from non_exponential_sudoku.core.packing import pack

pytestmark = pytest.mark.checkpoint


def crossing(size: int):
    net = simple_network(size,
        [([j], {(0,): 1, (1,): 1}) for j in range(size)],
        [([j], {(0,): 1, (1,): 1}) for j in range(size)])
    packing = pack(net, 64, 2,
        (tuple((0, 0) for _ in range(size)),
         tuple((1, 0) for _ in range(size))))
    return net, packing


def test_tiny_exact_factorization_witness_before_scaling() -> None:
    size, precision = 2, 8
    net, packing = crossing(size)
    answers = []
    for factorization in ('whole', 'components'):
        engine = ContractionEngine(ContractorConfig(
            size, precision, schedule='geometry64',
            mode=ModeConfig(factorization=factorization),
            leaf=LeafConfig(strategy='eliminate')))
        ring = Padic(engine.e, engine.f, precision)
        modes = mode_catalog(net, packing, 1, precision)
        answers.append(engine.evaluate_deformation(
            net, packing, modes, 1, ring.basis(3), ring, 0))
        assert answers[-1] == ring.scalar(1 << size)
    assert answers[0] == answers[1]


def _mode(weight: int, rows: int) -> Mode:
    return Mode(packet=0, y0=0, b=0, source=0, target=1, weight=weight,
                tile=(), rows=tuple(range(rows)))


def _plan(scopes: tuple[tuple[int, ...], ...]) -> FactorizationPlan:
    return FactorizationPlan(
        tuple(FactorSpec(index, 0, scope, None) for index, scope in enumerate(scopes)),
        'whole', 0, 0, 0, 0)


def test_preflight_counts_only_mandatory_first_factor() -> None:
    modes = [_mode(1, 1) for _ in range(12)]
    plan = _plan((tuple(range(12)), ()))
    # At precision 3 exactly 1 + 12 + 66 = 79 assignments.
    assert estimate_first_factor(plan, modes, 3, max_child_evaluations=80).first_factor_assignments == 79
    refused = estimate_first_factor(plan, modes, 3, max_child_evaluations=78)
    assert refused.outcome == 'refused'
    assert refused.first_factor_assignments is not None and refused.first_factor_assignments > 78
    assert estimate_first_factor(plan, modes, 3, max_child_evaluations=80,
                                 max_transitions=1).outcome == 'unknown'
    # Enormous later factors cannot justify rejecting before evaluating an
    # earlier factor that might return an identically zero table.
    later = _plan(((), tuple(range(12))))
    result = estimate_first_factor(later, modes, 3, max_child_evaluations=1)
    assert result.outcome == 'within_first_factor_limit'
    assert result.first_factor_assignments == 1


def test_first_factor_refusal_precedes_child_evaluation() -> None:
    net, packing = crossing(2)
    engine = ContractionEngine(ContractorConfig(
        2, 8, schedule='geometry64',
        mode=ModeConfig(factorization='whole'),
        limits=ModeLimits(max_child_contractions=1)))
    ring = Padic(engine.e, engine.f, 8)
    modes = mode_catalog(net, packing, 1, 8)
    with pytest.raises(CapacityError, match='preflight'):
        engine.evaluate_deformation(net, packing, modes, 1, ring.basis(3), ring, 0)
    assert engine.stats.child_networks == 0
