"""One feasibility rule shared by factor building, projections, sum and preflight.

The reference oracle is deliberately Cartesian and independent of the
production iterator. All differential cases are bounded small instances.
"""
from __future__ import annotations

from itertools import product
from random import Random

import pytest

from non_exponential_sudoku.contraction.admission import estimate_first_factor
from non_exponential_sudoku.contraction.planning import FactorSpec, FactorizationPlan
from non_exponential_sudoku.core.mode_assignments import (
    iter_mode_assignments, mode_domains,
)
from non_exponential_sudoku.core.modes import Mode, weighted_tuples
from non_exponential_sudoku.runtime.budget import CapacityError, ModeBudget
from non_exponential_sudoku.runtime.statistics import Counters

pytestmark = pytest.mark.checkpoint


def _oracle(modes: list[Mode], p: int, scope: tuple[int, ...],
            groups: tuple[int, ...]) -> tuple[tuple[int, ...], ...]:
    """Independent tiny exact Cartesian reference, including union of rows."""
    chosen = [modes[j] for j in scope]
    lengths = [min(len(m.rows), (p-1)//m.weight)+1 for m in chosen]
    capacities: dict[tuple[int, int], set[int]] = {}
    for mode in chosen:
        if mode.target in groups:
            capacities.setdefault((mode.target, mode.packet), set()).update(mode.rows)
    result = []
    for beta in product(*(range(q) for q in lengths)):
        if sum(mode.weight * b for mode, b in zip(chosen, beta)) >= p:
            continue
        if any(sum(b for mode, b in zip(chosen, beta)
                   if (mode.target, mode.packet) == key) > len(rows)
               for key, rows in capacities.items()):
            continue
        result.append(beta)
    return tuple(result)


@pytest.mark.parametrize('seed', range(20))
def test_shared_iterator_matches_independent_scoped_cartesian_oracle(seed: int) -> None:
    rng = Random(7501 + seed)
    for _ in range(25):
        p = rng.randint(1, 9)
        modes = [Mode(rng.randrange(3), 0, j, rng.randrange(4),
                      rng.randrange(3), rng.randrange(1, 5), (),
                      tuple(x for x in range(4) if rng.randrange(2)))
                 for j in range(rng.randrange(7))]
        indices = list(range(len(modes)))
        rng.shuffle(indices)
        scope = tuple(indices[:rng.randint(0, len(indices))])
        groups = tuple(g for g in range(3) if rng.randrange(2))
        expected = _oracle(modes, p, scope, groups)
        actual = tuple(iter_mode_assignments(
            modes, p, scope=scope, target_groups=groups))
        assert actual == expected
        if not groups and len(scope) == len(modes):
            if scope == tuple(range(len(modes))):
                assert tuple(weighted_tuples(modes, p)) == expected


def test_capacity_is_union_of_rows_and_source_modes_are_unrestricted() -> None:
    modes = [Mode(0, 0, j, 1, 0, 1, (), (0,)) for j in range(2)]
    assert tuple(iter_mode_assignments(modes, 4, target_groups=(0,))) == (
        (0, 0), (0, 1), (1, 0))
    assert tuple(iter_mode_assignments(modes, 4, target_groups=(1,))) == (
        (0, 0), (0, 1), (1, 0), (1, 1))
    # Factor construction must refuse on the fourth *feasible* state, not
    # on an infeasible raw-domain state.
    assert len(tuple(iter_mode_assignments(modes, 4, target_groups=(0,),
                                          max_states=3))) == 3
    with pytest.raises(CapacityError, match='factor size limit'):
        tuple(iter_mode_assignments(modes, 4, target_groups=(1,),
                                    max_states=3, capacity_error=CapacityError))


def _plan(*scopes: tuple[int, ...]) -> FactorizationPlan:
    return FactorizationPlan(
        tuple(FactorSpec(g, 0, s, None) for g, s in enumerate(scopes)),
        'whole', 0, 0, 0, 0)


def test_first_factor_preflight_uses_identical_packet_constraints() -> None:
    modes = [Mode(0, 0, j, 1, 0, 1, (), (0,)) for j in range(2)]
    plan = _plan((0, 1), ())
    accepted = estimate_first_factor(plan, modes, 4, max_child_evaluations=3,
                                     packet_row_caps=True)
    assert accepted.outcome == 'within_first_factor_limit'
    assert accepted.first_factor_assignments == 3
    refused = estimate_first_factor(plan, modes, 4, max_child_evaluations=3)
    assert refused.outcome == 'refused'
    assert refused.first_factor_assignments == 4
    # Early work caps are unknown rather than an invented refusal.
    unknown = estimate_first_factor(plan, modes, 4, max_child_evaluations=1,
                                    packet_row_caps=True, max_transitions=1)
    assert unknown.outcome == 'unknown'
    # Later factors do not constitute mandatory work.
    assert estimate_first_factor(_plan((), (0, 1)), modes, 4,
                                 max_child_evaluations=1).first_factor_assignments == 1


def test_resource_guard_charges_traversal_and_rejects_unbounded_scan() -> None:
    modes = [Mode(0, 0, j, 0, 1, 1, (), (0, 1)) for j in range(4)]
    budget = ModeBudget(stats=Counters(), max_operations=2)
    with pytest.raises(CapacityError, match='work limit'):
        tuple(iter_mode_assignments(modes, 9, work=budget.work))


def test_domains_must_be_canonical_subsets() -> None:
    m = Mode(0, 0, 0, 0, 1, 1, (), (0, 1))
    assert len(mode_domains([m], 4)[0]) == 3
    with pytest.raises(ValueError, match='domains'):
        tuple(iter_mode_assignments([m], 4, domains=(range(1, 2),)))
    with pytest.raises(ValueError, match='unique'):
        tuple(iter_mode_assignments([m], 4, scope=(0, 0)))
    with pytest.raises(ValueError, match='positive'):
        mode_domains([Mode(0, 0, 0, 0, 1, 0, (), (0,))], 4)


def test_large_mode_count_is_stack_independent() -> None:
    modes = [Mode(0, 0, j, 0, 1, 1, (), ()) for j in range(1600)]
    values = tuple(iter_mode_assignments(modes, 2, target_groups=(1,)))
    assert len(values) == 1
    assert values[0] == (0,) * len(modes)
