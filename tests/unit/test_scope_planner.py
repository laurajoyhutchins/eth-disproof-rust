"""TDD contracts for pure structural elimination planning.

The reference keys below intentionally model the three pre-refactor
call sites; this test protects their ordering and isolated-variable
semantics independently of coefficient arithmetic.
"""
from __future__ import annotations

from math import prod
from random import Random

import pytest

pytestmark = pytest.mark.checkpoint

from non_exponential_sudoku.elimination.scope_plan import (
    EliminationScope,
    choose_min_domain,
    choose_min_width,
    inspect_scope,
)


def test_incident_scope_and_nonmutating_analysis() -> None:
    factors = [(0, 1), (1, 2), (2,)]
    original = [tuple(f) for f in factors]
    step = inspect_scope(1, factors)
    assert step == EliminationScope(
        variable=1,
        incident=(0, 1),
        joined=(0, 1, 2),
        output=(0, 2),
    )
    assert factors == original


def test_isolated_variable_explicit_semantics() -> None:
    step = inspect_scope(3, [(0, 1), (1, 2)])
    assert step.incident == ()
    assert step.joined == (3,)
    assert step.output == ()
    # A free Boolean leaf variable multiplies the count by two.
    assert choose_min_width({0, 1, 2, 3}, [(0, 1), (1, 2)]).variable == 3
    # ETH's formerly empty union scope makes isolated groups cheap.
    assert choose_min_domain(
        {0, 1, 2, 3}, [(0, 1), (1, 2)], (2, 3, 5, 7)
    ).variable == 3


def test_min_domain_uses_domain_product_not_scope_length() -> None:
    scopes = [(0, 1), (1, 2)]
    step = choose_min_domain({0, 1, 2}, scopes, (2, 4, 8))
    assert step.variable == 0
    assert step.joined == (0, 1)
    assert prod((2, 4)) == 8


@pytest.mark.parametrize("seed", range(20))
def test_leaf_and_taylor_keys_match_independent_legacy_formulas(seed: int) -> None:
    rng = Random(seed)
    n = rng.randrange(1, 8)
    scopes = [
        tuple(sorted(rng.sample(range(n), rng.randrange(n + 1))))
        for _ in range(rng.randrange(0, 10))
    ]
    scopes = [s for s in scopes if s]
    remaining = set(range(n))
    domains = tuple(rng.randrange(1, 6) for _ in range(n))

    def incident(v: int) -> list[int]:
        return [j for j, scope in enumerate(scopes) if v in scope]

    def legacy_width(v: int) -> tuple[int, int, int]:
        inc = incident(v)
        union = set().union(*(scopes[j] for j in inc)) if inc else set()
        return len(union) - 1, len(inc), v

    def legacy_domain(v: int) -> tuple[int, int, int]:
        inc = incident(v)
        union = set().union(*(scopes[j] for j in inc)) if inc else set()
        return prod(domains[j] for j in union), len(union), v

    width = choose_min_width(remaining, scopes)
    assert width.variable == min(remaining, key=legacy_width)
    assert width.incident == tuple(incident(width.variable))
    expected_output = tuple(sorted(
        set().union(*(scopes[j] for j in width.incident)) - {width.variable}
    )) if width.incident else ()
    assert width.output == expected_output

    domain = choose_min_domain(remaining, scopes, domains)
    assert domain.variable == min(remaining, key=legacy_domain)
    assert domain.incident == tuple(incident(domain.variable))


def test_variable_selection_is_deterministic_and_rejects_empty_input() -> None:
    assert choose_min_width({1, 0}, [(0, 1)]).variable == 0
    assert choose_min_domain({1, 0}, [(0, 1)], (2, 2)).variable == 0
    with pytest.raises(ValueError):
        choose_min_width(set(), ())
    with pytest.raises(ValueError):
        choose_min_domain(set(), (), ())


def test_domain_validation_fails_before_incorrect_planning() -> None:
    with pytest.raises(ValueError):
        choose_min_domain({0}, [(0,)], (0,))
    with pytest.raises(ValueError):
        choose_min_domain({0}, [(0,)], ())
