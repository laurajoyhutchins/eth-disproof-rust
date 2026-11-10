"""Quantitative-selector-basis proof and exact source correspondence.

Row-space equivalence is compared with the real implicit projected
construction, not a hand-authored spectral projector. The selector
subbasis always consists of ORIGINAL integer selector rows, never
large primitive Gram row combinations.
"""
from __future__ import annotations

from dataclasses import replace
from fractions import Fraction
from itertools import combinations
from random import Random

import pytest

from non_exponential_sudoku.eth import (
    CNFFormula, ConstructionLimits, certify_measurements,
    construct_bounded_designs, construct_from_schedules,
    count_bruteforce, count_from_constructed, deterministic_schedules,
)
from non_exponential_sudoku.eth.construction import construct_implicit_auxiliary
from non_exponential_sudoku.eth.design import _row_combination
from non_exponential_sudoku.eth.selector_subbasis import (
    independent_selector_rows, prune_selector_design,
)
from reference.eth_measurement_basis_equivalence import (
    compare_transferred_rowspaces,
)
from reference.eth_quantitative_selector import (
    certify_quantitative_selector_subbasis,
)


@pytest.mark.checkpoint
def test_projected_rref_can_exceed_original_selector_l1() -> None:
    # Independent integer selector witnesses: each has L1=3.
    # Their common primitive integer RREF is [1,0,-1,1],
    # [0,1,2,-1], whose second row has L1=4.
    source = ((-1, -1, -1, 0), (-1, 0, 1, -1))
    basis = independent_selector_rows(source, width=4, max_l1=3)
    assert basis.rows == source
    assert basis.stats.selected_rows == 2
    assert basis.stats.maximum_selected_l1 == 3
    from tests.eth.test_projected_gram import _old_fraction_rref
    rref = _old_fraction_rref([[Fraction(x) for x in row] for row in source])
    assert rref == ((1, 0, -1, 1), (0, 1, 2, -1))
    assert max(sum(map(abs, row)) for row in rref) == 4


@pytest.mark.checkpoint
@pytest.mark.parametrize("source", [
    (),
    ((0, 0, 0),),
    ((1, 0, 0), (1, 0, 0), (0, 0, 0)),
    ((1, 1, 0), (0, 1, 1), (1, 2, 1), (2, 3, 1)),
    ((-1, 0, 1), (0, -1, -1), (-1, -1, 0)),
])
def test_integer_selector_subbasis_preserves_exact_rowspace(
    source: tuple[tuple[int, ...], ...],
) -> None:
    result = independent_selector_rows(source, width=3)
    for row in source:
        assert _row_combination(result.rows, tuple(map(Fraction, row)))
    assert result.stats.selected_rows <= len(source)
    assert result.stats.maximum_selected_l1 <= result.stats.maximum_input_l1
    assert (result.stats.maximum_fraction_component_bits <=
            result.stats.fraction_component_bits_upper)
    assert result.stats.rank == len(result.rows)


@pytest.mark.integration
def test_seeded_selector_subbasis_exact_span_and_numerical_norm() -> None:
    rng = Random(752073)
    checked = 0
    for width in range(0, 7):
        for _ in range(24):
            rows = tuple(
                tuple(rng.randrange(-3, 4) for _ in range(width))
                for _ in range(3 + width)
            )
            result = independent_selector_rows(rows, width=width)
            assert result.stats.rank <= width
            for row in rows:
                assert _row_combination(
                    result.rows, tuple(Fraction(x) for x in row)
                ) or not any(row)
            assert result.stats.maximum_selected_l1 <= result.stats.maximum_input_l1
            checked += 1
    assert checked == 7 * 24


@pytest.mark.integration
@pytest.mark.parametrize(("n", "clauses", "Q", "R"), [
    (3, ((1, -2), (-1, 3), (2, 3)), 2, 2),
    (4, ((1, 2), (-1, 3), (2, -4)), 2, 2),
    (4, ((1, 2), (3, 4)), 3, 2),
    (4, (), 2, 1),
    (4, ((),), 2, 2),
])
def test_actual_selector_subbasis_inherits_rowspace_and_quantitative_l1(
    n: int, clauses: tuple[tuple[int, ...], ...], Q: int, R: int,
) -> None:
    formula = CNFFormula(n, clauses)
    a, d = deterministic_schedules(formula, r=2, Q=Q)
    selectors = construct_from_schedules(
        formula,
        construct_implicit_auxiliary(
            r=2, Q=Q, R=R, measurement_basis="selectors",
            limits=ConstructionLimits(max_measurement_rows=1000)),
        a, d, limits=ConstructionLimits(max_measurement_rows=1000),
    )
    projected = construct_from_schedules(
        formula,
        construct_implicit_auxiliary(
            r=2, Q=Q, R=R, measurement_basis="projector"),
        a, d, limits=ConstructionLimits(max_measurement_rows=1000),
    )
    compressed_centers = []
    saw_nonempty = False
    for center, old in selectors.centers:
        compact, stats = prune_selector_design(old)
        assert compact.groups == old.groups
        assert compact.clause_groups == old.clause_groups
        assert sum(map(len, compact.matrices)) <= sum(map(len, old.matrices))
        assert compact.D <= old.D
        assert compact.tau <= old.tau
        assert max((s.selected_rows for s in stats), default=0) <= n
        saw_nonempty |= any(s.selected_rows for s in stats)
        certify_measurements(formula, selectors.replacements, compact, at=center)
        compressed_centers.append((center, compact))
    compare_transferred_rowspaces(
        selectors.centers, tuple(compressed_centers))
    compare_transferred_rowspaces(
        projected.centers, tuple(compressed_centers))
    exact = count_bruteforce(formula)
    compressed = replace(selectors, centers=tuple(compressed_centers))
    assert count_from_constructed(
        formula, compressed, summation="fused",
    ) == exact
    assert count_from_constructed(
        formula, selectors, summation="fused",
    ) == exact
    assert count_from_constructed(
        formula, projected, summation="fused",
    ) == exact
    if clauses and all(clauses):
        assert saw_nonempty


@pytest.mark.integration
def test_conditional_source_balancing_preserves_subbasis_certificates() -> None:
    f = CNFFormula(4, ((1, -2), (2, 3), (-3, 4)))
    limits = ConstructionLimits(max_measurement_rows=1000)
    source = construct_bounded_designs(
        f, r=2, Q=2, R=2, schedule="conditional",
        measurement_basis="selectors", limits=limits,
    )
    compressed_centers = []
    for at, design in source.centers:
        reduced, _ = prune_selector_design(design)
        certify_measurements(f, source.replacements, reduced, at=at)
        compressed_centers.append((at, reduced))
    compare_transferred_rowspaces(
        source.centers, tuple(compressed_centers))


@pytest.mark.checkpoint
def test_symbolic_full_step5_quantitative_selector_bound_without_n_allocation() -> None:
    lam = 2 ** 34
    nu = (lam - 1).bit_length()
    r = (lam**0 if False else 1)  # exact value assigned below
    from math import isqrt
    r = isqrt(lam) // (nu * nu)
    Q = lam // (128 * nu)
    R = 4 * isqrt(lam)
    assert (r, Q, R) == (113, 3_947_580, 524_288)
    proof = certify_quantitative_selector_subbasis(
        lambda_bits=lam, nu_bits=nu, r=r, Q=Q, R=R)
    assert proof.row_count_sufficient
    assert proof.spectral_tail_sufficient
    assert proof.tail_from_hoeffding_exponent <= 1 - 256 * nu
    assert proof.row_ratio_dyadic_exponent <= -2
    assert proof.group_and_label_lemma_required
    assert proof.actual_projected_gram_l1_certified is False


@pytest.mark.checkpoint
def test_quantitative_certificate_rejects_unproved_premises() -> None:
    valid = {
        "lambda_bits": 2**34, "nu_bits": 34, "r": 113,
        "Q": 3_947_580, "R": 524_288,
    }
    for update in (
        {"Q": 30},
        {"R": 4},
        {"nu_bits": 33},
        {"r": 1},
        {"r": 2**34},
    ):
        with pytest.raises(ValueError):
            certify_quantitative_selector_subbasis(**(valid | update))
    with pytest.raises(ValueError):
        independent_selector_rows(((2, 0),), width=2, max_l1=1)
    with pytest.raises(ValueError):
        independent_selector_rows(((1, 0),), width=3)
