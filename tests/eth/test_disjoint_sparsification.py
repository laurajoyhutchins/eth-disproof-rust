"""Disjoint-leaf partition and explicit numerical sparsification contracts."""
from __future__ import annotations

from fractions import Fraction
from importlib.util import find_spec
from random import Random

import pytest

from non_exponential_sudoku.eth import (
    CNFFormula, SparsificationLimits, count_bruteforce, count_ganak,
    iter_disjoint_leaves, paper_sparsification_parameters,
    prepare_bounded_cnf, reference_sparsification_parameters,
)
from non_exponential_sudoku.runtime.budget import CapacityError

pytestmark = pytest.mark.checkpoint


def _verify_disjoint(formula: CNFFormula, k: int, threshold: int) -> int:
    params = reference_sparsification_parameters(k, threshold)
    leaves = list(iter_disjoint_leaves(formula, params))
    assert leaves
    assert len({leaf.path for leaf in leaves}) == len(leaves)
    hits = [0] * (1 << formula.nvars)
    for leaf in leaves:
        assert leaf.formula.nvars == formula.nvars
        assert leaf.parameters is params
        assert max(map(len, leaf.formula.clauses), default=0) <= k
        count = 0
        for assignment in range(len(hits)):
            if leaf.formula.satisfied_mask(assignment):
                hits[assignment] += 1
                count += 1
        if find_spec("pyganak") is not None:
            assert count == count_ganak(leaf.formula)
        # Also exercise the disjoint->variable projection->bounded occurrence
        # count identity end to end. This is not running the ETH algorithm.
        prep = prepare_bounded_cnf(leaf.formula)
        if find_spec("pyganak") is not None:
            assert prep.restore_count(count_ganak(prep.formula)) == count
    assert hits == [int(formula.satisfied_mask(i)) for i in range(len(hits))]
    return len(leaves)


def test_repeated_shared_literal_branches_are_disjoint() -> None:
    f = CNFFormula(4, ((1, 2), (1, 3), (1, 4), (2, 3), (2, 4)))
    assert _verify_disjoint(f, k=3, threshold=2) > 1
    f2 = CNFFormula(5, ((-1, 2, 3), (-1, 2, 4), (-1, 2, 5),
                        (1, 3), (1, 4)))
    assert _verify_disjoint(f2, k=3, threshold=2) > 1


def test_randomized_disjoint_partition_including_unsat_and_free_bits() -> None:
    rng = Random(20261025)
    for _ in range(65):
        n = rng.randint(0, 6)
        if n:
            raw = tuple(tuple(rng.choice((-1, 1)) * rng.randint(1, n)
                              for _ in range(rng.randint(0, 4)))
                        for _ in range(rng.randint(0, 7)))
        else:
            raw = rng.choice(((), ((),)))
        f = CNFFormula(n, raw)
        _verify_disjoint(f, k=4, threshold=2)


def test_paper_parameter_search_is_exact_and_not_demo_threshold() -> None:
    for k, sigma in ((2, Fraction(1)), (3, Fraction(1)),
                     (3, Fraction(1, 3)), (4, Fraction(1, 2))):
        p = paper_sparsification_parameters(k, sigma)
        assert p.theorem_threshold
        assert p.sigma == sigma
        assert p.M >= p.gamma and p.M & (p.M - 1) == 0
        h = (4 * p.C * p.M - 1).bit_length()
        assert p.gamma * h * sigma.denominator <= sigma.numerator * p.M
        assert p.occurrence_bound <= 4 * p.M ** (k - 1)
        previous = p.M // 2
        if previous >= p.gamma:
            old_C = 4 * sum((3 * previous) ** j for j in range(k - 1))
            old_h = (4 * old_C * previous - 1).bit_length()
            assert p.gamma * old_h * sigma.denominator > sigma.numerator * previous
        # The theorem threshold is large enough that our toy examples do
        # not branch, but the count identity remains exact.
        f = CNFFormula(3, ((1, 2), (2, -3)))
        leaves = list(iter_disjoint_leaves(f, p))
        assert len(leaves) == 1
        assert count_bruteforce(leaves[0].formula) == count_bruteforce(f)
    assert paper_sparsification_parameters(3, Fraction(1)).M == 512


def test_explicit_refusals_for_limits_and_invalid_inputs() -> None:
    f = CNFFormula(4, ((1, 2), (1, 3), (1, 4)))
    p = reference_sparsification_parameters(3, 2)
    with pytest.raises(CapacityError, match='node limit'):
        list(iter_disjoint_leaves(f, p, limits=SparsificationLimits(max_nodes=1)))
    with pytest.raises(CapacityError, match='candidate work'):
        list(iter_disjoint_leaves(f, p, limits=SparsificationLimits(max_candidates_per_node=1)))
    with pytest.raises(CapacityError, match='clause limit'):
        list(iter_disjoint_leaves(f, p, limits=SparsificationLimits(max_clauses_per_node=1)))
    with pytest.raises(ValueError, match='width exceeds'):
        list(iter_disjoint_leaves(CNFFormula(3, ((1, 2, 3),)),
                                  reference_sparsification_parameters(2, 2)))
    with pytest.raises(CapacityError, match='parameter search'):
        paper_sparsification_parameters(3, Fraction(1),
                                        limits=SparsificationLimits(max_parameter_steps=1))
    for sigma in (Fraction(0), Fraction(2), 0.5):
        with pytest.raises(ValueError, match='sigma'):
            paper_sparsification_parameters(3, sigma)  # type: ignore[arg-type]
    with pytest.raises(ValueError, match='threshold'):
        reference_sparsification_parameters(3, 1)
    with pytest.raises(ValueError, match='k'):
        reference_sparsification_parameters(1, 2)
