"""Numerical manuscript admission contracts, separate from toy construction."""
from __future__ import annotations

from fractions import Fraction
from math import floor, isqrt
from random import Random

import pytest

from non_exponential_sudoku.eth import (
    CNFFormula, PaperParametersUnavailable, audit_bounded_cnf,
    audit_paper_bounds, construct_bounded_designs,
    construct_paper_bounded_designs, count_bruteforce,
    count_from_constructed, derive_paper_parameters,
)
from non_exponential_sudoku.runtime.budget import CapacityError

pytestmark = pytest.mark.checkpoint


def test_literal_parameters_and_hermite_bound() -> None:
    for n in (1, 2, 3, 8, 17, 256, 1 << 17, 1 << 1200):
        p = derive_paper_parameters(n)
        assert p.lambda_bits == (n - 1).bit_length()
        assert p.nu_bits == ((p.lambda_bits - 1).bit_length() if p.lambda_bits else 0)
        assert p.R == 4 * (isqrt(p.lambda_bits) + (isqrt(p.lambda_bits) ** 2 < p.lambda_bits))
        if p.nu_bits:
            assert p.r == isqrt(p.lambda_bits) // (p.nu_bits ** 2)
            assert p.Q == p.lambda_bits // (128 * p.nu_bits)
        if p.defined:
            assert p.D == p.r ** (2 * p.Q)
            assert p.tau == Fraction(1, p.r * p.lambda_bits)
            assert p.q == 3 * n * p.R // p.Q
            assert p.J == p.q + 1
            assert p.Q * p.J > 3 * n * p.R
            assert p.interval_start == floor(
                Fraction(p.Q * (p.r - 1), 2 * p.r) - Fraction(p.R - 1, 2))
        else:
            assert p.tau is None and p.q is None and p.J is None


def test_large_integer_parameters_do_not_create_variable_arrays() -> None:
    # n itself is a large symbolic parameter here, not a real CNF allocation.
    n = 1 << (2**20)
    p = derive_paper_parameters(n)
    assert p.lambda_bits == 2**20
    assert p.r == 2
    assert p.Q == 409
    assert p.R == 4096
    assert p.D == 2**818
    assert not audit_paper_bounds(n, n, b=3, w=3).admitted


def test_exact_paper_bounds_report_every_missing_premise() -> None:
    inputs = (
        CNFFormula(3, ((1, 2),)),
        CNFFormula(3, ((1, 2), (-1, 2))),
        CNFFormula(2, ((1, 2), (1, -2), (-1, 2))),
        CNFFormula(3, ()),
        CNFFormula(3, ((),)),
        CNFFormula(4, ((1, 2, 3, 4),)),
        CNFFormula(4, ((1, 2), (1, -2), (1, 3), (1, -3))),
    )
    for f in inputs:
        admission = audit_bounded_cnf(f)
        assert not admission.admitted
        assert admission.failures
        assert len(dict(admission.conditions)) == len(admission.conditions)
        assert all(not dict(admission.conditions)[name] for name in admission.failures)
        with pytest.raises(PaperParametersUnavailable, match='prerequisites not met'):
            admission.require()
        with pytest.raises(PaperParametersUnavailable):
            construct_paper_bounded_designs(f)
    assert 'three_occurrences_and_width_three' in audit_bounded_cnf(inputs[-1]).failures
    assert 'incidence_range' in audit_bounded_cnf(inputs[3]).failures


def test_toy_constructor_remains_exact_but_reports_paper_refusal() -> None:
    rng = Random(8252026)
    for _ in range(12):
        n = rng.randint(2, 4)
        clauses = tuple(tuple(rng.choice((-1, 1)) * rng.randint(1, n)
                              for _ in range(rng.randint(0, 3)))
                        for _ in range(rng.randint(0, 3)))
        f = CNFFormula(n, clauses)
        c = construct_bounded_designs(f, r=2, Q=2, R=2)
        assert c.paper_admission is not None
        assert not c.paper_admission.admitted
        assert count_from_constructed(f, c) == count_bruteforce(f)


def test_parameters_validate_inputs_and_integer_budget() -> None:
    for bad in (-1, True, 1.0):
        with pytest.raises(ValueError):
            derive_paper_parameters(bad)  # type: ignore[arg-type]
    assert not derive_paper_parameters(0).defined
    with pytest.raises(ValueError, match='max_integer_bits'):
        derive_paper_parameters(1, max_integer_bits=0)
    with pytest.raises(ValueError, match='nonnegative'):
        audit_paper_bounds(3, -1, b=3, w=3)
    with pytest.raises(CapacityError, match='integer-size'):
        derive_paper_parameters(1 << (2**20), max_integer_bits=100)
