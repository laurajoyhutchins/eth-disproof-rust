"""Exact tests of the unconditional FINAL output-height bound.

No fixture is represented as satisfying the literal paper-size admission
unless that status has been separately verified. The all-center bound is a
separate mathematical statement from constructibility or runtime totality.
"""
from __future__ import annotations

from fractions import Fraction
from math import prod
from random import Random

import pytest

from non_exponential_sudoku.eth.cnf import CNFFormula, count_bruteforce
from non_exponential_sudoku.eth.polynomial import (
    Polynomial, ReplacementForm, ReplacementSystem, deformation_polynomial,
)
from reference.eth_output_height import universal_deformation_output_height


def _deformed(formula: CNFFormula, seed: int) -> ReplacementSystem:
    rng = Random(seed)
    base = ReplacementSystem.identity(formula)
    return ReplacementSystem(tuple(
        tuple(ReplacementForm(tuple(
            poly + Polynomial((
                Fraction(0),
                Fraction(rng.randrange(-9, 10), rng.randrange(1, 14)),
                Fraction(rng.randrange(-9, 10), rng.randrange(1, 14)),
            ))
            for poly in form.coefficients))
            for form in clause)
        for clause in base.clauses
    ))


def _check_every_coefficient(
    formula: CNFFormula, replacements: ReplacementSystem,
    center: Fraction,
) -> None:
    proof = universal_deformation_output_height(formula, replacements, center)
    H = deformation_polynomial(formula, replacements)
    assert H.at_zero == count_bruteforce(formula)
    shifted = H.taylor(center, proof.output_degree_upper)
    assert shifted.degree <= proof.output_degree_upper
    # Test the stronger divisibility witness, not merely bit lengths.
    q = center.denominator
    Q = q ** proof.polynomial_degree * prod(
        coefficient.denominator
        for row in replacements.clauses
        for form in row
        for poly in form.coefficients
        for coefficient in poly.coefficients
    )
    denominator = Q ** proof.occurrences
    for coefficient in shifted.coefficients:
        assert denominator % coefficient.denominator == 0
        assert proof.covers(coefficient), (
            proof, coefficient.numerator.bit_length(),
            coefficient.denominator.bit_length(),
        )


@pytest.mark.integration
@pytest.mark.parametrize(("n", "clauses"), [
    (0, ()),
    (0, ((),)),
    (2, ((1, -1),)),
    (2, ((1,), (-1,))),
    (3, ((1, -2), (2, 3))),
])
def test_empty_signed_and_contradictory_output_height(
    n: int, clauses: tuple[tuple[int, ...], ...],
) -> None:
    f = CNFFormula(n, clauses)
    _check_every_coefficient(f, ReplacementSystem.identity(f), Fraction(-7, 9))


@pytest.mark.integration
@pytest.mark.parametrize("seed", list(range(18)))
def test_every_coefficient_against_independent_boolean_cube(seed: int) -> None:
    rng = Random(seed + 78401)
    n = 2 + seed % 4
    clauses = tuple(
        tuple(
            (v if rng.randrange(2) else -v)
            for v in rng.sample(range(1, n + 1), 1 + rng.randrange(min(3, n)))
        )
        for _ in range(2 + seed % 4)
    )
    formula = CNFFormula(n, clauses)
    replacement = _deformed(formula, 737 + seed)
    center = Fraction(rng.randrange(-7, 8), rng.randrange(1, 9))
    _check_every_coefficient(formula, replacement, center)


@pytest.mark.integration
def test_high_bit_denominators_are_input_charged_not_assumed_small() -> None:
    formula = CNFFormula(3, ((1, -2), (2, 3)))
    base = ReplacementSystem.identity(formula)
    giant = Fraction(10 ** 85 + 9, 10 ** 83 + 7)
    replacement = ReplacementSystem(tuple(
        tuple(ReplacementForm(tuple(
            poly + Polynomial((Fraction(0), giant))
            for poly in form.coefficients))
            for form in clause)
        for clause in base.clauses
    ))
    center = Fraction(-(10 ** 70 + 1), 10 ** 69 + 3)
    certificate = universal_deformation_output_height(formula, replacement, center)
    assert certificate.maximum_input_component_bits > 250
    _check_every_coefficient(formula, replacement, center)


@pytest.mark.integration
def test_actual_spectral_construction_is_covered_at_every_center() -> None:
    from benchmarks.eth.spectral_factor_width_probe import ring_formula
    from non_exponential_sudoku.eth import construct_bounded_designs

    f = ring_formula(6, width=2)
    actual = construct_bounded_designs(
        f, r=2, Q=2, R=2, schedule="conditional",
        representation="implicit", measurement_basis="projector",
    )
    assert actual.paper_admission is not None
    assert not actual.paper_admission.admitted
    for center, _design in actual.centers:
        _check_every_coefficient(f, actual.replacements, Fraction(center))


@pytest.mark.integration
def test_polynomial_final_output_coexists_with_exponential_dense_table() -> None:
    from reference.total_exact_cnf import count_total_reference

    k = 5
    clauses = tuple((i + 1, k + j + 1)
                    for i in range(k) for j in range(k))
    formula = CNFFormula(2 * k, clauses)
    replacements = ReplacementSystem.identity(formula)
    certificate = universal_deformation_output_height(
        formula, replacements, Fraction(1))
    counted = count_total_reference(formula)
    assert counted.count == (1 << (k + 1)) - 1
    assert certificate.covers(Fraction(counted.count))
    assert counted.stats.peak_single_factor_entries >= (1 << k)


@pytest.mark.integration
def test_output_height_requires_valid_replacement_and_exact_center() -> None:
    f = CNFFormula(2, ((1, 2),))
    r = ReplacementSystem.identity(f)
    with pytest.raises(TypeError):
        universal_deformation_output_height(f, r, 0.25)  # type: ignore[arg-type]
    with pytest.raises(ValueError, match="replacement"):
        universal_deformation_output_height(f, ReplacementSystem(()), 0)
