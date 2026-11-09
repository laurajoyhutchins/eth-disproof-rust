"""ETH-002: exact rational clause encoding and tiny direct deformation."""
from __future__ import annotations

from fractions import Fraction
from itertools import product
from random import Random

import pytest

from non_exponential_sudoku.eth import (
    CNFFormula, Polynomial, ReferenceLimits, ReplacementForm, ReplacementSystem,
    clause_satisfaction_polynomial, count_bruteforce, deformation_polynomial,
)
from non_exponential_sudoku.runtime.budget import CapacityError

pytestmark = pytest.mark.checkpoint


def test_rational_polynomial_arithmetic_and_taylor_shift() -> None:
    with pytest.raises(TypeError, match='exact'):
        Polynomial((0.1,))  # type: ignore[arg-type]
    with pytest.raises(TypeError, match='exact'):
        Polynomial.constant(0.5)  # type: ignore[arg-type]
    with pytest.raises(TypeError, match='exact'):
        Polynomial.variable().scale(0.25)  # type: ignore[arg-type]
    with pytest.raises(TypeError, match='exact'):
        Polynomial.variable().evaluate(0.25)  # type: ignore[arg-type]
    p = Polynomial((Fraction(1, 3), Fraction(-1, 2), Fraction(2, 5), Fraction(0)))
    q = Polynomial((Fraction(-2, 7), Fraction(4, 9)))
    assert p.degree == 2
    assert (p * q).evaluate(Fraction(3, 2)) == p.evaluate(Fraction(3, 2)) * q.evaluate(Fraction(3, 2))
    assert (p + q).evaluate(Fraction(4, 3)) == p.evaluate(Fraction(4, 3)) + q.evaluate(Fraction(4, 3))
    assert (p - p) == Polynomial.constant(0)
    assert p.scale(Fraction(3, 7)).evaluate(3) == p.evaluate(3) * Fraction(3, 7)
    assert p.taylor(Fraction(2, 3), 1).coefficients == (p.evaluate(Fraction(2, 3)), Fraction(1, 30))
    for order in range(4):
        shifted = p.taylor(Fraction(5, 6), order)
        assert shifted == p.taylor(Fraction(5, 6), 10).truncate(order)
    with pytest.raises(ValueError):
        p.taylor(1, -1)
    with pytest.raises(ValueError):
        p.truncate(-1)


def test_clause_polynomial_truth_tables() -> None:
    f = CNFFormula(3, ((1, -2, 3),))
    rows = ReplacementSystem.identity(f).clauses[0]
    for values in product((0, 1), repeat=3):
        mask = sum(value << index for index, value in enumerate(values))
        actual = clause_satisfaction_polynomial(f.clauses[0], rows, mask)
        assert actual.degree == 0
        assert actual.at_zero == int(values[0] or not values[1] or values[2])
    assert clause_satisfaction_polynomial((), (), 0) == Polynomial.constant(0)


def custom_forms(formula: CNFFormula, rng: Random) -> ReplacementSystem:
    rows: list[tuple[ReplacementForm, ...]] = []
    for clause in formula.clauses:
        occurrences = []
        for lit in clause:
            polynomials = tuple(Polynomial((int(index == abs(lit) - 1),
                                             Fraction(rng.randrange(-2, 3), 3)))
                                for index in range(formula.nvars))
            occurrences.append(ReplacementForm(polynomials))
        rows.append(tuple(occurrences))
    return ReplacementSystem(tuple(rows))


def direct_scalar_deformation(formula: CNFFormula, replacements: ReplacementSystem,
                              t: Fraction) -> Fraction:
    """Numerically evaluate H(t) without using polynomial operators."""
    total = Fraction(0)
    for values in product((False, True), repeat=formula.nvars):
        product_value = Fraction(1)
        for clause, forms in zip(formula.clauses, replacements.clauses):
            false_value = Fraction(1)
            for lit, form in zip(clause, forms):
                linear = sum((poly.evaluate(t) for poly, value in zip(form.coefficients, values) if value),
                             Fraction(0))
                false_value *= 1 - linear if lit > 0 else linear
            product_value *= 1 - false_value
        total += product_value
    return total


def test_identity_replacement_is_exact_count() -> None:
    examples = (
        CNFFormula(0, ()), CNFFormula(0, ((),)), CNFFormula(4, ()),
        CNFFormula(2, ((1,), (-1,))),
        CNFFormula(3, ((1, 2), (-1, 3))),
        CNFFormula(3, ((1,), (-2, 3))),
    )
    for f in examples:
        deformation = deformation_polynomial(f)
        assert deformation.degree == 0
        assert deformation.at_zero == count_bruteforce(f)


def test_random_nontrivial_replacements_preserve_zero_and_numeric_evaluation() -> None:
    rng = Random(378)
    for nvars in range(1, 5):
        for _ in range(32):
            clauses = tuple(tuple(rng.choice((-1, 1)) * rng.randint(1, nvars)
                                  for _ in range(rng.randint(0, 3)))
                            for _ in range(rng.randint(0, 4)))
            formula = CNFFormula(nvars, clauses)
            forms = custom_forms(formula, rng)
            forms.validate(formula)
            poly = deformation_polynomial(formula, forms)
            assert poly.at_zero == count_bruteforce(formula)
            for center in (Fraction(-2, 3), Fraction(1, 2), Fraction(2, 1)):
                assert poly.evaluate(center) == direct_scalar_deformation(formula, forms, center)
                assert poly.taylor(center, poly.degree).at_zero == poly.evaluate(center)


def test_invalid_replacements_fail_closed() -> None:
    formula = CNFFormula(2, ((1, -2),))
    first, second = ReplacementSystem.identity(formula).clauses[0]
    with pytest.raises(ValueError, match='unit|original'):
        deformation_polynomial(formula, ReplacementSystem(((second, first),)))
    with pytest.raises(ValueError, match='nvars'):
        deformation_polynomial(formula, ReplacementSystem(((ReplacementForm((Polynomial.constant(1),)), second),)))
    with pytest.raises(ValueError, match='occurrence'):
        deformation_polynomial(formula, ReplacementSystem(((first,),)))
    with pytest.raises(ValueError, match='clause'):
        deformation_polynomial(formula, ReplacementSystem(()))


def test_reference_capacity_and_bit_length_refusals() -> None:
    formula = CNFFormula(2, ((1, 2),))
    with pytest.raises(CapacityError, match='assignment'):
        deformation_polynomial(formula, limits=ReferenceLimits(max_variables=1))
    with pytest.raises(CapacityError, match='operation'):
        deformation_polynomial(formula, limits=ReferenceLimits(max_operations=1))
    rng = Random(1)
    forms = custom_forms(formula, rng)
    with pytest.raises(CapacityError, match='degree'):
        deformation_polynomial(formula, forms, limits=ReferenceLimits(max_degree=0))
    with pytest.raises(CapacityError, match='bit'):
        deformation_polynomial(formula, forms, limits=ReferenceLimits(max_coefficient_bits=1))
    with pytest.raises(ValueError):
        ReferenceLimits(max_coefficient_bits=0)
