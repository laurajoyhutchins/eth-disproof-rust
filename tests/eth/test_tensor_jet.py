"""Exact higher-order tensor Taylor tests against independent reference paths.

The truncated ring Q[z]/(z**(order+1)) has zero divisors. In particular,
a matrix whose constant coefficient is zero can have nonzero jet rank.
Every compression is checked as an exact ring identity, not by rational
constant-term pivoting.
"""
from __future__ import annotations

from fractions import Fraction

import pytest

from non_exponential_sudoku.eth import (
    BalanceLimits, CNFFormula, MeasurementDesign, Polynomial, ReplacementForm,
    ReplacementSystem, construct_bounded_designs, deformation_polynomial,
    taylor_coefficients_separated,
)
from non_exponential_sudoku.eth.taylor import Jet
from non_exponential_sudoku.eth.tensor_jet import (
    _JetBudget, _jet_column_factor, contract_certified_taylor,
)
from non_exponential_sudoku.eth.tensor_train import TensorLimits
from non_exponential_sudoku.runtime.budget import CapacityError


def _manual(formula: CNFFormula) -> MeasurementDesign:
    assert formula.nvars % 2 == 0
    groups = tuple((i, i + 1) for i in range(0, formula.nvars, 2))
    return MeasurementDesign(
        groups=groups,
        clause_groups=tuple((abs(c[0]) - 1) // 2 if c else 0
                            for c in formula.clauses),
        matrices=tuple(((1, 0), (0, 1)) for _ in groups),
        tau=Fraction(1, 2), D=1,
    )


def _deform(formula: CNFFormula) -> ReplacementSystem:
    identity = ReplacementSystem.identity(formula)
    return ReplacementSystem(tuple(
        tuple(ReplacementForm(tuple(
            poly + Polynomial((0, Fraction((e + 1) * (v % 3 - 1), 7),
                               Fraction((e + 2) * (v + 1), 19)))
            for v, poly in enumerate(form.coefficients)))
            for form in forms)
        for e, forms in enumerate(identity.clauses)
    ))


@pytest.mark.checkpoint
def test_nilpotent_pivot_matrix_factorizes_without_inverting_z() -> None:
    order = 3
    z = Jet((0, 1), order)
    z2 = z * z
    z3 = z * z2
    zero = Jet.constant(0, order)
    for matrix, expected_rank in (
        ([[z, z2], [z2, z3]], 1),
        ([[z, zero], [zero, z2]], 2),
        ([[zero, zero], [zero, zero]], 0),
    ):
        budget = _JetBudget(order, TensorLimits())
        left, right = _jet_column_factor(matrix, budget)
        assert len(right) == expected_rank
        for i in range(len(matrix)):
            for j in range(len(matrix[0])):
                reconstructed = sum(
                    (left[i][k] * right[k][j] for k in range(len(right))),
                    zero,
                )
                assert reconstructed == matrix[i][j]


@pytest.mark.integration
def test_zero_constant_tensor_is_not_discarded() -> None:
    formula = CNFFormula(2, ((1,),))
    replacement = ReplacementSystem(((
        ReplacementForm((Polynomial((1, -1)), Polynomial.constant(0))),
    ),))
    result = contract_certified_taylor(
        formula, _manual(formula), replacement, at=1, order=2)
    assert result.coefficients == (Fraction(0), Fraction(-2), Fraction(0))
    assert result.stats.peak_bond_after_compression >= 1


@pytest.mark.integration
def test_taylor_zero_order_agrees_with_scalar_tensor() -> None:
    from non_exponential_sudoku.eth.tensor_train import contract_certified_order_zero

    formula = CNFFormula(4, ((1, 3), (-2, 4)))
    original = contract_certified_order_zero(formula, _manual(formula), at=2)
    jet = contract_certified_taylor(formula, _manual(formula), at=2, order=0)
    assert jet.coefficients == (original.value,)


@pytest.mark.integration
@pytest.mark.parametrize("order", [1, 2, 3])
@pytest.mark.parametrize("at", [Fraction(1), Fraction(2, 3)])
def test_deformed_exact_jet_equals_independent_cube_and_taylor(
    order: int, at: Fraction,
) -> None:
    formula = CNFFormula(4, ((1, -3), (2, 4), (-1, 2, -4)))
    replacement = _deform(formula)
    design = _manual(formula)
    tensor = contract_certified_taylor(
        formula, design, replacement, at=at, order=order)
    cube = deformation_polynomial(formula, replacement).taylor(at, order)
    separated = taylor_coefficients_separated(
        formula, design, replacement, at=at, order=order,
        summation='eliminate',
    )
    assert tensor.coefficients == separated.coefficients
    assert tensor.coefficients == cube.coefficients + (
        Fraction(0),
    ) * (order + 1 - len(cube.coefficients))
    assert tensor.stats.maximum_coefficient_bits >= 1
    assert tensor.stats.rational_operations > 0


@pytest.mark.integration
@pytest.mark.parametrize("r,n,width,Q,R", [
    (2, 6, 2, 2, 2), (3, 6, 2, 2, 2),
])
def test_actual_spectral_construction_higher_order_jets(
    r: int, n: int, width: int, Q: int, R: int,
) -> None:
    from benchmarks.eth.spectral_factor_width_probe import ring_formula

    formula = ring_formula(n, width=width)  # type: ignore[arg-type]
    constructed = construct_bounded_designs(
        formula, r=r, Q=Q, R=R, schedule='conditional',
        measurement_basis='projector',
        balance_limits=BalanceLimits(
            max_domain_size=32, max_indicator_work=2_000_000,
        ),
    )
    for center, design in constructed.centers:
        actual = contract_certified_taylor(
            formula, design, constructed.replacements, at=center, order=1)
        reference = taylor_coefficients_separated(
            formula, design, constructed.replacements, at=center, order=1,
            summation='eliminate',
        )
        assert actual.coefficients == reference.coefficients


@pytest.mark.integration
def test_full_nilpotent_cross_group_factor_remains_exact() -> None:
    formula = CNFFormula(4, ((1, 3),))
    # At the center, the 3rd variable has coefficient zero, so its
    # higher-order z term is invisible to constant-term row rank.
    identity = ReplacementSystem.identity(formula)
    forms = list(identity.clauses[0])
    first = list(forms[0].coefficients)
    first[2] = Polynomial((0, 1))
    forms[0] = ReplacementForm(tuple(first))
    modified = ReplacementSystem((tuple(forms),))
    design = _manual(formula)
    actual = contract_certified_taylor(
        formula, design, modified, at=1, order=2)
    reference = deformation_polynomial(formula, modified).taylor(1, 2)
    assert actual.coefficients == reference.coefficients + (
        Fraction(0),
    ) * (3 - len(reference.coefficients))


@pytest.mark.integration
def test_dense_unfolding_jet_matrix_exact_factorization() -> None:
    from itertools import product

    order = 2
    zero = Jet.constant(0, order)
    z = Jet((0, 1), order)
    one = Jet.constant(1, order)
    # Matrices with nilpotents and nonunits; test exact U*V over ring.
    for matrix in (
        [[z, z * z, zero], [z * z, zero, z]],
        [[one, z], [z, one], [z * z, z]],
        [[zero, zero, zero], [zero, zero, zero]],
    ):
        left, right = _jet_column_factor(matrix, _JetBudget(order, TensorLimits()))
        for i, j in product(range(len(matrix)), range(len(matrix[0]))):
            assert sum(
                (left[i][k] * right[k][j] for k in range(len(right))),
                zero,
            ) == matrix[i][j]


@pytest.mark.integration
def test_jet_capacity_limits_refuse_without_approximation() -> None:
    formula = CNFFormula(4, ((1, 3), (2, 4)))
    design = _manual(formula)
    with pytest.raises(CapacityError, match="Taylor order"):
        contract_certified_taylor(
            formula, design, at=1, order=3,
            limits=TensorLimits(max_taylor_order=2))
    with pytest.raises(CapacityError, match="rational operation"):
        contract_certified_taylor(
            formula, design, at=1, order=1,
            limits=TensorLimits(max_rational_operations=1))
    with pytest.raises(CapacityError, match="bond"):
        contract_certified_taylor(
            formula, design, at=1, order=1, limits=TensorLimits(max_bond=1))


@pytest.mark.integration
@pytest.mark.parametrize("order", [1, 2, 3, 4])
def test_seeded_rectangular_nilpotent_factorizations(order: int) -> None:
    """Adversarial finite-ring matrices with nonunits and zero divisors."""
    from random import Random

    rng = Random(74601 + order)
    zero = Jet.constant(0, order)
    for rows, cols in ((2, 3), (3, 2), (3, 4), (4, 3)):
        for _ in range(8):
            matrix = [
                [Jet(tuple(rng.choice((-2, -1, 0, 0, 0, 1, 2))
                           for _ in range(order + 1)), order)
                 for _ in range(cols)]
                for _ in range(rows)
            ]
            budget = _JetBudget(
                order,
                TensorLimits(max_rational_operations=200_000),
            )
            left, right = _jet_column_factor(matrix, budget)
            assert len(right) <= min(rows, cols)
            for i in range(rows):
                for j in range(cols):
                    actual = sum(
                        (left[i][k] * right[k][j]
                         for k in range(len(right))),
                        zero,
                    )
                    assert actual == matrix[i][j]


@pytest.mark.integration
def test_tensor_jets_recover_exact_count_with_hermite_origin() -> None:
    from non_exponential_sudoku.eth.tensor_jet import count_origin_from_tensor_designs
    from non_exponential_sudoku.eth.interpolation import count_origin_from_manual_designs
    from non_exponential_sudoku.eth.cnf import count_bruteforce

    formula = CNFFormula(4, ((1, 3), (-2, 4)))
    design = _manual(formula)
    identity = ReplacementSystem.identity(formula)
    clauses = []
    for e, forms in enumerate(identity.clauses):
        deformed = []
        for form in forms:
            coefficients = list(form.coefficients)
            coefficients[e] = coefficients[e] + Polynomial((0, Fraction(1, 3)))
            deformed.append(ReplacementForm(tuple(coefficients)))
        clauses.append(tuple(deformed))
    replacement = ReplacementSystem(tuple(clauses))
    centers = ((Fraction(1), design), (Fraction(2), design))
    # Four degree-one literal occurrences give degree <= 4.
    # Two centers need three coefficients each for a unique interpolant.
    actual = count_origin_from_tensor_designs(
        formula, centers, replacement, order=2)
    reference = count_origin_from_manual_designs(
        formula, centers, replacement, order=2,
        summation='eliminate')
    assert actual.count == reference.count == count_bruteforce(formula)
    assert tuple(x.coefficients for x in actual.center_results) == tuple(
        x.coefficients for x in reference.taylor_data
    )
    assert actual.hermite_stats.total_conditions == 6


@pytest.mark.integration
def test_nilpotent_jet_is_essential_for_count_reconstruction() -> None:
    from non_exponential_sudoku.eth.tensor_jet import count_origin_from_tensor_designs

    formula = CNFFormula(2, ((1,),))
    replacement = ReplacementSystem(((
        ReplacementForm((Polynomial((1, -1)), Polynomial.constant(0))),
    ),))
    design = _manual(formula)
    recovered = count_origin_from_tensor_designs(
        formula, ((Fraction(1), design),), replacement, order=1)
    assert recovered.center_results[0].coefficients == (
        Fraction(0), Fraction(-2))
    assert recovered.count == 2


@pytest.mark.checkpoint
def test_tensor_hermite_checks_enough_conditions_and_centers() -> None:
    from non_exponential_sudoku.eth.tensor_jet import count_origin_from_tensor_designs

    formula = CNFFormula(2, ((1,),))
    design = _manual(formula)
    replacement = ReplacementSystem(((
        ReplacementForm((Polynomial((1, 1)), Polynomial.constant(0))),
    ),))
    with pytest.raises(ValueError, match='insufficient Hermite'):
        count_origin_from_tensor_designs(
            formula, ((Fraction(1), design),), replacement, order=0)
    with pytest.raises(ValueError, match='distinct'):
        count_origin_from_tensor_designs(
            formula, ((Fraction(1), design), (Fraction(1), design)),
            replacement, order=1)
    with pytest.raises(ValueError, match='nonzero'):
        count_origin_from_tensor_designs(
            formula, ((Fraction(0), design),), replacement, order=1)
