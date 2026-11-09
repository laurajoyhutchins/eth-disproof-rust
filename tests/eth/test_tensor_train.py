"""Independent exact tests of the bounded order-zero tensor-train path."""
from __future__ import annotations

from fractions import Fraction

import pytest

from non_exponential_sudoku.eth import (
    CNFFormula, BalanceLimits, MeasurementDesign, Polynomial, ReplacementForm,
    ReplacementSystem, construct_bounded_designs, count_bruteforce,
    deformation_polynomial, taylor_coefficients_separated,
)
from non_exponential_sudoku.eth.tensor_train import (
    TensorLimits, _Budget, _column_factor, contract_certified_order_zero,
)
from non_exponential_sudoku.runtime.budget import CapacityError


def _manual(formula: CNFFormula) -> MeasurementDesign:
    if formula.nvars % 2:
        raise ValueError('fixture requires even variable count')
    groups = tuple((i, i + 1) for i in range(0, formula.nvars, 2))
    return MeasurementDesign(
        groups=groups,
        clause_groups=tuple(
            (abs(clause[0]) - 1) // 2 if clause else 0
            for clause in formula.clauses
        ),
        matrices=tuple(((1, 0), (0, 1)) for _ in groups),
        tau=Fraction(1, 2), D=1,
    )


@pytest.mark.checkpoint
def test_small_exact_tensor_contraction_equals_two_independent_oracles() -> None:
    formula = CNFFormula(4, ((1, -3), (2, 4), (-1, 2, -4)))
    design = _manual(formula)
    value = contract_certified_order_zero(formula, design, at=Fraction(2))
    old = taylor_coefficients_separated(
        formula, design, at=Fraction(2), order=0, summation='eliminate')
    assert value.value == old.coefficients[0] == count_bruteforce(formula)
    assert value.stats.maximum_clause_width == 3
    assert value.stats.theoretical_clause_bond_bound == 9
    assert value.stats.peak_bond_after_compression <= 4
    assert value.stats.rational_operations > 0
    assert value.stats.clause_count == 3


@pytest.mark.checkpoint
@pytest.mark.parametrize('clauses,count', [
    ((), 16), (((),), 0), (((1,),), 8), (((-2, 3),), 12),
])
def test_exact_tensor_contraction_handles_boolean_edge_cases(
    clauses: tuple[tuple[int, ...], ...], count: int,
) -> None:
    formula = CNFFormula(4, clauses)
    result = contract_certified_order_zero(formula, _manual(formula), at=1)
    assert result.value == count_bruteforce(formula) == count


@pytest.mark.integration
def test_tensor_rational_deformation_and_full_boolean_oracle() -> None:
    formula = CNFFormula(4, ((1, -3), (2, 4), (-1, 2, -4)))
    base = ReplacementSystem.identity(formula)
    deformed = ReplacementSystem(tuple(
        tuple(ReplacementForm(tuple(
            poly + Polynomial((0, Fraction((e + 1) * (v + 1), 9)))
            for v, poly in enumerate(form.coefficients)))
            for form in forms)
        for e, forms in enumerate(base.clauses)
    ))
    design = _manual(formula)
    for center in (Fraction(1), Fraction(2, 3), Fraction(-1, 2)):
        value = contract_certified_order_zero(
            formula, design, deformed, at=center)
        oracle = deformation_polynomial(formula, deformed).evaluate(center)
        sep = taylor_coefficients_separated(
            formula, design, deformed, at=center, order=0,
            summation='tuples')
        assert value.value == oracle == sep.coefficients[0]


@pytest.mark.integration
@pytest.mark.parametrize('r,n,width,Q,R', [
    (2, 6, 2, 2, 2), (3, 6, 2, 2, 2), (4, 8, 2, 2, 2),
    (3, 9, 3, 3, 2),
])
def test_actual_spectral_auxiliary_exact_tensor_values(
    r: int, n: int, width: int, Q: int, R: int,
) -> None:
    from benchmarks.eth.spectral_factor_width_probe import ring_formula

    formula = ring_formula(n, width=width)  # type: ignore[arg-type]
    constructed = construct_bounded_designs(
        formula, r=r, Q=Q, R=R, schedule='conditional',
        measurement_basis='projector',
        balance_limits=BalanceLimits(max_domain_size=32, max_indicator_work=2_000_000))
    for center, design in constructed.centers:
        tensor = contract_certified_order_zero(
            formula, design, constructed.replacements, at=center)
        separated = taylor_coefficients_separated(
            formula, design, constructed.replacements,
            at=center, order=0, summation='eliminate')
        assert tensor.value == separated.coefficients[0]
        assert tensor.stats.final_bonds
        assert max(tensor.stats.final_bonds) <= (1 << n)
        assert tensor.stats.maximum_coefficient_bits >= 1


@pytest.mark.integration
def test_tensor_bonds_equal_dense_unfolding_rank() -> None:
    formula = CNFFormula(6, ((1, 3), (-2, 5), (3, 6), (-4, 6)))
    design = _manual(formula)
    value = contract_certified_order_zero(formula, design, at=1)
    # Independent dense truth tensor serves ONLY as a tiny rank oracle.
    from non_exponential_sudoku.eth.tensor_train import _column_factor

    for cut in (1, 2):
        left_bits = sum(len(g) for g in design.groups[:cut])
        right_bits = sum(len(g) for g in design.groups[cut:])
        matrix = []
        for left in range(1 << left_bits):
            matrix.append([
                Fraction(int(formula.satisfied_mask(left | (right << left_bits))))
                for right in range(1 << right_bits)
            ])
        _, coordinates = _column_factor(matrix, _Budget(TensorLimits()))
        assert value.stats.final_bonds[cut - 1] == len(coordinates)


@pytest.mark.checkpoint
def test_tensor_budgets_refuse_without_approximate_fallback() -> None:
    formula = CNFFormula(4, ((1, 3), (2, 4)))
    design = _manual(formula)
    with pytest.raises(CapacityError, match='measurement row'):
        contract_certified_order_zero(
            formula, design, at=1,
            limits=TensorLimits(max_measurement_rows=1))
    with pytest.raises(CapacityError, match='group count'):
        contract_certified_order_zero(
            formula, design, at=1,
            limits=TensorLimits(max_groups=1))
    with pytest.raises(CapacityError, match='clause count'):
        contract_certified_order_zero(
            formula, design, at=1,
            limits=TensorLimits(max_clauses=1))
    with pytest.raises(CapacityError, match='group-mask'):
        contract_certified_order_zero(
            formula, design, at=1,
            limits=TensorLimits(max_group_masks=3))
    with pytest.raises(CapacityError, match='bond'):
        contract_certified_order_zero(
            formula, design, at=1,
            limits=TensorLimits(max_bond=1))
    with pytest.raises(CapacityError, match='operation'):
        contract_certified_order_zero(
            formula, design, at=1,
            limits=TensorLimits(max_rational_operations=1))
    with pytest.raises(CapacityError, match='coefficient bit'):
        contract_certified_order_zero(
            formula, design, at=1,
            limits=TensorLimits(max_coefficient_bits=1))


@pytest.mark.integration
def test_dense_group_graph_can_still_have_low_exact_tensor_rank() -> None:
    from benchmarks.eth.factor_width_obstruction import build_clique_witness
    from non_exponential_sudoku.eth.factor_width import audit_factor_width
    from non_exponential_sudoku.eth.design import certify_measurements

    witness = build_clique_witness(3, 2)
    cert = certify_measurements(
        witness.formula, ReplacementSystem.identity(witness.formula),
        witness.design, at=1)
    assert audit_factor_width(cert).complete_graph
    actual = contract_certified_order_zero(
        witness.formula, witness.design, at=1,
        limits=TensorLimits(max_bond=256))
    assert actual.value == witness.expected_count
    assert max(actual.stats.final_bonds) < 1 << witness.formula.nvars
