"""Same-input differential tests for three independent exact ETH contractors.

All operands are the same canonical CNF, center, replacement polynomials,
variable partition and certified integer measurement rows. This exercises
the *group-mask difference* path, the *Boolean-variable fused factor*
path, and the *tensor-train truncated polynomial* path. No implementation
is allowed to substitute the Boolean cube as a production fallback.
"""
from __future__ import annotations

from fractions import Fraction

import pytest

from benchmarks.eth.three_way_contraction import (
    build_family, run_case, shared_limits, theoretical_count,
)
from non_exponential_sudoku.eth import (
    count_bruteforce, deformation_polynomial, taylor_coefficients_separated,
)
from non_exponential_sudoku.eth.tensor_jet import contract_certified_taylor
from non_exponential_sudoku.runtime.budget import CapacityError


@pytest.mark.checkpoint
@pytest.mark.parametrize("family", ("independent", "path", "clique"))
def test_family_count_is_independent_exact_oracle(family: str) -> None:
    formula, _, replacements = build_family(family, 2)
    assert count_bruteforce(formula) == theoretical_count(family, 2)
    assert deformation_polynomial(formula, replacements).at_zero == count_bruteforce(formula)


@pytest.mark.integration
@pytest.mark.parametrize("family", ("independent", "path", "clique"))
@pytest.mark.parametrize("groups", (2, 3))
@pytest.mark.parametrize("order", (0, 1, 2))
def test_three_way_jets_match_independent_polynomial(
    family: str, groups: int, order: int,
) -> None:
    formula, design, replacements = build_family(family, groups)
    expected = deformation_polynomial(formula, replacements).taylor(Fraction(1), order)
    padded = expected.coefficients + (
        Fraction(0),
    ) * (order + 1 - len(expected.coefficients))
    taylor_limits, tensor_limits = shared_limits()
    group = taylor_coefficients_separated(
        formula, design, replacements, at=1, order=order,
        limits=taylor_limits, summation="eliminate",
    )
    fused = taylor_coefficients_separated(
        formula, design, replacements, at=1, order=order,
        limits=taylor_limits, summation="fused",
    )
    tensor = contract_certified_taylor(
        formula, design, replacements, at=1, order=order,
        limits=tensor_limits,
    )
    assert group.coefficients == fused.coefficients == tensor.coefficients == padded
    assert tensor.stats.final_bonds or groups == 1
    assert group.stats.factor_scope_basis == "groups"
    assert fused.stats.factor_scope_basis == "variables"
    assert all(value.denominator > 0 for value in tensor.coefficients)


@pytest.mark.integration
def test_benchmark_outcome_includes_noncomparable_work_and_memory_scopes() -> None:
    record = run_case("path", 2, 1)
    assert record["exact_count"] == theoretical_count("path", 2) == 12
    assert record["polynomial_order"] == 1
    assert record["formula_variables"] == 4
    assert record["certified_measured_rows"] == 4
    assert record["paper_parameter_admitted"] is False
    arms = record["strategies"]
    assert set(arms) == {"group-mask-elimination", "boolean-variable-elimination",
                         "tensor-jet"}
    assert all(outcome["status"] == "exact" for outcome in arms.values())
    assert arms["group-mask-elimination"]["scope_basis"] == "groups"
    assert arms["boolean-variable-elimination"]["scope_basis"] == "variables"
    assert arms["tensor-jet"]["scope_basis"] == "ordered-tensor-cut"
    assert arms["tensor-jet"]["peak_bond_before_compression"] >= 1
    for outcome in arms.values():
        assert outcome["peak_traced_bytes"] >= 0
        assert outcome["arithmetic_work_units"] >= 0
        assert outcome["maximum_rational_coefficient_bits"] > 0
        assert outcome["bit_work_proxy"] >= 0
        assert outcome["bit_work_proxy_is_actual_bit_operations"] is False


@pytest.mark.integration
def test_resource_limits_refuse_no_exponential_fallback() -> None:
    formula, design, replacements = build_family("clique", 4)
    taylor_limits, tensor_limits = shared_limits(
        max_factor_entries=1, max_tensor_bond=1,
    )
    with pytest.raises(CapacityError):
        taylor_coefficients_separated(
            formula, design, replacements, at=1, order=1,
            summation="eliminate", limits=taylor_limits,
        )
    with pytest.raises(CapacityError):
        taylor_coefficients_separated(
            formula, design, replacements, at=1, order=1,
            summation="fused", limits=taylor_limits,
        )
    with pytest.raises(CapacityError):
        contract_certified_taylor(
            formula, design, replacements, at=1, order=1,
            limits=tensor_limits,
        )


@pytest.mark.integration
def test_only_expected_capacity_refusals_become_benchmark_outcomes() -> None:
    row = run_case("clique", 4, 1, max_factor_entries=4, max_tensor_bond=2)
    assert row["exact_count"] == theoretical_count("clique", 4)
    for arm in row["strategies"].values():
        assert arm["status"] == "refused"
        assert arm["reason"]
        assert "capacity" in arm["refusal_type"].lower()


@pytest.mark.integration
@pytest.mark.parametrize("family", ("alternating-path",
                                    "matching-separated", "matching-paired"))
def test_signed_and_cut_adversarial_cases_preserve_three_way_exactness(
    family: str,
) -> None:
    groups = 4
    formula, design, replacements = build_family(family, groups)
    assert theoretical_count(family, groups) == count_bruteforce(formula)
    limits, tensor_limits = shared_limits()
    group = taylor_coefficients_separated(
        formula, design, replacements, at=1, order=1,
        summation="eliminate", limits=limits)
    fused = taylor_coefficients_separated(
        formula, design, replacements, at=1, order=1,
        summation="fused", limits=limits)
    tensor = contract_certified_taylor(
        formula, design, replacements, at=1, order=1,
        limits=tensor_limits)
    assert group.coefficients == fused.coefficients == tensor.coefficients


@pytest.mark.integration
def test_fixed_cut_tensor_bonds_depend_on_order_not_sat_count() -> None:
    separated = run_case("matching-separated", 4, 1)
    paired = run_case("matching-paired", 4, 1)
    assert separated["exact_count"] == paired["exact_count"]
    a = separated["strategies"]["tensor-jet"]
    b = paired["strategies"]["tensor-jet"]
    assert a["status"] == b["status"] == "exact"
    assert a["max_final_bond"] == 4
    assert b["max_final_bond"] == 2
    assert a["coefficients"] == b["coefficients"]
    # Factorized alternatives keep the same exact value under both
    # orderings and are not forced to inherit the tensor cut rank.
    for method in ("group-mask-elimination", "boolean-variable-elimination"):
        assert separated["strategies"][method]["status"] == "exact"
        assert paired["strategies"][method]["status"] == "exact"
        assert (separated["strategies"][method]["coefficients"] ==
                paired["strategies"][method]["coefficients"])
