"""Reproducible, fair three-way exact ETH Taylor contraction comparison.

Run: PYTHONPATH=src:. python -m benchmarks.eth.three_way_contraction

Every arm receives the SAME canonical CNF, replacement system, certified
measurement design, rational center, Taylor order and Python runtime.
Strategies:
  - group-mask-elimination: separated Boolean differences then exact
    elimination of restricted *group* masks
  - boolean-variable-elimination: fuse differences before exact
    elimination over original Boolean variables
  - tensor-jet: direct exact truncated polynomial clause automata and
    valuation-safe tensor-train bond compression

This is a finite research benchmark, not literal manuscript admission.
The reference #SAT count is independently checked at T=0 for every
family. At small n an independent full deformation polynomial also
checks every reported Taylor coefficient.

Actual operand bit lengths are now observed in a separate second execution
for each completed arm. Every Fraction arithmetic primitive is replayed with
witnessed integer operands and a constructive schoolbook bit-cost bound,
including Euclidean gcd iterations and exact normalization. This is an
upper bound for the SPECIFIED rational reference computation only; not a
whole-program bound or measured CPython machine bit operations. Non-Fraction
integer arithmetic, hashing, allocation and Python overhead are outside
the bounded scope and explicitly reported. CapacityError is first-class.
"""
from __future__ import annotations

import gc
import json
import time
import tracemalloc
from fractions import Fraction
from typing import Any, Callable, Literal, TypeVar

from non_exponential_sudoku.eth import (
    CNFFormula, MeasurementDesign, Polynomial, ReplacementForm,
    ReplacementSystem, count_bruteforce, deformation_polynomial,
    taylor_coefficients_separated,
)
from non_exponential_sudoku.eth.parameters import audit_bounded_cnf
from non_exponential_sudoku.eth.taylor import TaylorLimits, TaylorResult
from non_exponential_sudoku.eth.tensor_jet import (
    TensorTaylorResult, contract_certified_taylor,
)
from non_exponential_sudoku.eth.tensor_train import TensorLimits
from non_exponential_sudoku.runtime.budget import CapacityError
from benchmarks.eth.rational_bit_accounting import trace_fraction_bit_work

Family = Literal["independent", "path", "clique", "alternating-path",
                 "matching-separated", "matching-paired"]
_Result = TypeVar("_Result", TaylorResult, TensorTaylorResult)
_CENTER = Fraction(1)


def _fibonacci(index: int) -> int:
    a, b = 0, 1
    for _ in range(index):
        a, b = b, a + b
    return a


def theoretical_count(family: str, groups: int) -> int:
    if type(groups) is not int or groups < 2:
        raise ValueError("at least two two-variable groups required")
    if family == "independent":
        return 3 ** groups
    if family == "path":
        return _fibonacci(groups + 2) * (1 << groups)
    if family in ("clique", "alternating-path"):
        return (groups + 1) * (1 << groups)
    if family in ("matching-separated", "matching-paired"):
        if groups % 2 or groups < 4:
            raise ValueError("matching needs an even number of groups >= 4")
        return 3 ** (groups // 2) * (1 << groups)
    raise ValueError("unknown CNF interaction family")


def build_family(
    family: str, groups: int,
) -> tuple[CNFFormula, MeasurementDesign, ReplacementSystem]:
    """Balanced manual certificates with identical local two-var domains.

    Positive clauses connect the FIRST variable of each selected group,
    while the second variable remains free in path/clique cases.
    Every occurrence substitutes (1+T/7)*x_original for its literal.
    Identity at T=0 makes independent Boolean #SAT a hard oracle.
    """
    theoretical_count(family, groups)  # also validates shape and family
    n = 2 * groups
    if family == "independent":
        clauses = tuple((2 * g + 1, 2 * g + 2) for g in range(groups))
    elif family == "path":
        clauses = tuple((2 * g + 1, 2 * (g + 1) + 1)
                        for g in range(groups - 1))
    elif family == "alternating-path":
        clauses = tuple((2 * g + 1, -(2 * (g + 1) + 1))
                        for g in range(groups - 1))
    elif family == "clique":
        clauses = tuple((2 * i + 1, 2 * j + 1)
                        for i in range(groups) for j in range(i + 1, groups))
    else:
        half = groups // 2
        clauses = tuple((2 * i + 1, 2 * (i + half) + 1)
                        for i in range(half))
    formula = CNFFormula(n, clauses)
    order = (
        tuple(g for i in range(groups // 2) for g in (i, i + groups // 2))
        if family == "matching-paired" else tuple(range(groups))
    )
    group_variables = tuple((2 * g, 2 * g + 1) for g in order)
    owner_by_variable = {
        variable: group_index
        for group_index, variables in enumerate(group_variables)
        for variable in variables
    }
    design = MeasurementDesign(
        groups=group_variables,
        clause_groups=tuple(owner_by_variable[abs(clause[0]) - 1]
                            for clause in formula.clauses),
        matrices=tuple(((1, 0), (0, 1)) for _ in group_variables),
        tau=Fraction(1, 2), D=1,
    )
    identity = ReplacementSystem.identity(formula)
    replacement = ReplacementSystem(tuple(
        tuple(ReplacementForm(tuple(
            Polynomial((1, Fraction(1, 7)))
            if i == abs(literal) - 1 else poly
            for i, poly in enumerate(form.coefficients)
        )) for literal, form in zip(clause, forms))
        for clause, forms in zip(formula.clauses, identity.clauses)
    ))
    replacement.validate(formula)
    return formula, design, replacement


def shared_limits(
    *, max_factor_entries: int = 256, max_tensor_bond: int = 64,
) -> tuple[TaylorLimits, TensorLimits]:
    """Shared coefficient/work refusal regime with distinct representations.

    Table *entries* and TT *bonds* are intentionally independent budgets:
    their dimensions are not commensurable. Both still cap rational bit
    growth and arithmetic units so an unintended exponential does not
    consume the entire host.
    """
    return (
        TaylorLimits(
            max_factor_entries=max_factor_entries,
            max_factor_total_entries=1_024,
            max_factor_work=50_000,
            max_jet_operations=400_000,
            max_coefficient_bits=2_048,
            max_taylor_pairs=4_096,
            max_group_assignments=100_000,
        ),
        TensorLimits(
            max_groups=12,
            max_group_masks=4,
            max_clauses=64,
            max_measurement_rows=64,
            max_bond=max_tensor_bond,
            max_core_entries=8_192,
            max_jet_coefficient_entries=32_768,
            max_rational_operations=400_000,
            max_coefficient_bits=2_048,
            max_taylor_order=3,
            max_replacement_degree=1,
        ),
    )


def _measured(
    evaluation: Callable[[], _Result],
) -> tuple[_Result | None, dict[str, Any]]:
    gc.collect()
    tracemalloc.start()
    start = time.perf_counter()
    refused: CapacityError | None = None
    result: _Result | None = None
    try:
        result = evaluation()
    except CapacityError as exc:
        refused = exc
    finally:
        seconds = time.perf_counter() - start
        _, peak = tracemalloc.get_traced_memory()
        tracemalloc.stop()
    shared: dict[str, Any] = {
        "elapsed_seconds": seconds,
        "peak_traced_bytes": peak,
    }
    if refused is not None:
        return None, {
            **shared,
            "status": "refused",
            "refusal_type": type(refused).__name__,
            "reason": str(refused),
            "arithmetic_work_units": None,
            "maximum_rational_coefficient_bits": None,
            "fraction_bit_accounting": {"status": "not-measured-on-capacity-refusal"},
        }
    if result is None:
        raise AssertionError("exact evaluator ended without result or CapacityError")
    return result, {**shared, "status": "exact"}


def _observed_rational_work(
    outcome: dict[str, Any],
    evaluation: Callable[[], _Result],
    expected: _Result,
    operations: int,
    bits: int,
) -> dict[str, Any]:
    """Replay and verify exact Fraction operands separately from timing.

    The reported constructive bit bound is for the observed rational
    primitives under a fully specified schoolbook implementation. It
    does NOT cover native CPython machine execution or all algorithmic
    integer work. Keep charged logical unit counters as separate data.
    """
    if operations < 0 or bits < 0:
        raise AssertionError("invalid exact arithmetic counters")
    replay, trace = trace_fraction_bit_work(evaluation)
    if type(replay) is not type(expected) or (
        replay.coefficients != expected.coefficients
    ):
        raise ArithmeticError("bit-accounting replay changed exact result")
    if replay.stats != expected.stats:
        raise ArithmeticError(
            "bit-accounting replay changed evaluator work or rank history"
        )
    return {
        **outcome,
        "arithmetic_work_units": operations,
        "maximum_rational_coefficient_bits": bits,
        "fraction_bit_accounting": {
            "status": "reference-arithmetic-bounded",
            **trace.report(),
        },
    }

def run_case(
    family: str, groups: int, order: int,
    *, max_factor_entries: int = 256, max_tensor_bond: int = 64,
) -> dict[str, Any]:
    """Return exact values or explicit capacity refusal for all three arms."""
    formula, design, replacement = build_family(family, groups)
    if type(order) is not int or order < 0 or order > 3:
        raise ValueError("Taylor order must lie between zero and three")
    exact_count = count_bruteforce(
        formula, max_variables=16, max_assignments=1 << 16,
    )
    if exact_count != theoretical_count(family, groups):
        raise ArithmeticError("family's independent count oracle disagrees")
    expected: tuple[Fraction, ...] | None = None
    if groups <= 3:
        full = deformation_polynomial(formula, replacement)
        if full.at_zero != exact_count:
            raise ArithmeticError("independent deformation origin changed #SAT")
        symbolic = full.taylor(_CENTER, order).coefficients
        expected = symbolic + (Fraction(0),) * (order + 1 - len(symbolic))
    taylor_limits, tensor_limits = shared_limits(
        max_factor_entries=max_factor_entries,
        max_tensor_bond=max_tensor_bond,
    )
    cases: dict[str, dict[str, Any]] = {}
    complete: list[tuple[str, tuple[Fraction, ...]]] = []
    for method in ("group-mask-elimination", "boolean-variable-elimination",
                   "tensor-jet"):
        if method == "tensor-jet":
            def tensor_evaluation() -> TensorTaylorResult:
                return contract_certified_taylor(
                    formula, design, replacement, at=_CENTER,
                    order=order, limits=tensor_limits,
                )
            result, basic = _measured(tensor_evaluation)
            if result is not None:
                if not isinstance(result, TensorTaylorResult):
                    raise AssertionError("tensor evaluator returned wrong result type")
                stats = result.stats
                basic = _observed_rational_work(
                    basic, tensor_evaluation, result,
                    stats.rational_operations, stats.maximum_coefficient_bits,
                )
                basic.update({
                    "work_counter_kind": "charged-rational-coefficient-operations",
                    "scope_basis": "ordered-tensor-cut",
                    "factor_scope_peak": None,
                    "factor_entries_peak": None,
                    "peak_bond_before_compression": stats.peak_bond_before_compression,
                    "peak_bond_after_compression": stats.peak_bond_after_compression,
                    "max_final_bond": max(stats.final_bonds, default=1),
                    "peak_core_entries": stats.peak_core_entries,
                    "peak_algebraic_coefficient_slots": (
                        stats.peak_core_entries * (order + 1)),
                    "final_bonds": list(stats.final_bonds),
                    "coefficients": [str(c) for c in result.coefficients],
                })
                complete.append((method, result.coefficients))
        else:
            strategy: Literal["eliminate", "fused"] = (
                "eliminate" if method == "group-mask-elimination" else "fused")
            def factor_evaluation() -> TaylorResult:
                return taylor_coefficients_separated(
                    formula, design, replacement, at=_CENTER,
                    order=order, summation=strategy, limits=taylor_limits,
                )
            result, basic = _measured(factor_evaluation)
            if result is not None:
                if not isinstance(result, TaylorResult):
                    raise AssertionError("factor evaluator returned wrong result type")
                stats = result.stats
                basic = _observed_rational_work(
                    basic, factor_evaluation, result,
                    stats.jet_operations, stats.max_coefficient_bits,
                )
                basic.update({
                    "work_counter_kind": "charged-jet-coefficient-operations",
                    "scope_basis": stats.factor_scope_basis,
                    "factor_scope_peak": stats.factor_scope_peak,
                    "factor_entries_peak": stats.factor_entries_peak,
                    "factor_assignments_tested": stats.factor_assignments_tested,
                    "factor_eliminations": stats.factor_eliminations,
                    "taylor_pairs": stats.taylor_pairs,
                    "peak_algebraic_coefficient_slots": (
                        stats.factor_entries_peak * (order + 1)),
                    "peak_bond_before_compression": None,
                    "peak_bond_after_compression": None,
                    "coefficients": [str(c) for c in result.coefficients],
                })
                complete.append((method, result.coefficients))
        cases[method] = basic

    for method, coefficients in complete:
        if expected is not None and coefficients != expected:
            raise ArithmeticError(
                f"{method} disagrees with independent full polynomial oracle")
        if any(coefficients != other for _, other in complete):
            raise ArithmeticError("three exact contractors returned different Taylor jets")

    admitted = audit_bounded_cnf(formula).admitted
    return {
        "family": family,
        "groups": groups,
        "formula_variables": formula.nvars,
        "formula_clauses": len(formula.clauses),
        "polynomial_order": order,
        "center": str(_CENTER),
        "exact_count": exact_count,
        "independent_deformation_oracle": expected is not None,
        "certified_measured_rows": sum(map(len, design.matrices)),
        "paper_parameter_admitted": admitted,
        "successes": len(complete),
        "refusals": 3 - len(complete),
        "strategies": cases,
    }


def probe() -> dict[str, Any]:
    """Bounded sparse-to-dense sequence; preserve all refusal outcomes."""
    work = [
        (family, groups, order)
        for groups, order in ((2, 2), (3, 2), (4, 1), (5, 1), (6, 0))
        for family in ("independent", "path", "clique",
                       "alternating-path")
    ]
    work += [
        (family, groups, order)
        for groups, order in ((4, 1), (6, 0))
        for family in ("matching-separated", "matching-paired")
    ]
    rows = [run_case(family, groups, order)
            for family, groups, order in work]
    return {
        "title": "three exact CNF contraction representations",
        "status": "finite-resource-evidence-not-worst-case-complexity-proof",
        "measurement_method": (
            "per-arm cold Python tracemalloc; setup excluded, exact "
            "center-specific certification included"
        ),
        "arithmetic_comparability": (
            "logical counters have different conventions; exact Fraction "
            "operands and Euclidean normalization are traced separately. "
            "reference_schoolbook_bit_steps_upper_bound is a constructive "
            "bound for a specified rational reference ALU only, NOT the "
            "total algorithm or measured CPython machine bit operations"
        ),
        "cases": rows,
    }


def main() -> None:
    print(json.dumps(probe(), indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
