"""Falsification probe for classical fused Taylor tables on coupled 3-CNF.

The source evaluator is eth/fused_taylor.py.  This research control uses
non-admitted, manually certified measurement designs and a degree-one
occurrence deformation.  A separate bounded structure audit follows the
evaluator's exact minimum-union-scope heuristic WITHOUT allocating tables.
It is not a paper-parameter execution or a general #SAT lower bound.

The cyclic family has an independent four-state transfer-matrix oracle;
the shuffled permutation family has a bounded full-cube oracle.
"""
from __future__ import annotations

import argparse
from collections.abc import Iterable
from dataclasses import asdict, dataclass
from fractions import Fraction
from itertools import product
import json
from pathlib import Path
from random import Random
from typing import Literal

from non_exponential_sudoku.elimination.scope_plan import inspect_scope
from non_exponential_sudoku.eth.cnf import CNFFormula
from non_exponential_sudoku.eth.design import MeasurementDesign
from non_exponential_sudoku.eth.polynomial import (
    ZERO, Polynomial, ReplacementForm, ReplacementSystem,
)
from non_exponential_sudoku.eth.taylor import TaylorLimits, taylor_coefficients_separated
from non_exponential_sudoku.runtime.budget import CapacityError
from reference.elimination_width import certify_dense_order

Family = Literal["cyclic", "shuffled"]
Jet1 = tuple[Fraction, Fraction]
_ZERO: Jet1 = (Fraction(0), Fraction(0))
_ONE: Jet1 = (Fraction(1), Fraction(0))
_CENTER = Fraction(1)


def coupled_formula(n: int, family: Family) -> CNFFormula:
    """n clauses, exactly three distinct positive literals per clause.

    The shuffled third permutation uses a *fixed* source seed and bounded
    retries, never an input-dependent oracle or guessed expansion theorem.
    """
    if type(n) is not int or n < 8:
        raise ValueError("coupled probe requires at least eight variables")
    third: tuple[int, ...]
    if family == "cyclic":
        third = tuple((i + 2) % n for i in range(n))
    elif family == "shuffled":
        rng = Random(20261109 + n)
        third = ()
        for _ in range(1024):
            candidate = list(range(n))
            rng.shuffle(candidate)
            if any(candidate[i] in (i, (i + 1) % n) for i in range(n)):
                continue
            triples = tuple(frozenset((i, (i + 1) % n, candidate[i]))
                            for i in range(n))
            if len(set(triples)) == n:
                third = tuple(candidate)
                break
        if not third:
            raise ArithmeticError("no valid deterministic permutation found")
    else:
        raise ValueError("unknown coupled family")

    formula = CNFFormula(n, tuple(
        (i + 1, (i + 1) % n + 1, third[i] + 1) for i in range(n)
    ))
    if len(formula.clauses) != n or any(len(clause) != 3 for clause in formula.clauses):
        raise AssertionError("normalization altered the claimed three-clause incidence")
    degrees = [0] * n
    for clause in formula.clauses:
        for literal in clause:
            degrees[literal - 1] += 1
    if any(degree != 3 for degree in degrees):
        raise AssertionError("three-permutation incidence changed")
    return formula


def coupled_deformation(
    formula: CNFFormula,
) -> tuple[MeasurementDesign, ReplacementSystem]:
    """Exact P_e,v(T)=(1+T/7)*x_v at every occurrence.

    The single group has no measurement rows and owns all clauses;
    it is a valid finite *manual* certificate, NOT the paper's
    r>=2 or tau main-body design.  Fusing ignores this grouping
    after certificate validation and performs variable elimination.
    """
    n = formula.nvars
    design = MeasurementDesign(
        groups=(tuple(range(n)),),
        clause_groups=(0,) * len(formula.clauses),
        matrices=((),), tau=Fraction(0), D=0,
    )
    scale = Polynomial((Fraction(1), Fraction(1, 7)))
    replacement = ReplacementSystem(tuple(
        tuple(
            ReplacementForm(tuple(
                scale if index == literal - 1 else ZERO
                for index in range(n)
            ))
            for literal in clause
        )
        for clause in formula.clauses
    ))
    replacement.validate(formula)
    return design, replacement


@dataclass(frozen=True, slots=True)
class FusedScopeAudit:
    family: Family
    variables: int
    max_initial_scope: int
    max_joined_scope: int
    max_dense_joined_entries: int
    initial_assignment_slots: int
    elimination_assignment_slots: int
    total_charged_assignment_slots: int
    order: tuple[int, ...]


def fused_scope_audit(
    formula: CNFFormula, replacements: ReplacementSystem, *,
    family: Family, center: Fraction = _CENTER, order: int = 1,
) -> FusedScopeAudit:
    """Exact dense scope geometry for this source's min-width order.

    Uses the same polynomial-truncated support criterion as fused_taylor,
    and inspect_scope for factor joins.  No 2**width table is allocated.
    Dynamic cancellations can only reduce actually retained supports,
    so this is an allocation/work *geometry*, NOT an abstract
    lower bound on every exact arithmetic representation.
    """
    replacements.validate(formula)
    nonzero: dict[Polynomial, bool] = {}
    scopes: list[tuple[int, ...]] = []
    for occurrences in replacements.clauses:
        active: set[int] = set()
        for occurrence in occurrences:
            for index, coefficient in enumerate(occurrence.coefficients):
                if coefficient not in nonzero:
                    shifted = coefficient.taylor(center, order)
                    nonzero[coefficient] = any(shifted.coefficients)
                if nonzero[coefficient]:
                    active.add(index)
        scopes.append(tuple(sorted(active)))

    initial = tuple(scopes)
    remaining = set(range(formula.nvars))
    ordering: list[int] = []
    while remaining:
        variable = min(remaining, key=lambda v: (
            len({other for scope in scopes if v in scope for other in scope}), v,
        ))
        next_scope = inspect_scope(variable, scopes)
        ordering.append(variable)
        remaining.remove(variable)
        if next_scope.incident:
            attached = set(next_scope.incident)
            scopes = [scope for i, scope in enumerate(scopes) if i not in attached]
            scopes.append(next_scope.output)

    certified = certify_dense_order(initial, (2,) * formula.nvars, ordering)
    # No isolated Boolean variables occur in these connected families.
    if any(not any(variable in scope for scope in initial)
           for variable in range(formula.nvars)):
        raise ValueError("this exact charge comparison requires no free variables")
    return FusedScopeAudit(
        family=family, variables=formula.nvars,
        max_initial_scope=max(map(len, initial), default=0),
        max_joined_scope=certified.max_joined_variables,
        max_dense_joined_entries=certified.max_joined_entries,
        initial_assignment_slots=certified.initial_factor_entries_upper,
        elimination_assignment_slots=certified.joined_assignments_upper,
        total_charged_assignment_slots=(
            certified.initial_factor_entries_upper + certified.joined_assignments_upper
        ),
        order=tuple(ordering),
    )


def _add(a: Jet1, b: Jet1) -> Jet1:
    return a[0] + b[0], a[1] + b[1]


def _mul(a: Jet1, b: Jet1) -> Jet1:
    return a[0] * b[0], a[0] * b[1] + a[1] * b[0]


def _clause_jet(bits: tuple[int, int, int], center: Fraction) -> Jet1:
    false_product = _ONE
    for bit in bits:
        false_term: Jet1 = (
            (Fraction(1) - (1 + center / 7), Fraction(-1, 7))
            if bit else _ONE
        )
        false_product = _mul(false_product, false_term)
    return _ONE[0] - false_product[0], -false_product[1]


def brute_force_center_jet(formula: CNFFormula, center: Fraction = _CENTER) -> Jet1:
    """Independent exact full-cube oracle; intentionally limited to n<=12."""
    n = formula.nvars
    if n > 12:
        raise CapacityError("independent brute-force jet oracle limited to twelve variables")
    total = _ZERO
    for assignment in product((0, 1), repeat=n):
        value = _ONE
        for clause in formula.clauses:
            bits = tuple(assignment[literal - 1] for literal in clause)
            assert len(bits) == 3
            value = _mul(value, _clause_jet((bits[0], bits[1], bits[2]), center))
        total = _add(total, value)
    return total


def cyclic_transfer_jet(n: int, center: Fraction = _CENTER) -> Jet1:
    """Independent constant-state exact H(center), H'(center) on cyclic triples.

    Trace(A**n) over the four pair states (x_i,x_(i+1)) counts every
    labelled cyclic Boolean assignment exactly once for n>=3.
    This is a polynomial-bit family control, NOT a universal CNF solver.
    """
    if type(n) is not int or n < 3:
        raise ValueError("cyclic transfer requires at least three variables")
    transition: list[list[Jet1]] = [[_ZERO] * 4 for _ in range(4)]
    for a, b, c in product((0, 1), repeat=3):
        transition[2 * a + b][2 * b + c] = _clause_jet((a, b, c), center)
    power: list[list[Jet1]] = [
        [(_ONE if i == j else _ZERO) for j in range(4)] for i in range(4)
    ]
    for _ in range(n):
        power = [[
            sum_jets(_mul(power[i][k], transition[k][j]) for k in range(4))
            for j in range(4)
        ] for i in range(4)]
    return sum_jets(power[i][i] for i in range(4))


def sum_jets(values: Iterable[Jet1]) -> Jet1:
    """A tiny independent additive reference for fixed-order dual numbers."""
    total = _ZERO
    for value in values:
        total = _add(total, value)
    return total


def run_case(
    n: int, family: Family, *, max_factor_entries: int = 1 << 10,
) -> dict[str, object]:
    """Run the real fused evaluator or return a structured capacity refusal."""
    formula = coupled_formula(n, family)
    design, replacements = coupled_deformation(formula)
    audit = fused_scope_audit(formula, replacements, family=family)
    result: dict[str, object] = {
        "scope": asdict(audit),
        "manuscript_step5_admitted": False,
        "source_evaluator": "eth.fused_taylor.contract_fused_taylor",
        "taylor_center": "1",
        "taylor_order": 1,
        "max_factor_entries": max_factor_entries,
        "status": "not_started",
    }
    try:
        observed = taylor_coefficients_separated(
            formula, design, replacements, at=_CENTER, order=1,
            summation="fused", limits=TaylorLimits(
                max_factor_entries=max_factor_entries,
                max_factor_total_entries=16_384,
                max_factor_work=5_000_000,
                max_jet_operations=5_000_000,
                max_coefficient_bits=8192,
            ),
        )
    except CapacityError as exc:
        result["status"] = "capacity_refusal"
        result["reason"] = str(exc)
    else:
        result["status"] = "exact"
        result["coefficients"] = tuple(str(x) for x in observed.coefficients)
        result["stats"] = asdict(observed.stats)
        if observed.stats.factor_scope_peak != audit.max_joined_scope:
            raise AssertionError("source fused scope and structural witness disagree")
        if observed.stats.factor_assignments_tested != audit.total_charged_assignment_slots:
            raise AssertionError("source fused slot charge and structural witness disagree")
        if n <= 12:
            independent = brute_force_center_jet(formula)
            if observed.coefficients != independent:
                raise AssertionError("source fused result differs from full-cube oracle")
            result["independent_full_cube"] = True
        if family == "cyclic":
            independent = cyclic_transfer_jet(n)
            if observed.coefficients != independent:
                raise AssertionError("source fused result differs from transfer matrix")
            result["independent_four_state_transfer"] = True
    return result


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--sizes", nargs="+", type=int, default=[8, 12, 16, 32, 64, 128])
    parser.add_argument("--max-factor-entries", type=int, default=1 << 10)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    rows: list[dict[str, object]] = []
    families: tuple[Family, Family] = ("cyclic", "shuffled")
    for family in families:
        for n in args.sizes:
            # A symbolic-only scope report at large sizes, never an
            # accidental huge exact execution of an exponential backend.
            if n > 32:
                formula = coupled_formula(n, family)
                _, replacements = coupled_deformation(formula)
                rows.append({
                    "scope": asdict(fused_scope_audit(formula, replacements, family=family)),
                    "status": "scope_only",
                    "manuscript_step5_admitted": False,
                })
            else:
                rows.append(run_case(n, family, max_factor_entries=args.max_factor_entries))
    output = json.dumps({
        "description": "finite, non-admitted fused-Taylor falsification; no uniform complexity claim",
        "results": rows,
    }, indent=2, sort_keys=True)
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(output + "\n")
    print(output)


if __name__ == "__main__":
    main()
