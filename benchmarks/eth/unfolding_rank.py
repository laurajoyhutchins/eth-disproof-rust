"""Source-pinned, bounded exact CNF tensor-rank obstruction experiment.

This *oracle* enumerates 2**n assignment cells. It certifies ranks for
specific variable cuts; it is not a candidate subexponential solver.
"""
from __future__ import annotations

import argparse
from dataclasses import asdict
from fractions import Fraction
import json
from pathlib import Path
import platform
import sys
from time import perf_counter_ns
from typing import Any

from non_exponential_sudoku.eth.cnf import CNFFormula, count_bruteforce
from non_exponential_sudoku.eth.construction import construct_bounded_designs
from non_exponential_sudoku.eth.polynomial import deformation_polynomial
from non_exponential_sudoku.eth.unfolding_rank import (
    RankLimits, crossing_pair_witness, rank_profile,
)
from scripts.evidence import fingerprints, git_provenance


ROOT = Path(__file__).resolve().parents[2]


def _profile(
    formula: CNFFormula, replacements: Any, at: int | Fraction,
    order: tuple[int, ...], limits: RankLimits,
) -> dict[str, Any]:
    start = perf_counter_ns()
    cuts = rank_profile(
        formula, replacements, at=at, variable_order=order, limits=limits,
    )
    return {
        "at": str(at),
        "order_1_based": [index + 1 for index in order],
        "ranks": [cut.rank for cut in cuts],
        "boundary_rank_upper": [cut.boundary_rank_upper for cut in cuts],
        "max_rank": max((cut.rank for cut in cuts), default=1),
        "matrix_cells_per_cut": 1 << formula.nvars,
        "charged_rational_operations": sum(cut.rational_operations for cut in cuts),
        "max_coefficient_bits": max((cut.max_coefficient_bits for cut in cuts), default=0),
        "elapsed_ns": max(1, perf_counter_ns() - start),
        "total_value": str(cuts[0].total_value) if cuts else None,
    }


def experiment(max_pairs: int = 4, *,
               limits: RankLimits = RankLimits()) -> dict[str, Any]:
    """Measure a proven ordering obstruction and a real ETH construction."""
    if type(max_pairs) is not int or max_pairs < 1:
        raise ValueError("max_pairs must be positive")
    if 2 * max_pairs > limits.max_variables:
        raise ValueError("rank-oracle variable budget too small for witness")
    before, git = fingerprints(), git_provenance()
    report: dict[str, Any] = {
        "schema_version": "1.0.0", "status": "incomplete",
        "source": before, "git": git,
        "environment": {"python": sys.version, "os": platform.platform()},
        "limits": asdict(limits), "pair_witnesses": [],
        "constructed_samples": [],
        "interpretation": {
            "rank": "minimum exact linear separation dimension at a specified cut",
            "scope": "one rational deformation center; not the complete truncated jet",
            "operations": "charged rational additions/multiplications/divisions; not bit operations",
            "totality": "explicit finite exponential oracle; no general non-refusal claim",
            "worst_case": "no non-exponential or polynomial worst-case algorithm established",
        },
    }
    for k in range(1, max_pairs + 1):
        formula, replacements = crossing_pair_witness(k)
        grouped = tuple(range(2 * k))
        interleaved = tuple(index for i in range(k) for index in (i, i + k))
        origin = _profile(formula, replacements, 0, grouped, limits)
        deformed = _profile(formula, replacements, 1, grouped, limits)
        reordered = _profile(formula, replacements, 1, interleaved, limits)
        if (origin["max_rank"] != 1
                or deformed["max_rank"] != 1 << k
                or reordered["max_rank"] != 2
                or origin["total_value"] != str(1 << k)
                or deformed["total_value"] != str(1 << (2 * k))):
            raise ArithmeticError("crossing-pair exact-rank identity not reproduced")
        report["pair_witnesses"].append({
            "pairs": k, "nvars": 2 * k, "original_cnf_count": 1 << k,
            "grouped_at_zero": origin,
            "grouped_at_one": deformed,
            "interleaved_at_one": reordered,
            "analytical_identity": "product_i(x_i + T*y_i)",
            "grouped_middle_rank_at_one": 1 << k,
            "interleaved_max_rank_at_one": 2,
        })
    formula = CNFFormula(3, ((1, 2), (2, 3)))
    construction = construct_bounded_designs(
        formula, r=2, Q=2, R=2, measurement_basis="projector",
    )
    polynomial = deformation_polynomial(formula, construction.replacements)
    if polynomial.at_zero != count_bruteforce(formula):
        raise ArithmeticError("constructed deformation changed original exact count")
    for center, _ in construction.centers:
        evidence = _profile(
            formula, construction.replacements, center,
            tuple(range(formula.nvars)), limits,
        )
        if evidence["total_value"] != str(polynomial.evaluate(center)):
            raise ArithmeticError("rank-cube sum disagrees with independent H(T)")
        report["constructed_samples"].append({
            "nvars": formula.nvars, "clauses": len(formula.clauses),
            "r_Q_R": [2, 2, 2], "center": str(center),
            "rank_profile": evidence,
            "independent_deformation_sum": str(polynomial.evaluate(center)),
        })
    report["inputs_stable"] = before == fingerprints() and git == git_provenance()
    report["status"] = "complete" if report["inputs_stable"] else "failed_input_drift"
    return report


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--max-pairs", type=int, default=4)
    parser.add_argument("--output", type=Path,
                        default=ROOT / "artifacts/eth-unfolding-rank.json")
    args = parser.parse_args()
    try:
        report = experiment(args.max_pairs)
    except Exception as exc:
        report = {"schema_version": "1.0.0", "status": "failed",
                  "error": f"{type(exc).__name__}: {exc}"}
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")
    print(f"Exact CNF tensor-unfolding rank: {report['status']}; {args.output}")
    return 0 if report["status"] == "complete" else 1


if __name__ == "__main__":
    raise SystemExit(main())
