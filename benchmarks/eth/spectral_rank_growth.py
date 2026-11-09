"""Growing-family *actual spectral construction* cut-rank audit.

Separates:
  - a symbolic, ALL-T polynomial-support upper certificate;
  - exact rational rank on a fixed support-selected variable order;
  - exact globally best TT order for small n, using an exponential oracle;
  - construction refusals, without substituting a different algorithm.

None constitutes a growing-n worst-case bound or an efficient constructive
tensor-train factorization. This module never participates in solving.
"""
from __future__ import annotations

import argparse
from dataclasses import asdict
import json
from pathlib import Path
import platform
import sys
from time import perf_counter_ns
from typing import Any, Sequence

from benchmarks.eth.cnf_scaling import FAMILIES, scenario
from non_exponential_sudoku.eth.cnf import count_bruteforce
from non_exponential_sudoku.eth.construction import construct_bounded_designs
from non_exponential_sudoku.eth.polynomial import deformation_polynomial
from non_exponential_sudoku.eth.support_rank import (
    SupportRankLimits, minimax_uniform_support_order,
)
from non_exponential_sudoku.eth.unfolding_rank import (
    RankLimits, minimax_unfolding_order, rank_profile,
)
from non_exponential_sudoku.runtime.budget import CapacityError
from scripts.evidence import fingerprints, git_provenance


ROOT = Path(__file__).resolve().parents[2]
DEFAULT_FAMILIES = ("path", "matching", "clique")
DEFAULT_SIZES = (3, 4, 5, 6)
SCHEMA = "1.0.0"


def experiment(
    families: Sequence[str] = DEFAULT_FAMILIES,
    sizes: Sequence[int] = DEFAULT_SIZES, *,
    max_exact_n: int = 5,
    max_profile_n: int = 6,
    max_total_cases: int = 40,
) -> dict[str, Any]:
    """Evaluate only given fixed finite r=Q=R=2 spectral parameters.

    Construction may refuse. A failure in an independent exact oracle is
    a failed experiment, NOT a capacity-refused solver result.
    """
    if (not families or not sizes or any(f not in FAMILIES for f in families)
            or len(set(families)) != len(families)
            or len(set(sizes)) != len(sizes)
            or any(type(n) is not int or not 2 <= n <= 12 for n in sizes)
            or type(max_exact_n) is not int or not 0 <= max_exact_n <= 12
            or type(max_profile_n) is not int or not 0 <= max_profile_n <= 12
            or max_exact_n > max_profile_n
            or type(max_total_cases) is not int or max_total_cases < 1
            or len(families) * len(sizes) > max_total_cases):
        raise ValueError("Invalid bounded rank-growth experiment configuration")
    cases = []
    for family in families:
        for n in sizes:
            if family in ("matching", "xor_pairs") and n % 2:
                continue
            cases.append(scenario(family, n))
    if not cases:
        raise ValueError("No admissible family-size combinations")
    before, git = fingerprints(), git_provenance()
    report: dict[str, Any] = {
        "schema_version": SCHEMA, "status": "incomplete",
        "source": before, "git": git,
        "environment": {"python": sys.version, "os": platform.platform()},
        "settings": {
            "families": list(families), "sizes": list(sizes),
            "max_exact_n": max_exact_n, "max_profile_n": max_profile_n,
            "finite_parameters": {"r": 2, "Q": 2, "R": 2,
                                  "measurement_basis": "projector"},
            "paper_schedule": False,
        },
        "samples": [],
        "mathematical_claims": {
            "symbolic_support_bound_all_rational_centers": True,
            "bound_on_each_taylor_coefficient_order_j": "(j+1)*cut_support_bound",
            "uniform_rank_proved": False,
            "worst_case_nonexponential": False,
            "general_nonrefusal": False,
            "polynomial_time_order_discovery": False,
            "small_support_implies_small_bit_work": False,
        },
    }
    for case in cases:
        started = perf_counter_ns()
        row: dict[str, Any] = {
            "family": case.family, "nvars": case.nvars,
            "clauses": len(case.formula.clauses),
            "expected_model_count": case.expected_count,
            "status": "incomplete",
        }
        try:
            construction = construct_bounded_designs(
                case.formula, r=2, Q=2, R=2,
                measurement_basis="projector",
            )
        except CapacityError as exc:
            row["status"] = "construction_refusal"
            row["reason"] = f"{type(exc).__name__}: {exc}"
            row["duration_ns"] = max(1, perf_counter_ns() - started)
            report["samples"].append(row)
            continue

        row["finite_construction_status"] = construction.algorithm_status
        row["lemma_hypotheses_met"] = (
            construction.balancing.lemma_hypotheses_met
            if construction.balancing is not None else None
        )
        row["lemma_bounds_met"] = (
            construction.balancing.lemma_bounds_met
            if construction.balancing is not None else None
        )
        uniform = minimax_uniform_support_order(
            case.formula, construction.replacements,
            limits=SupportRankLimits(
                max_variables=12, max_subsets=4096,
                max_support_checks=500_000,
            ),
        )
        row["uniform"] = {
            "best_rank_upper": uniform.peak_rank_upper,
            "order_1_based": [v + 1 for v in uniform.variable_order],
            "per_cut_rank_upper": list(uniform.upper_rank_per_cut),
            "subset_cuts": uniform.cuts_examined,
            "support_checks": uniform.support_checks,
            "polynomial_terms_inspected": uniform.polynomial_terms_inspected,
            "valid_all_rational_T": True,
        }
        independent_polynomial = None
        if case.nvars <= max_exact_n:
            if count_bruteforce(case.formula) != case.expected_count:
                raise ArithmeticError("independent Boolean count mismatch")
            independent_polynomial = deformation_polynomial(
                case.formula, construction.replacements,
            )
            if independent_polynomial.at_zero != case.expected_count:
                raise ArithmeticError("constructed polynomial changed original #SAT")

        row["centers"] = []
        if case.nvars <= max_profile_n:
            for center, _design in construction.centers:
                profile = rank_profile(
                    case.formula, construction.replacements,
                    at=center, variable_order=uniform.variable_order,
                    limits=RankLimits(max_variables=12, max_cells=4096),
                )
                peak = max((x.rank for x in profile), default=1)
                if peak > uniform.peak_rank_upper:
                    raise ArithmeticError("actual rank exceeded universal upper")
                check: bool | None = None
                if independent_polynomial is not None:
                    check = bool(
                        profile and profile[0].total_value
                        == independent_polynomial.evaluate(center)
                    )
                    if not check:
                        raise ArithmeticError("tensor sum disagreed with independent H(T)")
                optimum_rank: int | None = None
                exact_order: list[int] | None = None
                exact_operations: int | None = None
                exact_bits: int | None = None
                if case.nvars <= max_exact_n:
                    optimum = minimax_unfolding_order(
                        case.formula, construction.replacements,
                        at=center, limits=RankLimits(max_variables=12),
                        max_cuts=4096,
                    )
                    optimum_rank = optimum.peak_rank
                    exact_order = [v + 1 for v in optimum.variable_order]
                    exact_operations = optimum.charged_rational_operations
                    exact_bits = optimum.max_coefficient_bits
                    if optimum_rank > peak:
                        raise ArithmeticError("global best rank exceeds observed order")
                row["centers"].append({
                    "center": str(center),
                    "support_order_rank_peak": peak,
                    "support_order_ranks": [x.rank for x in profile],
                    "support_order_charged_rational_operations": sum(
                        x.rational_operations for x in profile
                    ),
                    "support_order_max_coefficient_bits": max(
                        (x.max_coefficient_bits for x in profile), default=0
                    ),
                    "exact_best_rank": optimum_rank,
                    "exact_best_order_1_based": exact_order,
                    "exact_rank_charged_rational_operations": exact_operations,
                    "exact_rank_max_coefficient_bits": exact_bits,
                    "independent_deformation_check": check,
                    "uniform_upper_to_exact_ratio": (
                        str(uniform.peak_rank_upper) + "/" + str(optimum_rank)
                        if optimum_rank is not None else None
                    ),
                })
        row["status"] = "verified"
        row["duration_ns"] = max(1, perf_counter_ns() - started)
        report["samples"].append(row)

    report["construction_refusals"] = sum(
        x["status"] == "construction_refusal" for x in report["samples"]
    )
    report["verified_cases"] = sum(
        x["status"] == "verified" for x in report["samples"]
    )
    report["inputs_stable"] = before == fingerprints() and git == git_provenance()
    report["status"] = "complete" if report["inputs_stable"] else "failed_input_drift"
    return report


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--families", nargs="+", choices=FAMILIES,
                        default=list(DEFAULT_FAMILIES))
    parser.add_argument("--sizes", nargs="+", type=int, default=list(DEFAULT_SIZES))
    parser.add_argument("--max-exact-n", type=int, default=5)
    parser.add_argument("--max-profile-n", type=int, default=6)
    parser.add_argument("--output", type=Path,
                        default=ROOT / "artifacts/eth-spectral-rank-growth.json")
    args = parser.parse_args()
    try:
        report = experiment(
            args.families, args.sizes, max_exact_n=args.max_exact_n,
            max_profile_n=args.max_profile_n,
        )
    except Exception as exc:
        report = {
            "schema_version": SCHEMA, "status": "failed",
            "error": f"{type(exc).__name__}: {exc}",
        }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, sort_keys=True, indent=2) + "\n")
    print(f"Spectral uniform-support rank growth: {report['status']}; {args.output}")
    return 0 if report["status"] == "complete" else 1


if __name__ == "__main__":
    raise SystemExit(main())
