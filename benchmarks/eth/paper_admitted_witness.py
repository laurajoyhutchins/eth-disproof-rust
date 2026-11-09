"""Source-pinned symbolic main-body and concrete balancing witnesses.

Original paper and Lean implementation: pinned openai/math commit
4eaee87548250b2682affda7d05d947c05554bae.
This research artifact explicitly does NOT execute the enormous formula,
the manuscript algorithm, or the upstream Lean primitive machine.
"""
from __future__ import annotations

import argparse
from dataclasses import asdict
import json
from pathlib import Path
import sys
from typing import Any

from non_exponential_sudoku.eth.paper_admitted_witness import (
    LEAN_PATH, LEAN_SCOPE_PATH, LEAN_THEOREM, PAPER_COMMIT, PAPER_PATH,
    concrete_unit_balance_witness, virtual_unit_cnf_step5,
    unit_copy_partition,
)
from scripts.evidence import fingerprints, git_provenance


ROOT = Path(__file__).resolve().parents[2]


def experiment(
    lambda_bits: int = 1 << 34, finite_n: int = 4096,
) -> dict[str, Any]:
    """Produce both independent certificate levels, never a solver result."""
    source_before, git_before = fingerprints(), git_provenance()
    virtual = virtual_unit_cnf_step5(lambda_bits)
    finite = concrete_unit_balance_witness(finite_n)
    block = unit_copy_partition(finite)
    if not virtual.admitted_by_sufficient_conditions:
        raise ArithmeticError("symbolic Step-5 candidate is not admitted")
    if not finite.balancing_lemma_hypotheses or not finite.balancing_lemma_conclusions:
        raise ArithmeticError("finite balancing lemma witness failed")
    if finite.paper_step5_admitted:
        raise ArithmeticError("finite example was incorrectly attributed to Step 5")
    report: dict[str, Any] = {
        "schema_version": "1.0.0",
        "status": "incomplete",
        "source": {
            "paper_repo": "openai/math",
            "paper_commit": PAPER_COMMIT,
            "paper_source_path": PAPER_PATH,
            "paper_location": "Step 5; lemma incidence-labels; theorem main",
            "lean_implementation_path": LEAN_PATH,
            "lean_scope_path": LEAN_SCOPE_PATH,
            "lean_theorem": LEAN_THEOREM,
            "lean_claim": "fixed-width exact count theorem on primitive BitProgram",
        },
        "git": git_before,
        "input_fingerprints": source_before,
        "environment": {"python": sys.version},
        "virtual_step5": {
            **{key: value for key, value in asdict(virtual).items()
               if key != "checks"},
            "checks": [asdict(check) for check in virtual.checks],
            "admitted_by_sufficient_conditions": virtual.admitted_by_sufficient_conditions,
            "source_formula": "AND_{i=1}^{n} x_i; n=2**lambda",
            "mathematical_count": 1,
        },
        "finite_balance": {
            **{key: value for key, value in asdict(finite).items()
               if key not in ("variable_schedules", "clause_schedules")},
            "schedule_rule": (
                "a_v=(bit0(v),bit1(v)), "
                "d_e=(bit2(e),bit3(e)); e=v; zero-based labels"
            ),
            "incidence_labels_checked": finite.n,
            "physical_schedules_materialized": True,
            "full_spectral_replacements_materialized": False,
        },
        "finite_copy_partition": {
            "copy_count": block.copy_count,
            "max_copy_variables": block.max_copy_variables,
            "rank_upper_all_rational_centers": block.rank_upper_all_centers,
            "rank_upper_for_taylor_coefficient_order_2":
                block.taylor_coefficient_rank_upper(2),
            "block_boundary_rank_upper": block.block_boundary_rank_upper,
            "source_step4_explanation": (
                "Each unit-clause occurrence reads only the variables "
                "in its assigned auxiliary copy; grouping copies "
                "factorizes the deformed assignment tensor."
            ),
            "applies_to_virtual_unit_family_symbolically": True,
            "full_spectral_tensor_constructed": False,
            "claim": "source-derived upper bound, not measured global rank",
        },
        "claim_boundary": {
            "executed_lean_machine": False,
            "executed_virtual_cnf": False,
            "executed_paper_algorithm": False,
            "actual_formula_for_step5": False,
            "finite_lemma_schedule_proves_full_step5": False,
            "theorem_complexity_reproduced": False,
        },
    }
    report["inputs_stable"] = (
        source_before == fingerprints() and git_before == git_provenance()
    )
    report["status"] = "complete" if report["inputs_stable"] else "failed_input_drift"
    return report


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lambda-bits", type=int, default=1 << 34)
    parser.add_argument("--finite-n", type=int, default=4096)
    parser.add_argument("--output", type=Path,
                        default=ROOT / "artifacts/eth-paper-lean-admission.json")
    args = parser.parse_args()
    try:
        report = experiment(args.lambda_bits, args.finite_n)
    except Exception as exc:
        report = {
            "schema_version": "1.0.0",
            "status": "failed",
            "error": f"{type(exc).__name__}: {exc}",
        }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")
    print(f"Paper/Lean admission crosswalk: {report['status']}; {args.output}")
    return 0 if report["status"] == "complete" else 1


if __name__ == "__main__":
    raise SystemExit(main())
