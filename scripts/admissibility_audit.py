"""Reproduce the finite Sudoku / Appendix-D admission checks as JSON."""
from __future__ import annotations

import argparse
import json
from pathlib import Path
from reference.admissibility import audit_sudoku_root, probe_sudoku_packing


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--box-orders", nargs="+", type=int, default=[2, 3, 4])
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    rows = []
    for b in args.box_orders:
        rows.append({
            "root_edges": audit_sudoku_root(b).as_record(),
            "root_vertices": audit_sudoku_root(b, parameterization="vertices").as_record(),
            "packing_probe": probe_sudoku_packing(b).as_record(),
        })
    report = {
        "status": "finite_counterfactual_audit_not_asymptotic_certificate",
        "paper_active_threshold_lambda": 131072,
        "paper_minimum_active_s_bit_length": 131072,
        "probe_geometry": {"r": 64, "a": 2, "t": 1, "mode_precision": 3},
        "cases": rows,
    }
    payload = json.dumps(report, indent=2, sort_keys=True) + "\n"
    if args.output is not None:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(payload)
    print(payload, end="")


if __name__ == "__main__":
    main()
