"""Sudoku-derived structural comparison of mode and lifted packet routes.

No Sudoku solution search, dense unit materialization, or mode-tuple
enumeration occurs here. Distinguish input-factor necessary width from
full induced elimination width, and support cardinality from runtime.
"""
from __future__ import annotations

import argparse
import json
from math import comb
from pathlib import Path
from typing import Any

from non_exponential_sudoku.sudoku.direct_network import DirectNetwork
from non_exponential_sudoku.sudoku.three_cnf import Puzzle
from reference.sudoku_unit_rank import unit_subset_rank


def _puzzle(box: int, case: str) -> Puzzle:
    if type(box) is not int or box < 1:
        raise ValueError("Box order must be positive")
    if case == "empty":
        n = box * box
        return Puzzle(box, (0,) * (n * n))
    if case == "hard" and box == 3:
        from reference.real_sudoku_bench import HARD_9
        return Puzzle.from_text(HARD_9, 3)
    raise ValueError("Hard fixture is available for box order three only")


def audit_sudoku_representation(
    box: int, *, with_packing: bool = False, case: str = "empty",
) -> dict[str, Any]:
    """Compute structural certificates; expensive packing is opt-in."""
    puzzle = _puzzle(box, case)
    source = DirectNetwork.from_puzzle(puzzle)
    n, t = puzzle.side, source.wire_bits
    units = 3 * n
    unit_arity = n * t
    assert len(source.vertices) == n*n + units
    assert source.edge_count == 3 * n*n*t
    rank = unit_subset_rank(n, n//2)
    result: dict[str, Any] = {
        "schema": "1.0.0",
        "box_order": box, "side": n, "case": case,
        "givens": sum(bool(x) for x in puzzle.entries),
        "original_boolean_wires": source.edge_count,
        "lifted_boolean_wires": 2 * source.edge_count,
        "original_tensor_vertices": len(source.vertices),
        "unit_factors": units,
        "digit_bits": t, "unit_arity_bits": unit_arity,
        "cell_arity_bits": 3*t,
        "dense_unit_table_entries": 1 << unit_arity,
        "min_input_factor_width": max(unit_arity, 3*t),
        "unit_input_arity_le_default_width": unit_arity <= 16,
        "unit_cut_digits": n//2,
        "projected_unit_cut_rank": rank,
        "raw_unit_rank_lower_bound": rank,
        "subset_rank_states_log2_upper_integer": (rank-1).bit_length(),
        "rank_statement": (
            "Exact over valid-digit unit tensor; raw unit permits distinct "
            "out-of-range binary codes, hence only >=rank is established. "
            "No global width or rank bound follows."
        ),
        "packing_included": with_packing,
    }
    if with_packing:
        from non_exponential_sudoku.sudoku.encoding import sudoku_network
        from non_exponential_sudoku.core.packing import pack, audit_packing
        from reference.scaling_experiment import mode_catalog_projection

        net = sudoku_network(puzzle)
        packing = pack(net, 64, 2)
        packing_audit = audit_packing(net, packing)
        occupancy = max(
            (sum(e is not None for e in packet.slots)
             for packet in packing.packets), default=0,
        )
        if not (packing_audit["all_edges_packed_exactly_once"]
                and packing_audit["orientation_geometry_valid"]):
            raise AssertionError("Invalid Sudoku packet geometry")
        projection = mode_catalog_projection(
            net, packing, precision=net.edges+1,
        )
        result.update({
            "packing_geometry_valid": True,
            "packet_count": len(packing.packets),
            "max_packet_occupied": occupancy,
            "packet_factor_arity_ceiling_observed": 2*occupancy,
            "min_input_factor_width": max(unit_arity, 3*t, 2*occupancy),
            "mode_center": 1,
            "mode_center_precision_bits": net.edges+1,
            "mode_center_descriptor_count": projection["exact_descriptor_count"],
            "mode_weighted_tuple_lower_log2": (
                projection["at_least_binary_mode_tuple_log2"]
            ),
            "mode_bound_semantics": (
                "Finite-mode b=0 binary support lower bound for independent "
                "weighted assignment count; NOT a lower bound on the "
                "operation count of factor elimination."
            ),
        })
    return result


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--boxes", nargs="+", type=int, default=[2, 3, 4])
    parser.add_argument("--packing", action="store_true")
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    if len(set(args.boxes)) != len(args.boxes):
        parser.error("Repeated Sudoku box order")
    results = [
        audit_sudoku_representation(box, with_packing=args.packing)
        for box in args.boxes
    ]
    data = {
        "status": "structural-certificates-only",
        "results": results,
    }
    output = json.dumps(data, indent=2, sort_keys=True) + "\n"
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(output)
    print(output, end="")


if __name__ == "__main__":
    main()
