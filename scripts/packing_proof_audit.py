"""Reproduce conditional-expectation packing certificates on admissible graphs."""
from __future__ import annotations

import argparse
import json
from pathlib import Path

from non_exponential_sudoku.core.network import Network, TensorRing, Vertex
from non_exponential_sudoku.core.lazy_coefficients import NestedCoords
from non_exponential_sudoku.core.packing import pack
from reference.packing_proof import packing_proof_record


def circulant(n: int, degree: int, *, parallel: bool = False) -> Network:
    left_ports: list[list[int]] = [[] for _ in range(n)]
    right_ports: list[list[int]] = [[] for _ in range(n)]
    edge = 0
    for i in range(n):
        for j in range(degree):
            target = (i + (j // 2 if parallel else j)) % n
            left_ports[i].append(edge)
            right_ports[target].append(edge)
            edge += 1

    def unit_oracle(_bits: tuple[int, ...], ring: TensorRing) -> NestedCoords:
        return ring.one  # No oracle evaluations occur in packing.

    return Network(
        [Vertex(f"l{i}", tuple(ports), unit_oracle) for i, ports in enumerate(left_ports)],
        [Vertex(f"r{i}", tuple(ports), unit_oracle) for i, ports in enumerate(right_ports)],
        edge,
    )


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    cases = [
        (2, 1, 64, 4, False),
        (3, 1, 192, 6, False),
        (2, 2, 512, 16, True),
    ]
    rows = []
    for r, a, n, degree, parallel in cases:
        net = circulant(n, degree, parallel=parallel)
        report = packing_proof_record(net, pack(net, r, a))
        rows.append({"parameters": {"r": r, "a": a, "vertices_per_side": n,
                                     "degree": degree, "parallel": parallel},
                     "certificate": report.as_record()})
    payload = json.dumps({"status": "finite_witnesses_support_symbolic_proof",
                          "cases": rows}, indent=2, sort_keys=True) + "\n"
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(payload)
    print(payload, end="")


if __name__ == "__main__":
    main()
