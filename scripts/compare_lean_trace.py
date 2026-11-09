"""Compare source-defined Lean 4.34.1 counting-DFS states and CNF bits with Python.

Accepts output from reference/lean_native_trace.lean, importing pinned
openai/math source. Does not claim primitive machine or asymptotic refinement.
"""
from __future__ import annotations

import argparse
from pathlib import Path

from non_exponential_sudoku.eth.cnf import CNFFormula
from non_exponential_sudoku.eth.lean_wire import encode_lean_cnf, _encode_nat, _encode_list
from non_exponential_sudoku.eth.sparsification import _children


def _bits(word: tuple[bool, ...]) -> str:
    return ''.join('1' if bit else '0' for bit in word)


def _truth(formula: CNFFormula) -> str:
    return ''.join('1' if formula.satisfied_mask(mask) else '0'
                   for mask in range(1 << formula.nvars))


def expected() -> dict[str, str]:
    """Exact correspondence points, with deterministic assignment-mask order."""
    shared = CNFFormula(3, ((1, 2), (1, 3)))
    negative = CNFFormula(3, ((-1, 2), (-1, 3), (2, 3)))
    a, b = _children(shared, 2, (1,))
    na, nb = _children(negative, 2, (-1,))
    formulas = {
        "empty0": CNFFormula(0, ()),
        "empty3": CNFFormula(3, ()),
        "normalized": CNFFormula(3, ((1, -1), (1, 2), (1,))),
        "shared": shared,
        "branchA": a,
        "branchB": b,
        "negativeA": na,
        "negativeB": nb,
    }
    def state(total: int, pending: tuple[tuple[CNFFormula, int], ...]) -> str:
        def entry(item: tuple[CNFFormula, int]) -> tuple[bool, ...]:
            formula, depth = item
            return _encode_nat(depth) + encode_lean_cnf(formula)
        return _bits(_encode_nat(total) + _encode_list(pending, entry))

    return {
        **{name: _bits(encode_lean_cnf(formula))
           for name, formula in formulas.items()},
        "truthSource": _truth(shared),
        "truthA": _truth(a),
        "truthB": _truth(b),
        "countDFS0": state(0, ((shared, 0),)),
        "countDFS1": state(0, ((a, 1), (b, 1))),
        "countDFS2": state(4, ((b, 1),)),
        "countDFS3": state(5, ()),
        "countDFSRun": state(5, ()),
    }


def parse_trace(source: str) -> dict[str, str]:
    result: dict[str, str] = {}
    for line in source.splitlines():
        if not line.strip():
            continue
        if "|" not in line:
            raise ValueError(f"unexpected Lean trace output: {line!r}")
        name, word = line.strip().split("|", 1)
        if name in result or not name or any(c not in '01' for c in word):
            raise ValueError(f"invalid or duplicate Lean trace record: {line!r}")
        result[name] = word
    return result


def compare(source: str) -> None:
    observed = parse_trace(source)
    wanted = expected()
    if observed.keys() != wanted.keys():
        raise AssertionError(
            f"Lean trace keys differ: missing={sorted(wanted.keys() - observed.keys())}"
            f", extra={sorted(observed.keys() - wanted.keys())}"
        )
    for key in wanted:
        if observed[key] != wanted[key]:
            raise AssertionError(
                f"Lean/Python {key} mismatch: Lean={observed[key]!r}, "
                f"Python={wanted[key]!r}"
            )
    assert all(not (a == '1' and b == '1') and
               src == ('1' if a == '1' or b == '1' else '0')
               for src, a, b in zip(observed['truthSource'],
                                    observed['truthA'], observed['truthB']))
    print(f"Lean 4.34.1 source execution agrees: {len(wanted)} complete traces")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--input', type=Path, required=True)
    args = parser.parse_args()
    compare(args.input.read_text())


if __name__ == '__main__':
    main()
