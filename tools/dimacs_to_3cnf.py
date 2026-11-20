#!/usr/bin/env python3
"""Convert DIMACS CNF into clauses of length <= 3 with a bijection of models.

A fresh auxiliary variable is defined as the OR of two earlier literals.
Each auxiliary variable is determined by the original assignment, so the
number of satisfying assignments over *all* output variables is preserved.

    python tools/dimacs_to_3cnf.py puzzle.cnf -o puzzle.3cnf

This is a format adapter, not an ETH algorithm or a complexity result.
"""
from __future__ import annotations

import argparse
from pathlib import Path
import sys
from typing import Sequence, TextIO


class DimacsError(ValueError):
    """Malformed or inconsistent DIMACS input."""


def parse_dimacs(source: str) -> tuple[int, tuple[tuple[int, ...], ...]]:
    """Preserve declared variable universe, including any unused variables."""
    header: tuple[int, int] | None = None
    clauses: list[tuple[int, ...]] = []
    pending: list[int] = []
    for number, original in enumerate(source.splitlines(), 1):
        line = original.strip()
        if not line or line.startswith("c"):
            continue
        if header is None:
            fields = line.split()
            if len(fields) != 4 or fields[:2] != ["p", "cnf"]:
                raise DimacsError(f"line {number}: expected 'p cnf <n> <m>'")
            try:
                n, m = int(fields[2]), int(fields[3])
            except ValueError as exc:
                raise DimacsError(f"line {number}: invalid header count") from exc
            if n < 0 or m < 0:
                raise DimacsError(f"line {number}: negative header count")
            header = n, m
            continue
        n, m = header
        for token in line.split():
            try:
                literal = int(token)
            except ValueError as exc:
                raise DimacsError(f"line {number}: invalid literal {token!r}") from exc
            if literal == 0:
                if len(clauses) == m:
                    raise DimacsError(f"line {number}: too many clauses")
                clauses.append(tuple(pending))
                pending.clear()
            else:
                if len(clauses) == m:
                    raise DimacsError(f"line {number}: literal after final clause")
                if abs(literal) > n:
                    raise DimacsError(f"line {number}: variable {abs(literal)} exceeds {n}")
                pending.append(literal)
    if header is None:
        raise DimacsError("missing DIMACS header")
    if pending or len(clauses) != header[1]:
        raise DimacsError("unterminated clause or incorrect clause count")
    return header[0], tuple(clauses)


def make_3cnf(variables: int, clauses: Sequence[Sequence[int]]) -> tuple[int, tuple[tuple[int, ...], ...]]:
    """Definitional OR chains; every input assignment has a unique extension.

    For (a | b | c | d), introduce y <-> (a | b), expressed by:
        (-a | y) & (-b | y) & (a | b | -y) & (y | c | d).
    Apply the same step repeatedly to clauses longer than four literals.
    This encoding is #SAT-preserving, unlike a one-way satisfiability chain.
    """
    if variables < 0:
        raise DimacsError("negative variable count")
    output: list[tuple[int, ...]] = []
    next_variable = variables
    for clause in clauses:
        if any(literal == 0 or abs(literal) > variables for literal in clause):
            raise DimacsError("clause contains zero or a literal outside the declared universe")
        if len(clause) <= 3:
            output.append(tuple(clause))
            continue
        # Define a new OR-prefix for each prefix ending before the final pair.
        first = clause[0]
        for second in clause[1:-2]:
            next_variable += 1
            y = next_variable
            output.extend(((-first, y), (-second, y), (first, second, -y)))
            first = y
        output.append((first, clause[-2], clause[-1]))
    return next_variable, tuple(output)


def write_dimacs(variables: int, clauses: Sequence[Sequence[int]], dest: TextIO) -> None:
    dest.write("c definitional 3-CNF with uniquely determined auxiliary variables\n")
    dest.write("c exact total model count is preserved; no projection required\n")
    dest.write(f"p cnf {variables} {len(clauses)}\n")
    for clause in clauses:
        dest.write(" ".join(map(str, clause)) + (" 0\n" if clause else "0\n"))


def main(argv: Sequence[str] | None = None) -> int:
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument("input", type=Path, help="input DIMACS CNF")
    p.add_argument("-o", "--output", type=Path, required=True, help="output DIMACS 3-CNF")
    args = p.parse_args(argv)
    try:
        if args.input.resolve() == args.output.resolve():
            raise DimacsError("output must not overwrite the input")
        variables, clauses = parse_dimacs(args.input.read_text(encoding="utf-8-sig"))
        out_variables, out_clauses = make_3cnf(variables, clauses)
        args.output.parent.mkdir(parents=True, exist_ok=True)
        with args.output.open("w", encoding="ascii", newline="\n") as stream:
            write_dimacs(out_variables, out_clauses, stream)
        print(f"{args.output}: {out_variables} variables, {len(out_clauses)} clauses "
              f"(source {variables} variables, {len(clauses)} clauses)", file=sys.stderr)
    except (OSError, DimacsError) as exc:
        p.error(str(exc))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
