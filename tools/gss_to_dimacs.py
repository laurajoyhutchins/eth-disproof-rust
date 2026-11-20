#!/usr/bin/env python3
"""Convert Generic Sudoku Solver (.gss) or compact 9x9 puzzles to DIMACS CNF.

Only Python's standard library is required. This is an encoding, not a solver.

    python gss_to_dimacs.py puzzle.gss -o puzzle.cnf
    python gss_to_dimacs.py corpus.txt --format compact --output-dir cnfs

GSS specification: https://bartp5.github.io/gss/
"""

from __future__ import annotations

import argparse
from collections import defaultdict
from dataclasses import dataclass
from itertools import combinations
from math import isqrt
from pathlib import Path
import re
import sys
from typing import Iterator, Sequence, TextIO


class GssFormatError(ValueError):
    """The input is not a supported, well-formed GSS puzzle."""


@dataclass(frozen=True)
class Puzzle:
    block_size: int  # Number of symbols and cells per block
    clues: tuple[int, ...]  # 0 means unknown; other values are 1..block_size
    blocks: tuple[tuple[int, ...], ...]  # Zero-based cell indices

    @property
    def variables(self) -> int:
        return len(self.clues) * self.block_size

    @property
    def clauses(self) -> int:
        n = self.block_size
        exactly_one = 1 + n * (n - 1) // 2
        return (len(self.clues) + len(self.blocks) * n) * exactly_one + sum(
            clue != 0 for clue in self.clues
        )


def _read_positive_integer(source: str, label: str) -> int:
    # GSS permits a trailing period in e.g. `<size>81.`.
    match = re.fullmatch(r"\s*(\d+)\.?\s*", source)
    if not match or int(match.group(1)) == 0:
        raise GssFormatError(f"invalid <{label}> value: {source!r}")
    return int(match.group(1))


def _square_side(num_cells: int, block_size: int) -> int:
    if num_cells != block_size * block_size:
        raise GssFormatError("grid/diagonal blocks require <size> = <blocksize> squared")
    return block_size


def _square_box_width(block_size: int) -> int:
    side = isqrt(block_size)
    if side * side != block_size:
        raise GssFormatError("<standardblocks>/<blockblocks> require a square blocksize")
    return side


def _generated_blocks(tag: str, cells: int, symbols: int) -> list[tuple[int, ...]]:
    side = _square_side(cells, symbols)
    tags = ("rowblocks", "colblocks", "blockblocks") if tag == "standardblocks" else (tag,)
    generated: list[tuple[int, ...]] = []
    for kind in tags:
        if kind == "rowblocks":
            generated.extend(tuple(r * side + c for c in range(side)) for r in range(side))
        elif kind == "colblocks":
            generated.extend(tuple(r * side + c for r in range(side)) for c in range(side))
        elif kind == "blockblocks":
            width = _square_box_width(symbols)
            for box_r in range(0, side, width):
                for box_c in range(0, side, width):
                    generated.append(tuple(
                        (box_r + dr) * side + box_c + dc
                        for dr in range(width) for dc in range(width)
                    ))
        elif kind == "downdiagblock":
            generated.append(tuple(i * side + i for i in range(side)))
        elif kind == "updiagblock":
            generated.append(tuple(i * side + side - 1 - i for i in range(side)))
        else:
            raise GssFormatError(f"unsupported block directive: <{kind}>")
    return generated


def _matrix_blocks(lines: Sequence[str], cells: int, symbols: int) -> list[tuple[int, ...]]:
    # In a GSS matrix, each occurrence of a numeric label selects a cell;
    # periods select cells not belonging to a matrix-defined block.
    tokens = re.findall(r"[0-9.]+", "\n".join(lines))
    if len(tokens) != cells:
        raise GssFormatError(f"<matrix> has {len(tokens)} cells; expected {cells}")
    members: dict[int, list[int]] = defaultdict(list)
    for index, token in enumerate(tokens):
        if token[0] != ".":
            members[int(re.match(r"[0-9]+", token).group())].append(index)
    for label, block in members.items():
        if len(block) != symbols:
            raise GssFormatError(
                f"<matrix> label {label} contains {len(block)} cells; expected {symbols}"
            )
    return [tuple(block) for block in members.values()]


def _parse_symbols(lines: Sequence[str], pattern: str, cells: int, symbols: int) -> tuple[int, ...]:
    if pattern.count(".") != 1:
        raise GssFormatError("<pattern> must contain exactly one '.' placeholder")
    prefix, suffix = pattern.split(".", 1)
    token = re.compile(re.escape(prefix) + r"([0-9.]+)" + re.escape(suffix))
    values: list[int] = []
    for line in lines:
        i = 0
        while i < len(line):
            if line[i] == '"':
                # GSS treats content in double quotes as formatting, not cells.
                closing = line.find('"', i + 1)
                i = len(line) if closing < 0 else closing + 1
                continue
            match = token.match(line, i)
            if match:
                digits = match.group(1).replace(".", "0")
                value = int(digits)
                if value > symbols:
                    raise GssFormatError(f"clue {value} outside symbol range 1..{symbols}")
                values.append(value)
                i = match.end()
            else:
                i += 1
    if len(values) != cells:
        raise GssFormatError(
            f"<sudoku> contains {len(values)} cells; expected {cells}; "
            "check <pattern> and the puzzle text"
        )
    return tuple(values)


def _validated_puzzle(symbols: int, clues: tuple[int, ...],
                      blocks: Sequence[tuple[int, ...]]) -> Puzzle:
    if not blocks:
        raise GssFormatError("no blocks specified")
    membership = [0] * len(clues)
    for number, block in enumerate(blocks, 1):
        if len(block) != symbols or len(set(block)) != symbols:
            raise GssFormatError(f"block {number} must contain {symbols} distinct cells")
        for cell in block:
            if cell < 0 or cell >= len(clues):
                raise GssFormatError(f"block {number} contains invalid cell {cell + 1}")
            membership[cell] += 1
    if 0 in membership:
        raise GssFormatError(f"cell {membership.index(0) + 1} belongs to no block")
    return Puzzle(symbols, clues, tuple(blocks))


def parse_native(text: str) -> Puzzle:
    """Read GSS native format, including custom blocks, matrices, and patterns."""
    lines = text.splitlines()
    size: int | None = None
    block_size: int | None = None
    pattern = "."
    directives: list[tuple[str, object]] = []
    body: list[str] | None = None
    known = {"size", "blocksize", "pattern", "emptychar", "block", "matrix",
             "standardblocks", "rowblocks", "colblocks", "blockblocks",
             "downdiagblock", "updiagblock", "sudoku", "endsudoku"}
    i = 0
    while i < len(lines):
        line = lines[i]
        i += 1
        if not line or line.startswith("#"):
            continue
        match = re.match(r"^<([a-z]+)>(.*)$", line)
        if not match:
            continue  # Formatting and arbitrary text outside directives.
        tag, arg = match.groups()
        if tag not in known:
            raise GssFormatError(f"unsupported GSS directive <{tag}>")
        if tag == "size":
            if size is not None:
                raise GssFormatError("duplicate <size>")
            size = _read_positive_integer(arg, tag)
        elif tag == "blocksize":
            if block_size is not None:
                raise GssFormatError("duplicate <blocksize>")
            block_size = _read_positive_integer(arg, tag)
        elif tag == "pattern":
            parts = arg.split()
            if len(parts) != 1:
                raise GssFormatError("<pattern> needs exactly one non-space pattern")
            pattern = parts[0]
        elif tag == "matrix":
            # The original C reader commits to the default dimensions as soon
            # as a generated or matrix block directive is encountered.
            # A subsequent <size>/<blocksize> is therefore not permitted.
            if size is None:
                size = 81
            if block_size is None:
                block_size = 9
            matrix_lines: list[str] = []
            while i < len(lines) and not re.match(r"^<[a-z]+>", lines[i]):
                matrix_lines.append(lines[i])
                i += 1
            directives.append((tag, matrix_lines))
        elif tag == "block":
            # Unlike generated blocks, the C reader does not infer <size>
            # for <block>. It needs the index domain to have been declared.
            if size is None:
                raise GssFormatError("<block> requires a preceding <size> (GSS C semantics)")
            if block_size is None:
                block_size = 9
            parts = arg.split()
            if not parts or any(not p.isdecimal() for p in parts):
                raise GssFormatError("<block> needs whitespace-separated integer cell indices")
            directives.append((tag, tuple(int(p) - 1 for p in parts)))
        elif tag in {"standardblocks", "rowblocks", "colblocks", "blockblocks",
                     "downdiagblock", "updiagblock"}:
            if size is None:
                size = 81
            if block_size is None:
                block_size = 9
            directives.append((tag, None))
        elif tag == "sudoku":
            if body is not None:
                raise GssFormatError("multiple <sudoku> sections")
            body = []
            while i < len(lines) and not lines[i].startswith("<endsudoku>"):
                body.append(lines[i])
                i += 1
            break
        # <emptychar> changes output formatting only, not clue parsing.
    if body is None:
        raise GssFormatError("missing <sudoku> section")
    cells, symbols = size or 81, block_size or 9
    blocks: list[tuple[int, ...]] = []
    for tag, argument in directives:
        if tag == "matrix":
            blocks.extend(_matrix_blocks(argument, cells, symbols))  # type: ignore[arg-type]
        elif tag == "block":
            blocks.append(argument)  # type: ignore[arg-type]
        else:
            blocks.extend(_generated_blocks(tag, cells, symbols))
    if not blocks:
        # GSS defaults to standard 9x9 only, not arbitrary square sizes.
        if (cells, symbols) != (81, 9):
            raise GssFormatError("non-9x9 native puzzles need explicit block directives")
        blocks.extend(_generated_blocks("standardblocks", cells, symbols))
    clues = _parse_symbols(body, pattern, cells, symbols)
    return _validated_puzzle(symbols, clues, blocks)


def parse_compact(text: str) -> list[Puzzle]:
    """Read a stream of 81-character standard puzzles, separated arbitrarily.

    Matches GSS's documented character-stream behavior for digits, periods,
    whitespace, and comments. Unlike the C reader, incomplete final puzzles
    are rejected instead of silently discarded.
    """
    blocks = _generated_blocks("standardblocks", 81, 9)
    symbols: list[str] = []
    for line_number, line in enumerate(text.splitlines(), 1):
        data = line.partition("#")[0]
        for char in data:
            if char in "0123456789.":
                symbols.append(char)
            elif not char.isspace():
                raise GssFormatError(
                    f"unexpected character {char!r} on compact line {line_number}"
                )
    if not symbols:
        raise GssFormatError("no compact puzzles found")
    if len(symbols) % 81:
        raise GssFormatError(
            f"compact input has {len(symbols)} cells, not a multiple of 81; "
            "partial puzzles must not be silently dropped"
        )
    puzzles: list[Puzzle] = []
    for offset in range(0, len(symbols), 81):
        clues = tuple(0 if c == "." else int(c) for c in symbols[offset:offset + 81])
        puzzles.append(_validated_puzzle(9, clues, blocks))
    return puzzles


def variable(cell: int, symbol: int, symbols: int) -> int:
    """DIMACS index for zero-based cell and 1-based symbol."""
    return cell * symbols + symbol


def _exactly_one(vars_: Sequence[int]) -> Iterator[tuple[int, ...]]:
    yield tuple(vars_)
    for a, b in combinations(vars_, 2):
        yield (-a, -b)


def encode_clauses(puzzle: Puzzle) -> Iterator[tuple[int, ...]]:
    """One-to-one encoding: models correspond exactly to completed grids."""
    n = puzzle.block_size
    for cell in range(len(puzzle.clues)):
        yield from _exactly_one(tuple(variable(cell, digit, n) for digit in range(1, n + 1)))
    for block in puzzle.blocks:
        for digit in range(1, n + 1):
            yield from _exactly_one(tuple(variable(cell, digit, n) for cell in block))
    for cell, clue in enumerate(puzzle.clues):
        if clue:
            yield (variable(cell, clue, n),)


def write_dimacs(puzzle: Puzzle, stream: TextIO) -> None:
    stream.write("c Generic Sudoku Solver puzzle: exact cell/block CNF encoding\n")
    stream.write("c variable(cell,digit) = cell*blocksize + digit; cell is zero-based\n")
    stream.write(f"p cnf {puzzle.variables} {puzzle.clauses}\n")
    for clause in encode_clauses(puzzle):
        stream.write(" ".join(map(str, clause)) + " 0\n")


def main(argv: Sequence[str] | None = None) -> int:
    cli = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    cli.add_argument("input", type=Path, help="GSS .gss or compact 9x9 text file")
    cli.add_argument("--format", choices=("auto", "native", "compact"), default="auto")
    target = cli.add_mutually_exclusive_group()
    target.add_argument("-o", "--output", type=Path, help="output .cnf for a single puzzle")
    target.add_argument("--output-dir", type=Path, help="directory for numbered .cnf files")
    args = cli.parse_args(argv)
    try:
        source = args.input.read_text(encoding="utf-8-sig")
        fmt = args.format
        if fmt == "auto":
            fmt = "native" if args.input.suffix.lower() == ".gss" or re.search(
                r"(?m)^<(?:sudoku|size|blocksize|pattern|block|matrix|standardblocks|rowblocks|colblocks|blockblocks|downdiagblock|updiagblock)>", source
            ) else "compact"
        puzzles = [parse_native(source)] if fmt == "native" else parse_compact(source)
        if args.output and len(puzzles) != 1:
            raise GssFormatError("multiple compact puzzles require --output-dir")
        if args.output_dir or len(puzzles) > 1:
            directory = args.output_dir or args.input.with_name(args.input.stem + "_cnf")
            directory.mkdir(parents=True, exist_ok=True)
            destinations = [directory / f"{args.input.stem}_{i:04d}.cnf"
                            for i in range(1, len(puzzles) + 1)]
        else:
            destinations = [args.output or args.input.with_suffix(".cnf")]
        if any(path.resolve() == args.input.resolve() for path in destinations):
            raise GssFormatError("output path must not overwrite the input puzzle")
        for puzzle, path in zip(puzzles, destinations):
            path.parent.mkdir(parents=True, exist_ok=True)
            with path.open("w", encoding="ascii", newline="\n") as stream:
                write_dimacs(puzzle, stream)
            print(f"{path}: {puzzle.variables} variables, {puzzle.clauses} clauses", file=sys.stderr)
    except (OSError, GssFormatError) as exc:
        cli.error(str(exc))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
