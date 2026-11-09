"""Fail-closed cost contract for *canonical direct Sudoku* vertex programs.

Neither arbitrary Network callbacks nor packet-entry oracles can be certified
by this model. It counts one full pass of *original* cell/unit tensors. A
separate bound on how often the contraction invokes those callbacks is needed
to close the whole-frame recurrence.

Costs are conservative schoolbook *abstract bit-operation* envelopes, not
exact CPython bytecode counts or a claim about native/FLINT execution.
"""
from __future__ import annotations

from dataclasses import dataclass

from non_exponential_sudoku.core.network import Network
from non_exponential_sudoku.sudoku.input_oracles import CellEntryOracle, UnitEntryOracle
from non_exponential_sudoku.sudoku.three_cnf import Puzzle


class UncertifiedSudokuInput(ValueError):
    """Input tensor programs or topology are not the certified Sudoku ABI."""


@dataclass(frozen=True, slots=True)
class OriginalOracleProgramWork:
    """One bounded 0/1 tensor entry, excluding the supplied ring.scalar call."""

    validated_bits: int
    decoded_bits: int
    shift_or_updates: int
    distinctness_mask_bits: int
    distinctness_updates: int
    ring_scalar_calls: int
    boolean_bit_work_ceiling: int


@dataclass(frozen=True, slots=True)
class CertifiedSudokuInput:
    box_order: int
    side: int
    cells: int
    units: int
    vertices: int
    wires: int
    digit_width: int
    root_name_bits: int
    cell_work: OriginalOracleProgramWork
    unit_work: OriginalOracleProgramWork
    per_pass_boolean_bit_work_ceiling: int
    per_pass_scalar_calls: int


def _program_work(side: int, width: int) -> tuple[
    OriginalOracleProgramWork, OriginalOracleProgramWork
]:
    """Bound the exact Boolean loops of the immutable source implementations.

    Cell: 3*width Boolean checks, 3*width decoded input bits, plus a fixed
    number of width-bit comparisons and clue checks.

    Unit: side*width Boolean checks and decoded bits, at most side shifts,
    tests and unions of a bitset with width<=2**width. Duplicates only shorten
    the loop. The bitset may include out-of-range digits, just as the
    original independent unit's all-distinctness predicate does.

    The coefficients 64 are a deliberately loose allowance in a schoolbook
    bit model for indexing, shifts, OR, equality and loop counters. They do
    NOT bound arbitrary Python interpreter overhead, allocated object bytes,
    optimizer variants or user-supplied callback bodies.
    """
    cell_bits = 3 * width
    unit_bits = side * width
    mask_bits = 1 << width
    cell = OriginalOracleProgramWork(
        cell_bits, cell_bits, cell_bits, 0, 0, 1,
        64 * (cell_bits + 1) * (width + 1)**2,
    )
    unit = OriginalOracleProgramWork(
        unit_bits, unit_bits, unit_bits, mask_bits, side, 1,
        64 * (unit_bits + 1) * (width + mask_bits + 1)**2,
    )
    return cell, unit


def certify_original_sudoku_oracles(
    puzzle: Puzzle, net: Network,
) -> CertifiedSudokuInput:
    """Validate full source geometry, clues, and *exact* callable classes.

    Not just checking degree or a sample answer: every port index is
    reconstructed from the independent cell/row/column/box specification.
    The program identity is explicit and dataclass fields are immutable.
    """
    b = puzzle.b
    if type(b) is not int or b < 1:
        raise UncertifiedSudokuInput("positive box order is required")
    n = b * b
    N = n * n
    t = max(1, (n - 1).bit_length())
    if (type(puzzle.entries) is not tuple or len(puzzle.entries) != N or
            any(type(clue) is not int or not 0 <= clue <= n
                for clue in puzzle.entries)):
        raise UncertifiedSudokuInput("invalid direct Sudoku clue input")
    expected_M = 3 * N * t
    if (net.edges != expected_M or len(net.left) != N or
            len(net.right) != 3 * n):
        raise UncertifiedSudokuInput("noncanonical direct Sudoku network shape")
    try:
        net.validate()
    except AssertionError as exc:
        raise UncertifiedSudokuInput("invalid network incidence") from exc

    expected_unit_ports: list[list[int]] = [[] for _ in range(3 * n)]
    for cell in range(N):
        row, col = divmod(cell, n)
        box = (row // b) * b + col // b
        expected_ports = tuple(range(3 * t * cell, 3 * t * (cell + 1)))
        actual = net.left[cell]
        if actual.name != f"cell:{cell}":
            raise UncertifiedSudokuInput("cell vertex name mismatch")
        if actual.ports != expected_ports:
            raise UncertifiedSudokuInput("cell vertex ports mismatch")
        cb = actual.oracle
        if (type(cb) is not CellEntryOracle or cb.side != n or cb.width != t):
            raise UncertifiedSudokuInput("cell must use canonical immutable oracle")
        if cb.clue != puzzle.entries[cell]:
            raise UncertifiedSudokuInput("cell clue does not match input puzzle")
        for group_offset, unit_id in enumerate((row, n + col, 2 * n + box)):
            offset = 3 * t * cell + group_offset * t
            expected_unit_ports[unit_id].extend(range(offset, offset + t))

    for index, actual in enumerate(net.right):
        expected_name = (
            ("row" if index < n else "column" if index < 2 * n else "box")
            + f":{index % n}"
        )
        if actual.name != expected_name:
            raise UncertifiedSudokuInput("unit vertex name mismatch")
        if actual.ports != tuple(expected_unit_ports[index]):
            raise UncertifiedSudokuInput("unit vertex ports mismatch")
        cb = actual.oracle
        if (type(cb) is not UnitEntryOracle or cb.side != n or cb.width != t):
            raise UncertifiedSudokuInput("unit must use canonical immutable oracle")

    cell_work, unit_work = _program_work(n, t)
    name_bits = sum(
        8 * len(v.name.encode("utf-8")) for v in net.left + net.right
    )
    return CertifiedSudokuInput(
        box_order=b, side=n, cells=N, units=3 * n, vertices=N + 3 * n,
        wires=expected_M, digit_width=t, root_name_bits=name_bits,
        cell_work=cell_work, unit_work=unit_work,
        per_pass_boolean_bit_work_ceiling=(
            N * cell_work.boolean_bit_work_ceiling +
            3 * n * unit_work.boolean_bit_work_ceiling
        ),
        per_pass_scalar_calls=N + 3 * n,
    )


def original_oracle_bit_work_per_pass(
    proof: CertifiedSudokuInput, *, extension_degree: int, precision: int,
) -> int:
    """One *complete pass* of original tensor oracles over a supplied Padic.

    Every original entry calls ring.scalar exactly once with 0 or 1.
    Its canonical output is a vector with at most e*p mathematical bits.
    The ring scalar ceiling reuses the conservative schoolbook budget
    128*(e*p+1)**2, already employed in packet preparation's cost model.

    This only bounds original entry computations if the ring uses the
    analyzed eager Padic scalar algorithm. It does not charge generating
    assignments/indices, packet entries, leaf factor joining, or the *number*
    of passes executed by the whole contractor.
    """
    if (type(proof) is not CertifiedSudokuInput or
            type(extension_degree) is not int or extension_degree < 2 or
            type(precision) is not int or precision < 1):
        raise ValueError("certified Sudoku and canonical finite Padic shape required")
    scalar_ceiling = 128 * (extension_degree * precision + 1)**2
    return (proof.per_pass_boolean_bit_work_ceiling +
            proof.per_pass_scalar_calls * scalar_ceiling)
