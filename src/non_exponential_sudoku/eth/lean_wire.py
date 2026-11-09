"""Lean's canonical finite-CNF wire format, at a pinned upstream revision.

This is a direct implementation of the *finite encoding definitions* in
openai/math/lean/OAI/Algorithms/SubexponentialSAT/Encoding.lean.
See reference/lean_eth_source.json. It is NOT the certified SAT machine.
"""
from __future__ import annotations

from collections.abc import Callable, Iterable
from typing import TypeVar

from .cnf import CNFFormula

BitWord = tuple[bool, ...]
_T = TypeVar("_T")


def _encode_nat(n: int) -> BitWord:
    # Encoding.encodeNat: List.replicate n true ++ [false].
    if type(n) is not int or n < 0:
        raise ValueError("Lean unary fields must be nonnegative integers")
    return (True,) * n + (False,)


def _frame(bits: BitWord) -> BitWord:
    # Encoding.frame: every data bit escaped by true, terminated by false.
    out: list[bool] = []
    for bit in bits:
        out.extend((True, bit))
    out.append(False)
    return tuple(out)


def _encode_list(values: Iterable[_T], encode: Callable[[_T], BitWord]) -> BitWord:
    # Encoding.encodeList: true ++ frame(item), repeated, then false.
    out: list[bool] = []
    for item in values:
        out.append(True)
        out.extend(_frame(encode(item)))
    out.append(False)
    return tuple(out)


def encode_lean_cnf(formula: CNFFormula) -> BitWord:
    """Encode a *normalized* CNF in exact Lean Encoding.encodeCNF syntax.

    Finite Lean clauses are sorted by their numeric literal codes, and clauses
    by the lexicographic order of their code lists. This is NOT DIMACS.
    """
    if not isinstance(formula, CNFFormula):
        raise TypeError("expected CNFFormula")
    numbered = sorted(
        tuple(sorted(2 * (abs(literal) - 1) + int(literal > 0)
                     for literal in clause))
        for clause in formula.clauses
    )
    body = _encode_list(numbered, lambda row: _encode_list(row, _encode_nat))
    return _encode_nat(formula.nvars) + body


class _Decoder:
    __slots__ = ("bits", "position")

    def __init__(self, bits: BitWord) -> None:
        self.bits = bits
        self.position = 0

    def bit(self) -> bool:
        if self.position >= len(self.bits):
            raise ValueError("truncated Lean CNF encoding")
        value = self.bits[self.position]
        self.position += 1
        return value

    def nat(self) -> int:
        # Encoding.readNat.
        value = 0
        while self.bit():
            value += 1
        return value

    def frame(self) -> BitWord:
        # Encoding.readFrame: false ends a frame; true means one payload bit.
        values: list[bool] = []
        while self.bit():
            values.append(self.bit())
        return tuple(values)

    def items(self, decode: Callable[[_Decoder], _T]) -> tuple[_T, ...]:
        # Encoding.encodeList/readFrame nesting: each item's frame must be used
        # completely, so malformed junk within a frame never gets ignored.
        result: list[_T] = []
        while self.bit():
            child = _Decoder(self.frame())
            value = decode(child)
            if child.position != len(child.bits):
                raise ValueError("unconsumed bits inside Lean CNF frame")
            result.append(value)
        return tuple(result)


def decode_lean_cnf(bits: Iterable[bool]) -> CNFFormula:
    """Decode any well-formed finite Lean SAT.CNF, then normalize its clauses.

    Lean's source encoding accepts non-normalized Finset formulas. Our
    CNFFormula representation normalizes after decoding; thus re-encoding an
    arbitrary unreduced Lean source need not reproduce the original bits.
    """
    word = tuple(bits)
    if any(type(bit) is not bool for bit in word):
        raise TypeError("Lean CNF input must be a sequence of bool bits")
    reader = _Decoder(word)
    nvars = reader.nat()
    rows = reader.items(lambda row: row.items(lambda code: code.nat()))
    if reader.position != len(word):
        raise ValueError("trailing bits after Lean CNF")
    if tuple(sorted(set(rows))) != rows:
        raise ValueError("Lean CNF clauses must be strictly sorted and unique")
    clauses: list[tuple[int, ...]] = []
    for row in rows:
        if tuple(sorted(set(row))) != row:
            raise ValueError("Lean clause literal codes must be sorted and unique")
        if any(code >= 2 * nvars for code in row):
            raise ValueError("literal code outside declared Fin n")
        clauses.append(tuple(
            code // 2 + 1 if code % 2 else -(code // 2 + 1) for code in row
        ))
    return CNFFormula(nvars, tuple(clauses))
