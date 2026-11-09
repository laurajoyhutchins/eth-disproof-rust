"""Finite source-derived tests against pinned OpenAI Lean definitions.

These are independent Python interpretations of explicit Lean *definitions*,
not execution of Lean, extraction of its noncomputable machine, or evidence of
the manuscript's running-time claim. See reference/lean_eth_source.json.
"""
from __future__ import annotations

from itertools import combinations
import json
from pathlib import Path

import pytest

from non_exponential_sudoku.eth.cnf import CNFFormula
from non_exponential_sudoku.eth.lean_wire import (
    decode_lean_cnf, encode_lean_cnf,
)
from non_exponential_sudoku.eth.sparsification import (
    _children, iter_disjoint_leaves, reference_sparsification_parameters,
)

def _source_set(raw: tuple[tuple[int, ...], ...]) -> frozenset[frozenset[int]]:
    return frozenset(frozenset(clause) for clause in raw)


def _lean_absorb(
    cnf: frozenset[frozenset[int]],
) -> frozenset[frozenset[int]]:
    # SAT.lean: absorb F := F.filter (fun C => ¬ ∃ D ∈ F, D ⊂ C).
    return frozenset(clause for clause in cnf
                     if not any(other < clause for other in cnf))


def _lean_normalize(
    cnf: frozenset[frozenset[int]],
) -> frozenset[frozenset[int]]:
    # SAT.lean: absorb (removeTautologies F).
    proper = frozenset(c for c in cnf
                       if not any(-literal in c for literal in c))
    return _lean_absorb(proper)


def _lean_children(
    cnf: frozenset[frozenset[int]], width: int, heart: frozenset[int],
) -> tuple[frozenset[frozenset[int]], frozenset[frozenset[int]]]:
    # SqrtLogSpace/DisjointSparsify.lean: selected, petals, childA/B.
    selected = frozenset(c for c in cnf if len(c) == width and heart <= c)
    rest = cnf - selected
    petals = frozenset(c - heart for c in selected)
    units = frozenset(frozenset((-literal,)) for literal in heart)
    return (_lean_absorb(rest | {heart}),
            _lean_absorb(rest | petals | units))


def _set_value(cnf: frozenset[frozenset[int]], mask: int) -> bool:
    # Independent pointwise CNF semantics, not CNFFormula.satisfied_mask.
    return all(any(bool(mask & (1 << (abs(literal) - 1))) == (literal > 0)
                   for literal in clause) for clause in cnf)


def _wire_reference(nvars: int, raw: tuple[tuple[int, ...], ...]) -> tuple[bool, ...]:
    # Minimal *test-side* interpretation of Encoding.lean, deliberately
    # independent of the production encoder.
    def nat(n: int) -> str:
        return '1' * n + '0'

    def sequence(words: list[str]) -> str:
        def frame(w: str) -> str:
            return ''.join('1' + bit for bit in w) + '0'
        return ''.join('1' + frame(w) for w in words) + '0'

    numbered = sorted(tuple(sorted(
        2 * (abs(v) - 1) + int(v > 0) for v in clause
    )) for clause in raw)
    word = nat(nvars) + sequence([
        sequence([nat(code) for code in row]) for row in numbered
    ])
    return tuple(bit == '1' for bit in word)


def _clauses_as_set(formula: CNFFormula) -> frozenset[frozenset[int]]:
    return _source_set(formula.clauses)


@pytest.mark.parametrize('raw', [
    (), ((),), ((1,),), ((-1,),), ((1, -1),), ((1, 2), (1,)),
    ((1, -1), (1, 2), (1,)), ((1, 2), (2, 1), (1, -1)),
    ((2, -3), (-2, 3), (1, 3), (2, -3)),
    ((1,), (-1,)), ((1,), (-1,), ()),
])
@pytest.mark.integration
def test_normalize_is_lean_sat_normalize(raw: tuple[tuple[int, ...], ...]) -> None:
    formula = CNFFormula(4, raw)
    assert _clauses_as_set(formula) == _lean_normalize(_source_set(raw))
    assert formula.nvars == 4


@pytest.mark.integration
def test_lean_sparsifier_child_definitions_and_partition() -> None:
    raw = ((1, 2), (1, 3), (-1, 2, 3), (2, -3))
    formula = CNFFormula(4, raw)
    for clause in formula.clauses:
        if len(clause) < 2:
            continue
        for length in range(1, len(clause)):
            for heart in combinations(clause, length):
                a, b = _children(formula, len(clause), heart)
                expected_a, expected_b = _lean_children(
                    _clauses_as_set(formula), len(clause), frozenset(heart),
                )
                assert _clauses_as_set(a) == expected_a
                assert _clauses_as_set(b) == expected_b
                assert a.nvars == b.nvars == formula.nvars
                for mask in range(1 << formula.nvars):
                    original = _set_value(_clauses_as_set(formula), mask)
                    ina, inb = _set_value(expected_a, mask), _set_value(expected_b, mask)
                    assert original == (ina or inb)
                    assert not (ina and inb)


@pytest.mark.integration
def test_negative_core_overlapping_petals_and_absorption() -> None:
    formula = CNFFormula(3, ((-1, 2), (-1, 3), (2, 3)))
    a, b = _children(formula, 2, (-1,))
    ea, eb = _lean_children(_clauses_as_set(formula), 2, frozenset((-1,)))
    assert _clauses_as_set(a) == ea
    assert _clauses_as_set(b) == eb
    assert a.nvars == b.nvars == 3


@pytest.mark.integration
def test_complete_disjoint_leaves_retain_ambient_universe() -> None:
    formula = CNFFormula(6, ((1, 2), (1, 3)))
    leaves = tuple(iter_disjoint_leaves(
        formula, reference_sparsification_parameters(3, 2),
    ))
    assert len(leaves) == 2
    assert all(leaf.formula.nvars == 6 for leaf in leaves)
    for mask in range(1 << formula.nvars):
        hits = sum(leaf.formula.satisfied_mask(mask) for leaf in leaves)
        assert hits == int(_set_value(_clauses_as_set(formula), mask))


@pytest.mark.parametrize('nvars,raw,expected', [
    (0, (), '00'),
    (1, (), '100'),
    (1, ((),), '1011000'),
    (1, ((1,),), '1011111111110101000'),
    (1, ((-1,),), '101111110101000'),
])
@pytest.mark.checkpoint
def test_lean_wire_fixed_vectors(
    nvars: int, raw: tuple[tuple[int, ...], ...], expected: str,
) -> None:
    formula = CNFFormula(nvars, raw)
    bits = encode_lean_cnf(formula)
    assert ''.join('1' if bit else '0' for bit in bits) == expected
    assert decode_lean_cnf(bits) == formula


@pytest.mark.integration
def test_lean_wire_literal_polarity_and_clause_ordering() -> None:
    # Lean encodes negative variable i with 2*(i-1), positive with +1.
    # Clause lists and clauses themselves sort by encoded numeric values.
    formula = CNFFormula(4, ((-2, 1), (3,), (1, -1), (2, -4)))
    assert encode_lean_cnf(formula) == _wire_reference(
        4, tuple(formula.clauses),
    )
    assert decode_lean_cnf(encode_lean_cnf(formula)) == formula


@pytest.mark.integration
def test_lean_wire_decodes_unreduced_lean_set_semantically() -> None:
    # A raw Lean SAT.CNF is a Finset, not necessarily normalized.
    # Importing into CNFFormula intentionally applies SAT.normalize.
    raw = ((1, -1), (1, 2), (1,), (2, -3))
    encoded = _wire_reference(3, raw)
    assert decode_lean_cnf(encoded) == CNFFormula(3, raw)


@pytest.mark.parametrize('bad', [
    (), (True,), (False, True), (True, False, True),
    (False, False, True), (False, False, 1),
])
@pytest.mark.integration
def test_lean_wire_rejects_malformed_bits(bad: tuple[object, ...]) -> None:
    with pytest.raises((ValueError, TypeError)):
        decode_lean_cnf(bad)  # type: ignore[arg-type]


@pytest.mark.checkpoint
def test_upstream_revision_and_file_blobs_are_pinned() -> None:
    path = Path(__file__).resolve().parents[2] / 'reference/lean_eth_source.json'
    pin = json.loads(path.read_text())
    assert pin['repository'] == 'openai/math'
    assert len(pin['commit']) == 40
    assert pin['toolchain'] == 'leanprover/lean4:v4.34.1'
    required = ('Encoding.lean', 'SAT.lean', 'DisjointSparsify.lean',
                'Final.lean', 'NativeLeafProgram.lean', 'FiniteFallback.lean')
    assert all(any(name.endswith(suffix) for name in pin['files']) for suffix in required)
    assert all(len(value) == 40 for value in pin['files'].values())
