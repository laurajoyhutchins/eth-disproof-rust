"""Structural work envelope for one already-prepared Python packet entry.

This counts *outer coefficient-ring calls* made by PacketEntry._evaluate_python,
not bit operations and not coefficient preparation, embedding, caches or Python
allocation/hash costs. It is an ingredient, not closure of a bit recurrence.
"""
from __future__ import annotations

from dataclasses import dataclass
from math import prod
from typing import TYPE_CHECKING

if TYPE_CHECKING:
    from non_exponential_sudoku.contraction.packets import PacketEntry


@dataclass(frozen=True)
class PacketEvaluationEnvelope:
    rows: int
    target_modes: int
    coefficient_states: int
    table_transitions: int
    additions: int
    subtractions: int
    negations: int
    multiplications: int
    scalar_constructions: int
    powers: int
    maximum_integer_power_bits: int
    coefficient_payload_bits: int
    exponent_key_payload_bits: int
    prepared_coefficient_slots: int
    prepared_coefficient_payload_bits: int

    @property
    def ring_calls(self) -> int:
        return (self.additions + self.subtractions + self.negations
                + self.multiplications + self.scalar_constructions + self.powers)


def coefficient_state_capacity(multiplicities: tuple[int, ...]) -> int:
    """Every exponent coordinate lies in [0, beta_i]; never enumerate states."""
    if any(type(b) is not int or b < 0 for b in multiplicities):
        raise ValueError('target mode multiplicities must be nonnegative integers')
    return prod(b + 1 for b in multiplicities)


def coefficient_payload_bits(ring: object) -> int:
    """Canonical scalar payload width in a finite Padic / nested JetRing.

    This does not cover temporary Python integers, fractions, Python object
    overhead, expression DAGs, or native FLINT memory. The ring must be one
    of the actual finite coefficient rings.
    """
    from non_exponential_sudoku.core.algebra import Padic
    from non_exponential_sudoku.core.jets import JetRing

    if not isinstance(ring, (Padic, JetRing)):
        raise TypeError('a finite Padic or JetRing is required')
    digits = ring.e
    layer: Padic | JetRing = ring
    while isinstance(layer, JetRing):
        digits *= layer.q
        layer = layer.base  # type: ignore[assignment]
    return digits * ring.p


def packet_evaluation_envelope(entry: PacketEntry) -> PacketEvaluationEnvelope:
    """Conservative call envelope derived from the actual prepared topology.

    The eager Python implementation keeps a dictionary keyed by a bounded
    exponent tuple. At every row it processes at most S states, and each
    state has one constant transition plus at most c_row contributions.
    Without target modes the algorithm follows a separate linear path.
    Every source tile contributes one final scalar-power/multiplication.
    """
    from non_exponential_sudoku.core.algebra import Padic
    from non_exponential_sudoku.core.jets import JetRing

    if not isinstance(entry.work_ring, (Padic, JetRing)):
        raise TypeError('only eager finite-ring Python packet evaluation is bounded')
    if getattr(entry, 'native', None) is not None:
        raise TypeError('native packet evaluation requires a separate cost argument')
    shape = entry.geometry.row_terms
    desired = entry.terms.desired
    states = coefficient_state_capacity(desired)
    if len(desired) != len(entry.terms.target):
        raise ValueError("target multiplicity vector does not match modes")
    for row, _, _ in shape:
        for index, _ in entry.terms.contributions.get(row, ()):
            if type(index) is not int or not 0 <= index < len(desired):
                raise ValueError("packet contribution references invalid target mode")
    rows = len(shape)
    target = bool(desired)
    additions = sum(len(right) for _, _, right in shape)
    subtractions = rows
    negations = sum(len(entry.terms.contributions[row]) for row, _, _ in shape) if target else 0
    transitions = 0
    multiplications = rows if not target else 0
    if target:
        transitions = sum(states * (1 + len(entry.terms.contributions[row]))
                          for row, _, _ in shape)
        additions += transitions
        multiplications += transitions
    # Python tests 'bits[pos]' before making each term; use full tile size.
    tiles = entry.terms.tile_bits
    additions += sum(len(tile) for _, _, tile in tiles)
    scalar_constructions = sum(len(tile) for _, _, tile in tiles)
    multiplications += len(tiles)
    power_bits = max((max(1, abs(coefficient).bit_length()) * max(1, mode.b)
                      for mode, _, tile in tiles for _, coefficient in tile), default=0)
    payload = coefficient_payload_bits(entry.R)
    slots = len(entry.cauchy) + sum(len(v) for v in entry.terms.contributions.values())
    return PacketEvaluationEnvelope(
        rows=rows,
        target_modes=len(desired),
        coefficient_states=states,
        table_transitions=transitions,
        additions=additions,
        subtractions=subtractions,
        negations=negations,
        multiplications=multiplications,
        scalar_constructions=scalar_constructions,
        powers=len(tiles),
        maximum_integer_power_bits=power_bits,
        coefficient_payload_bits=payload,
        exponent_key_payload_bits=sum(max(1, b.bit_length()) for b in desired),
        prepared_coefficient_slots=slots,
        prepared_coefficient_payload_bits=slots * payload,
    )
