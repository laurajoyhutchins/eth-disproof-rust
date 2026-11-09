"""Conditional schoolbook bit-cost envelopes for canonical finite ring values.

These bounds describe a specified *abstract bit-operation model*: B-bit
addition/bitwise work costs O(B), and schoolbook multiplication costs O(B**2).
The explicit numerical ceilings include deliberately generous constants for
finite-loop bookkeeping. They are not CPython instructions, native FLINT/Cython
instructions, resident process memory, ring construction, or a full solver
recurrence. They assume canonical, shape-correct input values and a supplied
irreducible modulus f. Unbounded input-oracle integers invalidate the premise.
"""
from __future__ import annotations

from dataclasses import dataclass
from math import prod
from collections.abc import Sequence

from non_exponential_sudoku.core.algebra import Padic
from non_exponential_sudoku.core.jets import JetRing


class UncertifiedRingInput(ValueError):
    """Ring arithmetic has not been supplied with canonical finite inputs."""


@dataclass(frozen=True, slots=True)
class BitOperationEnvelope:
    """One value shape and a conservative schoolbook operation-cost model.

    Payload and tuple counts are representation-independent. The bit-work
    estimates apply to the reference algorithms, with fixed schoolbook
    arithmetic and canonical input values. They are *conditional numeric
    envelopes*, not observed running times or machine-checked proof objects.
    """

    extension_degree: int
    precision: int
    jet_lengths: tuple[int, ...]  # inner first
    coordinate_count: int
    tuple_nodes: int
    canonical_payload_bits: int
    intermediate_scalar_bits: int
    add_bits: int
    sub_bits: int
    neg_bits: int
    mul_bits: int
    inv_bits: int
    # Peak abstract *temporary* coefficient storage for one arithmetic call,
    # including a conservative allowance for operands and intermediate values.
    # Excludes GC/shared-object/native/allocator overhead and stored factor tables.
    temporary_payload_bits: int

    def pow_bits(self, exponent: int) -> int:
        if type(exponent) is not int:
            raise ValueError('exponent must be an exact integer')
        n = abs(exponent)
        # Padic squares once even after the last exponent bit; JetRing does
        # not, so 2*bit_length works uniformly. Sign handling may call inv.
        return ((self.inv_bits if exponent < 0 else 0)
                + 2 * n.bit_length() * self.mul_bits
                + 16 * (n.bit_length() + 1)
                * (self.canonical_payload_bits + self.tuple_nodes + 1))


def _validate_ring(ring: Padic | JetRing) -> tuple[Padic, tuple[int, ...]]:
    lengths: list[int] = []
    base: Padic | JetRing = ring
    while isinstance(base, JetRing):
        if type(base.q) is not int or base.q < 1:
            raise ValueError('invalid Taylor length')
        lengths.append(base.q)
        base = base.base  # type: ignore[assignment]
    if not isinstance(base, Padic):
        raise TypeError('expected a Padic or finite JetRing')
    return base, tuple(reversed(lengths))


def canonical_value(ring: Padic | JetRing, value: object) -> bool:
    """Check the finite-input premise, refusing unbounded/noncanonical ints.

    Never silently normalizes high-bit inputs: that could disguise a failure
    of an oracle's output-size contract. This is a structural predicate only;
    evaluating the predicate also has a cost and is not free in the solver.
    """
    if isinstance(ring, JetRing):
        return (type(value) is tuple and len(value) == ring.q and
                all(canonical_value(ring.base, v) for v in value))  # type: ignore[arg-type]
    if isinstance(ring, Padic):
        return (type(value) is tuple and len(value) == ring.e and
                all(type(v) is int and 0 <= v < (1 << ring.p) for v in value))
    raise TypeError('expected a Padic or finite JetRing')


def finite_shape_bit_envelope(
    extension_degree: int, precision: int, jet_lengths: Sequence[int] = (),
) -> BitOperationEnvelope:
    """Solve the add/mul/inv recurrence without constructing large rings.

    Let A,B,I denote worst-case add,mul,inv bit costs in the abstract model.
    For Taylor length q over a coefficient ring C:

      A_q <= q*A_C + O(q*payload(C))
      B_q <= q(q+1)/2*(A_C+B_C) + O(q**2*payload(C))
      I_q <= I_C + q(q-1)/2*(A_C+B_C)
                     + (q-1)*(B_C+neg_C) + O(q**2*payload(C)).

    The dense bounds include skipped-zero fast paths, so support sparsity
    can only improve actual work. All levels are computed as exact integers.
    The separate modulus search and intermediate rational recovery remain
    excluded and must be accounted for independently.
    """
    e, p = extension_degree, precision
    lengths = tuple(jet_lengths)
    if (type(e) is not int or e < 2 or type(p) is not int or p < 1
            or any(type(q) is not int or q < 1 for q in lengths)):
        raise ValueError('finite canonical coefficient shape required')
    # A convolution coefficient is a sum of at most e p-bit products plus
    # at most e reduced p-bit terms. This safely bounds absolute
    # intermediate integer bit lengths for canonical operands.
    B = 2 * p + (e + 1).bit_length() + 4
    A = 32 * (e + 1) * (B + 1)
    N = A
    M = 64 * (e + 1) ** 2 * (B + 1) ** 2
    # The GF(2**e) seed uses O(e) carryless polynomial multiplications,
    # each O(e**2) bit operations, followed by bit_length(p)+1 Newton
    # rounds (two multiplications and one subtraction each), then an
    # explicit correctness multiply. Modulus f is assumed already known.
    I = (128 * (e + 1) ** 3
         + (p.bit_length() + 1) * (2 * M + A) + M)
    coords = e
    nodes = 1   # one coordinate tuple
    payload = e * p
    # One Padic convolution holds 2e-1 temporary signed integer values,
    # input/output tuples and Newton iterates. Deliberately loose.
    temporary = (2 * e + 12) * (e * p + B + 1)
    for q in lengths:
        old_payload = payload
        old_nodes = nodes
        # Charge index comparisons, zero scans, tuple/allocation work and
        # bounded-value equality, independent of the Python/native dispatch.
        O = 64 * (q + 1) ** 2 * (old_payload + old_nodes + q.bit_length() + 1)
        pairs = q * (q + 1) // 2
        inv_pairs = q * (q - 1) // 2
        next_A = q * A + O
        next_N = q * N + O
        next_M = pairs * (M + A) + O
        next_I = I + inv_pairs * (M + A) + (q - 1) * (M + N) + O
        # Peak local scratch is bounded by several dense coefficient
        # vectors plus one live recursive base operation. This is not a
        # process-RSS bound: pointer widths, shared values, allocator
        # state and non-ring factor tables are excluded.
        temporary = max(temporary, (6 * q + 12) * (old_payload + old_nodes + B + 1)
                        + temporary)
        coords *= q
        payload *= q
        nodes = 1 + q * old_nodes
        A, N, M, I = next_A, next_N, next_M, next_I
    return BitOperationEnvelope(
        extension_degree=e, precision=p, jet_lengths=lengths,
        coordinate_count=coords, tuple_nodes=nodes,
        canonical_payload_bits=payload, intermediate_scalar_bits=B,
        add_bits=A, sub_bits=A, neg_bits=N, mul_bits=M, inv_bits=I,
        temporary_payload_bits=temporary,
    )


def bit_operation_envelope(ring: Padic | JetRing) -> BitOperationEnvelope:
    """Specialize the allocation-free recurrence to a real validated ring."""
    base, lengths = _validate_ring(ring)
    return finite_shape_bit_envelope(base.e, base.p, lengths)


def canonical_cost_envelope(ring: Padic | JetRing, *values: object) -> BitOperationEnvelope:
    """Bound a particular operation only when all operands meet its premise."""
    if not values or not all(canonical_value(ring, v) for v in values):
        raise UncertifiedRingInput('canonical, shape-correct ring operands required')
    return bit_operation_envelope(ring)


def family_payload_envelope(
    extension_degree: int, precision: int, jet_lengths: Sequence[int],
) -> tuple[int, int, int]:
    """Allocation-free formula: coordinates, canonical payload bits, tuple nodes.

    Unlike bit_operation_envelope, this need not instantiate an enormous
    precision ring or enumerate its exponentially large elements. It makes
    **no** claim about object allocation or a real execution succeeding.
    """
    if (type(extension_degree) is not int or extension_degree < 2
            or type(precision) is not int or precision < 1
            or any(type(q) is not int or q < 1 for q in jet_lengths)):
        raise ValueError('invalid finite-ring shape')
    coords = extension_degree * prod(jet_lengths)
    nodes = 1
    for q in jet_lengths:
        nodes = 1 + q * nodes
    return coords, coords * precision, nodes


def paper_padic_bit_envelopes(
    config: object, *, edges: int, vertices: int,
) -> tuple[BitOperationEnvelope, ...]:
    """Paper path: symbolic precision bounds at each depth, with NO jets.

    The literal paper configuration forbids jet recovery; each coefficient
    arithmetic call is over Padic at its current center precision. This
    does not charge interpolation, factor states, rational recovery, or
    modulus search. It proves *one ring operation* has polynomially sized
    schoolbook work given the published precision path hypotheses.
    """
    from non_exponential_sudoku.runtime.config import ContractorConfig
    from reference.precision_envelope import paper_frame_envelopes

    if not isinstance(config, ContractorConfig) or config.schedule != 'paper':
        raise ValueError('paper schedule with interpolation is required')
    lam = max(1, (config.s - 1).bit_length())
    e = max(2, 4 * lam)
    frames = paper_frame_envelopes(config, edges, vertices)
    return tuple(finite_shape_bit_envelope(e, f.child_precision) for f in frames)
