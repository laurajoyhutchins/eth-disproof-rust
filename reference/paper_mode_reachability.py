"""Combinatorial reachability envelope for literal paper-schedule packet tables.

A row contributes either no target exponent or one unit to one target
mode. This bounds *reachable* dictionary keys independently of their full
Cartesian exponent-box size. The proof concerns prepared Python packet
entries, not global mode elimination, arithmetic bit cost, or non-refusal.
"""
from __future__ import annotations

from dataclasses import dataclass
from math import comb, prod
from collections.abc import Sequence

from non_exponential_sudoku.contraction.engine import paper_schedule_parameters
from non_exponential_sudoku.runtime.config import ContractorConfig
from reference.precision_envelope import paper_frame_envelopes


PAPER_EXPONENT_DENOMINATOR = 32768


def reachable_state_ceiling(multiplicities: Sequence[int], rows_processed: int) -> int:
    """Upper bound on distinct exponent keys after a given number of rows.

    By induction, every key satisfies 0 <= alpha_i <= beta_i and
    sum(alpha_i) <= rows_processed. Stars-and-bars counts all nonnegative
    vectors with total <= rows_processed; each box constraint can only
    remove keys. No intermediate exponent vector is materialized here.
    """
    if type(rows_processed) is not int or rows_processed < 0:
        raise ValueError("rows_processed must be a nonnegative integer")
    if any(type(b) is not int or b < 0 for b in multiplicities):
        raise ValueError("multiplicities must be nonnegative integers")
    k = len(multiplicities)
    return min(prod(b + 1 for b in multiplicities), comb(k + rows_processed, rows_processed))


def reachable_transition_ceiling(
    multiplicities: Sequence[int], row_contributions: Sequence[int],
) -> int:
    """Maximum table transitions, evaluated before each row's update.

    Each existing key causes exactly one constant update and at most
    `row_contributions[j]` targeted updates. This counts outer ring
    additions and multiplications, not the bit cost of those calls.
    """
    if any(type(c) is not int or c < 0 or c > len(multiplicities)
           for c in row_contributions):
        raise ValueError("row contribution counts must be between 0 and k")
    return sum(
        (1 + c) * reachable_state_ceiling(multiplicities, j)
        for j, c in enumerate(row_contributions)
    )


def paper_mode_count_ceiling(precision: int, slots: int) -> int:
    """Modes targeting one group in one packet at any nonzero paper center.

    The engine requests a mode catalog only for centers with v2(t)<u.
    On the paper schedule a>=2*u, so i=v2(t)<a and the y0 loop has
    2**(i+1)<=L iterations. At t=-L, v2(t)=a and q=0: this center
    is never passed to mode_catalog. Each y0 has at most p-1 b values.
    This ignores exclusions,
    so it is a valid overestimate even for padded, partly empty packets.
    """
    if type(precision) is not int or precision < 1:
        raise ValueError("precision must be positive")
    if type(slots) is not int or slots < 1 or slots & (slots - 1):
        raise ValueError("slots must be a positive power of two")
    return (precision - 1) * slots


@dataclass(frozen=True)
class PaperPacketStateExponent:
    """An upper bound on log2 of per-packet reachable key count.

    The bound is symbolic and does not allocate 2**exponent keys or
    assume that the packet can actually be constructed at this size.
    """

    depth: int
    slots: int
    precision: int
    target_modes_ceiling: int
    log2_reachable_states_ceiling: int


def paper_packet_state_exponents(
    config: ContractorConfig, *, edges: int, vertices: int,
) -> tuple[PaperPacketStateExponent, ...]:
    """Conditional path bounds for the literal paper/interpolate schedule.

    A paper-active frame evaluates centers at precision <= child_precision.
    Every packet has <= L row slots and <= (p-1)*L target modes, so its
    key count is <= (k+1)**L. We return an integer ceiling on log2.
    A capacity refusal or failure of the packing hypotheses does not
    establish an exact count; those are separate theorem obligations.
    """
    if config.schedule != "paper":
        raise ValueError("literal paper schedule required")
    frames = paper_frame_envelopes(config, edges, vertices)
    lam = max(1, (config.s - 1).bit_length())
    result: list[PaperPacketStateExponent] = []
    for frame in frames:
        if frame.terminal:
            continue
        _, a, u, _ = paper_schedule_parameters(config.s, lam, frame.depth)
        assert u > 0 and frame.slots == (1 << a)
        # The geometric-series inequality 2 * sum floor(lambda/(2^17*2^j))
        # < lambda/32768 is strict at every finite depth.
        assert PAPER_EXPONENT_DENOMINATOR * a < lam
        max_modes = paper_mode_count_ceiling(frame.child_precision, frame.slots)
        log2_bound = frame.slots * max_modes.bit_length() if max_modes else 0
        result.append(PaperPacketStateExponent(
            frame.depth, frame.slots, frame.child_precision,
            max_modes, log2_bound,
        ))
    return tuple(result)


@dataclass(frozen=True)
class UniformPaperPacketBound:
    """Uniform symbolic bound assuming M0<=s and p0<=s on a paper path.

    The premise is a *successful* application of the schedule's child
    shrinkage/precision inequalities. This does NOT prove the full solver
    admits every input or that global factor elimination is inexpensive.
    """

    input_scale: int
    lambda_bits: int
    maximum_slots: int
    maximum_precision: int
    maximum_target_modes: int
    log2_local_state_ceiling: int


def uniform_paper_packet_bound(
    *, s: int, initial_edges: int, initial_precision: int,
) -> UniformPaperPacketBound:
    """Give a size-only worst-case envelope without materializing any packet.

    If lambda=ceil(log2 s), every active slot exponent satisfies
    a_d < lambda/32768. Thus L<=2^floor((lambda-1)/32768).
    With M_d<=M_0<=s, u_d>=1, h_d=ceil(3M_d/u_d)<=3M_d,
    and a_d+1<=L_d, each active precision rise is <=32*s*Lmax.
    There are at most lambda active levels, yielding a polynomial-bit
    precision bound when the input precision itself is <=s.
    """
    if any(type(v) is not int for v in (s, initial_edges, initial_precision)):
        raise ValueError("all bounds must be exact integers")
    if s < 2 or not 0 <= initial_edges <= s or not 1 <= initial_precision <= s:
        raise ValueError("requires s>=2, M0<=s, and 1<=p0<=s")
    lam = (s - 1).bit_length()
    if lam < 131072 or initial_edges == 0:
        return UniformPaperPacketBound(s, lam, 0, initial_precision, 0, 0)
    max_slots = 1 << ((lam - 1) // PAPER_EXPONENT_DENOMINATOR)
    max_precision = initial_precision + 32 * lam * s * max_slots
    max_modes = paper_mode_count_ceiling(max_precision, max_slots)
    log2_states = max_slots * max_modes.bit_length() if max_modes else 0
    return UniformPaperPacketBound(
        s, lam, max_slots, max_precision, max_modes, log2_states,
    )
