"""Conservative paper-schedule edge, vertex and precision envelopes.

These envelopes apply along a potential execution path, including those that
later refuse capacity. They do not bound arbitrary vertex-oracle work,
Hermite rational intermediates, or the complete local bit-operation cost.
"""
from __future__ import annotations

from dataclasses import dataclass

from non_exponential_sudoku.contraction.engine import paper_schedule_parameters
from non_exponential_sudoku.runtime.config import ContractorConfig


@dataclass(frozen=True)
class PaperFrameEnvelope:
    depth: int
    edges: int
    vertices: int
    precision: int
    terminal: bool
    slots: int
    centers: int
    evaluations_per_center: int
    children_per_evaluation: int
    child_edges: int
    child_vertices: int
    child_precision: int


def paper_frame_envelopes(
    config: ContractorConfig, edges: int, vertices: int,
    *, precision: int | None = None, depth: int = 0,
) -> tuple[PaperFrameEnvelope, ...]:
    """Bounds on all possible paths of paper-schedule calls.

    The bound assumes validated network incidence: exactly two ports per
    edge, and each nonempty packet owns at least one edge. A child contains
    at most V retained vertices plus M packet vertices. Returning early or
    refusing capacity only shortens a path.
    """
    if config.schedule != "paper":
        raise ValueError("This envelope applies only to the literal paper schedule")
    if edges < 0 or vertices < 0 or depth < 0:
        raise ValueError("edges, vertices and depth must be nonnegative")
    p = config.precision if precision is None else precision
    if p < 1:
        raise ValueError("precision must be positive")
    lam = max(1, (config.s - 1).bit_length())
    frames: list[PaperFrameEnvelope] = []
    m, v, d = edges, vertices, depth
    while True:
        groups, a, u, h_leaf = paper_schedule_parameters(config.s, lam, d)
        active_possible = u > 0 and m > h_leaf and m >= u
        if not active_possible:
            frames.append(PaperFrameEnvelope(d, m, v, p, True, 0, 0, 0, 0, m, v, p))
            return tuple(frames)
        L = 1 << a
        centers = 2 * L - 1
        # Here q = ceil(3*M/u) * max(0,u-v2(t)); maximum at v2(t)=0.
        h = (3 * m + u - 1) // u
        high_precision = p + 8 * h * L + 8 * m * (a + 1)
        sample_count = m * centers + 1
        children = (config.limits.max_child_contractions
                    if config.mode.strategy == "eliminate"
                    else groups * config.mode.max_tuples)
        child_m = 3 * m // 32
        # Each child retains at most V original vertices and adds <= M packet
        # vertices; this is a bound even with zero-port retained vertices.
        child_v = v + m
        frames.append(PaperFrameEnvelope(
            d, m, v, p, False, L, centers, sample_count, children,
            child_m, child_v, high_precision,
        ))
        m, v, p, d = child_m, child_v, high_precision, d + 1


def max_padic_vector_bits(config: ContractorConfig, frames: tuple[PaperFrameEnvelope, ...]) -> int:
    """Maximum canonical Padic vector payload along the hypothetical path.

    This excludes Python object overhead, Taylor jets, and rational recovery.
    Paper recovery is interpolation only under validated ContractorConfig.
    """
    if config.schedule != "paper":
        raise ValueError("paper configuration required")
    e = max(2, 4 * max(1, (config.s - 1).bit_length()))
    if not frames:
        raise ValueError("at least one frame required")
    return e * max(max(frame.precision, frame.child_precision) for frame in frames)


def recursive_call_bound_from_frames(frames: tuple[PaperFrameEnvelope, ...]) -> int:
    """Unfold the same inductive call bound using a paper-size envelope."""
    if not frames:
        raise ValueError("at least one frame required")
    bound = 1
    for frame in reversed(frames):
        if not frame.terminal:
            bound = (1 + frame.centers * frame.evaluations_per_center *
                     frame.children_per_evaluation * bound)
    return bound
