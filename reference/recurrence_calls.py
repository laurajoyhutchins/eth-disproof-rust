"""Proved upper bound on *recursive call count*, not total bit complexity.

This separately models both experimental schedules and the literal paper
schedule. It does not construct a network or assume that an arbitrary vertex
oracle has bounded evaluation time. See docs/recurrence.md for the proof.
"""
from __future__ import annotations

from math import isqrt

from non_exponential_sudoku.runtime.config import ContractorConfig

EPS_DENOM = 128 * 1024


def recursive_call_bound(config: ContractorConfig, wires: int, depth: int = 0) -> int:
    """Upper bound on recursive contract() entries in any terminating run.

    A capacity refusal can terminate earlier. The bound is on invocation
    count, not running time, memory, or a successful exact Sudoku decision.
    """
    if wires < 0 or depth < 0:
        raise ValueError("wires and depth must be nonnegative")
    if config.schedule == "paper":
        log_s = max(1, (config.s - 1).bit_length())
        divisor = max(1, isqrt(log_s))
        threshold = (config.s + divisor - 1) // divisor
        u = log_s // (EPS_DENOM * (1 << depth))
        if u < 1 or wires <= threshold:
            return 1
        a = 2 * sum(log_s // (EPS_DENOM * (1 << level))
                    for level in range(depth + 1))
        groups = 64
        next_wires = 3 * wires // 32
    else:
        threshold = config.leaf.micro_threshold if depth < config.micro_active_depth else wires
        if (depth >= config.micro_active_depth or wires <= threshold or
            (depth > 0 and config.leaf.adaptive_limit and
             wires <= min(config.leaf.adaptive_limit, config.leaf.limit))):
            return 1
        groups = 2 if config.schedule == "micro" else 64
        slots = 1 if groups == 2 else 2
        a = slots
        # Each child edge comes from a parent vertex port. The two sides of
        # a parent network contain exactly 2*wires ports in total.
        next_wires = 2 * wires
    L = 1 << a
    centers = 2 * L - 1
    evaluations = 1 if config.recovery.method == "jet" else wires * centers + 1
    children_per_evaluation = (
        config.limits.max_child_contractions
        if config.mode.strategy == "eliminate" else
        groups * config.mode.max_tuples
    )
    return (1 + centers * evaluations * children_per_evaluation *
            recursive_call_bound(config, next_wires, depth + 1))
