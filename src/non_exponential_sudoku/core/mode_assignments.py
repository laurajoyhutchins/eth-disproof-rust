"""One exact, iterative mode-assignment feasibility engine.

For a scoped assignment beta, require positive-weight total < precision,
per-mode finite domains, and optionally a target packet/group row capacity.
The last constraint is necessary only for literal paper PacketEntry targets;
it is not a general restriction on arbitrary child-factor callbacks.

This iterator intentionally does NOT test the more expensive Hall matching
condition. That remains an independent, opt-in reference diagnostic.
"""
from __future__ import annotations

from collections.abc import Callable, Iterator, Sequence
from typing import TypeVar

from .modes import Mode

_Error = TypeVar("_Error", bound=Exception)


def mode_domains(modes: Sequence[Mode], precision: int) -> tuple[range, ...]:
    """Canonical mode multiplicity domains, including the zero assignment."""
    if type(precision) is not int or precision < 1:
        raise ValueError('positive integer precision required')
    if any(type(m.weight) is not int or m.weight < 1 for m in modes):
        raise ValueError('mode weights must be positive integers')
    return tuple(range(min(len(m.rows), (precision - 1) // m.weight) + 1)
                 for m in modes)


def iter_mode_assignments(
    modes: Sequence[Mode], precision: int, *,
    scope: Sequence[int] | None = None,
    target_groups: Sequence[int] = (),
    domains: Sequence[range] | None = None,
    max_states: int | None = None,
    capacity_error: type[Exception] = RuntimeError,
    label: str = 'mode assignments',
    work: Callable[[], None] | None = None,
) -> Iterator[tuple[int, ...]]:
    """Yield every feasible tuple exactly once in lexicographic order.

    Target-row caps count *distinct* rows in the union of a packet's targeted
    modes, not the sum of individual mode.row counts. Source-tile modes have
    no target-row cap. Prefix feasibility is monotone, so a rejected prefix
    cannot acquire a valid extension. Iteration uses O(|scope| + #packets)
    workspace regardless of the number of feasible assignments.

    A supplied work callback is charged for each explored candidate state,
    including rejected prefixes, for independent resource accounting.
    ``max_states`` refuses *before* yielding an additional over-limit tuple.
    """
    canonical = mode_domains(modes, precision)
    chosen = tuple(range(len(modes))) if scope is None else tuple(scope)
    if (any(type(j) is not int or j < 0 or j >= len(modes) for j in chosen)
            or len(set(chosen)) != len(chosen)):
        raise ValueError('scope must contain unique valid mode indices')
    if max_states is not None and (type(max_states) is not int or max_states < 1):
        raise ValueError('max_states must be positive or None')
    if domains is not None:
        if len(domains) != len(modes):
            raise ValueError('domain count differs from mode count')
        if any(not isinstance(d, range) or d.start != 0 or d.step != 1
               or len(d) < 1 or len(d) > len(canonical[j])
               for j, d in enumerate(domains)):
            raise ValueError('domains must be zero-based subsets of canonical mode domains')
        actual_domains = tuple(domains)
    else:
        actual_domains = canonical
    if any(type(g) is not int for g in target_groups):
        raise ValueError('target group labels must be integers')
    target_set = set(target_groups)
    eligible: dict[tuple[int, int], set[int]] = {}
    for j in chosen:
        m = modes[j]
        if m.target in target_set:
            eligible.setdefault((m.target, m.packet), set()).update(m.rows)
    caps = {key: len(rows) for key, rows in eligible.items()}
    used = dict.fromkeys(caps, 0)
    keys = tuple((modes[j].target, modes[j].packet)
                 if (modes[j].target, modes[j].packet) in caps else None
                 for j in chosen)
    n = len(chosen)
    if not n:
        yield ()
        return
    assignment = [0] * n
    remaining = [precision - 1] * (n + 1)
    level = 0
    yielded = 0
    while level >= 0:
        if work is not None:
            work()
        j = chosen[level]
        m = modes[j]
        count = assignment[level]
        key = keys[level]
        if (count >= len(actual_domains[j]) or
                m.weight * count > remaining[level] or
                (key is not None and used[key] + count > caps[key])):
            assignment[level] = 0
            level -= 1
            if level >= 0:
                parent_key = keys[level]
                if parent_key is not None:
                    used[parent_key] -= assignment[level]
                assignment[level] += 1
            continue
        remaining[level + 1] = remaining[level] - m.weight * count
        if level == n - 1:
            yielded += 1
            if max_states is not None and yielded > max_states:
                raise capacity_error(
                    f'Mode DP factor size limit ({label}: more than {max_states} feasible states)'
                )
            yield tuple(assignment)
            assignment[level] += 1
        else:
            if key is not None:
                used[key] += count
            level += 1
            assignment[level] = 0
