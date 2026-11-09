"""Bounded, opt-in observations of mathematical work and structural reuse.

A topology match is not a result match. Exact-input *candidates* also do not
prove safe memoization when arbitrary input vertex oracles have mutable state.
Tracing records outer calls, not hidden native operations or coefficient memory
residency. No trace object is created during ordinary contraction.
"""
from __future__ import annotations

from collections import Counter
from dataclasses import asdict, dataclass
from time import perf_counter_ns
from typing import Literal


@dataclass(frozen=True)
class WorkEvent:
    sequence: int
    operation: str
    topology_id: str
    input_id: str
    start_offset_ns: int
    end_offset_ns: int
    elapsed_ns: int
    output_coordinates: int | None
    status: Literal["completed", "failed"]
    cache_hit: bool


class WorkTrace:
    """Capture at most ``max_events`` events and ``max_keys`` identities.

    Summary counters include dropped events; distinct-key and repeated-work
    counts only include tracked keys. A key-budget overflow is explicit and
    never misclassified as a unique or repeated computation.
    """

    def __init__(self, *, max_events: int = 20_000, max_keys: int = 20_000) -> None:
        if max_events < 1 or max_keys < 1:
            raise ValueError("Trace budgets must be positive")
        self.max_events = max_events
        self.max_keys = max_keys
        self.events: list[WorkEvent] = []
        self._topologies: dict[tuple[str, object], str] = {}
        self._inputs: dict[tuple[str, object], str] = {}
        self.operations: Counter[str] = Counter()
        self.cache_hits: Counter[str] = Counter()
        self.repeated_topologies: Counter[str] = Counter()
        self.repeated_inputs: Counter[str] = Counter()
        self.unclassified_topologies: Counter[str] = Counter()
        self.unclassified_inputs: Counter[str] = Counter()
        self.failed: Counter[str] = Counter()
        self.output_peak: dict[str, int] = {}
        self.dropped_events = 0
        self.sequence = 0
        self._epoch_ns = perf_counter_ns()

    def observe(
        self, *, operation: str, topology: object, exact_input: object,
        started_ns: int, output: object | None, cache_hit: bool = False,
        failed: bool = False,
    ) -> None:
        finished_ns = perf_counter_ns()
        self.sequence += 1
        self.operations[operation] += 1
        if cache_hit:
            self.cache_hits[operation] += 1
        if failed:
            self.failed[operation] += 1
        topology_key = (operation, topology)
        exact_key = (operation, exact_input)
        # Intern only bounded, hashable identities. Formatting the entire key
        # would recursively stringify exact, potentially enormous coefficients.
        identifiers: list[str] = []
        for kind, key, seen, repeats, unclassified in (
            ("topology", topology_key, self._topologies, self.repeated_topologies,
             self.unclassified_topologies),
            ("input", exact_key, self._inputs, self.repeated_inputs,
             self.unclassified_inputs),
        ):
            identifier = seen.get(key)
            if identifier is not None:
                repeats[operation] += 1
            elif len(seen) < self.max_keys:
                identifier = f"{kind}:{len(seen) + 1}"
                seen[key] = identifier
            else:
                unclassified[operation] += 1
                identifier = f"{kind}:unclassified"
            identifiers.append(identifier)
        size = (len(output) if isinstance(output, tuple) else
                1 if output is not None else None)
        if size is not None:
            self.output_peak[operation] = max(self.output_peak.get(operation, 0), size)
        if len(self.events) < self.max_events:
            # IDs are interned within this run, never portable fingerprints.
            self.events.append(WorkEvent(
                self.sequence, operation, identifiers[0], identifiers[1],
                max(0, started_ns - self._epoch_ns),
                max(0, finished_ns - self._epoch_ns),
                max(0, finished_ns - started_ns), size,
                "failed" if failed else "completed", cache_hit,
            ))
        else:
            self.dropped_events += 1

    def report(self) -> dict[str, object]:
        def counts(mapping: Counter[str]) -> dict[str, int]:
            return dict(sorted(mapping.items()))

        return {
            "schema_version": "1.0",
            "scope": "optional observed operations; not an equivalence or complexity proof",
            "operation_counts": counts(self.operations),
            "cache_hits": counts(self.cache_hits),
            "tracked_unique_topologies": len(self._topologies),
            "tracked_unique_exact_input_candidates": len(self._inputs),
            "repeated_topologies": counts(self.repeated_topologies),
            "repeated_exact_input_candidates": counts(self.repeated_inputs),
            "unclassified_topologies": counts(self.unclassified_topologies),
            "unclassified_exact_inputs": counts(self.unclassified_inputs),
            "failed_operations": counts(self.failed),
            "peak_top_level_result_coordinates": dict(sorted(self.output_peak.items())),
            "truncation": {"events": self.dropped_events,
                           "max_events": self.max_events,
                           "max_keys_per_identity_kind": self.max_keys},
            "events": [asdict(event) for event in self.events],
            "interpretation": [
                "Topology equality does not imply equivalent coefficient values",
                "Exact-input candidates depend on process-local object identity and cannot authorize caching of arbitrary mutable oracles",
                "Event identities are within-run interned labels, not hashes or cross-run fingerprints",
                "Each event duration includes nested work; durations cannot be summed as exclusive time",
                "Output size is top-level coordinates, not allocated bytes or value lifetime",
                "Native calls and implicit coefficient allocations are not decomposed",
            ],
        }
