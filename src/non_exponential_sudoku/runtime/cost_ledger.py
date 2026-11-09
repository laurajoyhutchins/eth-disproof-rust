"""Opt-in execution/cost ledger for exact recursive contractions.

This records an *observed* recursion DAG as a call tree, with exclusive work
counters on each frame. It is not a bit-complexity proof: coefficient-oracle
bodies and native kernel primitive operations remain opaque. An explicit
truncation flag records when bounded detail storage loses per-frame records;
aggregate counters continue to be updated.
"""
from __future__ import annotations

from collections import Counter
from collections.abc import Iterator, Mapping
from contextlib import contextmanager
from contextvars import ContextVar
from dataclasses import dataclass, field
from typing import Literal, TypeAlias
import json
from pathlib import Path
from time import perf_counter_ns

Status = Literal["completed", "refused", "failed", "running"]
RingCallKey: TypeAlias = tuple[str, str, str, int | None, int | None, int, int]


def _ring_call_label(key: RingCallKey) -> str:
    phase, kind, operation, precision, e, q, depth = key
    return f"{phase}/{kind}.{operation}/p={precision}/e={e}/q={q}/depth={depth}"


def _render_ring_calls(values: Mapping[RingCallKey, int]) -> dict[str, int]:
    """Format structured ring counters only at the human/JSON boundary."""
    return dict(sorted((_ring_call_label(key), count) for key, count in values.items()))


@dataclass
class OperandGeometry:
    """Observed argument geometry, NOT an estimate of elementary bit operations.

    A nested jet is visited once at its public call boundary. When its
    Python implementation recursively calls the base ring, those calls
    appear as *separate* ring-method observations and cannot be added to
    obtain a number of unique scalar operations.
    """
    calls: int = 0
    scalar_coordinates: int = 0
    sum_operand_bit_lengths: int = 0
    max_scalar_bits: int = 0
    max_coordinates_per_call: int = 0
    max_total_bits_per_call: int = 0

    def observe(self, operands: tuple[object, ...]) -> None:
        count = 0
        total_bits = 0
        maximum = 0
        stack = list(operands)
        while stack:
            value = stack.pop()
            if type(value) is int:
                size = abs(value).bit_length()
                count += 1
                total_bits += size
                maximum = max(maximum, size)
            elif isinstance(value, (tuple, list)):
                stack.extend(value)
            else:
                raise TypeError("Ring-operand geometry expects exact nested integers")
        self.calls += 1
        self.scalar_coordinates += count
        self.sum_operand_bit_lengths += total_bits
        self.max_scalar_bits = max(self.max_scalar_bits, maximum)
        self.max_coordinates_per_call = max(self.max_coordinates_per_call, count)
        self.max_total_bits_per_call = max(self.max_total_bits_per_call, total_bits)

    def combine(self, other: OperandGeometry) -> None:
        self.calls += other.calls
        self.scalar_coordinates += other.scalar_coordinates
        self.sum_operand_bit_lengths += other.sum_operand_bit_lengths
        self.max_scalar_bits = max(self.max_scalar_bits, other.max_scalar_bits)
        self.max_coordinates_per_call = max(self.max_coordinates_per_call,
                                            other.max_coordinates_per_call)
        self.max_total_bits_per_call = max(self.max_total_bits_per_call,
                                           other.max_total_bits_per_call)

    def as_dict(self) -> dict[str, int]:
        return {key: getattr(self, key) for key in (
            "calls", "scalar_coordinates", "sum_operand_bit_lengths",
            "max_scalar_bits", "max_coordinates_per_call", "max_total_bits_per_call",
        )}


def _render_operand_geometry(
    values: Mapping[RingCallKey, OperandGeometry],
) -> dict[str, dict[str, int]]:
    return dict(sorted((_ring_call_label(key), stats.as_dict())
                       for key, stats in values.items()))


_ACTIVE: ContextVar[CostLedger | None] = ContextVar("sudoku_cost_ledger", default=None)


@dataclass
class CostFrame:
    call_id: int
    parent_id: int | None
    depth: int
    wires: int
    precision: int
    ring_depth: int
    schedule: str
    status: Status = "running"
    exception: str | None = None
    # Exclusive counters: operations performed in this frame, NOT its descendants.
    work: dict[str, int] = field(default_factory=dict)
    ring_calls: dict[RingCallKey, int] = field(default_factory=dict)
    operand_geometry: dict[RingCallKey, OperandGeometry] = field(default_factory=dict)
    exclusive_wall_ns: int = 0
    child_wall_ns: int = 0
    inclusive_wall_ns: int = 0
    exclusive_phase_wall_ns: dict[str, int] = field(default_factory=dict)
    native_calls: dict[str, int] = field(default_factory=dict)
    peaks: dict[str, int] = field(default_factory=dict)

    def as_dict(self) -> dict[str, object]:
        return {
            "call_id": self.call_id, "parent_id": self.parent_id,
            "depth": self.depth, "wires": self.wires,
            "precision": self.precision, "ring_depth": self.ring_depth,
            "schedule": self.schedule, "status": self.status,
            "exception": self.exception, "work": dict(sorted(self.work.items())),
            "ring_calls": _render_ring_calls(self.ring_calls),
            "operand_geometry": _render_operand_geometry(self.operand_geometry),
            "exclusive_wall_ns": self.exclusive_wall_ns,
            "child_wall_ns": self.child_wall_ns,
            "inclusive_wall_ns": self.inclusive_wall_ns,
            "exclusive_phase_wall_ns": dict(sorted(self.exclusive_phase_wall_ns.items())),
            "native_calls": dict(sorted(self.native_calls.items())),
            "peaks": dict(sorted(self.peaks.items())),
        }


@dataclass
class Center:
    call_id: int
    t: int
    valuation: int
    jet_coefficients: int
    lifted_precision: int
    mode_count: int | None = None
    status: Status = "running"
    exception: str | None = None

    def as_dict(self) -> dict[str, object]:
        return vars(self).copy()


class CostLedger:
    """Exact *event* accounting, separate from algorithmic complexity bounds.

    Ring method invocations count at every layer (a JetRing.mul can cause base
    Padic.mul calls); they are not independent scalar/bit operations. Operations
    executed entirely inside compiled extensions are not recursively exposed.
    All observed event totals are retained even if detailed frames/centers are
    truncated to enforce the ledger's own memory cap.
    """

    def __init__(self, *, max_frames: int = 20_000,
                 max_centers: int = 20_000,
                 observe_operand_bits: bool = False) -> None:
        if max_frames < 1 or max_centers < 1:
            raise ValueError("Cost-ledger detail budgets must be positive")
        self.max_frames = max_frames
        self.max_centers = max_centers
        self.observe_operand_bits = observe_operand_bits
        self._last_tick_ns: int | None = None
        self.total_operand_geometry: dict[RingCallKey, OperandGeometry] = {}
        self.frames: list[CostFrame] = []
        self.centers: list[Center] = []
        self._stack: list[CostFrame] = []
        self._phases: list[str] = []
        self.total_work: Counter[str] = Counter()
        self.total_ring_calls: Counter[RingCallKey] = Counter()
        self.global_peaks: dict[str, int] = {}
        self.frames_observed = 0
        self.centers_observed = 0
        self.truncated_frames = 0
        self.truncated_centers = 0
        self.refusals: Counter[str] = Counter()
        self.failures: Counter[str] = Counter()
        self.native_paths: Counter[str] = Counter()

    def charge(self, event: str, n: int = 1) -> None:
        if n < 0:
            raise ValueError("Ledger event counts cannot be negative")
        if not n:
            return
        self.total_work[event] += n
        if self._stack:
            frame = self._stack[-1]
            frame.work[event] = frame.work.get(event, 0) + n

    def peak(self, metric: str, value: int) -> None:
        self.global_peaks[metric] = max(self.global_peaks.get(metric, 0), value)
        if self._stack:
            current = self._stack[-1]
            current.peaks[metric] = max(current.peaks.get(metric, 0), value)

    def ring_call(self, operation: str, ring: object,
                  operands: tuple[object, ...] = ()) -> None:
        phase = self._phases[-1] if self._phases else "unscoped"
        kind = type(ring).__name__
        precision = getattr(ring, "p", None)
        depth = getattr(ring, "depth", 0)
        # Preserve precision: a method call at p=4000 is not comparable to p=9.
        e = getattr(ring, "e", None)
        q = getattr(ring, "q", 1)
        key: RingCallKey = (phase, kind, operation, precision, e, q, depth)
        self.total_ring_calls[key] += 1
        if self._stack:
            frame = self._stack[-1]
            frame.ring_calls[key] = frame.ring_calls.get(key, 0) + 1
        if self.observe_operand_bits and operands:
            observation = OperandGeometry()
            observation.observe(operands)
            self.total_operand_geometry.setdefault(key, OperandGeometry()).combine(observation)
            if self._stack:
                self._stack[-1].operand_geometry.setdefault(
                    key, OperandGeometry()).combine(observation)

    def _tick(self) -> None:
        """Attribute one non-overlapping interval to the innermost active frame.

        The clock runs only while a frame exists. Parent times exclude
        child-frame execution. A frame's exclusive phase times partition its
        exclusive time, including any unclassified orchestration intervals.
        All measured durations include observer overhead.
        """
        now = perf_counter_ns()
        if self._stack and self._last_tick_ns is not None:
            delta = max(0, now - self._last_tick_ns)
            frame = self._stack[-1]
            frame.exclusive_wall_ns += delta
            phase = self._phases[-1]
            frame.exclusive_phase_wall_ns[phase] = (
                frame.exclusive_phase_wall_ns.get(phase, 0) + delta)
        self._last_tick_ns = now

    @contextmanager
    def frame(self, *, depth: int, wires: int, precision: int,
              ring_depth: int, schedule: str) -> Iterator[None]:
        self._tick()
        self.frames_observed += 1
        parent_id = self._stack[-1].call_id if self._stack else None
        node = CostFrame(self.frames_observed, parent_id, depth, wires,
                         precision, ring_depth, schedule)
        if len(self.frames) < self.max_frames:
            self.frames.append(node)
        else:
            self.truncated_frames += 1
        self._stack.append(node)
        self._phases.append("orchestration")
        token = _ACTIVE.set(self)
        self.charge("exhaustive_completion_calls" if schedule == "exhaustive"
                    else "recursive_calls")
        try:
            yield
        except Exception as exc:
            node.exception = type(exc).__name__
            # Classify refusals by their declared type, not their message.
            from .budget import CapacityError
            if isinstance(exc, CapacityError):
                node.status = "refused"
                self.refusals[str(exc)] += 1
            else:
                node.status = "failed"
                self.failures[type(exc).__name__] += 1
            raise
        else:
            node.status = "completed"
        finally:
            self._tick()
            node.inclusive_wall_ns = node.exclusive_wall_ns + node.child_wall_ns
            _ACTIVE.reset(token)
            self._phases.pop()
            self._stack.pop()
            if self._stack:
                self._stack[-1].child_wall_ns += node.inclusive_wall_ns
            else:
                self._last_tick_ns = None

    @contextmanager
    def phase(self, name: str) -> Iterator[None]:
        if not self._stack:
            yield
            return
        self._tick()
        self._phases.append(name)
        try:
            yield
        finally:
            self._tick()
            self._phases.pop()

    @contextmanager
    def center(self, *, t: int, valuation: int,
               coefficients: int, precision: int) -> Iterator[Center]:
        self.centers_observed += 1
        record = Center(self._stack[-1].call_id, t, valuation, coefficients, precision)
        if len(self.centers) < self.max_centers:
            self.centers.append(record)
        else:
            self.truncated_centers += 1
        self.charge("hermite_centers")
        self.charge("hermite_coefficient_slots", coefficients)
        with self.phase("interpolation_center"):
            try:
                yield record
            except Exception as exc:
                record.exception = type(exc).__name__
                from .budget import CapacityError
                record.status = "refused" if isinstance(exc, CapacityError) else "failed"
                raise
            else:
                record.status = "completed"

    def native(self, path: str) -> None:
        """Record kernel boundaries globally *and* in their owning frame."""
        self.native_paths[path] += 1
        if self._stack:
            frame = self._stack[-1]
            frame.native_calls[path] = frame.native_calls.get(path, 0) + 1

    def report(self) -> dict[str, object]:
        # Independently reconstruct the *observed* call-tree recurrence.
        # Only ring-method invocations are the additive unit here; this is
        # deliberately NOT an elementary machine- or bit-operation bound.
        complete_frames = (self.truncated_frames == 0 and
                           len(self.frames) == self.frames_observed)
        children: dict[int, list[int]] = {f.call_id: [] for f in self.frames}
        for f in self.frames:
            if f.parent_id is not None and f.parent_id in children:
                children[f.parent_id].append(f.call_id)
        subtree_ring_calls: dict[int, int] = {}
        subtree_native_calls: dict[int, int] = {}
        for f in reversed(self.frames):
            subtree_ring_calls[f.call_id] = (
                sum(f.ring_calls.values()) +
                sum(subtree_ring_calls[ch] for ch in children[f.call_id]))
            subtree_native_calls[f.call_id] = (
                sum(f.native_calls.values()) +
                sum(subtree_native_calls[ch] for ch in children[f.call_id]))
        reconciled = (complete_frames and
                      sum(f.work.get("recursive_calls", 0) +
                          f.work.get("exhaustive_completion_calls", 0)
                          for f in self.frames) == self.frames_observed and
                      sum(sum(f.ring_calls.values()) for f in self.frames)
                          == sum(self.total_ring_calls.values()) and
                      sum(sum(f.native_calls.values()) for f in self.frames)
                          == sum(self.native_paths.values()) and
                      all(f.parent_id is None or f.parent_id < f.call_id
                          for f in self.frames) and
                      all(f.inclusive_wall_ns == f.exclusive_wall_ns + f.child_wall_ns
                          and sum(f.exclusive_phase_wall_ns.values())
                              == f.exclusive_wall_ns
                          for f in self.frames) and
                      all(f.child_wall_ns == sum(
                          self.frames[ch - 1].inclusive_wall_ns
                          for ch in children[f.call_id])
                          for f in self.frames) and
                      (not self.observe_operand_bits or all(
                          sum(stats.calls for stats in f.operand_geometry.values())
                          <= sum(f.ring_calls.values()) for f in self.frames)))
        counts_by_depth: Counter[int] = Counter()
        for f in self.frames:
            counts_by_depth[f.depth] += 1
        frame_reports = []
        for f in self.frames:
            item = f.as_dict()
            item["child_call_ids"] = children[f.call_id]
            item["exclusive_ring_method_calls"] = sum(f.ring_calls.values())
            item["subtree_ring_method_calls"] = subtree_ring_calls[f.call_id]
            item["exclusive_native_kernel_calls"] = sum(f.native_calls.values())
            item["subtree_native_kernel_calls"] = subtree_native_calls[f.call_id]
            frame_reports.append(item)
        return {
            "schema_version": "1.2",
            "scope": "observed execution, not a worst-case or bit-complexity certificate",
            "observed_recurrence": "C(call) = exclusive ring-method calls + sum C(direct child calls)",
            "frames_observed": self.frames_observed,
            "centers_observed": self.centers_observed,
            "truncation": {"frames": self.truncated_frames,
                           "centers": self.truncated_centers},
            "frame_tree_reconciled": reconciled,
            "detail_complete": reconciled and self.truncated_centers == 0,
            "counts_by_depth": dict(sorted(counts_by_depth.items())),
            "work_totals": dict(sorted(self.total_work.items())),
            "ring_call_totals": _render_ring_calls(self.total_ring_calls),
            "operand_geometry_enabled": self.observe_operand_bits,
            "operand_geometry_totals": _render_operand_geometry(self.total_operand_geometry),
            "time_scope": "observational wall clock ns, includes instrumentation; per-frame exclusive time excludes child frames",
            "root_inclusive_wall_ns": sum(
                f.inclusive_wall_ns for f in self.frames if f.parent_id is None),
            "global_peaks": dict(sorted(self.global_peaks.items())),
            "opaque_native_calls": dict(sorted(self.native_paths.items())),
            "refusals": dict(sorted(self.refusals.items())),
            "failures": dict(sorted(self.failures.items())),
            "frames": frame_reports,
            "centers": [c.as_dict() for c in self.centers],
            "known_gaps": [
                "Native Cython kernels expose calls, not internal primitive operations",
                "Tensor oracle implementations have opaque internal computational costs",
                "Python allocations and elementary integer bit-operation counts are not instrumented",
                "Opt-in operand bit lengths cover only public add/sub/mul inputs, not native inner-loop temporaries",
                "Frame/phase wall-clock measurements include instrumentation overhead",
                "Observed finite call trees do not establish worst-case recurrence bounds",
                "Precision-dependent ring method calls are not uniform-cost operations",
            ],
            "worst_case_subexponential_bound_proven": False,
            "non_refusing_recursive_path_proven": False,
        }

    def write_json(self, path: str | Path) -> None:
        Path(path).write_text(json.dumps(self.report(), indent=2) + "\n", encoding="utf-8")


def active_ledger() -> CostLedger | None:
    return _ACTIVE.get()


def charge(event: str, n: int = 1) -> None:
    current = _ACTIVE.get()
    if current is not None:
        current.charge(event, n)


def ring_call(operation: str, ring: object, *operands: object) -> None:
    current = _ACTIVE.get()
    if current is not None:
        current.ring_call(operation, ring, operands)


def native_call(path: str) -> None:
    current = _ACTIVE.get()
    if current is not None:
        current.native(path)


def charge_peak(metric: str, value: int) -> None:
    current = _ACTIVE.get()
    if current is not None:
        current.peak(metric, value)
