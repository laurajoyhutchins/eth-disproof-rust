"""One-off native overhead decomposition using real recursive benchmark cases.

Data are diagnostic: sampling and Python instrumentation change cache and CPU
conditions. Never use this output by itself to change production defaults.
"""
from __future__ import annotations

import json
import sys
from collections import Counter, defaultdict
from pathlib import Path
from statistics import median
from time import perf_counter_ns
from typing import Any, Callable

import native_recursive
from benchmarks.recursive_cases import IDS, get_case
from non_exponential_sudoku.contraction.packets import NativePacketTerms, PacketEntry
from non_exponential_sudoku.contraction.engine import ContractionEngine
from non_exponential_sudoku.core.network import compile_leaf_plan, eliminate_leaf


def time_call(fn: Callable[[], object]) -> float:
    start = perf_counter_ns()
    fn()
    elapsed = perf_counter_ns() - start
    repeats = 64 if elapsed < 20_000 else 8 if elapsed < 300_000 else 2
    samples: list[float] = []
    for _ in range(5):
        start = perf_counter_ns()
        for _ in range(repeats):
            fn()
        samples.append((perf_counter_ns() - start) / repeats)
    return median(samples)


def category(packet: PacketEntry) -> str:
    n = len(packet.terms.desired)
    return "0" if n == 0 else ("1" if n == 1 else ("2" if n == 2 else "3+"))


def native_prep(packet: PacketEntry) -> NativePacketTerms:
    right = packet.geometry.right_positions
    geometry = packet.geometry
    return NativePacketTerms(
        left_positions=tuple(geometry.port_map["Y", row] for row in packet.rows),
        row_cauchy=tuple(
            tuple((slot, packet.cauchy[slot - row]) for slot, _ in right)
            for row in packet.rows
        ),
        contributions=tuple(packet.terms.contributions[row] for row in packet.rows),
        right_positions=right,
    )


def raw_packet(packet: PacketEntry, bits: tuple[int, ...]) -> object:
    native = packet.native
    assert native is not None
    return native_recursive.packet_evaluate(
        bits, packet.work_ring,
        native.left_positions, native.row_cauchy, native.contributions,
        packet.terms.desired, packet.terms.tile_slots, native.right_positions,
    )


def packet_probe(name: str) -> dict[str, Any]:
    original_call = PacketEntry.__call__
    original_init = PacketEntry.__init__
    calls: Counter[str] = Counter()
    created: Counter[str] = Counter()
    samples: dict[str, list[tuple[PacketEntry, tuple[int, ...]]]] = defaultdict(list)
    failures: list[str] = []

    def observe_init(self: PacketEntry, *args: Any, **kwargs: Any) -> None:
        original_init(self, *args, **kwargs)
        if self.native is not None:
            created[category(self)] += 1

    def observe_call(self: PacketEntry, bits: tuple[int, ...], R: Any) -> Any:
        if self.native is not None:
            key = category(self)
            calls[key] += 1
            if len(samples[key]) < 6:
                samples[key].append((self, tuple(bits)))
        return original_call(self, bits, R)

    PacketEntry.__init__ = observe_init  # type: ignore[method-assign]
    PacketEntry.__call__ = observe_call  # type: ignore[method-assign]
    try:
        answer, _ = get_case(name, "packet").validate()
    finally:
        PacketEntry.__call__ = original_call  # type: ignore[method-assign]
        PacketEntry.__init__ = original_init  # type: ignore[method-assign]

    records: list[dict[str, Any]] = []
    for key, members in sorted(samples.items()):
        for packet, bits in members:
            python_result = packet._evaluate_python(bits)
            raw_result = raw_packet(packet, bits)
            native_result = packet._evaluate_native(bits)
            if not (python_result == raw_result == native_result):
                failures.append(f"{name}: {key} unequal packet result")
                continue
            records.append({
                "category": key,
                "rows": len(packet.rows),
                "right_slots": len(packet.geometry.right_positions),
                "tile_terms": len(packet.terms.tile_slots),
                "python_ns": time_call(lambda: packet._evaluate_python(bits)),
                "native_raw_ns": time_call(lambda: raw_packet(packet, bits)),
                "native_wrapper_ns": time_call(lambda: packet._evaluate_native(bits)),
                "native_prep_ns": time_call(lambda: native_prep(packet)),
            })
    if failures:
        raise AssertionError(failures)

    groups: dict[str, dict[str, Any]] = {}
    for key in sorted(calls):
        subset = [r for r in records if r["category"] == key]
        if not subset:
            continue
        rows = {field: median(r[field] for r in subset)
                for field in ("python_ns", "native_raw_ns", "native_wrapper_ns", "native_prep_ns")}
        # Extrapolation uses per-category medians and measured call/object counts.
        groups[key] = {
            "calls": calls[key], "created": created[key],
            "samples": len(subset),
            "median_ns": rows,
            "estimated_python_eval_ms": calls[key] * rows["python_ns"] / 1e6,
            "estimated_native_eval_ms": calls[key] * rows["native_wrapper_ns"] / 1e6,
            "estimated_native_prep_ms": created[key] * rows["native_prep_ns"] / 1e6,
            "estimated_wrapper_ms": calls[key] * (rows["native_wrapper_ns"] - rows["native_raw_ns"]) / 1e6,
            "estimated_kernel_delta_ms": calls[key] * (rows["native_raw_ns"] - rows["python_ns"]) / 1e6,
        }
    return {"case": name, "answer": answer, "total_calls": sum(calls.values()),
            "total_created": sum(created.values()), "groups": groups, "samples": records}


def leaf_probe(name: str) -> dict[str, Any]:
    original = ContractionEngine._leaf_impl
    samples: list[tuple[Any, Any, Any]] = []
    calls = 0

    def capture(self: ContractionEngine, net: Any, ring: Any) -> Any:
        nonlocal calls
        calls += 1
        if len(samples) < 8 and net.edges > 0:
            samples.append((net, ring, self.config.leaf))
        return original(self, net, ring)

    ContractionEngine._leaf_impl = capture  # type: ignore[method-assign]
    try:
        answer, _ = get_case(name, "leaf").validate()
    finally:
        ContractionEngine._leaf_impl = original  # type: ignore[method-assign]

    records: list[dict[str, Any]] = []
    for net, ring, policy in samples:
        scopes = tuple(v.ports for v in net.left + net.right if v.ports)
        plan = compile_leaf_plan(
            net.edges, scopes,
            max_width=policy.max_width,
            lookup_budget=policy.lookup_entries,
        )
        args = (net, ring, policy.limit)
        ref = lambda: eliminate_leaf(
            *args, max_width=policy.max_width,
            max_factor_bytes=policy.max_factor_bytes,
        )
        compiled = lambda: eliminate_leaf(
            *args, max_width=policy.max_width, plan=plan,
            max_factor_bytes=policy.max_factor_bytes,
        )
        native = lambda: native_recursive.eliminate_leaf(
            *args, policy.max_width,
        )
        expected = ref()
        if native() != expected:
            raise AssertionError(f"native leaf disagrees: {name}")
        if plan is not None and compiled() != expected:
            raise AssertionError(f"compiled leaf disagrees: {name}")
        records.append({
            "edges": net.edges, "vertices": len(net.left) + len(net.right),
            "plan_exists": plan is not None,
            "python_ns": time_call(ref),
            "native_ns": time_call(native),
            "compiled_python_ns": time_call(compiled) if plan is not None else None,
            "compile_plan_ns": time_call(lambda: compile_leaf_plan(
                net.edges, scopes, max_width=policy.max_width,
                lookup_budget=policy.lookup_entries,
            )),
        })
    return {"case": name, "answer": answer, "total_leaf_calls": calls, "samples": records}


def main() -> None:
    out = {"schema_version": 1, "source": "real recursive cases, head-specific diagnostic",
           "packet": [], "leaf": []}
    for name in IDS:
        out["packet"].append(packet_probe(name))
        print(f"packet {name}: {out['packet'][-1]['total_calls']} calls", flush=True)
    for name in IDS:
        out["leaf"].append(leaf_probe(name))
        print(f"leaf {name}: {out['leaf'][-1]['total_leaf_calls']} calls", flush=True)

    path = Path(sys.argv[1] if len(sys.argv) > 1 else "artifacts/native-overhead.json")
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(out, indent=2, sort_keys=True) + "\n")

    print("\nPacket category decomposition (times in microseconds; approximate):")
    for item in out["packet"]:
        for mode, grp in item["groups"].items():
            med = grp["median_ns"]
            print(f"  {item['case']} / modes={mode}: n={grp['calls']}, objects={grp['created']}, "
                  f"Python={med['python_ns']/1000:.2f}, native_raw={med['native_raw_ns']/1000:.2f}, "
                  f"native_wrapped={med['native_wrapper_ns']/1000:.2f}, "
                  f"prep/object={med['native_prep_ns']/1000:.2f}")
    print("\nLeaf sample medians (microseconds):")
    for item in out["leaf"]:
        if not item["samples"]:
            print(item["case"], "no captured leaves")
            continue
        for field in ("python_ns", "native_ns", "compiled_python_ns", "compile_plan_ns"):
            values = [s[field] / 1000 for s in item["samples"] if s[field] is not None]
            print(f"  {item['case']}: {field}={median(values):.2f} us")
    print("Saved", path)


if __name__ == "__main__":
    main()
