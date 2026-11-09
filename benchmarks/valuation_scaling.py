"""Controlled exact A/B scaling of pre-pruning and certified mode valuations.

Only the center mode catalogue changes. Both arms use the same production
contraction engine, packing, precision, factorization, limits and input.
Fresh Linux workers isolate runs and preserve failures instead of inventing
results. This tests finite regimes, not the literal astronomical schedule.
"""
from __future__ import annotations

import argparse
from collections import defaultdict
from dataclasses import asdict, dataclass, replace
from itertools import product
import json
import os
from pathlib import Path
import platform
import resource
import subprocess
import sys
from time import perf_counter
from typing import Any

from benchmarks.recursive_cases import get_case
from non_exponential_sudoku import (
    ContractionEngine, ContractorConfig, LeafConfig, ModeConfig, ModeLimits,
    Padic, Network, RecoveryConfig, simple_network,
)
from non_exponential_sudoku.contraction import engine as engine_module
from non_exponential_sudoku.core.modes import Mode, mode_catalog
from non_exponential_sudoku.core.packing import pack
from non_exponential_sudoku.sudoku.encoding import independently_evaluate_F
from non_exponential_sudoku.runtime.budget import CapacityError
from reference.global_mode_support import exact_weighted_assignment_count
from reference.legacy_mode_catalog import original_catalog

# Intentionally small enough for independent exact reference evaluation.
# Exponents 1,2,3,4 correspond to L=2,4,8,16 padded packet slots.
CASES = (
    "center-L2-p5-n2",
    "center-L4-p5-n2",
    "center-L4-p9-n2",
    "center-L8-p7-n2",
    "center-L8-p11-n2",
    "center-L8-p11-n4",
    "center-L16-p11-n4",
    "recursive-p5",
    "recursive-p7",
    "recursive-L4-p5",
)
ARMS = ("original", "pruned")
SCHEMA = "1.0"


@dataclass(frozen=True)
class Case:
    case_id: str
    precision: int
    slot_exponent: int
    expected: int
    network: Network
    config: ContractorConfig
    labels: tuple[tuple[tuple[int, ...], ...], tuple[tuple[int, ...], ...]] | None
    full_recursive: bool


def make_case(case_id: str) -> Case:
    if case_id not in CASES:
        raise ValueError(f"Unknown valuation-scaling case: {case_id}")
    if case_id == "recursive-L4-p5":
        n, p, a = 2, 5, 2
        tab = {(0,): 1, (1,): 1}
        net = simple_network(
            n, [((i,), tab) for i in range(n)],
            [((i,), tab) for i in range(n)])
        labels = (tuple((0, 0) for _ in range(n)),
                  tuple((1, 0) for _ in range(n)))
        config = ContractorConfig(
            n, p, schedule="geometry64", micro_active_depth=1,
            root_labels=labels,
            mode=ModeConfig(strategy="eliminate", factorization="components",
                            join="sparse", native_sparse=False),
            recovery=RecoveryConfig(method="jet", streaming=True),
            leaf=LeafConfig(strategy="eliminate"),
        )
        return Case(case_id, p, a, 1 << n, net, config, labels, True)
    if case_id.startswith("recursive-p"):
        p = int(case_id.partition("-p")[2])
        base = get_case("nested-2wire", "plans")
        # Two active deformation levels, with exact count four from a
        # two-wire all-one tensor. Disable native sparse joins in both arms.
        config = replace(
            base.config, precision=p,
            mode=replace(base.config.mode, native_sparse=False),
        )
        return Case(case_id, p, 1, base.expected, base.network, config,
                    None, True)
    family, width, bits, size = case_id.split("-")
    if family != "center" or not width.startswith("L") or not bits.startswith("p") or not size.startswith("n"):
        raise ValueError("Malformed case identity")
    L, p, n = int(width[1:]), int(bits[1:]), int(size[1:])
    a = L.bit_length() - 1
    if 1 << a != L or not (1 <= a <= 4) or n not in (2, 4):
        raise ValueError("Invalid reference packet dimensions")
    ports = tuple(range(n))
    table = {bits: 1 for bits in product((0, 1), repeat=n)}
    net = simple_network(n, [(ports, table)], [(ports, table)])
    labels = (((0,) * a,), ((1,) + (0,) * (a - 1),))
    limits = ModeLimits(
        max_factor_states=8192, max_live_terms=50000,
        max_operations=2_000_000, max_child_contractions=50000,
        max_estimated_bytes=96 * 1024 * 1024,
    )
    cfg = ContractorConfig(
        n, p, schedule="micro",
        mode=ModeConfig(strategy="eliminate", factorization="components",
                        join="sparse", native_sparse=False),
        leaf=LeafConfig(strategy="eliminate", limit=18),
        limits=limits,
    )
    return Case(case_id, p, a, 1 << n, net, cfg, labels, False)


def _catalog_record(
    modes: list[Mode], *, t: int, p: int, L: int,
) -> dict[str, int]:
    return {
        "center": t, "precision": p, "slots": L,
        "mode_descriptors": len(modes),
        "higher_order_modes": sum(m.b > 0 for m in modes),
        "admissible_assignments": exact_weighted_assignment_count(
            tuple(m.weight for m in modes),
            tuple(len(m.rows) for m in modes), p,
        ),
    }


def run_sample(case_id: str, arm: str) -> dict[str, Any]:
    if arm not in ARMS:
        raise ValueError("Unknown comparison arm")
    spec = make_case(case_id)
    engine = ContractionEngine(spec.config)
    ring = Padic(engine.e, engine.f, spec.precision)
    oracle: tuple[int, ...] = spec.network.direct(ring, spec.network.edges)
    if oracle != ring.scalar(spec.expected):
        raise AssertionError("Independent exact root contraction mismatch")
    packing = None
    z = ring.basis(3)
    if not spec.full_recursive:
        assert spec.labels is not None
        packing = pack(spec.network, 2, spec.slot_exponent, spec.labels)
        oracle = independently_evaluate_F(spec.network, packing, 1, z, ring)
        if oracle != ring.scalar(spec.expected):
            raise AssertionError("Independent deformed Boolean sum mismatch")

    catalogue = original_catalog if arm == "original" else mode_catalog
    records: list[dict[str, int]] = []

    def record_catalog(net: Network, packing_arg: Any, t: int, p: int,
                       max_modes: int | None = None, *,
                       max_catalog_bytes: int = 128 * 1024 * 1024) -> list[Mode]:
        modes = catalogue(
            net, packing_arg, t, p, max_modes,
            max_catalog_bytes=max_catalog_bytes,
        )
        records.append(_catalog_record(modes, t=t, p=p,
                                       L=1 << packing_arg.a))
        return modes

    # The only intervention is the selected catalog function, including
    # all nested recursive levels. Restore the module binding in finally.
    previous = engine_module.mode_catalog
    actual: tuple[int, ...] | None = None
    message: str | None = None
    status = "verified"
    start = perf_counter()
    try:
        engine_module.mode_catalog = record_catalog
        if spec.full_recursive:
            actual = engine.contract(spec.network)
        else:
            assert packing is not None
            modes = record_catalog(spec.network, packing, 1, spec.precision)
            actual = engine.evaluate_deformation(
                spec.network, packing, modes, 1, z, ring, 0,
            )
        if actual != oracle:
            status = "incorrect"
            message = "Different from independent exact reference"
    except CapacityError as exc:
        status = "capacity_refused"
        message = str(exc)
    finally:
        engine_module.mode_catalog = previous
    duration = perf_counter() - start
    stats = asdict(engine.stats)
    work_keys = (
        "mode_dp_local_child_evaluations", "mode_dp_operations",
        "mode_dp_peak_factor_states", "mode_dp_peak_polynomial_terms",
        "child_networks", "recursive_calls", "leaves",
        "active_paper_calls", "max_nested_jet_depth",
        "max_jet_coordinates", "mode_tuples", "interpolation_evaluations",
        "mode_dp_sparse_joins",
    )
    return {
        "schema": SCHEMA, "case_id": case_id, "arm": arm,
        "status": status, "reason": message,
        "scope": "full_recursive" if spec.full_recursive else "single_center",
        "precision": spec.precision, "packet_slots": 1 << spec.slot_exponent,
        "edges": spec.network.edges, "expected": list(oracle),
        "actual": list(actual) if actual is not None else None,
        "elapsed_seconds": duration,
        "rss_high_water_bytes": resource.getrusage(resource.RUSAGE_SELF).ru_maxrss * 1024,
        "catalogs": records,
        "total_modes": sum(row["mode_descriptors"] for row in records),
        "total_admissible_domains": sum(row["admissible_assignments"] for row in records),
        "solver_work": {key: stats[key] for key in work_keys},
        "process_id": os.getpid(),
    }


def _verified(row: dict[str, Any]) -> bool:
    return (
        row.get("status") == "verified"
        and row.get("actual") == row.get("expected")
        and isinstance(row.get("actual"), list)
        and isinstance(row.get("elapsed_seconds"), (int, float))
        and row["elapsed_seconds"] >= 0
        and isinstance(row.get("total_modes"), int)
        and isinstance(row.get("total_admissible_domains"), int)
        and row["total_modes"] >= 0
        and row["total_admissible_domains"] >= 1
    )


def compare_rows(
    rows: list[dict[str, Any]], *, required_cases: tuple[str, ...] = CASES,
) -> dict[str, Any]:
    grouped: dict[str, dict[str, list[dict[str, Any]]]] = {
        name: {arm: [] for arm in ARMS} for name in required_cases
    }
    if len(set(required_cases)) != len(required_cases):
        raise ValueError("Duplicate requested experiment case")
    for row in rows:
        case_id, arm = row.get("case_id"), row.get("arm")
        if case_id not in grouped or arm not in ARMS:
            raise ValueError("Unexpected case or arm in study")
        grouped[case_id][arm].append(row)
    conclusions = []
    for case_id in required_cases:
        old = grouped[case_id]["original"]
        new = grouped[case_id]["pruned"]
        complete = (
            bool(old) and len(old) == len(new)
            and all(_verified(row) for row in old + new)
            and all(a["expected"] == b["expected"] and a["actual"] == b["actual"]
                    for a, b in zip(old, new))
        )
        old_modes = sum(s.get("total_modes", 0) for s in old)
        new_modes = sum(s.get("total_modes", 0) for s in new)
        if complete:
            reductions = {
                "mode_descriptors_avoided": old_modes - new_modes,
                "admissible_domain_states_avoided": sum(
                    s["total_admissible_domains"] for s in old) - sum(
                    s["total_admissible_domains"] for s in new),
                "child_evaluations_avoided": sum(
                    s["solver_work"]["mode_dp_local_child_evaluations"] for s in old) - sum(
                    s["solver_work"]["mode_dp_local_child_evaluations"] for s in new),
                "recursive_calls_avoided": sum(
                    s["solver_work"]["recursive_calls"] for s in old) - sum(
                    s["solver_work"]["recursive_calls"] for s in new),
            }
        else:
            reductions = None
        conclusions.append({
            "case_id": case_id,
            "status": "verified" if complete else "incomplete",
            "exact_equal": complete,
            "repeat_count": len(old) if len(old) == len(new) else None,
            "old_total_modes": old_modes,
            "new_total_modes": new_modes,
            "work_reduction": reductions,
            "original_samples": old,
            "pruned_samples": new,
        })
    return {
        "schema": SCHEMA,
        "status": "verified" if all(c["exact_equal"] for c in conclusions) else "incomplete",
        "comparisons": conclusions,
    }


def _git_head() -> str | None:
    result = subprocess.run(
        ["git", "rev-parse", "HEAD"], capture_output=True, text=True,
        check=False, timeout=5,
    )
    return result.stdout.strip() if result.returncode == 0 else None


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--worker", action="store_true")
    parser.add_argument("--case", choices=CASES)
    parser.add_argument("--arm", choices=ARMS)
    parser.add_argument("--cases", nargs="+", choices=CASES, default=list(CASES))
    parser.add_argument("--repeats", type=int, default=2)
    parser.add_argument("--timeout", type=float, default=40.0)
    parser.add_argument("--memory-mib", type=int, default=768)
    parser.add_argument("--output", type=Path, default=Path("artifacts/valuation-scaling.json"))
    args = parser.parse_args()

    if args.worker:
        if args.case is None or args.arm is None:
            parser.error("--worker requires --case and --arm")
        if sys.platform != "linux":
            raise SystemExit("Linux required for resource measurements")
        if args.memory_mib > 0:
            mem = args.memory_mib * 1024 * 1024
            resource.setrlimit(resource.RLIMIT_AS, (mem, mem))
        try:
            row = run_sample(args.case, args.arm)
            print(json.dumps(row, sort_keys=True))
            return 0 if row["status"] in ("verified", "capacity_refused") else 1
        except BaseException as exc:
            print(json.dumps({
                "schema": SCHEMA, "case_id": args.case, "arm": args.arm,
                "status": "error", "error": f"{type(exc).__name__}: {exc}",
            }, sort_keys=True))
            return 1

    if args.repeats < 1 or args.timeout <= 0 or args.memory_mib < 1:
        parser.error("Positive repeat count, timeout, and memory limit required")
    if len(set(args.cases)) != len(args.cases):
        parser.error("Repeated case names are not permitted")

    samples: list[dict[str, Any]] = []
    for name in args.cases:
        for repetition in range(args.repeats):
            # Interleaved arms, but independent process/solver state.
            for arm in (ARMS if repetition % 2 == 0 else tuple(reversed(ARMS))):
                command = [
                    sys.executable, "-m", "benchmarks.valuation_scaling",
                    "--worker", "--case", name, "--arm", arm,
                    "--memory-mib", str(args.memory_mib),
                ]
                try:
                    result = subprocess.run(
                        command, capture_output=True, text=True,
                        check=False, timeout=args.timeout,
                    )
                    if result.returncode or len(result.stdout.splitlines()) != 1:
                        raise RuntimeError(
                            f"{name}/{arm}: returncode={result.returncode}; "
                            f"stdout={result.stdout[-400:]!r}; stderr={result.stderr[-400:]!r}"
                        )
                    row = json.loads(result.stdout)
                    if row.get("case_id") != name or row.get("arm") != arm:
                        raise ValueError("Worker identity mismatch")
                    samples.append(row)
                except (subprocess.TimeoutExpired, RuntimeError, ValueError) as exc:
                    samples.append({
                        "schema": SCHEMA, "case_id": name, "arm": arm,
                        "status": "incomplete", "reason": f"{type(exc).__name__}: {exc}",
                    })
    report = compare_rows(samples, required_cases=tuple(args.cases))
    report["environment"] = {
        "python": sys.version.split()[0],
        "platform": platform.platform(),
        "git_commit": _git_head(),
        "worker_memory_mib": args.memory_mib,
        "worker_timeout_seconds": args.timeout,
        "worker_process_isolation": True,
        "native_sparse_disabled_both_arms": True,
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")
    for item in report["comparisons"]:
        reduction = item["work_reduction"]
        print(
            f'{item["case_id"]}: {item["status"]}; modes '
            f'{item["old_total_modes"]}->{item["new_total_modes"]}; '
            f'avoided={reduction if reduction is not None else "not comparable"}',
            flush=True,
        )
    print(f'Study status: {report["status"]}; raw evidence: {args.output}')
    # Refusals are explicit research data but never a verified equivalence.
    return 0 if report["status"] == "verified" else 2


if __name__ == "__main__":
    raise SystemExit(main())
