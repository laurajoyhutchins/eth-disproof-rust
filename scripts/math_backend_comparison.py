#!/usr/bin/env python3
"""Reproducible exact-ring backend comparison with optional FLINT.

Standard cases are independently checked by SymPy. --wide includes larger
cases and checks Python, Cython (when built), and FLINT for exact agreement.
The production FLINT path includes tuple conversions and ledger dispatch;
FLINT-resident timing intentionally excludes representation conversions.

Run: python scripts/math_backend_comparison.py --wide --output results.json
"""
from __future__ import annotations

import argparse
from collections.abc import Callable
from hashlib import sha256
import importlib
import json
import os
from pathlib import Path
import platform
import random
import statistics
import sys
import time
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
sys.path[:0] = [str(ROOT / "src"), str(ROOT)]

import non_exponential_sudoku.core.algebra as algebra
from non_exponential_sudoku.core.algebra import Padic, modulus_polynomial
from non_exponential_sudoku.core.flint_backend import FlintRingArithmetic, flint_arithmetic
from research.sympy_oracle import SympyRingOracle
from scripts.evidence import git_provenance
import sympy  # type: ignore[import-untyped]

SMALL_CASES = ((3, 8), (5, 64), (8, 256))
LARGE_CASES = ((16, 64), (16, 256), (16, 1024),
               (32, 64), (32, 256), (32, 1024),
               (64, 64), (64, 256), (64, 1024))


def _measure(fn: Callable[[], Any], repeats: int) -> dict[str, Any]:
    times: list[int] = []
    fn()
    for _ in range(repeats):
        start = time.perf_counter_ns()
        fn()
        times.append(time.perf_counter_ns() - start)
    return {"wall_ns": times, "median_wall_ns": int(statistics.median(times))}


def _hash_file(filename: str) -> str:
    return sha256((ROOT / filename).read_bytes()).hexdigest()


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=ROOT / "benchmark-results/math-backends.json")
    parser.add_argument("--seed", type=int, default=44021)
    parser.add_argument("--samples", type=int, default=32)
    parser.add_argument("--repeats", type=int, default=5)
    parser.add_argument("--wide", action="store_true", help="Include 16/32/64-degree rings and 1024-bit precision")
    parser.add_argument("--wheel-file", type=Path, help="Optional installed python-flint wheel for exact SHA-256 provenance")
    args = parser.parse_args()
    if args.samples < 1 or args.repeats < 1:
        parser.error("--samples and --repeats must both be positive")
    if args.wheel_file is not None and not args.wheel_file.is_file():
        parser.error("--wheel-file must be an existing file")

    native = None
    try:
        native = importlib.import_module("native_ring")
    except ImportError:
        pass
    native_path = Path(native.__file__).resolve() if native is not None and native.__file__ else None
    if native_path is not None and native_path.parent not in (ROOT, ROOT / "src"):
        print(f"Ignoring native extension outside checkout: {native_path}", file=sys.stderr)
        native = None
        native_path = None
    try:
        flint_module = importlib.import_module("flint")
    except ImportError:
        flint_module = None
    original_native = getattr(algebra, "_native_ring")
    results: list[dict[str, Any]] = []
    try:
        for degree, precision in SMALL_CASES + (LARGE_CASES if args.wide else ()):
            ring = Padic(degree, modulus_polynomial(degree), precision)
            rng = random.Random(args.seed + 101 * degree + precision)
            modulus = 1 << precision
            operands = [(
                tuple(rng.randrange(-modulus, 2 * modulus) for _ in range(degree)),
                tuple(rng.randrange(-modulus, 2 * modulus) for _ in range(degree)),
            ) for _ in range(args.samples)]

            def compute_python() -> list[tuple[int, ...]]:
                setattr(algebra, "_native_ring", None)
                return [ring.mul(a, b) for a, b in operands]

            def compute_native() -> list[tuple[int, ...]]:
                setattr(algebra, "_native_ring", native)
                return [ring.mul(a, b) for a, b in operands]

            oracle = SympyRingOracle(ring) if (degree, precision) in SMALL_CASES else None

            def compute_sympy() -> list[tuple[int, ...]]:
                assert oracle is not None
                return [oracle.mul(a, b) for a, b in operands]

            candidate = FlintRingArithmetic(ring) if flint_module is not None else None

            def compute_flint() -> list[tuple[int, ...]]:
                with flint_arithmetic():
                    return [ring.mul(a, b) for a, b in operands]

            # An upper bound on potential gains from keeping coefficients in FLINT.
            flint_operands = [(candidate._poly(a), candidate._poly(b)) for a, b in operands] if candidate else []

            def compute_flint_resident() -> list[Any]:
                assert candidate is not None
                return [a.mul_mod(b, candidate.modulus) for a, b in flint_operands]

            expected = compute_sympy() if oracle else compute_python()
            if compute_python() != expected:
                raise AssertionError(f"Pure Python disagrees with SymPy at {degree=}, {precision=}")
            if native is not None and compute_native() != expected:
                raise AssertionError(f"Cython disagrees with reference at {degree=}, {precision=}")
            if candidate is not None:
                if compute_flint() != expected:
                    raise AssertionError(f"Production FLINT disagrees with reference at {degree=}, {precision=}")
                if [candidate._coords(p) for p in compute_flint_resident()] != expected:
                    raise AssertionError(f"FLINT-resident result disagrees at {degree=}, {precision=}")

            options = (("python", compute_python), ("native", compute_native),
                       ("sympy_zz_poly", compute_sympy),
                       ("flint_fmpz_mod_poly", compute_flint),
                       ("flint_resident", compute_flint_resident))
            backends: dict[str, dict[str, Any]] = {}
            for name, fn in options:
                if (name == "native" and native is None) or (name == "sympy_zz_poly" and oracle is None) or (name.startswith("flint_") and candidate is None):
                    continue
                backends[name] = _measure(fn, args.repeats)
            baseline = backends["python"]["median_wall_ns"]
            flint_time = backends.get("flint_fmpz_mod_poly", {}).get("median_wall_ns")
            native_time = backends.get("native", {}).get("median_wall_ns")
            results.append({
                "degree": degree,
                "two_adic_precision_bits": precision,
                "calls_per_sample": len(operands),
                "reference": "SymPy ZZ polynomial remainder" if oracle else "independent pure-Python quotient ring",
                "all_backends_equivalent": True,
                "backends": backends,
                "python_speedup_over_sympy": (round(backends["sympy_zz_poly"]["median_wall_ns"] / baseline, 2)
                                               if oracle else None),
                "flint_speedup_over_python": round(baseline / flint_time, 2) if flint_time else None,
                "native_speedup_over_python": round(baseline / native_time, 2) if native_time else None,
                "flint_speedup_over_native": round(native_time / flint_time, 2)
                                             if native_time and flint_time else None,
            })
    finally:
        setattr(algebra, "_native_ring", original_native)

    report: dict[str, Any] = {
        "schema_version": "1.2.0",
        "status": "verified",
        "comparison": "Public Padic.mul, including dispatch and tuple conversion; resident FLINT excludes conversions",
        "semantic_domain": "Z/(2**p)[U]/(f); monic f irreducible modulo 2",
        "timing_scope": "in-process sequential wall time, full-batch warmup; no cross-host or worst-case complexity claims",
        "oracle": "Independent SymPy for small cases; pure Python vs native/FLINT agreement for large cases",
        "not_measured": ["peak RSS", "bit-operation complexity", "native C primitive counts", "end-to-end speedup"],
        "environment": {
            "python": sys.version.split()[0],
            "platform": platform.platform(),
            "machine": platform.machine(),
            "processor": platform.processor(),
            "cpu_count": os.cpu_count(),
            "sympy": sympy.__version__,
            "flint": getattr(flint_module, "__version__", None) if flint_module else None,
            "flint_c_library": getattr(flint_module, "__FLINT_VERSION__", None) if flint_module else None,
            "flint_wheel_sha256": sha256(args.wheel_file.read_bytes()).hexdigest() if args.wheel_file else None,
            "native_ring": bool(native),
            "native_binary_path": str(native_path.relative_to(ROOT)) if native_path else None,
            "native_binary_sha256": sha256(native_path.read_bytes()).hexdigest() if native_path else None,
            "git": git_provenance(),
            "source_sha256": {name: _hash_file(name) for name in (
                "src/non_exponential_sudoku/core/algebra.py", "src/non_exponential_sudoku/core/flint_backend.py",
                "native_ring.pyx", "research/sympy_oracle.py", "research/flint_oracle.py",
                "scripts/math_backend_comparison.py")},
        },
        "parameters": {"seed": args.seed, "samples": args.samples, "repeats": args.repeats, "wide": args.wide},
        "results": results,
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")
    for row in results:
        print(f"e={row['degree']} p={row['two_adic_precision_bits']}: "
              f"native/Python={row['native_speedup_over_python']}x; "
              f"FLINT/Python={row['flint_speedup_over_python']}x; "
              f"FLINT/native={row['flint_speedup_over_native']}x")
    print("Verified comparison:", args.output)
    return 0


if __name__ == "__main__":
    sys.exit(main())
