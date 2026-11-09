"""Paired exact coefficient-ring timings with identical Padic entry overhead.

This is a microbenchmark: the full exact-contraction benchmarks remain
authoritative for dispatch and scheduling decisions.
"""
from __future__ import annotations

import random

import pytest

from non_exponential_sudoku.core import algebra as algebra
from non_exponential_sudoku.core.algebra import Padic, modulus_polynomial

pytestmark = pytest.mark.benchmark

CASES = (
    ("scalar-e3-p17", 3, 17, "scalar"),
    ("square-e3-p17", 3, 17, "square"),
    ("dense-e3-p17", 3, 17, "dense"),
    ("scalar-e12-p129", 12, 129, "scalar"),
    ("square-e12-p129", 12, 129, "square"),
    ("dense-e12-p129", 12, 129, "dense"),
    ("scalar-e32-p521", 32, 521, "scalar"),
    ("square-e32-p521", 32, 521, "square"),
    ("dense-e32-p521", 32, 521, "dense"),
)


@pytest.mark.parametrize(
    "case_id,degree,precision,kind,backend",
    [(name, e, p, kind, backend)
     for name, e, p, kind in CASES for backend in ("python", "cython")],
)
def test_coefficient_kernel_pair(
    case_id: str, degree: int, precision: int, kind: str,
    backend: str, benchmark: object, monkeypatch: pytest.MonkeyPatch,
) -> None:
    native = pytest.importorskip("native_ring")
    ring = Padic(degree, modulus_polynomial(degree), precision)
    rng = random.Random(degree * 1_000_000 + precision * 10 + len(kind))
    a = tuple(rng.randrange(1 << precision) for _ in range(degree))
    b = tuple(rng.randrange(1 << precision) for _ in range(degree))
    if kind == "scalar":
        a = (a[0],) + (0,) * (degree - 1)
    elif kind == "square":
        b = a  # Same tuple identity activates the exact square kernel.

    with monkeypatch.context() as ref_patch:
        ref_patch.setattr(algebra, "_native_ring", None)
        expected = ring.mul(a, b)
    monkeypatch.setattr(
        algebra, "_native_ring", native if backend == "cython" else None,
    )
    assert ring.mul(a, b) == expected
    benchmark.group = case_id
    benchmark.extra_info.update({
        "benchmark.case": case_id, "benchmark.variant": backend,
        "benchmark.precision": precision,
        "benchmark.extension_degree": degree,
        "benchmark.operand_kind": kind,
        "benchmark.duration.unit": "s",
    })
    benchmark.pedantic(ring.mul, args=(a, b), iterations=40,
                       rounds=11, warmup_rounds=2)
