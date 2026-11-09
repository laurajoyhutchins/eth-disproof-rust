"""Independent exact-zero certificate and resource-refusal contracts."""
from __future__ import annotations
from dataclasses import replace
from itertools import product
from random import Random

import pytest

from benchmarks.recursive_cases import get_case
from non_exponential_sudoku import (
    ContractionEngine, Padic, ZeroSupportPolicy, simple_network,
    modulus_polynomial,
)
from non_exponential_sudoku.contraction.zero_support import (
    certify_zero, _packet_may_be_nonzero,
)
from non_exponential_sudoku.contraction.compiled_children import CompiledChildPlan
from non_exponential_sudoku.contraction.packets import PacketEntry

pytestmark = pytest.mark.checkpoint


def run_case(name: str, *, enabled: bool,
             policy: ZeroSupportPolicy | None = None):
    case = get_case(name, 'plans')
    selection = policy or ZeroSupportPolicy(enabled=enabled)
    config = replace(case.config, recursion=replace(
        case.config.recursion, zero_support=selection))
    engine = ContractionEngine(config)
    return engine.contract(case.network)[0], engine.stats, case.expected


@pytest.mark.parametrize('name,certified', (
    ('sudoku-4wire', 4), ('sudoku-8wire', 120),
    ('nested-2wire', 8), ('parity-2wire', 0),
))
def test_proven_zeros_reduce_recursion_without_count_change(
    name: str, certified: int,
) -> None:
    baseline, before, expected = run_case(name, enabled=False)
    result, after, _ = run_case(name, enabled=True)
    assert result == baseline == expected
    assert after.zero_support_certificates == certified
    assert before.recursive_calls - after.recursive_calls == certified
    assert before.child_networks == after.child_networks
    assert after.zero_support_attempts == after.child_networks
    assert after.zero_support_evaluated_rows > 0


def test_budgets_decline_preflight_not_exact_contraction() -> None:
    net = simple_network(2,
        [((0, 1), {(0, 0): 1, (1, 1): 1})],
        [((0, 1), {(0, 0): 1, (1, 1): 1})])
    ring = Padic(5, modulus_polynomial(5), 8)
    for settings in (
        {'max_child_edges': 1}, {'max_vertex_arity': 1},
        {'max_support_rows': 1},
    ):
        result = certify_zero(net, ring, ZeroSupportPolicy(**settings))
        assert result.verdict == 'unsupported'
        assert result.evaluated_rows == 0
    baseline, _, _ = run_case('sudoku-4wire', enabled=False)
    outcome, counters, _ = run_case('sudoku-4wire', enabled=True,
        policy=ZeroSupportPolicy(enabled=True, max_child_edges=1))
    assert outcome == baseline
    assert counters.zero_support_certificates == 0
    assert counters.zero_support_unsupported == counters.zero_support_attempts


def test_random_tensors_never_receive_false_zero_certificate() -> None:
    rng = Random(734183)
    ring = Padic(5, modulus_polynomial(5), 6)
    for n in range(1, 6):
        for _ in range(24):
            left = {bits: rng.randrange(3) for bits in product((0, 1), repeat=n)}
            right = {bits: rng.randrange(3) for bits in product((0, 1), repeat=n)}
            net = simple_network(n, [(tuple(range(n)), left)],
                                    [(tuple(range(n)), right)])
            certificate = certify_zero(net, ring, ZeroSupportPolicy())
            if certificate.verdict == 'zero':
                assert net.direct(ring, n) == ring.zero
            assert certificate.verdict in ('zero', 'possible')


def test_packet_symbolic_zeros_match_full_padic_jet_oracle(monkeypatch) -> None:
    checks = [0]
    certified = [0]
    original = CompiledChildPlan.instantiate

    def inspect(self, modes, beta, t, z, ring, context):
        child = original(self, modes, beta, t, z, ring, context)
        if checks[0] < 700:
            for vertex in child.right:
                packet = vertex.oracle
                if not isinstance(packet, PacketEntry):
                    continue
                for bits in product((0, 1), repeat=len(vertex.ports)):
                    possible = _packet_may_be_nonzero(packet, bits)
                    value = packet(bits, ring)
                    checks[0] += 1
                    if not possible:
                        certified[0] += 1
                        assert value == ring.zero
        return child

    monkeypatch.setattr(CompiledChildPlan, 'instantiate', inspect)
    result, _, expected = run_case('sudoku-4wire', enabled=False)
    assert result == expected
    assert checks[0] > 0 and certified[0] > 0


@pytest.mark.requires_native
def test_native_kernel_uses_same_certificates() -> None:
    pytest.importorskip('native_recursive')
    for name in ('sudoku-4wire', 'sudoku-8wire'):
        case = get_case(name, 'combined')
        config = replace(case.config, recursion=replace(
            case.config.recursion, zero_support=ZeroSupportPolicy(enabled=True)))
        engine = ContractionEngine(config)
        assert engine.contract(case.network)[0] == case.expected
        assert engine.stats.zero_support_certificates > 0


@pytest.mark.parametrize('settings', (
    {'enabled': 1}, {'max_child_edges': 0},
    {'max_vertex_arity': 0}, {'max_support_rows': 0},
))
def test_preflight_limits_validate(settings) -> None:
    with pytest.raises(ValueError):
        ZeroSupportPolicy(**settings)


def test_huge_mode_exponents_do_not_create_large_integers() -> None:
    from types import SimpleNamespace

    huge = SimpleNamespace(b=10**12)
    packet = SimpleNamespace(
        terms=SimpleNamespace(tile_bits=((huge, 1, ((0, 0), (1, 2))),), desired=()),
        geometry=SimpleNamespace(row_terms=()),
    )
    assert not _packet_may_be_nonzero(packet, (1, 0))
    assert _packet_may_be_nonzero(packet, (0, 1))
