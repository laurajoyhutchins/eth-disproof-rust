"""Large but structurally cheap problems must not hit demonstration-size ceilings."""
from __future__ import annotations

from fractions import Fraction

import pytest

from non_exponential_sudoku.core.modes import mode_catalog
from non_exponential_sudoku.core.network import simple_network
from non_exponential_sudoku.core.packing import Packet, Packing
from non_exponential_sudoku.eth.cnf import CNFFormula
from non_exponential_sudoku.eth.design import MeasurementDesign
from non_exponential_sudoku.eth.evaluation import SeparatedLimits, evaluate_separated
from non_exponential_sudoku.eth.taylor import (
    TaylorLimits, restricted_taylor_sum, taylor_coefficients_separated,
)
from non_exponential_sudoku.runtime.budget import CapacityError
from non_exponential_sudoku.runtime.config import ModeConfig, RecursionConfig

pytestmark = pytest.mark.checkpoint


def test_mode_catalog_capacity_depends_on_bytes_not_global_mode_count() -> None:
    # Valid packet orientation gives two nonzero b=0 modes at p=3.
    # The synthetic geometry must agree with the paper's slot-bit convention;
    # arbitrary opposite left/right labels can create invalid cross terms.
    packets = 1001
    edges = 2 * packets
    factors = [((edge,), {(0,): 1, (1,): 1}) for edge in range(edges)]
    net = simple_network(edges, factors, factors)
    packing = Packing(
        groups_left=tuple((2 * (edge // 2) + (edge % 2),)
                          for edge in range(edges)),
        groups_right=tuple((2 * (edge // 2) + (1 - edge % 2),)
                           for edge in range(edges)),
        packets=[Packet((2 * k, 2 * k + 1), ()) for k in range(packets)],
        r=2 * packets, a=1, max_load=2,
    )
    assert ModeConfig().max_modes is None
    modes = mode_catalog(net, packing, 1, 3, ModeConfig().max_modes)
    assert len(modes) == 2 * packets
    assert len({(mode.source, mode.target) for mode in modes}) == packets
    with pytest.raises(CapacityError, match='Mode catalog resource limit'):
        mode_catalog(net, packing, 1, 3, max_modes=100)
    with pytest.raises(CapacityError, match='estimated-byte limit'):
        mode_catalog(net, packing, 1, 3, max_catalog_bytes=1024)


def _many_groups(n: int) -> tuple[CNFFormula, MeasurementDesign]:
    formula = CNFFormula(n, ((1,),))
    design = MeasurementDesign(
        groups=tuple((index,) for index in range(n)),
        clause_groups=(0,),
        matrices=tuple(() for _ in range(n)),
        tau=Fraction(0), D=0,
    )
    return formula, design


def test_separated_evaluation_above_twelve_variables_without_global_cube() -> None:
    formula, design = _many_groups(40)
    result = evaluate_separated(formula, design)
    assert result.value == 1 << 39
    assert result.stats.measurement_tuples == 1
    assert result.stats.group_assignments_tried == 80
    with pytest.raises(CapacityError, match='variable'):
        evaluate_separated(formula, design, limits=SeparatedLimits(max_variables=12))


def test_taylor_restricted_evaluation_above_twelve_variables() -> None:
    formula, design = _many_groups(40)
    result = restricted_taylor_sum(formula, design, at=1, E=(), U=(), order=0)
    assert result.coefficients == (Fraction(1 << 39),)
    assert result.stats.group_assignments_tried == 80
    with pytest.raises(CapacityError, match='variable'):
        restricted_taylor_sum(formula, design, at=1, E=(), U=(), order=0,
                              limits=TaylorLimits(max_variables=12))


def test_taylor_order_above_twelve_when_pair_work_is_small() -> None:
    formula, design = _many_groups(1)
    result = taylor_coefficients_separated(formula, design, at=1, order=13)
    assert result.coefficients == (Fraction(1),) + (Fraction(0),) * 13
    assert result.stats.taylor_pairs == 3
    with pytest.raises(CapacityError, match='order'):
        taylor_coefficients_separated(formula, design, at=1, order=13,
                                      limits=TaylorLimits(max_taylor_order=12))


def test_packet_cache_configuration_has_no_arbitrary_4096_entry_ceiling() -> None:
    limits = RecursionConfig(
        packet_memo_entries=4097, packet_memo_bytes=4096,
        prepared_packet_entries=4097, prepared_packet_bytes=4096,
    )
    assert limits.packet_memo_entries == 4097
    assert limits.prepared_packet_entries == 4097
    with pytest.raises(ValueError, match='bounded packet-entry'):
        RecursionConfig(packet_memo_entries=-1)
    with pytest.raises(ValueError, match='prepared packet budget'):
        RecursionConfig(prepared_packet_entries=-1)
