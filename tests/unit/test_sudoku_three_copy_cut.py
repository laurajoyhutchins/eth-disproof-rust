"""Restricted three-interface information-cut tests, not a universal lower bound."""
from __future__ import annotations

import pytest

from reference.bit_work import sudoku_direct_encoding_size
from reference.sudoku_three_copy_cut import three_copy_cut

pytestmark = pytest.mark.checkpoint


@pytest.mark.parametrize('box_order', (2, 3, 4, 5, 8, 16, 32))
def test_existing_direct_reduction_saturates_each_three_copy_binary_cut(box_order: int) -> None:
    bound = three_copy_cut(box_order)
    dims = sudoku_direct_encoding_size(box_order)
    assert bound.actual_direct_wires == dims.wires
    assert bound.minimum_three_copy_wires == 3 * dims.cells * bound.minimum_boolean_wires_per_copy
    assert bound.saturates_cut
    t = bound.minimum_boolean_wires_per_copy
    assert (1 << (t - 1)) < bound.side <= (1 << t)


def test_degenerate_one_symbol_case_has_padded_wire_in_source() -> None:
    bound = three_copy_cut(1)
    assert bound.minimum_three_copy_wires == 0
    assert bound.actual_direct_wires == 3
    assert not bound.saturates_cut


def test_exponential_box_orders_force_log_factor_in_this_architecture() -> None:
    # N=b**4 and b=2**k, hence n=b**2 and t=2k. This is a
    # lower bound ONLY for three separate information-bearing digit copies.
    for k in (1, 2, 4, 8, 16):
        bound = three_copy_cut(1 << k)
        assert bound.cells == 1 << (4 * k)
        assert bound.minimum_three_copy_wires == 6 * k * bound.cells


@pytest.mark.parametrize('bad', (0, -2, 1.3, True))
def test_reject_unsupported_box_orders(bad: object) -> None:
    with pytest.raises(ValueError):
        three_copy_cut(bad)  # type: ignore[arg-type]
