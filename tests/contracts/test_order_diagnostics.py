"""DLX-like ordering diagnostics are structural, not a solver fallback."""
import pytest
from benchmarks.order_diagnostics import compare,simulate_elimination

pytestmark=pytest.mark.checkpoint


def test_minimum_column_not_assumed_to_minimize_tensor_size():
    study=compare()
    for row in study['results']:
        methods={s['method']:s for s in row['strategies']}
        assert set(methods)=={'minimum_column','min_fill','size_estimate'}
        assert all(len(s['order'])==row['modes'] for s in methods.values())
    grid4=next(x for x in study['results'] if x['network']=='grid-4x4')
    measures={s['method']:s for s in grid4['strategies']}
    assert measures['minimum_column']['max_projected_factor_states'] > measures['min_fill']['max_projected_factor_states']
    assert measures['minimum_column']['sum_projected_factor_states'] > measures['min_fill']['sum_projected_factor_states']
