"""End-to-end bounded ETH reference: independent model-count agreement."""
from __future__ import annotations

from dataclasses import replace
import json
from pathlib import Path
import subprocess
import sys

import pytest

from non_exponential_sudoku.eth import CNFFormula, count_bruteforce
from non_exponential_sudoku.eth.pipeline import (
    ReferencePipelineConfig, count_cnf_reference,
)
from non_exponential_sudoku.eth.sparsification import (
    reference_sparsification_parameters,
)
from non_exponential_sudoku.eth.construction import ConstructionLimits
from non_exponential_sudoku.runtime.budget import CapacityError

@pytest.mark.integration
def test_constructed_path_is_reached_without_fallback(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    formula = CNFFormula(2, ((1, 2),))
    expected = count_bruteforce(formula)

    import non_exponential_sudoku.eth.cnf as cnf
    import non_exponential_sudoku.eth.ganak as ganak
    import non_exponential_sudoku.eth.polynomial as polynomial

    def forbidden(*_args: object, **_kwargs: object) -> None:
        raise AssertionError('full-cube counting oracle used in production path')

    with monkeypatch.context() as patched:
        patched.setattr(cnf, 'count_bruteforce', forbidden)
        patched.setattr(ganak, 'count_ganak', forbidden)
        patched.setattr(polynomial, 'deformation_polynomial', forbidden)
        report = count_cnf_reference(formula)

    assert report.count == expected == 3
    assert not report.source_width_reduced
    assert not report.sparsification_theorem_threshold
    assert len(report.leaves) == 1
    leaf = report.leaves[0]
    assert leaf.method == 'certified-construction'
    assert leaf.centers == 2
    assert leaf.taylor_pairs > 0
    assert leaf.hermite_operations > 0
    assert leaf.contribution == 3


@pytest.mark.integration
def test_disjoint_leaves_and_explicit_base_case() -> None:
    # A: x1 is true (4 assignments), B: x1 is false and x2=x3=true.
    formula = CNFFormula(3, ((1, 2), (1, 3)))
    result = count_cnf_reference(formula)
    assert result.count == count_bruteforce(formula) == 5
    assert [leaf.path for leaf in result.leaves] == [('A',), ('B',)]
    assert sum(leaf.contribution for leaf in result.leaves) == 5
    assert {leaf.method for leaf in result.leaves} == {
        'two-assignment-base', 'certified-construction',
    }
    assert all(leaf.contribution >= 0 for leaf in result.leaves)


@pytest.mark.parametrize('formula,expected', [
    (CNFFormula(0, ()), 1),
    (CNFFormula(0, ((),)), 0),
    (CNFFormula(5, ()), 32),
    (CNFFormula(5, ((),)), 0),
    (CNFFormula(5, ((1, 2),)), 24),
    (CNFFormula(3, ((1,),)), 4),
])
@pytest.mark.integration
def test_empty_unsat_and_free_variable_multiplicity(
    formula: CNFFormula, expected: int,
) -> None:
    report = count_cnf_reference(formula)
    assert report.count == expected == count_bruteforce(formula)
    assert sum(leaf.contribution for leaf in report.leaves) == expected
    assert all(leaf.method in ('two-assignment-base', 'certified-construction')
               for leaf in report.leaves)


@pytest.mark.integration
def test_no_partial_result_after_a_leaf_capacity_refusal() -> None:
    formula = CNFFormula(3, ((1, 2), (1, 3)))
    config = replace(ReferencePipelineConfig(), max_leaves=1)
    with pytest.raises(CapacityError, match='leaf evaluation'):
        count_cnf_reference(formula, config=config)


@pytest.mark.integration
def test_general_width_is_reduced_before_sparsification() -> None:
    # The width-four input is legal even though the partitioner needs k=3.
    # A deliberately tiny construction budget proves that the path refuses,
    # rather than changing algorithm or pretending a partial count is final.
    formula = CNFFormula(4, ((1, 2, 3, 4),))
    config = replace(
        ReferencePipelineConfig(),
        sparsification=reference_sparsification_parameters(3, 512),
        construction_limits=ConstructionLimits(max_variables=2),
    )
    with pytest.raises(CapacityError, match='transferred CNF dimensions'):
        count_cnf_reference(formula, config=config)


@pytest.mark.integration
def test_explicit_reference_threshold_is_not_paper_admission() -> None:
    config = replace(
        ReferencePipelineConfig(),
        sparsification=reference_sparsification_parameters(3, 3),
    )
    report = count_cnf_reference(CNFFormula(2, ((1, 2),)), config=config)
    assert report.count == 3
    assert report.leaves[0].path == ()
    assert not report.sparsification_theorem_threshold


@pytest.mark.checkpoint
def test_invalid_pipeline_parameters_are_rejected() -> None:
    with pytest.raises(ValueError, match='positive integers'):
        ReferencePipelineConfig(max_leaves=0)
    with pytest.raises(ValueError, match='r>=2'):
        ReferencePipelineConfig(r=1)
    with pytest.raises(ValueError, match='backend'):
        ReferencePipelineConfig(backend='float')  # type: ignore[arg-type]


@pytest.mark.integration
def test_cli_dimacs_count_and_fail_closed_json(tmp_path: Path) -> None:
    source = tmp_path / 'case.cnf'
    destination = tmp_path / 'evidence.json'
    source.write_text(CNFFormula(2, ((1, 2),)).to_dimacs())
    completed = subprocess.run(
        [sys.executable, '-m', 'scripts.eth_reference', '--dimacs', str(source),
         '--output', str(destination)],
        capture_output=True, text=True, check=False,
    )
    assert completed.returncode == 0, completed.stderr
    report = json.loads(destination.read_text())
    assert report['status'] == 'completed'
    assert report['count'] == 3
    assert report['leaves'][0]['method'] == 'certified-construction'

    source.write_text(CNFFormula(3, ((1, 2), (1, 3))).to_dimacs())
    refused = subprocess.run(
        [sys.executable, '-m', 'scripts.eth_reference', '--dimacs', str(source),
         '--max-leaves', '1', '--output', str(destination)],
        capture_output=True, text=True, check=False,
    )
    assert refused.returncode == 2, refused.stderr
    report = json.loads(destination.read_text())
    assert report['status'] == 'capacity_refusal'
    assert report['count'] is None
    assert 'leaf evaluation' in report['error']


@pytest.mark.integration
def test_factorized_taylor_is_equal_on_integrated_branched_input() -> None:
    formula = CNFFormula(3, ((1, 2), (1, 3)))
    config = replace(ReferencePipelineConfig(), summation='eliminate')
    result = count_cnf_reference(formula, config=config)
    assert result.count == count_bruteforce(formula) == 5
    assert result.summation == 'eliminate'
    assert any(leaf.method == 'certified-construction' for leaf in result.leaves)


@pytest.mark.integration
def test_leaf_factor_evidence_matches_actual_taylor_work(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    # Inspect exactly the completed per-center results used by the pipeline.
    # A zero tuple count in elimination mode must not hide exponential factor
    # assignment work behind an apparently empty report.
    import non_exponential_sudoku.eth.pipeline as pipeline

    original = pipeline.count_from_manual_designs
    observed = []

    def record(*args, **kwargs):
        result = original(*args, **kwargs)
        observed.append(result)
        return result

    monkeypatch.setattr(pipeline, 'count_from_manual_designs', record)
    formula = CNFFormula(3, ((1, 2), (1, 3)))
    report = count_cnf_reference(
        formula, config=replace(ReferencePipelineConfig(), summation='eliminate'),
    )
    assert report.count == count_bruteforce(formula) == 5
    constructed = [leaf for leaf in report.leaves
                   if leaf.method == 'certified-construction']
    base = [leaf for leaf in report.leaves
            if leaf.method == 'two-assignment-base']
    assert len(observed) == len(constructed) >= 1
    assert base
    for leaf, reconstructed in zip(constructed, observed):
        stats = [value.stats for value in reconstructed.taylor_data]
        assert leaf.factor_assignments_tested == sum(
            item.factor_assignments_tested for item in stats)
        assert leaf.factor_scope_peak == max(
            (item.factor_scope_peak for item in stats), default=0)
        assert leaf.factor_entries_peak == max(
            (item.factor_entries_peak for item in stats), default=0)
        assert leaf.factor_eliminations == sum(
            item.factor_eliminations for item in stats)
        assert leaf.measurement_tuples == 0
        assert leaf.factor_assignments_tested > 0
    for leaf in base:
        assert leaf.factor_assignments_tested == 0
        assert leaf.factor_scope_peak == 0
        assert leaf.factor_entries_peak == 0
        assert leaf.factor_eliminations == 0
