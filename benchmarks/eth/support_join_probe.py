"""Research-only exact order-zero factor-support experiment.

The live ETH path is CNF -> disjoint leaves -> certified designs -> Taylor
factors -> elimination -> Hermite readout. This isolated experiment examines
ONE bottleneck: enumerating a dense induced bucket versus joining only the
nonzero supports of its factors. It is not a substitute for measurement
certification, Taylor jets, the paper's parameter schedule, or a #SAT solver.

Run: PYTHONPATH=src:. python -m benchmarks.eth.support_join_probe
Both strategies evaluate exactly the same sum-product expression. Each
family has an independent exhaustive or closed-form count for cross-checks.
"""
from __future__ import annotations

import argparse
from dataclasses import asdict, dataclass
from fractions import Fraction
from itertools import combinations, product
import json
import resource
import subprocess
import sys
import time
import tracemalloc
from typing import Literal


Strategy = Literal['dense', 'support']
Family = Literal['chain', 'equality-clique', 'or-clique']


class CapacityRefusal(RuntimeError):
    """Experiment cannot continue within the explicitly declared budget."""


@dataclass(frozen=True, slots=True)
class Factor:
    scope: tuple[int, ...]
    entries: dict[tuple[int, ...], Fraction]  # missing key means exact zero


@dataclass(frozen=True, slots=True)
class Step:
    eliminated: int
    joined_scope: tuple[int, ...]
    dense_domain: int  # counterfactual 2**width, not observed work
    candidate_assignments: int
    candidate_pairs: int
    output_scope: tuple[int, ...]
    output_entries: int
    output_bits: int


@dataclass(frozen=True, slots=True)
class Result:
    answer: int
    strategy: Strategy
    steps: tuple[Step, ...]
    candidate_assignments: int
    candidate_pairs: int
    arithmetic_adds: int
    arithmetic_muls: int
    schoolbook_bit_proxy: int
    peak_nonzero_entries: int
    peak_coefficient_bits: int
    peak_retained_coefficient_bits: int
    maximum_induced_scope: int
    cross_backend_conversions: int  # no Python/FLINT exchange in this experiment
    recursive_calls: int  # bucket elimination is iterative; no recursion DAG
    distinct_subproblems: int  # one bucket per original variable, no memoization
    reuse_hits: int


def _bits(value: Fraction) -> int:
    return max(abs(value.numerator).bit_length(), value.denominator.bit_length())


def make_family(family: Family, n: int) -> tuple[Factor, ...]:
    if type(n) is not int or n < 2:
        raise ValueError('family requires at least two Boolean variables')
    if family == 'chain':
        edges = tuple((i, i + 1) for i in range(n - 1))
    elif family in ('equality-clique', 'or-clique'):
        edges = tuple(combinations(range(n), 2))
    else:
        raise ValueError('unknown family')
    result = []
    for i, j in edges:
        if family == 'equality-clique':
            # A PRE-COMBINED equality relation, not two uncompressed CNF clauses.
            entries = {(0, 0): Fraction(1), (1, 1): Fraction(1)}
        else:
            entries = {(0, 1): Fraction(1), (1, 0): Fraction(1),
                       (1, 1): Fraction(1)}
        result.append(Factor((i, j), entries))
    return tuple(result)


def brute_count(n: int, factors: tuple[Factor, ...]) -> int:
    """Independent exhaustive truth-table specification, small n only."""
    if n > 16:
        raise CapacityRefusal('exhaustive oracle limited to 16 variables')
    count = 0
    for assignment in product((0, 1), repeat=n):
        weight = Fraction(1)
        for factor in factors:
            weight *= factor.entries.get(tuple(assignment[i] for i in factor.scope), 0)
        count += weight
    if count.denominator != 1:
        raise ArithmeticError('oracle count is not an integer')
    return count.numerator


def run_contraction(
    n: int, initial: tuple[Factor, ...], *, strategy: Strategy,
    max_entries: int = 1_000_000, max_candidates: int = 5_000_000,
) -> Result:
    """Exact rational bucket elimination; compare only the join representation.

    Dense: scan every Boolean assignment in the induced bucket.
    Support: represent partial joins by a map of only nonzero compatible rows.
    The order (0..n-1) and original factors are IDENTICAL in both arms.
    The latter may still require exponential nonzero intermediate states.
    """
    if strategy not in ('dense', 'support'):
        raise ValueError('unknown strategy')
    if type(n) is not int or n < 1 or min(max_entries, max_candidates) < 1:
        raise ValueError('invalid dimensions or resource limits')
    for factor in initial:
        if not factor.scope or tuple(sorted(set(factor.scope))) != factor.scope:
            raise ValueError('factor scopes must be sorted and unique')
        if any(i < 0 or i >= n for i in factor.scope):
            raise ValueError('factor outside declared variables')
        if any(len(key) != len(factor.scope) or any(bit not in (0, 1) for bit in key)
               for key in factor.entries):
            raise ValueError('non-Boolean factor assignment')
        if any(value == 0 for value in factor.entries.values()):
            raise ValueError('store only nonzero support')
    factors = list(initial)
    candidate_assignments = candidate_pairs = adds = muls = bit_proxy = 0
    peak_entries = peak_bits = peak_retained_bits = max_scope = 0
    steps: list[Step] = []

    def observe(*temporary: dict[tuple[int, ...], Fraction]) -> None:
        nonlocal peak_entries, peak_bits, peak_retained_bits
        arrays = [f.entries for f in factors] + list(temporary)
        entries = sum(len(values) for values in arrays)
        bits = sum(_bits(value) for values in arrays for value in values.values())
        peak_entries = max(peak_entries, entries)
        peak_retained_bits = max(peak_retained_bits, bits)
        peak_bits = max(peak_bits, max((_bits(v) for a in arrays for v in a.values()), default=0))
        if entries > max_entries:
            raise CapacityRefusal('retained nonzero factor entry budget')

    def mult(left: Fraction, right: Fraction) -> Fraction:
        nonlocal muls, bit_proxy
        muls += 1
        bit_proxy += _bits(left) * _bits(right)  # proxy, not actual measured bit operations
        return left * right

    def add(left: Fraction, right: Fraction) -> Fraction:
        nonlocal adds, bit_proxy
        adds += 1
        bit_proxy += _bits(left) * _bits(right)
        return left + right

    observe()
    for eliminated in range(n):
        attached = [f for f in factors if eliminated in f.scope]
        factors = [f for f in factors if eliminated not in f.scope]
        scope = tuple(sorted({variable for f in attached for variable in f.scope}))
        max_scope = max(max_scope, len(scope))
        output_scope = tuple(v for v in scope if v != eliminated)
        before_candidates, before_pairs = candidate_assignments, candidate_pairs
        output: dict[tuple[int, ...], Fraction] = {}
        if not attached:
            # An unconstrained Boolean variable multiplies the count by two.
            output[()] = Fraction(2)
        elif strategy == 'dense':
            domain = 1 << len(scope)
            if candidate_assignments + domain > max_candidates:
                raise CapacityRefusal('dense bucket candidate budget')
            candidate_assignments += domain
            for bits in product((0, 1), repeat=len(scope)):
                assignment = dict(zip(scope, bits))
                weight = Fraction(1)
                for f in attached:
                    entry = f.entries.get(tuple(assignment[g] for g in f.scope))
                    if entry is None:
                        break
                    weight = mult(weight, entry)
                else:
                    key = tuple(assignment[g] for g in output_scope)
                    output[key] = add(output.get(key, Fraction(0)), weight)
                    if len(output) > max_entries:
                        raise CapacityRefusal('dense output factor entry budget')
        else:
            partial: dict[tuple[int, ...], Fraction] = {(): Fraction(1)}
            seen: tuple[int, ...] = ()
            # Supports are composed as indexed relations. With shared values,
            # incompatible partial rows are rejected before full-bucket scan.
            for factor in attached:
                joined_scope = tuple(sorted(set(seen) | set(factor.scope)))
                new: dict[tuple[int, ...], Fraction] = {}
                pairs = len(partial) * len(factor.entries)
                if candidate_pairs + pairs > max_candidates:
                    raise CapacityRefusal('support pair candidate budget')
                candidate_pairs += pairs
                for left, left_value in partial.items():
                    known = dict(zip(seen, left))
                    for right, right_value in factor.entries.items():
                        if any(g in known and known[g] != bit
                               for g, bit in zip(factor.scope, right)):
                            continue
                        merged = {**known, **dict(zip(factor.scope, right))}
                        key = tuple(merged[g] for g in joined_scope)
                        new[key] = mult(left_value, right_value)
                        if len(new) > max_entries:
                            raise CapacityRefusal('support partial factor entry budget')
                observe(partial, new)
                partial, seen = new, joined_scope
                if not partial:
                    break
            candidate_assignments += len(partial)
            if candidate_assignments > max_candidates:
                raise CapacityRefusal('support final candidate budget')
            for assignment, weight in partial.items():
                key = tuple(assignment[seen.index(g)] for g in output_scope)
                output[key] = add(output.get(key, Fraction(0)), weight)
                if len(output) > max_entries:
                    raise CapacityRefusal('support output factor entry budget')
            # Release partial support before checking the retained output.
            partial = {}
        output = {key: value for key, value in output.items() if value}
        observe(output)
        factors.append(Factor(output_scope, output))
        observe()
        steps.append(Step(
            eliminated=eliminated, joined_scope=scope,
            dense_domain=1 << len(scope),
            candidate_assignments=candidate_assignments - before_candidates,
            candidate_pairs=candidate_pairs - before_pairs,
            output_scope=output_scope, output_entries=len(output),
            output_bits=max((_bits(value) for value in output.values()), default=0),
        ))
        if not output:
            break
    answer = Fraction(1)
    for factor in factors:
        if factor.scope:
            raise ArithmeticError('uneliminated factor scope')
        answer = mult(answer, factor.entries.get((), Fraction(0)))
    if answer.denominator != 1:
        raise ArithmeticError('count is not an integer')
    return Result(
        answer=answer.numerator, strategy=strategy, steps=tuple(steps),
        candidate_assignments=candidate_assignments, candidate_pairs=candidate_pairs,
        arithmetic_adds=adds, arithmetic_muls=muls,
        schoolbook_bit_proxy=bit_proxy, peak_nonzero_entries=peak_entries,
        peak_coefficient_bits=peak_bits,
        peak_retained_coefficient_bits=peak_retained_bits,
        maximum_induced_scope=max_scope, cross_backend_conversions=0,
        recursive_calls=0, distinct_subproblems=len(steps), reuse_hits=0,
    )


def _case(family: Family, n: int, strategy: Strategy) -> dict[str, object]:
    tracemalloc.start()
    factors = make_family(family, n)
    started = time.perf_counter()
    result = run_contraction(n, factors, strategy=strategy)
    elapsed = time.perf_counter() - started
    _, peak = tracemalloc.get_traced_memory()
    tracemalloc.stop()
    rss = resource.getrusage(resource.RUSAGE_SELF).ru_maxrss
    # Linux ru_maxrss is kilobytes. Each CLI case is isolated in a process.
    return {
        'family': family, 'variables': n, 'strategy': strategy,
        'clauses_or_factors': len(factors),
        'result': result.answer,
        'seconds': elapsed, 'peak_traced_bytes': peak,
        'peak_rss_bytes': rss * 1024,
        'peak_nonzero_entries': result.peak_nonzero_entries,
        'max_coefficient_bits': result.peak_coefficient_bits,
        'retained_coefficient_bits_peak': result.peak_retained_coefficient_bits,
        'max_induced_scope': result.maximum_induced_scope,
        'full_bucket_candidates': result.candidate_assignments,
        'support_join_pairs': result.candidate_pairs,
        'arithmetic_adds': result.arithmetic_adds,
        'arithmetic_muls': result.arithmetic_muls,
        'schoolbook_bit_proxy': result.schoolbook_bit_proxy,
        'cross_backend_conversions': result.cross_backend_conversions,
        'recursive_calls': result.recursive_calls,
        'distinct_subproblems': result.distinct_subproblems,
        'reuse_hits': result.reuse_hits,
        'first_step': asdict(result.steps[0]),
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument('--worker', nargs=3, metavar=('FAMILY', 'N', 'STRATEGY'))
    parser.add_argument('--output')
    options = parser.parse_args()
    if options.worker:
        family, n, strategy = options.worker
        print(json.dumps(_case(family, int(n), strategy), sort_keys=True))
        return
    rows = []
    for family, sizes in (
        ('chain', (4, 6, 8, 10, 12)),
        ('equality-clique', (4, 6, 8, 10, 12)),
        ('or-clique', (4, 6, 8, 10)),
    ):
        for n in sizes:
            for strategy in ('dense', 'support'):
                completed = subprocess.run(
                    [sys.executable, '-m', 'benchmarks.eth.support_join_probe',
                     '--worker', family, str(n), strategy],
                    capture_output=True, check=True, text=True,
                )
                rows.append(json.loads(completed.stdout))
    result = {
        'claim': 'exact finite-size order-zero support contraction, not ETH bound',
        'families': {
            'chain': 'sparse graph, OR(x_i,x_(i+1)); count F_(n+2)',
            'equality-clique': 'pre-combined equalities on every pair; count 2',
            'or-clique': 'positive OR on every pair; count n+1',
        },
        'measurements': rows,
    }
    rendered = json.dumps(result, indent=2, sort_keys=True) + '\n'
    if options.output:
        from pathlib import Path
        Path(options.output).write_text(rendered)
    else:
        print(rendered)


if __name__ == '__main__':
    main()
