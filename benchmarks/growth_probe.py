"""Opt-in exact structural measurements; no solver semantics are changed.

Counts materialized nonzero factor rows and retained polynomial coefficients,
including temporary factor tables. A formal budget coefficient is one entry
in a sparse polynomial over the *existing* coefficient ring; it is not a
2-adic scalar or a Taylor coordinate. ``scalar_coordinate_factor`` records
that separate multiplicative expansion.

Ring operation counts instrument Python ring method entry, including calls
that dispatch to Cython. They do NOT count integer multiplications within the
native kernels, nor unobserved memory held by the Python allocator.
"""
from __future__ import annotations

from collections import Counter
from contextlib import contextmanager
from math import prod


def admissible_assignments(scope, modes, domains, precision):
    """Exact weighted state upper bound, not a dense assignment traversal."""
    counts = [0] * precision
    counts[0] = 1
    for j in scope:
        w = modes[j].weight
        next_counts = [0] * precision
        for degree, n in enumerate(counts):
            if n:
                for b in domains[j]:
                    d = degree + w * b
                    if d >= precision:
                        break
                    next_counts[d] += n
        counts = next_counts
    return sum(counts)


def scalar_coordinates(ring):
    result = ring.e
    while hasattr(ring, 'q'):
        result *= ring.q
        ring = ring.base
    return result


class GrowthCollector:
    """Observe bounded actual factor tables along the recursive call stack."""

    def __init__(self):
        self.frames = {}
        self.records = []
        self.peak_simultaneous_retained_coefficients = 0
        self.peak_simultaneous_with_temporary = 0
        self.max_factor_scope = 0
        self.max_factor_states = 0
        self.max_factor_coefficients = 0
        self.peak_jet_scalar_coordinates_per_coefficient = 0
        self.peak_active_elimination_frames = 0
        self.observed_factor_scopes = 0

    def begin(self, budget, modes, domains, ring):
        key = id(budget)
        if key in self.frames:
            raise AssertionError('Duplicate active elimination frame')
        frame = dict(modes=len(modes), precision=ring.p,
                     scalar_coordinate_factor=scalar_coordinates(ring),
                     max_scope=0, max_factor_rows=0, max_factor_coefficients=0,
                     max_raw_domain_states=0, max_admissible_states=0,
                     max_planned_scope=0, max_planned_domain_states=0,
                     planned_child_evaluations_upper_bound=0,
                     global_raw_mode_tuples=prod(len(d) for d in domains),
                     global_weighted_admissible_tuples=admissible_assignments(
                         tuple(range(len(modes))), modes, domains, ring.p),
                     max_admissible_coefficient_bound=0,
                     live_coefficients=0, peak_live_coefficients=0,
                     peak_build_coefficients=0, peak_build_rows=0,
                     peak_factor_count=0, factor_observations=0,
                     temporary_observations=0, join_observations=0,
                     _modes=modes, _domains=domains)
        self.frames[key] = frame
        self.peak_active_elimination_frames = max(self.peak_active_elimination_frames, len(self.frames))
        self.peak_jet_scalar_coordinates_per_coefficient = max(
            self.peak_jet_scalar_coordinates_per_coefficient, frame['scalar_coordinate_factor'])

    def planned(self, budget, scopes):
        f = self.frames.get(id(budget))
        if f is None:
            return
        for scope in scopes:
            f['max_planned_scope'] = max(f['max_planned_scope'], len(scope))
            bound = admissible_assignments(scope, f['_modes'], f['_domains'], f['precision'])
            f['max_planned_domain_states'] = max(f['max_planned_domain_states'],bound)
            f['planned_child_evaluations_upper_bound'] += bound

    def _scope(self, frame, scope, rows, coefficients):
        frame['factor_observations'] += 1
        self.observed_factor_scopes += 1
        width = len(scope)
        frame['max_scope'] = max(frame['max_scope'], width)
        frame['max_factor_rows'] = max(frame['max_factor_rows'], rows)
        frame['max_factor_coefficients'] = max(frame['max_factor_coefficients'], coefficients)
        self.max_factor_scope = max(self.max_factor_scope, width)
        self.max_factor_states = max(self.max_factor_states, rows)
        self.max_factor_coefficients = max(self.max_factor_coefficients, coefficients)
        raw = prod(len(frame['_domains'][j]) for j in scope)
        allowed = admissible_assignments(scope, frame['_modes'], frame['_domains'], frame['precision'])
        frame['max_raw_domain_states'] = max(frame['max_raw_domain_states'], raw)
        frame['max_admissible_states'] = max(frame['max_admissible_states'], allowed)
        frame['max_admissible_coefficient_bound'] = max(
            frame['max_admissible_coefficient_bound'], allowed * frame['precision'])
        if rows > allowed:
            raise AssertionError('Observed factor rows exceed exact weighted-state bound')
        if coefficients > rows * frame['precision']:
            raise AssertionError('Observed polynomial coefficients exceed precision bound')

    def _stack_totals(self, *, temporary=0):
        retained = sum(f['live_coefficients'] for f in self.frames.values())
        self.peak_simultaneous_retained_coefficients = max(
            self.peak_simultaneous_retained_coefficients, retained)
        self.peak_simultaneous_with_temporary = max(
            self.peak_simultaneous_with_temporary, retained + temporary)

    def retained(self, budget, factors):
        f = self.frames.get(id(budget))
        if f is None:
            return
        terms = 0
        for factor in factors:
            coeffs = sum(len(p) for p in factor.table.values())
            terms += coeffs
            self._scope(f, factor.scope, len(factor.table), coeffs)
        f['live_coefficients'] = terms
        f['peak_live_coefficients'] = max(f['peak_live_coefficients'], terms)
        f['peak_factor_count'] = max(f['peak_factor_count'], len(factors))
        self._stack_totals()

    def temporary(self, budget, rows, terms, description):
        f = self.frames.get(id(budget))
        if f is None:
            return
        f['temporary_observations'] += 1
        f['peak_build_coefficients'] = max(f['peak_build_coefficients'], terms)
        f['peak_build_rows'] = max(f['peak_build_rows'], rows)
        # The table under construction coexists with already retained factors.
        # During elimination it may replace factors and temporarily double count
        # them; thus this is a conservative *observed structural envelope*.
        self._stack_totals(temporary=terms)

    def joined(self, budget, factor):
        f = self.frames.get(id(budget))
        if f is None:
            return
        f['join_observations'] += 1
        self._scope(f, factor.scope, len(factor.table),
                    sum(len(p) for p in factor.table.values()))

    def end(self, budget, *, status):
        f = self.frames.pop(id(budget), None)
        if f is None:
            return
        # This budget's operations and children are per invocation, not
        # inclusive sums across nested elimination frames.
        if budget.children > f['planned_child_evaluations_upper_bound']:
            raise AssertionError('Child evaluations exceed planned local factor bound')
        f.update(status=status, direct_dp_operations=budget.operations,
                 direct_order_scans=budget.order_scans,
                 direct_child_contractions=budget.children)
        del f['_modes'], f['_domains']
        self.records.append(f)
        self._stack_totals()

    def summary(self):
        return dict(
            invocations=len(self.records),
            completed_invocations=sum(r['status'] == 'completed' for r in self.records),
            max_factor_scope=self.max_factor_scope,
            max_planned_factor_scope=max((r["max_planned_scope"] for r in self.records),default=0),
            max_planned_factor_states_bound=max((r["max_planned_domain_states"] for r in self.records),default=0),
            max_global_weighted_mode_tuples=max((r["global_weighted_admissible_tuples"] for r in self.records),default=0),
            peak_factor_rows=self.max_factor_states,
            peak_factor_coefficients=self.max_factor_coefficients,
            peak_simultaneous_retained_coefficients=self.peak_simultaneous_retained_coefficients,
            peak_simultaneous_with_temporary_upper_envelope=self.peak_simultaneous_with_temporary,
            peak_scalar_coordinates_per_coefficient=self.peak_jet_scalar_coordinates_per_coefficient,
            peak_active_elimination_frames=self.peak_active_elimination_frames,
            max_raw_factor_domain_states=max((r['max_raw_domain_states'] for r in self.records), default=0),
            max_admissible_factor_states_bound=max((r['max_admissible_states'] for r in self.records), default=0),
            max_admissible_factor_coefficients_bound=max((r['max_admissible_coefficient_bound'] for r in self.records), default=0),
            exact_direct_dp_operations=sum(r['direct_dp_operations'] for r in self.records),
            exact_direct_order_scans=sum(r['direct_order_scans'] for r in self.records),
            exact_direct_child_evaluations=sum(r['direct_child_contractions'] for r in self.records),
            planned_child_evaluations_upper_bound=sum(
                r['planned_child_evaluations_upper_bound'] for r in self.records),
            factor_scope_observations=self.observed_factor_scopes,
        )


class RingOperationCounter:
    """Count exact Python ring-method entries; native internals are opaque."""

    def __init__(self):
        self.counts = Counter()
        self.originals = {}

    def __enter__(self):
        from non_exponential_sudoku.core.algebra import Padic
        from non_exponential_sudoku.core.jets import JetRing
        for cls in (Padic, JetRing):
            for name in ('add', 'sub', 'mul', 'neg', 'inv', 'pow'):
                original = getattr(cls, name)
                key = f'{cls.__name__}.{name}'
                def wrapped(self_ring, *args, _original=original, _key=key, **kwargs):
                    self.counts[_key] += 1
                    return _original(self_ring, *args, **kwargs)
                setattr(cls, name, wrapped)
                self.originals[(cls, name)] = original
        return self

    def __exit__(self, *exc):
        for (cls, name), method in self.originals.items():
            setattr(cls, name, method)
        self.originals.clear()

    def summary(self):
        return {'by_ring_method': dict(sorted(self.counts.items())),
                'add_sub_mul_calls': sum(value for name, value in self.counts.items()
                                         if name.endswith(('.add', '.sub', '.mul'))),
                'all_ring_method_calls': sum(self.counts.values()),
                'unit': 'ring API method invocation; native arithmetic internals not expanded'}
