"""Polynomial-time DLX-inspired propagation of Sudoku exact-cover incidence.

One row per (cell,digit) candidate, four columns per cell/row-digit/
column-digit/box-digit constraint.  Incremental support counts and forced rows
replace repeated full scans.  No Algorithm X, guessing, branching or Hall
subset enumeration.  Optional matching projection is the separate polynomial
all-different consistency algorithm supplied by the caller.
"""
from __future__ import annotations
from collections import deque
from dataclasses import dataclass, asdict


class ExactCoverContradiction(ValueError):
    pass


class PropagationCapacityError(RuntimeError):
    pass


@dataclass(frozen=True)
class PropagationLimits:
    max_candidates: int = 500_000
    max_updates: int = 10_000_000
    max_matching_checks: int = 2_000_000
    max_unit_scans: int = 200_000

    def __post_init__(self):
        if min(vars(self).values()) < 1:
            raise ValueError('Propagation limits must be positive')


class ExactCoverPropagation:
    """Incremental, deterministic exact-cover unit propagation; no search.

    A row stays active while admissible.  Selecting a row covers four columns,
    deletes conflicting rows, and queues any newly singleton column. Every
    deletion touches exactly four supports, with bounded total work.
    """
    def __init__(self, puzzle, *, limits=None):
        self.puzzle=puzzle
        self.n=puzzle.side
        n=self.n
        self.limits=limits or PropagationLimits()
        self.row_count=n*n*n
        if self.row_count>self.limits.max_candidates:
            raise PropagationCapacityError('Exact cover candidate limit')
        self.column_count=4*n*n
        self.rows=[]
        self.columns=[[] for _ in range(self.column_count)]
        for cell in range(n*n):
            r,c=divmod(cell,n)
            box=(r//puzzle.b)*puzzle.b+c//puzzle.b
            for d in range(n):
                cols=(cell,n*n+r*n+d,2*n*n+c*n+d,3*n*n+box*n+d)
                row_id=cell*n+d
                self.rows.append(cols)
                for col in cols:
                    self.columns[col].append(row_id)
        self.active=bytearray(b'\1')*self.row_count
        self.selected=bytearray(self.row_count)
        self.covered=[-1]*self.column_count
        self.supports=[len(rs) for rs in self.columns]
        self.domains=[(1<<n)-1 for _ in range(n*n)]
        self.queue=deque()
        self.changed_cells=set(range(n*n))
        self.removed_candidates=0
        self.forced_placements=0
        self.support_updates=0
        self.matching_checks=0
        self.unit_scans=0
        self.initial_candidates=self.row_count
        # Each fixed clue is an *exact-cover row*, not a hypothetical branch.
        for cell,digit in enumerate(puzzle.entries):
            if digit:
                if not 1<=digit<=n:
                    raise ExactCoverContradiction('Clue outside digit range')
                self.select(cell*n+digit-1)
        self.propagate_forced()

    def _update(self):
        self.support_updates+=1
        if self.support_updates>self.limits.max_updates:
            raise PropagationCapacityError('Exact cover support-update limit')

    def remove(self,row):
        if not self.active[row]:
            return False
        if self.selected[row]:
            raise ExactCoverContradiction('Attempted to eliminate a forced placement')
        self.active[row]=0
        self.removed_candidates+=1
        cell,d=divmod(row,self.n)
        self.domains[cell]&=~(1<<d)
        self.changed_cells.add(cell)
        for col in self.rows[row]:
            self._update()
            self.supports[col]-=1
            if not self.supports[col]:
                raise ExactCoverContradiction('Zero-support exact-cover column')
            if self.supports[col]==1 and self.covered[col]<0:
                self.queue.append(col)
        return True

    def select(self,row):
        if not self.active[row]:
            raise ExactCoverContradiction('Forced row has been eliminated')
        if self.selected[row]:
            return False
        for col in self.rows[row]:
            if self.covered[col]>=0 and self.covered[col]!=row:
                raise ExactCoverContradiction('Conflicting exact-cover placement')
        self.selected[row]=1
        self.forced_placements+=1
        for col in self.rows[row]:
            self.covered[col]=row
        for col in self.rows[row]:
            for rival in self.columns[col]:
                if rival!=row:
                    self.remove(rival)
        return True

    def propagate_forced(self):
        while self.queue:
            col=self.queue.popleft()
            if self.covered[col]>=0 or self.supports[col]!=1:
                continue
            row=next((r for r in self.columns[col] if self.active[r]),None)
            if row is None:
                raise ExactCoverContradiction('Empty support for forced column')
            self.select(row)

    def remove_cell_digit(self,cell,digit):
        if not (0<=cell<self.n*self.n and 1<=digit<=self.n):
            raise ValueError('Candidate outside grid')
        changed=self.remove(cell*self.n+digit-1)
        if changed:
            self.propagate_forced()
        return changed

    def project_matching(self, matching_possible):
        """Event-driven generalized all-different consistency, no recursion tree.

        A changed domain queues precisely its row/column/box units. A signature
        avoids recomputing any unit whose domains have not changed.
        """
        units=[tuple(unit) for unit in self.puzzle.units()]
        incident=[[] for _ in self.domains]
        for i,unit in enumerate(units):
            for cell in unit:
                incident[cell].append(i)
        pending=deque(range(len(units)))
        pending_set=set(range(len(units)))
        last=[None]*len(units)
        self.changed_cells.clear()
        while pending:
            unit_index=pending.popleft()
            pending_set.remove(unit_index)
            unit=units[unit_index]
            ds=tuple(self.domains[c] for c in unit)
            if last[unit_index]==ds:
                continue
            last[unit_index]=ds
            self.unit_scans+=1
            if self.unit_scans>self.limits.max_unit_scans:
                raise PropagationCapacityError('Exact cover matching-unit scan limit')
            # A fully free permutation unit trivially supports every entry.
            if all(x==(1<<self.n)-1 for x in ds):
                continue
            self.matching_checks+=1
            if self.matching_checks>self.limits.max_matching_checks:
                raise PropagationCapacityError('Exact cover matching-check limit')
            if not matching_possible(list(ds),self.n):
                raise ExactCoverContradiction('A Sudoku all-different factor has no completion')
            for j,cell in enumerate(unit):
                candidates=self.domains[cell]
                while candidates:
                    bit=candidates&-candidates
                    candidates-=bit
                    if self.domains[cell]&bit==0:
                        continue
                    # A forced singleton has support in any valid matching.
                    if self.domains[cell]==bit:
                        continue
                    test=[self.domains[c] for c in unit]
                    test[j]=bit
                    self.matching_checks+=1
                    if self.matching_checks>self.limits.max_matching_checks:
                        raise PropagationCapacityError('Exact cover matching-check limit')
                    if not matching_possible(test,self.n):
                        self.remove_cell_digit(cell,bit.bit_length())
            if self.changed_cells:
                for cell in sorted(self.changed_cells):
                    for affected in incident[cell]:
                        if affected not in pending_set:
                            pending.append(affected)
                            pending_set.add(affected)
                self.changed_cells.clear()
        return tuple(self.domains)

    def connected_components(self):
        """Residual row-column bipartite components, O(number of incidences)."""
        seen_rows=set()
        seen_cols=set()
        components=[]
        for start in range(self.row_count):
            if not self.active[start] or self.selected[start] or start in seen_rows:
                continue
            pending=[start]
            seen_rows.add(start)
            rows=0
            cols=0
            while pending:
                row=pending.pop()
                rows+=1
                for col in self.rows[row]:
                    if self.covered[col]>=0 or col in seen_cols:
                        continue
                    seen_cols.add(col)
                    cols+=1
                    for other in self.columns[col]:
                        if self.active[other] and not self.selected[other] and other not in seen_rows:
                            seen_rows.add(other)
                            pending.append(other)
            components.append((rows,cols))
        return tuple(components)

    def metrics(self):
        return {
            'initial_candidates':self.initial_candidates,
            'remaining_candidates':sum(map(int,self.active)),
            'unforced_candidates':sum(map(int,self.active))-sum(map(int,self.selected)),
            'removed_candidates':self.removed_candidates,
            'forced_placements':self.forced_placements,
            'support_updates':self.support_updates,
            'matching_checks':self.matching_checks,
            'matching_unit_scans':self.unit_scans,
            'residual_components':len(self.connected_components()),
        }


def propagate(puzzle, *, matching=False, matching_possible=None, limits=None):
    state=ExactCoverPropagation(puzzle,limits=limits)
    if matching:
        if matching_possible is None:
            raise ValueError('A polynomial matching implementation is required')
        state.project_matching(matching_possible)
    return state
