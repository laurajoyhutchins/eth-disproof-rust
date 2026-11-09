# cython: language_level=3, boundscheck=False, wraparound=False, initializedcheck=False
"""Complete, optional Cython sparse factor join and elimination kernels.

Exact ring values remain arbitrary precision Python objects; no float or
fixed-width integer arithmetic is used for coefficients.  The formal degree
is distinct from nested Taylor jet variables.  Resource refusals and work
counts have the same semantics as the Python reference implementation.
"""
from non_exponential_sudoku.elimination.factors import Factor
from non_exponential_sudoku.runtime.cost_ledger import charge as ledger_charge, native_call
from native_ring cimport mul_coords, add_coords

cdef class _Kernel:
    cdef object ring, budget, stats, zero, modulus, mask
    cdef int extension_degree
    cdef bint padic
    cdef Py_ssize_t cap, pending, ceiling, native_ring_muls, native_ring_adds

    def __cinit__(self, object ring, Py_ssize_t cap, object budget, object stats):
        self.ring=ring
        self.padic=hasattr(ring,'mask')
        if self.padic:
            self.mask=ring.mask
            self.modulus=ring.f
            self.extension_degree=ring.e
        self.zero=ring.zero
        self.cap=cap
        self.budget=budget
        self.stats=stats
        self.ceiling=budget.max_operations-budget.operations-budget.order_scans
        self.pending=0
        self.native_ring_muls=0
        self.native_ring_adds=0

    cdef inline void work(self) except *:
        self.pending+=1
        if self.pending>self.ceiling:
            self.flush()
            raise self.budget.CapacityError('Mode DP arithmetic work limit')

    cdef void flush(self):
        if self.pending:
            self.budget.operations += self.pending
            self.stats.mode_dp_operations += self.pending
            ledger_charge("mode_dp_work_units", self.pending)
            self.ceiling -= self.pending
            self.pending=0
        if self.native_ring_muls:
            ledger_charge("native_sparse_padic_mul_calls",self.native_ring_muls)
            self.native_ring_muls=0
        if self.native_ring_adds:
            ledger_charge("native_sparse_padic_add_calls",self.native_ring_adds)
            self.native_ring_adds=0

    cdef inline void guard(self, Py_ssize_t states, Py_ssize_t terms, object description) except *:
        if self.budget.growth_probe is not None:
            self.flush()  # observation gets the current exact work count
        self.budget.guard_build(states,terms,description)

    cdef inline object ring_mul(self, object a, object b):
        if self.padic:
            self.native_ring_muls+=1
            return mul_coords(a,b,self.extension_degree,self.modulus,self.mask)
        return self.ring.mul(a,b)

    cdef inline object ring_add(self, object a, object b):
        if self.padic:
            self.native_ring_adds+=1
            return add_coords(a,b,self.mask)
        return self.ring.add(a,b)

    cdef dict mul(self, dict a, dict b):
        cdef dict out={}
        cdef object ia, ib, va, vb, val, updated, degree
        if not a or not b:
            return out
        for ia,va in a.items():
            for ib,vb in b.items():
                degree=ia+ib
                if degree>=self.cap:
                    continue
                self.work()
                val=self.ring_mul(va,vb)
                if val==self.zero:
                    continue
                updated=self.ring_add(out.get(degree,self.zero),val)
                if updated==self.zero:
                    out.pop(degree,None)
                else:
                    out[degree]=updated
                self.guard(1,len(out),'polynomial convolution')
        return out

    cdef void add(self, dict target, dict source) except *:
        cdef object degree, value, got
        for degree,value in source.items():
            if degree>=self.cap:
                continue
            self.work()
            got=self.ring_add(target.get(degree,self.zero),value)
            if got==self.zero:
                target.pop(degree,None)
            else:
                target[degree]=got

    cdef object join(self, list factors, object modes):
        cdef list remaining=list(factors)
        cdef object joined, nxt, f, ra, rp, la, lp, poly, key, lookup, assignment
        cdef dict index, new_table, a_map
        cdef tuple union, shared, left_indices, right_indices, right_only, positions, weight_values
        cdef object js, score, candidate, j, at, b, d, v
        cdef Py_ssize_t idx, i, new_terms, assigned_weight
        remaining.sort(key=lambda f:(len(f.table),len(f.scope),f.scope))
        joined=remaining.pop(0)
        while remaining:
            js=set(joined.scope)
            idx=min(range(len(remaining)),key=lambda i:(
                -len(js.intersection(remaining[i].scope)),
                len(joined.table)*len(remaining[i].table),
                len(js.union(remaining[i].scope)),remaining[i].scope))
            nxt=remaining.pop(idx)
            union=tuple(sorted(set(joined.scope).union(nxt.scope)))
            shared=tuple(sorted(set(joined.scope).intersection(nxt.scope)))
            left_indices=tuple(joined.scope.index(j) for j in shared)
            right_indices=tuple(nxt.scope.index(j) for j in shared)
            right_only=tuple((j,nxt.scope.index(j)) for j in nxt.scope if j not in js)
            positions=tuple((0,joined.scope.index(j)) if j in js
                            else (1,nxt.scope.index(j)) for j in union)
            weight_values=tuple(modes[j].weight for j in union)
            index={}
            for ra,rp in nxt.table.items():
                self.work()
                key=tuple(ra[i] for i in right_indices)
                index.setdefault(key,[]).append((ra,rp))
            new_table={}
            new_terms=0
            for la,lp in joined.table.items():
                self.work()
                lookup=tuple(la[i] for i in left_indices)
                for ra,rp in index.get(lookup,()):
                    self.work()
                    assignment=tuple(la[at] if side==0 else ra[at] for side,at in positions)
                    assigned_weight=sum(weight*b for weight,b in zip(weight_values,assignment))
                    if assigned_weight>=self.cap:
                        continue
                    poly=self.mul(lp,rp)
                    if not poly:
                        continue
                    poly={d:v for d,v in poly.items() if d+assigned_weight<self.cap}
                    if not poly:
                        continue
                    if assignment in new_table:
                        raise AssertionError('Duplicate natural-join row')
                    new_table[assignment]=poly
                    new_terms+=len(poly)
                    self.guard(len(new_table),new_terms,'sparse separator join')
                    self.stats.mode_dp_sparse_join_rows+=1
            joined=Factor(union,new_table)
            if self.budget.growth_probe is not None:
                self.flush()
                self.budget.growth_probe.joined(self.budget,joined)
            self.stats.mode_dp_sparse_joins+=1
            self.stats.mode_dp_peak_join_states=max(self.stats.mode_dp_peak_join_states,len(new_table))
            if not joined.table:
                break
        return joined

    cdef object eliminate(self, object var, list incident, object modes):
        cdef object joined=self.join(incident,modes)
        cdef tuple out_scope=tuple(j for j in joined.scope if j!=var)
        cdef dict out={}, position={j:k for k,j in enumerate(joined.scope)}
        cdef object assignment, poly, projected, shifted, d, v, b
        cdef Py_ssize_t out_terms=0, prior, shift, retained_weight
        for assignment,poly in joined.table.items():
            self.work()
            b=assignment[position[var]]
            shift=modes[var].weight*b
            projected=tuple(assignment[position[j]] for j in out_scope)
            retained_weight=sum(modes[j].weight*x for j,x in zip(out_scope,projected))
            shifted={d+shift:v for d,v in poly.items()
                     if d+shift+retained_weight<self.cap}
            if not shifted:
                continue
            if projected not in out:
                out[projected]={}
            prior=len(out[projected])
            self.add(out[projected],shifted)
            out_terms+=len(out[projected])-prior
            if not out[projected]:
                del out[projected]
            self.guard(len(out),out_terms,'sparse elimination output')
        return Factor(out_scope,out)

def join_factors_sparse(list factors, object modes, object ring, object budget, object stats):
    """Optional native natural join. Keep a separate Python reference path."""
    native_call("native_sparse_kernel")
    cdef _Kernel kernel=_Kernel(ring,ring.p,budget,stats)
    try:
        return kernel.join(factors,modes)
    finally:
        kernel.flush()

def eliminate_one_sparse(object var, list incident, object modes,
                         object ring, object budget, object stats):
    """Entire join/convolve/weighted-project kernel in one native call."""
    native_call("native_sparse_kernel")
    cdef _Kernel kernel=_Kernel(ring,ring.p,budget,stats)
    try:
        return kernel.eliminate(var,incident,modes)
    finally:
        kernel.flush()
