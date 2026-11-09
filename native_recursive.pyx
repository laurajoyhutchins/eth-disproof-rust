# cython: language_level=3, boundscheck=False, wraparound=False, initializedcheck=False
"""Complete packet and bounded leaf contraction kernels.

All ring values are Python arbitrary-precision objects. Python oracle callbacks
remain mandatory at the abstraction boundary; the entire table construction,
convolution, and elimination loops stay within a single Cython invocation.
"""

from non_exponential_sudoku.runtime.cost_ledger import charge as ledger_charge
from non_exponential_sudoku.core.network import _check_leaf_factor_budget


from native_ring cimport mul_coords, add_coords
import native_ring as native_ring_module
from non_exponential_sudoku.core.algebra import Padic
from non_exponential_sudoku.core.jets import JetRing
from non_exponential_sudoku.core import algebra as core_algebra
from non_exponential_sudoku.core.flint_backend import flint_enabled
from non_exponential_sudoku.runtime.cost_ledger import active_ledger


cdef class _RingArithmetic:
    """Kernel-local dispatch that retains observable public ring semantics.

    Only built-in Padic and one-level JetRing are fused. Opt-in FLINT,
    observed ledger frames, non-native ring settings and custom ring
    implementations stay on their existing Python ring methods.
    """
    cdef object py_add, py_sub, py_neg, py_mul, mask, modulus
    cdef object jet_add_fn, jet_sub_fn, jet_neg_fn, jet_mul_fn
    cdef int degree
    cdef bint padic, jet

    def __cinit__(self, object ring):
        self.py_add=ring.add
        self.py_sub=ring.sub
        self.py_neg=ring.neg
        self.py_mul=ring.mul
        self.padic=False
        self.jet=False
        if active_ledger() is not None or flint_enabled():
            return
        # Measured crossover: tiny extension rings spend more time entering
        # this adapter than they save in direct native arithmetic. This is
        # performance dispatch, not an algorithmic size/capacity limit.
        if ring.e < 8:
            return
        if type(ring) is Padic and core_algebra._native_ring is not None:
            self.padic=True
        elif (type(ring) is JetRing and type(ring.base) is Padic and
              ring.depth == 1 and
              ring._native_add is native_ring_module.jet_add and
              ring._native_sub is native_ring_module.jet_sub and
              ring._native_neg is native_ring_module.jet_neg and
              ring._native_mul is native_ring_module.jet_mul):
            self.jet=True
        else:
            return
        self.degree=ring.e
        self.modulus=ring.f
        self.mask=ring.mask if self.padic else ring.base.mask
        if self.jet:
            self.jet_add_fn=native_ring_module.jet_add
            self.jet_sub_fn=native_ring_module.jet_sub
            self.jet_neg_fn=native_ring_module.jet_neg
            self.jet_mul_fn=native_ring_module.jet_mul

    cdef inline object add(self, object a, object b):
        if self.padic:
            return add_coords(<tuple>a, <tuple>b, self.mask)
        if self.jet:
            return self.jet_add_fn(<tuple>a, <tuple>b, self.mask)
        return self.py_add(a,b)

    cdef inline object sub(self, object a, object b):
        if self.padic:
            return tuple((a[i]-b[i])&self.mask for i in range(self.degree))
        if self.jet:
            return self.jet_sub_fn(<tuple>a, <tuple>b, self.mask)
        return self.py_sub(a,b)

    cdef inline object neg(self, object a):
        if self.padic:
            return tuple((-a[i])&self.mask for i in range(self.degree))
        if self.jet:
            return self.jet_neg_fn(<tuple>a, self.mask)
        return self.py_neg(a)

    cdef inline object mul(self, object a, object b):
        if self.padic:
            return mul_coords(<tuple>a, <tuple>b,
                              self.degree, self.modulus, self.mask)
        if self.jet:
            return self.jet_mul_fn(<tuple>a, <tuple>b,
                           self.degree, self.modulus, self.mask)
        return self.py_mul(a,b)




cdef inline bint _can_finish(object encoded, tuple desired,
                              list strides, list minimums,
                              object min_total):
    """Necessary condition for a partial monomial to reach the target."""
    cdef Py_ssize_t k
    cdef object digit, degree=0
    for k in range(len(desired)):
        digit=(encoded//strides[k])%(desired[k]+1)
        if digit<minimums[k]:
            return False
        degree+=digit
    return degree>=min_total


def packet_evaluate(tuple bits, object ring, tuple left_positions,
                    tuple row_cauchy, object contributions, tuple desired,
                    tuple tile_slots, tuple right_positions,
                    bint positions_are_bits=False):
    """Exact packet evaluation using mixed-radix coefficient indices.

    No Python dict of exponent tuples, and no Python-level per-row callbacks.
    Dense storage only when the checked state product is <= 512; otherwise
    sparse integer-key storage retains the original mathematical semantics.
    """
    cdef Py_ssize_t k, n=len(desired), x, y, idx, step, size
    cdef object cap=1, stride
    cdef list strides=[], states, nxt_dense
    cdef object bits_right
    cdef dict coeffs, nxt, target_map={}
    cdef _RingArithmetic ops
    cdef object add, mul, sub
    cdef object zero=ring.zero, one=ring.one
    cdef object pow_=ring.pow, scalar=ring.scalar
    cdef object v, local, const, coef, new, val, state, key, term, value
    cdef object row, entry, m, b, tile
    cdef object target_degree=sum(desired), min_total, encoded
    cdef list support=[], available=[0]*n, lower, eligible
    cdef object allowed_mask
    cdef set indices
    cdef bint impossible=False, restrict
    for k in range(n):
        strides.append(cap)
        cap *= desired[k]+1   # Python's int arithmetic for products if needed.
        if cap > 1000000000:
            # Keep huge radix computations as Python integers, but never
            # attempt a huge dense buffer.
            pass
    # Store packet right-bit values in a single slot-indexed array. The slot
    # vector may contain absent ports; these are zero by construction.
    if positions_are_bits:
        # PacketEntry binds slot IDs to bit positions once at construction.
        # Reuse the same assignment tuple directly, with no per-call
        # scatter, maximal-slot scan, or temporary Python list.
        bits_right=bits
        size=len(bits)
    else:
        # Keep the public kernel ABI for direct independent-oracle calls.
        if right_positions:
            size=max(pos for pos,_ in right_positions)+1
        else:
            size=0
        bits_right=[0]*size
        for y,idx in right_positions:
            bits_right[y]=bits[idx]
    if n==0:
        # Direct Cauchy products are already specialized. Their tiny ring
        # operations do not amortize the additional native dispatch adapter.
        add=ring.add
        mul=ring.mul
        sub=ring.sub
        value=one
        for x,(idx,row) in enumerate(zip(left_positions,row_cauchy)):
            local=zero
            for y,coef in row:
                if bits_right[y]:
                    local=add(local,coef)
            const=local if bits[idx] else sub(one,local)
            value=mul(value,const)
            if value==zero:
                break
        for m,b,tile in tile_slots:
            term=zero
            for y,coef in tile:
                if y<size and bits_right[y]:
                    term=add(term,scalar(coef**m.b))
            value=mul(value,pow_(term,b))
        return value
    # A packet row is a linear polynomial in the target modes: it can
    # increase at most one exponent, regardless of how many terms it has.
    # Count each mode at most once per row, even with duplicate entries.
    # Counts are upper bounds: cancellation can only reduce true support.
    for row in contributions:
        indices=set()
        for k,coef in row:
            if desired[k] and coef!=zero:
                indices.add(k)
        support.append(tuple(indices))
        for k in indices:
            available[k]+=1
    impossible=(target_degree>len(left_positions) or
                any(desired[k]>available[k] for k in range(n)))
    ops=_RingArithmetic(ring)
    if impossible:
        # Still apply source tile factors below: this maintains the same
        # caller-visible ring computation and backend contract.
        value=zero
    elif cap<=512:
        states=[zero]*cap
        states[0]=one
        for x,(idx,row) in enumerate(zip(left_positions,row_cauchy)):
            for k in support[x]:
                available[k]-=1
            lower=[max(0,desired[k]-available[k]) for k in range(n)]
            min_total=max(0,target_degree-(len(left_positions)-x-1))
            # Dense states are bounded to 512. Materialize only monomials
            # that can still reach the target, before doing ring arithmetic.
            allowed_mask=None
            if min_total or any(lower):
                eligible=[0]
                for k in range(n):
                    eligible=[encoded+digit*strides[k] for encoded in eligible
                              for digit in range(lower[k],desired[k]+1)]
                allowed_mask=bytearray(cap)
                for encoded in eligible:
                    if _can_finish(encoded,desired,strides,lower,min_total):
                        allowed_mask[encoded]=1
            local=zero
            for y,coef in row:
                if bits_right[y]:
                    local=ops.add(local,coef)
            if bits[idx]:
                const=local
                active=contributions[x]
            else:
                const=ops.sub(one,local)
                active=tuple((k,ops.neg(coef)) for k,coef in contributions[x])
            nxt_dense=[zero]*cap
            for step in range(cap):
                v=states[step]
                if v==zero:
                    continue
                if const!=zero and (allowed_mask is None or allowed_mask[step]):
                    new=ops.mul(v,const)
                    if new!=zero:
                        nxt_dense[step]=ops.add(nxt_dense[step],new)
                for k,coef in active:
                    if coef==zero:
                        continue
                    stride=strides[k]
                    if (step//stride)%(desired[k]+1)>=desired[k]:
                        continue
                    key=step+stride
                    if allowed_mask is not None and not allowed_mask[key]:
                        continue
                    new=ops.mul(v,coef)
                    if new!=zero:
                        nxt_dense[key]=ops.add(nxt_dense[key],new)
            states=nxt_dense
        value=states[cap-1]
    else:
        coeffs={0:one}
        for x,(idx,row) in enumerate(zip(left_positions,row_cauchy)):
            for k in support[x]:
                available[k]-=1
            lower=[max(0,desired[k]-available[k]) for k in range(n)]
            min_total=max(0,target_degree-(len(left_positions)-x-1))
            restrict=bool(min_total or any(lower))
            local=zero
            for y,coef in row:
                if bits_right[y]:
                    local=ops.add(local,coef)
            if bits[idx]:
                const=local
                active=contributions[x]
            else:
                const=ops.sub(one,local)
                active=tuple((k,ops.neg(coef)) for k,coef in contributions[x])
            nxt={}
            for state,v in coeffs.items():
                if v==zero:
                    continue
                if (const!=zero and
                    (not restrict or _can_finish(state,desired,strides,lower,min_total))):
                    new=ops.mul(v,const)
                    if new!=zero:
                        nxt[state]=ops.add(nxt.get(state,zero),new)
                for k,coef in active:
                    if coef==zero:
                        continue
                    stride=strides[k]
                    if (state//stride)%(desired[k]+1)>=desired[k]:
                        continue
                    key=state+stride
                    if restrict and not _can_finish(key,desired,strides,lower,min_total):
                        continue
                    new=ops.mul(v,coef)
                    if new!=zero:
                        nxt[key]=ops.add(nxt.get(key,zero),new)
            coeffs=nxt
        value=coeffs.get(cap-1,zero)
    for m,b,tile in tile_slots:
        term=zero
        for y,coef in tile:
            if y<size and bits_right[y]:
                term=ops.add(term,scalar(coef**m.b))
        value=ops.mul(value,pow_(term,b))
    return value



cdef object _execute_compiled_leaf(object plan, dict tables, object R,
                                   object max_factor_bytes, _RingArithmetic ops):
    """Use the reference LeafPlan without re-planning or reindexing factors."""
    cdef object zero=R.zero, one=R.one
    cdef object scalar=one, step, involved, table, indices, value
    cdef object acc, term, row, positions, out_scope
    cdef list out
    cdef Py_ssize_t mask, bit, ix, offset, pos, involved_entries
    # The exact same live-table envelope as the Python reference, but
    # updated incrementally instead of rescanning all surviving tables
    # after every elimination.
    cdef Py_ssize_t live_entries=sum(len(table) for table in tables.values())
    for step in plan.steps:
        if not step.incident:
            scalar=ops.mul(scalar,R.scalar(2))
            continue
        involved=[tables.pop(index) for index in step.incident]
        involved_entries=sum(len(table) for table in involved)
        live_entries-=involved_entries
        _check_leaf_factor_budget(
            live_entries + involved_entries +
            (1 << len(step.out_scope)), R, max_factor_bytes)
        out=[]
        if step.lookup is not None:
            for row in step.lookup:
                ledger_charge("leaf_elimination_rows")
                acc=zero
                for bit in range(2):
                    term=one
                    for table,indices in zip(involved,row):
                        value=table[indices[bit]]
                        if value is zero:
                            term=zero
                            break
                        if term is one:
                            term=value
                        elif value is not one:
                            term=ops.mul(term,value)
                        if term==zero:
                            break
                    acc=ops.add(acc,term)
                out.append(acc)
        else:
            for mask in range(1 << len(step.out_scope)):
                ledger_charge("leaf_elimination_rows")
                acc=zero
                for bit in range(2):
                    term=one
                    for positions,table in zip(step.positions,involved):
                        ix=0
                        for offset,pos in enumerate(positions):
                            ix |= ((bit if pos<0 else (mask>>pos)&1)<<offset)
                        value=table[ix]
                        if value is zero:
                            term=zero
                            break
                        if term is one:
                            term=value
                        elif value is not one:
                            term=ops.mul(term,value)
                        if term==zero:
                            break
                    acc=ops.add(acc,term)
                out.append(acc)
        if step.out_scope:
            tables[step.output_id]=tuple(out)
            live_entries+=len(out)
        else:
            scalar=ops.mul(scalar,out[0])
            if scalar==zero:
                return zero
    if tables:
        raise AssertionError('Native compiled leaf left unresolved factors')
    return scalar

def eliminate_leaf(object net, object R, int max_edges=20, int max_width=16,
                   *, object plan=None, object max_factor_bytes=None):
    """One native call for complete exact factor-table leaf elimination.

    External tensor-entry oracles remain arbitrary Python callables. Fallback
    to the original direct sum uses the same guards as the reference kernel.
    """
    cdef list factors=[], values, out, compiled, positions, ins
    cdef object scope, table
    cdef _RingArithmetic ops=_RingArithmetic(R)
    cdef object zero=R.zero, one=R.one, scalar_fn=R.scalar
    cdef object scalar=one, v, entry, ans, term, val, target, key, edge
    cdef set remaining, incident, scope_union
    cdef tuple ports, out_scope, tmp
    cdef dict by_var, tables
    cdef object scopes
    cdef Py_ssize_t table_index=0
    cdef Py_ssize_t i,j,k,mask,bit,ix,pos,offset,lim
    if max_factor_bytes is not None and max_factor_bytes < 1:
        raise ValueError('Leaf factor memory budget must be positive')
    if net.edges>max_edges:
        from non_exponential_sudoku.runtime.budget import CapacityError
        raise CapacityError(f'Leaf has {net.edges} wires; limit is {max_edges}')
    if plan is not None:
        scopes=tuple(v.ports for v in net.left+net.right if v.ports)
        if (plan.edges != net.edges or plan.input_scopes != scopes or
                plan.max_width != max_width):
            raise ValueError('Leaf plan does not match this network topology')
        tables={}
        scalar=one
        for v in net.left+net.right:
            ports=tuple(v.ports)
            if not ports:
                ledger_charge("vertex_oracle_calls")
                scalar=ops.mul(scalar,v.oracle((),R))
                if scalar==zero:
                    return scalar
                continue
            _check_leaf_factor_budget(
                sum(len(table) for table in tables.values()) +
                (1 << len(ports)), R, max_factor_bytes)
            values=[]
            for ix in range(1<<len(ports)):
                ledger_charge("vertex_oracle_calls")
                values.append(v.oracle(tuple((ix>>i)&1 for i in range(len(ports))),R))
            if all(t==zero for t in values):
                return zero
            tables[table_index]=tuple(values)
            table_index+=1
        return ops.mul(scalar,_execute_compiled_leaf(plan,tables,R,max_factor_bytes,ops))
    for v in net.left+net.right:
        ports=tuple(v.ports)
        if not ports:
            ledger_charge("vertex_oracle_calls")
            scalar=ops.mul(scalar,v.oracle((),R))
            if scalar==zero:
                return scalar
            continue
        if len(ports)>max_width:
            return net.direct(R,max_edges)
        _check_leaf_factor_budget(
            sum(len(table) for _,table in factors) +
            (1 << len(ports)), R, max_factor_bytes)
        values=[]
        for ix in range(1<<len(ports)):
            ledger_charge("vertex_oracle_calls")
            values.append(v.oracle(tuple((ix>>i)&1 for i in range(len(ports))),R))
        if all(t==zero for t in values):
            return zero
        factors.append((ports,tuple(values)))
    remaining=set(range(net.edges))
    while remaining:
        by_var={e:[i for i,(scope,table) in enumerate(factors) if e in scope]
                for e in remaining}
        def cost(e):
            ins=by_var[e]
            return (len(set().union(*(factors[i][0] for i in ins)))-1 if ins else -1,
                    len(ins),e)
        edge=min(remaining,key=cost)
        incident=set(by_var[edge])
        if not incident:
            scalar=ops.mul(scalar,scalar_fn(2))
            remaining.remove(edge)
            continue
        scope_union=set()
        for i in incident:
            scope_union.update(factors[i][0])
        scope_union.remove(edge)
        out_scope=tuple(sorted(scope_union))
        if len(out_scope)>max_width:
            return net.direct(R,max_edges)
        _check_leaf_factor_budget(
            sum(len(table) for _,table in factors) +
            (1 << len(out_scope)), R, max_factor_bytes)
        compiled=[]
        for i in sorted(incident):
            ports,table=factors[i]
            positions=[out_scope.index(x) if x!=edge else -1 for x in ports]
            compiled.append((positions,table))
        out=[]
        for mask in range(1<<len(out_scope)):
            ledger_charge("leaf_elimination_rows")
            ans=zero
            for bit in range(2):
                term=one
                for positions,table in compiled:
                    ix=0
                    for offset,pos in enumerate(positions):
                        ix |= ((bit if pos<0 else (mask>>pos)&1)<<offset)
                    term=ops.mul(term,table[ix])
                    if term==zero: break
                ans=ops.add(ans,term)
            out.append(ans)
        factors=[f for i,f in enumerate(factors) if i not in incident]
        if out_scope:
            factors.append((out_scope,tuple(out)))
        else:
            scalar=ops.mul(scalar,out[0])
            if scalar==zero:
                return scalar
        remaining.remove(edge)
    if factors:
        raise AssertionError('Native leaf elimination left unresolved variables')
    return scalar
