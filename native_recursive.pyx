# cython: language_level=3, boundscheck=False, wraparound=False, initializedcheck=False
"""Complete packet and bounded leaf contraction kernels.

All ring values are Python arbitrary-precision objects. Python oracle callbacks
remain mandatory at the abstraction boundary; the entire table construction,
convolution, and elimination loops stay within a single Cython invocation.
"""

from non_exponential_sudoku.runtime.cost_ledger import charge as ledger_charge


def packet_evaluate(tuple bits, object ring, tuple left_positions,
                    tuple row_cauchy, object contributions, tuple desired,
                    tuple tile_slots, tuple right_positions):
    """Exact packet evaluation using mixed-radix coefficient indices.

    No Python dict of exponent tuples, and no Python-level per-row callbacks.
    Dense storage only when the checked state product is <= 512; otherwise
    sparse integer-key storage retains the original mathematical semantics.
    """
    cdef Py_ssize_t k, n=len(desired), x, y, idx, step, size
    cdef object cap=1, stride
    cdef list strides=[], states, nxt_dense, bits_right=[]
    cdef dict coeffs, nxt, target_map={}
    cdef object zero=ring.zero, one=ring.one, add=ring.add, mul=ring.mul
    cdef object sub=ring.sub, neg=ring.neg, pow_=ring.pow, scalar=ring.scalar
    cdef object v, local, const, coef, new, val, state, key, term, value
    cdef object row, entry, m, b, tile
    for k in range(n):
        strides.append(cap)
        cap *= desired[k]+1   # Python's int arithmetic for products if needed.
        if cap > 1000000000:
            # Keep huge radix computations as Python integers, but never
            # attempt a huge dense buffer.
            pass
    # Store packet right-bit values in a single slot-indexed array. The slot
    # vector may contain absent ports; these are zero by construction.
    if right_positions:
        size=max(pos for pos,_ in right_positions)+1
    else:
        size=0
    bits_right=[0]*size
    for y,idx in right_positions:
        bits_right[y]=bits[idx]
    if n==0:
        # Common case: no target coefficients. Avoid constructing a dense
        # one-state DP table, its per-row zero test, and a redundant ring.add.
        # All source tile factors below still execute unchanged.
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
    elif cap<=512:
        states=[zero]*cap
        states[0]=one
        for x,(idx,row) in enumerate(zip(left_positions,row_cauchy)):
            local=zero
            for y,coef in row:
                if bits_right[y]:
                    local=add(local,coef)
            if bits[idx]:
                const=local
                active=contributions[x]
            else:
                const=sub(one,local)
                active=tuple((k,neg(coef)) for k,coef in contributions[x])
            nxt_dense=[zero]*cap
            for step in range(cap):
                v=states[step]
                if v==zero:
                    continue
                new=mul(v,const)
                if new!=zero:
                    nxt_dense[step]=add(nxt_dense[step],new)
                for k,coef in active:
                    stride=strides[k]
                    if (step//stride)%(desired[k]+1)>=desired[k]:
                        continue
                    key=step+stride
                    new=mul(v,coef)
                    if new!=zero:
                        nxt_dense[key]=add(nxt_dense[key],new)
            states=nxt_dense
        value=states[cap-1]
    else:
        coeffs={0:one}
        for x,(idx,row) in enumerate(zip(left_positions,row_cauchy)):
            local=zero
            for y,coef in row:
                if bits_right[y]:
                    local=add(local,coef)
            if bits[idx]:
                const=local
                active=contributions[x]
            else:
                const=sub(one,local)
                active=tuple((k,neg(coef)) for k,coef in contributions[x])
            nxt={}
            for state,v in coeffs.items():
                new=mul(v,const)
                if new!=zero:
                    nxt[state]=add(nxt.get(state,zero),new)
                for k,coef in active:
                    stride=strides[k]
                    if (state//stride)%(desired[k]+1)>=desired[k]:
                        continue
                    key=state+stride
                    new=mul(v,coef)
                    if new!=zero:
                        nxt[key]=add(nxt.get(key,zero),new)
            coeffs=nxt
        value=coeffs.get(cap-1,zero)
    for m,b,tile in tile_slots:
        term=zero
        for y,coef in tile:
            if y<size and bits_right[y]:
                term=add(term,scalar(coef**m.b))
        value=mul(value,pow_(term,b))
    return value


def eliminate_leaf(object net, object R, int max_edges=20, int max_width=16):
    """One native call for complete exact factor-table leaf elimination.

    External tensor-entry oracles remain arbitrary Python callables. Fallback
    to the original direct sum uses the same guards as the reference kernel.
    """
    cdef list factors=[], values, out, compiled, positions, ins
    cdef object scope, table
    cdef object zero=R.zero, one=R.one, add=R.add, mul=R.mul, scalar_fn=R.scalar
    cdef object scalar=one, v, entry, ans, term, val, target, key, edge
    cdef set remaining, incident, scope_union
    cdef tuple ports, out_scope, tmp
    cdef dict by_var
    cdef Py_ssize_t i,j,k,mask,bit,ix,pos,offset,lim
    if net.edges>max_edges:
        from non_exponential_sudoku.runtime.budget import CapacityError
        raise CapacityError(f'Leaf has {net.edges} wires; limit is {max_edges}')
    for v in net.left+net.right:
        ports=tuple(v.ports)
        if not ports:
            ledger_charge("vertex_oracle_calls")
            scalar=mul(scalar,v.oracle((),R))
            if scalar==zero:
                return scalar
            continue
        if len(ports)>max_width:
            return net.direct(R,max_edges)
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
            scalar=mul(scalar,scalar_fn(2))
            remaining.remove(edge)
            continue
        scope_union=set()
        for i in incident:
            scope_union.update(factors[i][0])
        scope_union.remove(edge)
        out_scope=tuple(sorted(scope_union))
        if len(out_scope)>max_width:
            return net.direct(R,max_edges)
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
                    term=mul(term,table[ix])
                    if term==zero: break
                ans=add(ans,term)
            out.append(ans)
        factors=[f for i,f in enumerate(factors) if i not in incident]
        if out_scope:
            factors.append((out_scope,tuple(out)))
        else:
            scalar=mul(scalar,out[0])
            if scalar==zero:
                return scalar
        remaining.remove(edge)
    if factors:
        raise AssertionError('Native leaf elimination left unresolved variables')
    return scalar
