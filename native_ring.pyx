# cython: boundscheck=False, wraparound=False, initializedcheck=False
"""Optional Cython-native execution of exact Z/2^p[U]/f arithmetic.
The operations remain Python arbitrary-precision integers; only loops are native.
"""
cdef tuple mul_coords(tuple a, tuple b, int e, object f, object mask):
    if e < 1 or len(a) != e or len(b) != e:
        raise ValueError("Ring coordinate length mismatch")
    cdef list tmp=[0]*(2*e-1)
    cdef int i,j
    cdef object ai, bj, h
    for i in range(e):
        ai=a[i]
        if ai:
            for j in range(e):
                bj=b[j]
                if bj:
                    tmp[i+j] = tmp[i+j] + ai*bj
    for i in range(2*e-2,e-1,-1):
        h=tmp[i] & mask
        if h:
            for j in range(e):
                if (f>>j)&1:
                    tmp[i-e+j] = tmp[i-e+j]-h
    return tuple([tmp[i]&mask for i in range(e)])

cdef tuple add_coords(tuple a, tuple b, object mask):
    cdef Py_ssize_t i, e=len(a)
    if len(b) != e: raise ValueError("Ring coordinate length mismatch")
    return tuple([(a[i]+b[i])&mask for i in range(e)])

def mul(tuple a, tuple b, int e, object f, object mask):
    return mul_coords(a,b,e,f,mask)

def add(tuple a, tuple b, object mask):
    return add_coords(a,b,mask)

def sub(tuple a, tuple b, object mask):
    cdef Py_ssize_t i, e=len(a)
    if len(b) != e: raise ValueError("Ring coordinate length mismatch")
    return tuple([(a[i]-b[i])&mask for i in range(e)])

# Exact truncated polynomial operations in A_p[z]/(z**q).
# All loops compile to C, while the large integer arithmetic remains Python-exact.
def jet_add(tuple a, tuple b, object mask):
    """Coordinatewise exact sum; preserve sparse coefficients unchanged."""
    cdef Py_ssize_t i, j, q=len(a), e=len(a[0])
    cdef tuple zero=(0,)*e
    cdef list out=[]
    cdef object ai,bi
    if len(b)!=q: raise ValueError('jet degree mismatch')
    for i in range(q):
        ai=a[i]; bi=b[i]
        if len(ai)!=e or len(bi)!=e:
            raise ValueError('Ring coordinate length mismatch')
        if ai==zero:
            out.append(tuple([bi[j]&mask for j in range(e)]))
        elif bi==zero:
            out.append(tuple([ai[j]&mask for j in range(e)]))
        else:
            out.append(tuple([(ai[j]+bi[j])&mask for j in range(e)]))
    return tuple(out)

def jet_sub(tuple a, tuple b, object mask):
    """Coordinatewise exact difference with sparse coefficient bypass."""
    cdef Py_ssize_t i, j, q=len(a), e=len(a[0])
    cdef tuple zero=(0,)*e
    cdef list out=[]
    cdef object ai,bi
    if len(b)!=q: raise ValueError('jet degree mismatch')
    for i in range(q):
        ai=a[i]; bi=b[i]
        if len(ai)!=e or len(bi)!=e:
            raise ValueError('Ring coordinate length mismatch')
        if bi==zero:
            out.append(tuple([ai[j]&mask for j in range(e)]))
        elif ai==zero:
            out.append(tuple([(-bi[j])&mask for j in range(e)]))
        else:
            out.append(tuple([(ai[j]-bi[j])&mask for j in range(e)]))
    return tuple(out)

def jet_neg(tuple a, object mask):
    cdef Py_ssize_t i, j, q=len(a), e=len(a[0])
    cdef list out=[]
    for i in range(q):
        out.append(tuple([(-a[i][j])&mask for j in range(e)]))
    return tuple(out)

def jet_mul_pairwise(tuple a, tuple b, int e, object f, object mask):
    cdef Py_ssize_t i,j,q=len(a)
    cdef list out
    cdef tuple zero=(0,)*e
    cdef object term
    if len(b)!=q: raise ValueError('jet degree mismatch')
    out=[zero]*q
    for i in range(q):
        if a[i]==zero: continue
        for j in range(q-i):
            if b[j]==zero: continue
            term=mul(a[i],b[j],e,f,mask)
            out[i+j]=add(out[i+j],term,mask)
    return tuple(out)


def jet_mul(tuple a, tuple b, int e, object f, object mask):
    """Exact sparse, truncated Taylor convolution over Z/(2**p)[U]/f.

    Classify nonzero Taylor coefficients once instead of testing every (i,j)
    pair. Scalar coefficients are especially common in recursive packet jets:
    multiplying two scalar Taylor polynomials requires no extension-ring
    polynomial multiplication or modulus reduction. A scalar times a general
    extension element likewise needs only coordinatewise multiplication.
    Mixed general coefficients retain the fused arbitrary-precision reduction.
    """
    cdef Py_ssize_t q=len(a), i,j,k,l,offset,width,degree
    cdef list active_a=[], active_b=[], raw, coords, accum, out=[]
    cdef tuple zero=(0,)*e
    cdef object ai,bj,h,product
    cdef bint scalar_a=True, scalar_b=True
    if len(b)!=q or e<1:
        raise ValueError('jet degree mismatch')
    for i in range(q):
        ai=a[i]
        bj=b[i]
        if len(ai)!=e or len(bj)!=e:
            raise ValueError('Ring coordinate length mismatch')
        if ai!=zero:
            active_a.append((i,ai))
            if scalar_a:
                for k in range(1,e):
                    if ai[k]:
                        scalar_a=False
                        break
        if bj!=zero:
            active_b.append((i,bj))
            if scalar_b:
                for k in range(1,e):
                    if bj[k]:
                        scalar_b=False
                        break
    if not active_a or not active_b:
        return (zero,)*q
    if scalar_a and scalar_b:
        # Every coefficient lives in the scalar subring Z/(2**p).
        # Integer sums are unbounded; reduce only once per Taylor degree.
        accum=[0]*q
        for i,ai in active_a:
            for j,bj in active_b:
                degree=i+j
                if degree>=q:
                    break
                accum[degree]=accum[degree]+ai[0]*bj[0]
        return tuple((accum[i]&mask,)+(0,)*(e-1) for i in range(q))
    if scalar_a or scalar_b:
        # A scalar extension factor cannot create powers of U. Retain the
        # complete base-coordinate vector and reduce once per coefficient.
        coords=[0]*(q*e)
        for i,ai in active_a:
            for j,bj in active_b:
                degree=i+j
                if degree>=q:
                    break
                offset=degree*e
                if scalar_a:
                    product=ai[0]
                    for k in range(e):
                        coords[offset+k]=coords[offset+k]+product*bj[k]
                else:
                    product=bj[0]
                    for k in range(e):
                        coords[offset+k]=coords[offset+k]+product*ai[k]
        return tuple(tuple(coords[i*e+k]&mask for k in range(e))
                     for i in range(q))
    # General extension-ring coefficients: keep the existing fused reduction
    # instead of materializing intermediate base-ring products.
    width=2*e-1
    raw=[0]*(q*width)
    for i,ai in active_a:
        for j,bj in active_b:
            degree=i+j
            if degree>=q:
                break
            offset=degree*width
            for k in range(e):
                if not ai[k]:
                    continue
                for l in range(e):
                    if bj[l]:
                        raw[offset+k+l]=raw[offset+k+l]+ai[k]*bj[l]
    for i in range(q):
        offset=i*width
        for k in range(width-1,e-1,-1):
            h=raw[offset+k] & mask
            if h:
                for l in range(e):
                    if (f>>l)&1:
                        raw[offset+k-e+l]=raw[offset+k-e+l]-h
        out.append(tuple(raw[offset+k]&mask for k in range(e)))
    return tuple(out)
