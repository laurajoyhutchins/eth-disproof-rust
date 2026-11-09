"""Cook--Mertz interpolation identity over the existing 2-adic extension ring.

This is an exact algebraic proof-of-concept, NOT a complete Cook--Mertz
Tree-Evaluation procedure or a claim about its time complexity in the solver.
For odd m dividing 2**e-1, an unramified 2-adic extension contains a lifted
primitive m-th root of unity, and m remains invertible modulo 2**p.
"""
from non_exponential_sudoku.core.algebra import Padic


def distinct_prime_factors(n):
    factors=[]; k=2
    while k*k <= n:
        if n%k==0:
            factors.append(k)
            while n%k==0:n//=k
        k+=1
    if n>1:factors.append(n)
    return tuple(factors)


def primitive_odd_root(R: Padic, m: int):
    """Hensel-lift a primitive m-th root, retaining exact ring arithmetic."""
    if m<3 or m%2==0 or (1<<R.e)-1 < m or ((1<<R.e)-1)%m:
        raise ValueError('Odd m must divide the residue-field unit order')
    residue=Padic(R.e,R.f,1)
    primes=distinct_prime_factors(m)
    candidate=None
    for bits in range(1,1<<R.e):
        x=residue.basis(bits)
        if residue.pow(x,m)==residue.one and all(
                residue.pow(x,m//ell)!=residue.one for ell in primes):
            candidate=R.basis(bits)
            break
    if candidate is None:raise AssertionError('Primitive residue root missing')
    x=candidate
    for _ in range(R.p.bit_length()+3):
        numerator=R.sub(R.pow(x,m),R.one)
        if numerator==R.zero:break
        derivative=R.mul(R.scalar(m),R.pow(x,m-1))
        x=R.sub(x,R.mul(numerator,R.inv(derivative)))
    if R.pow(x,m)!=R.one or any(R.pow(x,m//ell)==R.one for ell in primes):
        raise AssertionError('Hensel lift failed')
    return x


def root_average_polynomial(R, root, m, v, x, coefficients):
    """Exactly (1/m) sum_j P(v+omega**j*x) mod 2**p."""
    total=R.zero
    for j in range(m):
        argument=R.add(v,R.mul(R.pow(root,j),x))
        term=R.zero
        for c in reversed(coefficients):
            term=R.add(R.mul(term,argument),c)
        total=R.add(total,term)
    return R.mul(total,R.inv(R.scalar(m)))
