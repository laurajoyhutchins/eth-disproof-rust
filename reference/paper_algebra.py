#!/usr/bin/env python3
"""Exact miniature implementations of OpenAI ETH paper Appendix D ingredients.

This is an exact-arithmetic audit tool, NOT the full recursive contractor and
NOT an asymptotically subexponential implementation.  It reproduces the
Cauchy deformation W_xy(T) (quantitative-contraction.tex, eq. tensor-cauchy),
and exact Hermite recovery at zero from jets at other integer nodes.
"""
from __future__ import annotations
from fractions import Fraction
from math import comb

# Polynomials in ascending coefficient order with rational coefficients.
def add(a, b):
    return [Fraction(a[i] if i < len(a) else 0) + Fraction(b[i] if i < len(b) else 0) for i in range(max(len(a),len(b)))]

def mul(a, b):
    r = [Fraction(0)] * (len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b):
            r[i+j] += x*y
    return r

def product(polys):
    acc = [Fraction(1)]
    for p in polys:
        acc = mul(acc,p)
    return acc

def eval_poly(p,t):
    ans = Fraction(0)
    for c in reversed(p):
        ans = ans*t + c
    return ans

def jet(p,t,size):
    """Coefficients [z^j] p(t+z) for j=0,..,size-1."""
    return [sum((p[i]*comb(i,j)*t**(i-j) for i in range(j,len(p))),Fraction(0)) for j in range(size)]

def quotient_series(num, den):
    """Truncated (num / den), where den[0] is nonzero."""
    assert den[0] != 0
    q = []
    for j in range(len(num)):
        q.append((num[j]-sum((q[i]*den[j-i] for i in range(j)),Fraction(0)))/den[0])
    return q

def hermite_at_zero(jets: list[tuple[int, list[Fraction]]]) -> Fraction:
    """Recover p(0) given jets at distinct NONZERO nodes, if deg(p)<sum sizes.

    Exact Newton/CRT Hermite reconstruction, no numerical differences.
    This is the algebraic recovery mechanism in the ETH paper, WITHOUT its
    2-adic tapered precision optimization.
    """
    if not jets or any(t == 0 for t,_ in jets) or len({t for t,_ in jets}) != len(jets):
        raise ValueError('Expected distinct nonzero interpolation nodes')
    p, basis = [Fraction(0)], [Fraction(1)]
    for t, coeff in jets:
        m = len(coeff)
        if not m:
            raise ValueError('A node must supply at least one coefficient')
        pjet = jet(p,t,m)
        bjet = jet(basis,t,m)
        quot = quotient_series([Fraction(coeff[i])-pjet[i] for i in range(m)],bjet)
        shift = [Fraction(0)]
        power = [Fraction(1)]
        for c in quot:
            shift = add(shift,[c*x for x in power])
            power = mul(power,[-Fraction(t),Fraction(1)])
        p = add(p,mul(basis,shift))
        basis = mul(basis,product([[-Fraction(t),Fraction(1)]]*m))
    return p[0]

def cauchy_kernel(L: int, x: int, y: int):
    """Paper W_xy(T)=C(T)/(C'(0)*(T-(y-x))), S={-L,..,L-1}."""
    if not 0 <= x < L or not 0 <= y < L:
        raise ValueError('Ports must be in packet')
    if L < 1:
        raise ValueError('L>=1')
    S = list(range(-L,L))
    delta = y-x
    if delta not in S:
        raise ValueError('Invalid delta')
    derivative_at_zero = product([[-Fraction(q),Fraction(1)] for q in S if q != 0])
    c0 = eval_poly(derivative_at_zero,0)
    return [a / c0 for a in product([[-Fraction(q),Fraction(1)] for q in S if q != delta])]

if __name__ == '__main__':
    from pprint import pprint
    for L in (2,4):
        print('L=', L, 'W(0)')
        pprint([[eval_poly(cauchy_kernel(L,x,y),0) for y in range(L)] for x in range(L)])


def direct_cauchy_deformation(graph, max_edges: int = 6):
    """Construct the paper's F(T) exactly for a TINY bipartite tensor graph.

    Implements equation (tensor-deformed-contraction) with one packet of
    L=2^ceil(log2(M)) slots, where M is the graph's number of wires.
    This deliberately uses the direct sum of all X,Y and is ONLY an audit
    oracle for the algebra, NOT the paper's recursive subexponential step.
    """
    from itertools import product as assignments
    M = graph.edges
    if M > max_edges:
        raise ValueError(f'Only for tiny audit graphs with <= {max_edges} wires, got {M}')
    graph.validate()
    L = 1 << (max(1,M)-1).bit_length()
    W = [[cauchy_kernel(L,x,y) for y in range(M)] for x in range(M)]
    row_vertices = [(k,p,v) for k,p,v in graph.vertices if k != 'copy']
    col_vertices = [(k,p,v) for k,p,v in graph.vertices if k == 'copy']
    def eval_factor(kind, ports, payload, assignment):
        vals = [assignment[j] for j in ports]
        if kind == 'clause':
            return int(any(bool(x) if sign > 0 else not x for x,sign in zip(vals,payload)))
        if kind == 'link':
            return int(vals[0] == vals[1])
        if not vals:
            return 2
        return int(all(x == vals[0] for x in vals))

    Z = [Fraction(0)]
    for X in assignments((0,1), repeat=M):
        b = 1
        for kind,ports,payload in col_vertices:
            b *= eval_factor(kind,ports,payload,X)
        if not b:
            continue
        forms = []
        for row in range(M):
            forms.append([sum((W[row][col][i] * X[col] if i < len(W[row][col]) else 0
                              for col in range(M)), Fraction(0))
                          for i in range(2*L)])
        for Y in assignments((0,1),repeat=M):
            a = b
            for kind,ports,payload in row_vertices:
                a *= eval_factor(kind,ports,payload,Y)
            if not a:
                continue
            p = [Fraction(a)]
            for bit, form in zip(Y, forms):
                p = mul(p, form if bit else add([Fraction(1)],[-x for x in form]))
            Z = add(Z,p)
    return Z


def cauchy_deform_direct_sudoku(graph, max_edges: int = 4):
    """Full deformation polynomial for a tiny DIRECT Sudoku tensor network.

    This evaluates exactly the paper's deformed sum at all X,Y, not its fast
    recursive child contractions. It is a small-instance algebraic oracle.
    """
    from itertools import product as assignments
    M=graph.edge_count
    if M>max_edges:
        raise ValueError('Only tiny networks supported by this audit oracle')
    L=1 << (max(1,M)-1).bit_length()
    W=[[cauchy_kernel(L,x,y) for y in range(M)] for x in range(M)]
    Z=[Fraction(0)]
    rows=[v for v in graph.vertices if v.kind == 'cell']
    columns=[v for v in graph.vertices if v.kind == 'unit']
    for X in assignments((0,1),repeat=M):
        b=1
        for v in columns:
            b *= graph.local_entry(v,X)
        if not b:
            continue
        forms=[[sum((W[row][col][i]*X[col] if i<len(W[row][col]) else 0
                      for col in range(M)),Fraction(0)) for i in range(2*L)]
               for row in range(M)]
        for Y in assignments((0,1),repeat=M):
            a=b
            for v in rows:
                a*=graph.local_entry(v,Y)
            if not a:
                continue
            p=[Fraction(a)]
            for bit,form in zip(Y,forms):
                p=mul(p,form if bit else add([Fraction(1)],[-x for x in form]))
            Z=add(Z,p)
    return Z
