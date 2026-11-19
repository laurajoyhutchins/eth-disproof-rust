# Staged affine boundary composition

This research module is a **restricted exact planner** for two affine interfaces
with disjoint hidden variables. A merge retains specified external ports and
eliminates the remaining union of ports by certified Gaussian elimination.

For child interfaces \(F(x,z)\) and \(G(y,z)\), the merge computes

\[
H(z)=\sum_{x,y} F(x,z)G(y,z).
\]

The implementation converts the *residual parity equations* of both children
back into a single affine region, eliminates the unretained ports, verifies the
row-operation transcript using the independent dense checker, and adds both
child free-dimension exponents to the new elimination's exponent. It does not
enumerate assignments or construct a truth table.

A hidden variable must not be shared by two child interiors, nor be exposed
as a boundary variable in the other child. A variable appearing in both child
boundaries is shared **once**, not independently summed twice. An unretained
port is summed out exactly once at the parent.

## Instrumentation

Each stage records:

- \(D_k\): number of ports + residual rows + nonzero residual incidences.
  This measures the explicit representation; it is **not** minimum circuit size.
- \(B_k\): free-variable exponent + 1, the bit length of a nonzero fiber
  multiplicity \(2^{f_k}\). For an identically inconsistent interface,
  the observed value is zero and the reported \(B_k\) is only a conservative
  exponent-based upper bound.
- Ports, residual rows, incidence count, elimination XORs, and replay steps.

The tests compare two distinct parenthesizations of a three-region chain to
a Boolean enumeration of the **original** three regions. They also cover
unconstrained multiplicities, contradictions and invalid hidden/port seams.

This is a concrete exactness experiment. It does **not** establish a uniform
polynomial upper bound for \(D_k\) or \(B_k\) over general SAT factors,
nor prove correspondence of the Rust code to Lean. In the affine class,
the representation is polynomial in explicit matrix size; extending this
to nonlinear and truncated operations is the actual open problem.

Related notebook studies: affine elimination certificates, linear boundary
interfaces, equality-component contraction, factored full-rank operators.

## Reproducible contraction-order experiments

See [ORDER-STUDY.md](ORDER-STUDY.md) for generated equality-chain and circulant-parity networks, three explicit contraction orders, per-stage D/B receipts, and bounded independent exact-count oracles.
