# Symmetry quotient versus explicit intermediate tables

Research-only follow-up to #51. This is a **constructive counterexample to
treating exponential explicit-table size as necessary computational work**,
not a general worst-case algorithm or an ETH result.

For the positive-OR clique on n Boolean variables, every pair (xi OR xj)
must hold. The satisfying assignments are exactly those with at most one
zero, hence the exact count is n+1. The first bucket of explicit elimination
has 2^(n-1) nonzero entries even though its function is
1 + product(x1,...,x_(n-1)), with O(n) expression size.

A different representation tracks the **number of zeros capped at two**.
For k processed variables, let a be the number of assignments with no zeros,
and b the number with exactly one zero. Starting at (1,0), appending a
variable gives (a,b) -> (a,a+b). The state has two exact integer coefficients
and uses one addition per variable, plus one final addition. The coefficients
are a=1, b=k, so their maximum bit length is O(log(n+1)). The implementation
retains all states as a trace, using O(n log n) bits for that trace; a streaming
implementation would retain O(log n) bits. This bound counts arithmetic in
this **special quotient**, not recognition of the clique from arbitrary CNF.

Tests compare this independent recurrence against exhaustive truth-table
counting, the existing dense elimination experiment, and evaluation of the
first induced factor. No production path or native kernel changes.

## What is and is not established

- Established algebraically: an explicit exponential intermediate support
  can coexist with a polynomial-time exact representation on this family.
- Established by the tests: agreement for the finite tested instances.
- Not established: a polynomial-size quotient for arbitrary CNF, arbitrary
  certified spectral coefficients, high-order jets, or the paper's recurrence.
- Not measured: circuit canonicalization, general symmetry discovery,
  Python/FLINT conversion overhead, or actual machine bit operations.

The next falsification target is a family that breaks permutation symmetry
while preserving a large induced bucket. An honest generalization must
provide a closed representation under both product and sum-out, plus an
end-to-end bit-complexity recurrence that includes construction costs.
