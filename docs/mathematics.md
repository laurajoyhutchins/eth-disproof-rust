# Exact contraction model

The engine represents a constraint instance as a bipartite tensor network with
binary edges and exact local evaluation oracles. Packet geometry groups edges
for a recursive Cauchy-style deformation. Mode coefficients are combined by
weighted polynomial/factor elimination, and exact recovery reconstructs the
desired contraction from deformation evaluations.

The implementation separates ring arithmetic (`core/`), recursion and packet
construction (`contraction/`), elimination of modes (`elimination/`), and
coefficient recovery (`recovery/`). Different schedules are not interchangeable
complexity theorems. Exactness of individual arithmetic kernels and equivalence
of alternative local evaluation paths do not establish a bound on recursive work.

Resource limits produce explicit `CapacityError` outcomes. An explicit
exhaustive reference operation may be useful for differential testing, but its
exponential enumeration must not be counted as a non-exponential solver path.


## Exact coefficients in the source

For a packet of width \(L=2^a\), the Cauchy sample points are
\(T=t+\alpha z\), where \(\alpha=2L\) and
\(S=\{-L,\ldots,L-1\}\). In the coefficient ring
\(\mathbb Z/2^p\mathbb Z[U]/(f(U))\), powers of two are generally **not
invertible**. For each \(q\ne t\), `contraction/packets.py` forms the unit
factor

\[
u_q = \frac{t-q+\alpha z}{2^{v_2(t-q)}}.
\]

The common denominator is the odd part of
\(D=\prod_{q\in S,\ q\ne0}(-q)\). Packet weights and cross-mode
coefficients use the **same normalized factors**, with the remaining
valuation and multiplicity factors kept explicit. The code does not implement
field division by an even residue or assume that a composite modulus is a
finite field.

For tapered Hermite recovery, each nonzero center contributes a unit Taylor
series

\[
E_t(t+\alpha z)
= \prod_{s\ne t}
  \left(1+\frac{\alpha z}{t-s}\right)^{q_s},
\qquad E_t(t)=1.
\]

The reciprocal series is calculated by the exact recurrence
\(E^{-1}_0=1\) and
\(E^{-1}_k=-\sum_{j=1}^k E_j E^{-1}_{k-j}\). Contributions from every
center are accumulated as **exact rationals first**, then converted to
2-adic coordinates at the target precision. Early modular reduction would
lose factors needed for cancellation. `recovery/streaming.py` owns this
calculation; both eager recovery and streaming call it.

The external oracle `reference/paper_algebra.py` independently computes
Cauchy coefficients over \(\mathbb Q\) on small inputs. This establishes
local exact identities, not an asymptotic upper bound.

## Reading the implementation

The recursive executor's control flow is the mathematical outline:

1. **Terminal contraction.** Validate the network and ring precision. A
   bounded leaf computes the exact contraction, or refuses its configured
   capacity. No exhaustive computation is selected as a silent fallback.
2. **Active packing.** Compute the schedule, pack wires, and check the
   paper-specific conservation and shrinkage conditions when that schedule is
   selected. `paper_schedule_parameters` is pure, so symbolic-size schedules
   can be verified without constructing a huge extension ring.
3. **Deformation centers.** Evaluate the required Cauchy centers at explicit
   precision. `PacketGeometry` contains shared immutable topology; each
   `PacketModeTerms` contains only the changing mode assignment and its exact
   coefficients. Both Python and native evaluators consume those same terms.
4. **Mode elimination.** Construct the factors and eliminate multiplicities
   subject to one validated `ModeLimits` object. Refusal cannot silently
   switch to a different mathematical algorithm.
5. **Exact recovery.** Either collect Taylor jets or interpolate exact points,
   then recover the contraction. Streaming recovery changes retention, not
   the coefficient identity being reconstructed.

Runtime `Counters` measure the execution; they do not define the computation.
The shared mathematical types own their invariants, while optional Python,
Cython, and FLINT implementations remain distinguishable at the evaluation
boundary. The cost ledger is observational rather than an asymptotic proof.

See [research-agenda.md](research-agenda.md) for the proof obligations and
[validation.md](claims.md) for the tests and experimental cost accounting.
