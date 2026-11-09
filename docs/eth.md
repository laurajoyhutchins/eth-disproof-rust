# Exact CNF, reductions, and interpolation

`CNFFormula` retains **declared variables**. For an empty conjunction on `m`
variables there are `2^m` assignments, whereas an empty clause gives zero.
Eliminating free variables therefore requires an explicit multiplicative
power-of-two factor. Tseitin-style helper variables require a *unique*
extension to be parsimonious, not just equisatisfiable.

The bounded CNF preprocessing and disjoint-leaf sparsification implementations
state their counting identities and enforce finite resource limits. Their
small-instance reference is deliberately exponential brute-force enumeration;
Ganak is an independent optional oracle, not the implementation of the
proposed general algorithm.

The construction modules build rational-polynomial measurements and perform
exact Taylor/Hermite recovery. The exact coefficient arithmetic and separated
measurement checks are tested independently from the candidate parameter
admission. Constructing a small exact instance does not prove that a full
worst-case recurrence achieves the paper's asymptotic bound.

See `eth/{cnf,preprocess,sparsification,polynomial,design,taylor,interpolation,
construction,parameters}.py` and their checkpoint tests. The goal is to make
incorrect count preservation, inaccurate interpolation or unbounded
intermediate work **falsifiable**, rather than hide it behind a single solver
entrypoint.

## Exact arithmetic representations

The `Polynomial` and `Jet` classes are canonical, independent `Fraction`
reference implementations. They never require FLINT. The optional FLINT
backend retains `fmpq_poly` objects throughout the Boolean-cube deformation
reference calculation and the incremental Hermite reconstruction. The
restricted Taylor evaluator retains native truncated jets in the same way.

Input coefficients cross into FLINT once per use, and full coefficients are
exported to validated `Fraction` values only at public result boundaries.
Export constructs fractions directly from integer numerators and denominators;
there is no string conversion or floating-point intermediary. Native
numerators and denominators are inspected at the same coefficient-bit
checkpoints as the reference implementation. The operation ledger charges
logical schoolbook work under **both** backends; its counts must not be
interpreted as elapsed native instructions or a complexity improvement.

Hermite uses a local, explicit truncation order on `fmpq_poly`, not FLINT's
process-global series cap. Differential tests check exact results, refusal
conditions, operation statistics, and the number of public exports. Ganak
remains a separate, independent #SAT correctness oracle.


## Exact coefficient-compression experiments

The auxiliary spectral polynomial for alternating values on consecutive
integers uses the integer-valued Newton basis

`f(W) = (-1)^a sum_{j=0}^{R-1} (-2)^j * binom(W-a,j)`.

Its Walsh/Fourier coefficient depends only on the cardinality of its
subset, and vanishes above degree `R-1`. The cardinality transform in
`eth/construction.py` replaces the original `4**Q` coefficient
enumeration. **It does not remove the dense `D = r**(2*Q)` auxiliary
rows**: that remains a separate practical obstacle.

For a general rational Hermite polynomial of degree less than the number
of Taylor conditions, `interpolate_origin_hermite` reads the value at zero
using a local CRT functional, without constructing the full polynomial.
The routine does not certify an independent tighter degree claim for
inconsistent overdetermined data. The constructed #SAT path uses it only
after validating its replacement system and certifying the Taylor
measurements. `count_from_constructed(..., readout='polynomial')`
retains the full original rational reference for differential comparison.

`eth/modular_readout.py` provides a separate exact finite-ring origin
functional. Rational inputs are accepted only if their denominators and
Hermite center differences are invertible modulo the selected moduli.
The bounded CRT readout requires a **proved bound on the true integer
origin** before reconstruction. This applies to count-valued deformations,
not automatically to the revised paper's parity-lift scalar whose value
is only congruent to the count modulo a power of two. The modular
prototype receives *precomputed rational Taylor jets*, so it does not
yet prevent upstream rational coefficient growth.

The paper's parity-lift linear coefficients have the closed form
`e_0(Y)=1-Y` and `e_j(Y)=(-1)^j binom(2*j,j)/2 * (1-2Y)` for `j>=1`.
They have linear bit height in `ell`; the helper and independent
polynomial-identity tests are in `eth/parity_lift.py`. The general
parity-lift counting path itself is not yet implemented.

Reproduce isolated algebraic experiments and a tiny end-to-end
constructed-count comparison (not a worst-case scaling claim):

```bash
PYTHONPATH=src:. python -m benchmarks.eth.algebraic_readout --repeats 3 --output readout.json
```

## Implicit auxiliary operator and measured evidence

`construct_implicit_auxiliary(r,Q,R)` is the default for
`construct_bounded_designs(...)`. The original `construct_auxiliary`
remains a separately executable dense correctness oracle, and
`construct_bounded_designs(..., representation='dense')` selects it
explicitly. Both use identical spectral interpolation and measurements.

The new `ImplicitAuxiliaryDesign` represents `f(W)` by an exact
`(Q+1) x (Q+1)` kernel indexed by the number of diagonal coordinates
and unswapped off-diagonal coordinates. Individual `P[u,w](T)`
coefficients are calculated when needed. Exceptional product
eigenvectors are stored as selector tuples, never vectors of length
`D=r**(2*Q)`. Transfer now iterates only over occupied incidence
labels, rather than constructing all `D` labels or all `D**2` row
entries. The implementation counts exceptional selectors
combinatorially before allocation and refuses if the bound is exceeded.
It also has an explicit maximum for `Q` in this research backend.

**Observed on GitHub-hosted Python 3.13, 2026-11-09, workflow run
`42669627090`:**

| r | Q | R | dense seconds | implicit seconds | dense peak traced bytes | implicit peak traced bytes |
|---|---|---|---|---|---|---|
| 2 | 2 | 2 | 0.00872 | 0.000603 | 27,312 | 4,222 |
| 2 | 3 | 2 | 0.04497 | 0.000847 | 168,352 | 3,936 |

The Q=12,R=12 implicit constructor completed in 0.00656 seconds with
20,312 peak traced Python allocation bytes. Its virtual `D` was
16,777,216, corresponding to 281,474,976,710,656 potential dense
matrix entries, but only 169 kernel coefficients and one exceptional
selector were retained. No dense Q=12 timing was attempted.

**End-to-end witness on the same GitHub-hosted setup, workflow run
`42669890039`:** for a *three-variable* CNF and implicit
`r=2,R=Q`, `Q=5` and `Q=12` each produced exact count 4,
matching independent exhaustive enumeration. Counting took about
0.51 seconds and 1.29 seconds respectively (under Python
`tracemalloc`; timings include its overhead). The completed operator
preparation took about 0.002 and 0.013 seconds. This establishes that
a huge *virtual* dimension does not require allocating the dense
matrix; it is not evidence for improved worst-case scaling in the
number of Boolean variables. Only the `R=Q` spectral regime was
exercised at the huge dimension, where the exceptional-direction count
is one. General regimes can retain exponentially many exceptional
directions and are explicitly resource-limited.

Reproduce these measurements with
`PYTHONPATH=src:. python -m benchmarks.eth.implicit_auxiliary_probe`;
and exercise the larger count as an optional integration test:
`python -m pytest -q tests/integration/test_implicit_large_dimension.py`.
The one-off GitHub benchmark workflow was removed after the measurements
to avoid a permanent extra CI job.
