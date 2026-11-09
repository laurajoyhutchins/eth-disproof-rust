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
