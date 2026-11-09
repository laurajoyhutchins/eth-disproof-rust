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

## Bounded end-to-end executable path

`count_cnf_reference(formula, config=ReferencePipelineConfig(...))` now
connects the previously isolated exact operations:

1. If the input exceeds the sparsifier's clause-width `k`, first apply
   count-preserving width/occurrence reduction while recording the
   removed-free-variable multiplier.
2. Enumerate the **disjoint** sparsification leaves, stopping with an explicit
   capacity refusal if the complete tree exceeds its configured budget.
3. For **every** leaf, re-project free variables and apply parsimonious
   width/occurrence reduction, since branching can add occurrences.
4. With at least two active variables, construct and certify auxiliary
   measurement designs, evaluate separated Taylor coefficients, and
   reconstruct the exact count by Hermite interpolation. Never substitute
   brute-force or Ganak on a failure.
5. For zero or one active variables, use the explicitly reported 1- or
   2-assignment base case. Restore all leaf multipliers, sum only after
   successful leaf evaluation, then restore the initial multiplier.

The return type contains a complete count and per-leaf evidence: branch path,
preprocessed dimensions, restored contribution, execution method, center
count, Taylor pair count, measurement tuples and coefficient-size observations.
No partial count is returned if any leaf refuses.

To reproduce with a DIMACS file:

```bash
python -m scripts.eth_reference
python -m scripts.eth_reference --dimacs small.cnf --output evidence.json
```

A successful run writes `"status": "completed"`; capacity refusal emits
`"status": "capacity_refusal"`, `count: null` and exits 2. The default
threshold `M=2` is **experimental**, not the theorem's sparsification
parameter. These are finite certified *reference* constructions, with
potentially exponential work, strict resource limits, and no general
non-refusal or subexponential running-time claim. The literal theorem
admission remains a separate, fail-closed entrypoint.

The optional `summation='eliminate'` path uses the independently
certified group-factor elimination backend described above. The default
`'tuples'` retains the original explicit measurement-reference evaluator.
The CLI accepts `--summation eliminate`, and every result records the
selected backend, summation and construction parameters.
