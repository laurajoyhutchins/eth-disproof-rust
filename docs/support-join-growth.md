# Exact support joins: first induced-bucket growth experiment

**Status:** finite-size experiment, November 9, 2026. **No ETH complexity
result.** This investigates one order-zero subproblem, not the paper's
n-derived parameter admission, high-order Taylor jets, or recursive Sudoku
contraction. It does not change the production evaluator.

## Execution path and earliest observable obstruction

The current exact CNF reference follows

    CNF -> bounded preprocessing -> disjoint sparsification leaves
        -> certified auxiliary measurement designs -> exact Taylor summation
        -> Hermite reconstruction -> restored exact count.

The new opt-in 'fused' Taylor path telescopes Boolean differences before
factor elimination; the older 'eliminate' path sums group-mask factors.
Both can form buckets spanning all live Boolean variables or groups. In
a clique of pairwise interactions, the **first elimination bucket** already
has domain 2**n. This is a structural bound on the explicit table approach,
not a lower bound against all possible exact representations. The current
factor-domain work preflight correctly refuses large domains.

This experiment compares *two join representations for the same exact,
order-zero, binary factor contraction under the same variable order*:

- **dense:** visit every candidate assignment in the induced bucket, then
  look up the existing sparse factor dictionaries.
- **support:** join only compatible nonzero factor entries, retaining the
  partial join as a sparse relation; sum out the same variable at each step.

Neither method uses approximations or a counting oracle during contraction.
An independent exhaustive truth table validates small cases. Both strategies
use Python Fraction arithmetic. No Python/FLINT or Python/Cython conversion
occurs; this **does not** measure conversion overhead in the actual solver.

## Controlled families

1. **Chain:** binary positive OR clauses on adjacent variables, count F_(n+2).
   Its maximum induced bucket contains two variables.
2. **Equality clique:** for every pair, one *pre-combined equality factor*
   with two nonzero rows. Count 2. This is deliberately NOT the uncombined
   two-CNF encoding, so any future implementation must explain and certify
   that initial compression separately.
3. **OR clique (adversary):** for every pair, a positive OR factor with
   three nonzero rows. Count n+1. The first eliminated bucket is n variables.
   Its remaining factor is exactly
   g(x_1,...,x_(n-1)) = 1 + product_i x_i.
   Thus an explicit nonzero table has **2**(n-1)** entries, although the
   same function has an O(n)-size arithmetic circuit. This demonstrates
   a limitation of explicit nonzero support, **not** a complexity lower bound
   for symbolic representations or #SAT.

## Measured baseline and change

Initial baseline (before the live-bucket accounting correction), CPython 3.13.5, Linux x86-64; each benchmark arm in a fresh process,
with tracemalloc enabled. Durations are one execution each, not confidence
intervals. "Dense assignments" and "support candidate pairs" count different
loops and should not be directly compared as identical operations.

| Family | n | Dense assignments | Support join candidate pairs | First output support | Dense time | Support time | Dense traced peak | Support traced peak |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| Chain | 12 | 46 | 95 | 2 | 0.0029 s | 0.0074 s | 18,672 B | 20,232 B |
| Equality clique | 8 | 510 | 124 | 2 | 0.0155 s | 0.0080 s | 77,648 B | 27,120 B |
| Equality clique | 10 | 2,046 | 196 | 2 | 0.0557 s | 0.0117 s | 141,784 B | 39,504 B |
| Equality clique | 12 | 8,190 | 284 | 2 | 0.2222 s | 0.0208 s | 152,808 B | 54,424 B |
| OR clique | 8 | 510 | 11,978 | 128 | 0.0283 s | 0.1765 s | 167,048 B | 105,576 B |
| OR clique | 10 | 2,046 | 178,929 | 512 | 0.1351 s | 2.3191 s | 329,164 B | 351,612 B |

The original equality-clique support contraction at n=12 recorded 132 peak
nonzero entries, performs 155 recorded
Fraction multiplications instead of 8,189, and reaches 2-bit coefficients.
The original OR clique at n=10 recorded 878 peak retained entries and only **4-bit
maximum coefficients** while spending 178,929 support pair checks. The
structural representation and join cost dominate before big-integer
coefficient growth appears in these **order-zero** inputs.

The initial peak RSS was about 98 to 99 MB across isolated processes, mostly
Python interpreter overhead; the traced Python-allocation difference is
the more informative metric at these sizes. **Review correction:** the original
entry peak calculation excluded attached factors while constructing a bucket.
The reviewed implementation counts those live inputs and temporary joins;
therefore the historical peak-entry and traced-memory values above are
baseline observations, not corrected exact-head measurements. Regenerate
`support-join.json` on the final head before comparing revised peak figures.
The benchmark also records
retained coefficient-bit totals, exact add/multiply counts, a labeled
schoolbook bit-geometry proxy, induced scope, isolated RSS, and elapsed
time for every row. The proxy is **not** a measurement of actual native
bit-operation cost. There are no recursive ETH/Sudoku calls or reusable
subproblems in this isolated iterative bucket experiment.

## Hypothesis and verdict

**Hypothesis:** replacing a full Cartesian assignment scan with exact
support joins avoids constructing and visiting exponentially many
intermediate assignments when the factor product has sparse support.

**Supported for pre-combined equality cliques.** Same exact result, same
variable order, drastically fewer arithmetic multiplications and less
traced Python memory in the measured range.

**Falsified as a general worst-case remedy.** The OR clique produces an
explicit table of 2**(n-1) nonzero entries after the first elimination,
despite its polynomial-size symbolic representation. Its support join can
also be slower than a dense scan. Merely choosing a sparse dictionary
does not solve the representation problem.

The next mathematical target is to define an exact factored/circuit
representation for induced functions, and prove that **both multiplication
and summing out variables** preserve a sufficiently small representation
under the *actual certified spectral coefficients* and admitted parameter
schedule. Absent that closure and bit-work recurrence, no worst-case
subexponential claim follows. The explicit output table in this experiment
is not proved to be necessary mathematical information.

## Reproduction and boundaries

    PYTHONPATH=src:. python -m pytest -q tests/eth/test_support_join_probe.py
    PYTHONPATH=src:. python -m benchmarks.eth.support_join_probe --output support-join.json

Tests first failed to import the nonexistent experiment (red); after adding
the implementation, the eight standalone test functions/parameterizations
passed locally. Additional integration cases exercise the *repository's*
certified 'eliminate' and merged 'fused' paths on small OR cliques.
The initial exact-head native/integration/extended verification passed on
`d64545f`; the review corrections require a fresh exact-head check.

All resource failures are explicit. The benchmark is deliberately kept
outside production dispatch, and makes no claim about the native backend,
higher-order jets, Lean conformance, or the published recurrence. None of
these family instances is asserted to meet the paper's full parameter
admission.