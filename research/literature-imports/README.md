# Import related mathematics into the ETH Lean proof

The unit of work is a **missing Lean proof obligation**, not a paper or a LaTeX document.
For an obligation, find an existing formal theorem first, specialize it, and keep every
source-specific assumption visible. Only formalize from a paper when existing libraries
cannot supply the required result.

## First import: fixed-mode independent-group factorization

Target: [`mode_product_contraction`](../two-adic-recursion.md#lean-proof-obligations).

Literature context: [Markov and Shi, *Simulating Quantum Computation by Contracting
Tensor Networks* (2008)](https://doi.org/10.1137/050644756). The work provides the
tensor-network contraction framework. **We do not attribute the Mathlib lemma to
that paper.** Its exact source is the pinned Mathlib declaration
[`Finset.prod_univ_sum`](https://github.com/leanprover-community/mathlib4/blob/d13f23b723b8a846827a245b89c10fc7d3f11612/Mathlib/Algebra/BigOperators/Ring/Finset.lean).

The [Lean bridge](../../instrumentation/lean-env/LiteratureImports/ModeProductContraction.lean)
shows that the sum of the routed contributions equals the product of child sums,
for **any finite number of groups**, using only a commutative semiring and a
finite global assignment set. The mathematical work is delegated to Mathlib.

The source-specific hypotheses are *not* discharged:

- `route`: a genuine bijection between global and tuple-of-child assignments;
- `hvalid`: exactly the allowed assignments survive the routing;
- `hfactor`: each original contribution equals the product of child contributions.

That is the intended separation: the reusable algebra is imported once; the ETH
packet-specific source proof remains a visible, testable obligation.

## A reusable import record

[`mode-product-contraction.json`](mode-product-contraction.json) records the
target, reference DOI, how the paper is being used, exact formal-theorem source
and revision, Lean output, assumptions and unresolved work. It distinguishes
**paper context** from **formal theorem source**. We should not manufacture a
paper-to-Lean theorem citation when the useful theorem came from Mathlib.

To reproduce the checked bridge:

```sh
node research/literature-imports/verify.mjs
cd instrumentation/lean-env
lake env lean LiteratureImports/ModeProductContraction.lean
```

The `literature-import.yml` CI job uses Lean 4.34.1 and the repository's pinned
Mathlib revision. It checks the bridge and reports axioms without proving the
original OAI routing assumptions or its complexity theorem.

## Next import workflow

1. Start from a named, genuinely open Lean obligation.
2. Retrieve exact candidate statements and hypotheses from the relevant
   literature, including the publisher location and equation/theorem number.
3. Search pinned Mathlib and already verified local Lean theorems first.
4. Typecheck a *bridge* between the source interface and the existing formal
   result. An exact match or proved specialization is preferable to new code.
5. Report the remaining hypotheses. No source-faithfulness credit or theorem
   completion is awarded until the original source-side premises are checked.
6. Add the bridge as an importable Lean module and exercise it in the actual
   proof that needed it.

The first step demonstrates reuse and explicit obligations, **not yet automatic
paper discovery, extraction of new published theorems, or complete original-source
ETH proof integration**. Those are separate capabilities to build around this
interface rather than around a parser-comparison benchmark.
