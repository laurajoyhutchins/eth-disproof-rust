# Evaluating LaTeX → Lean formalization for ETH research

**Scope:** proposed reproducible benchmark and acceptance policy, not a claim that named tools have already passed. The default output is a **Lean theorem and independent checker receipt**, not Python output or an English approximation.

## Why this belongs here

The spectral and two-adic investigations contain fragile qualifications: valuation cutoffs, integer/rational denominators, sum/product interchanges, group routing, source-dependent symbol identities and asymptotic quantifiers. A plausible Lean translation is insufficient when a missing hypothesis could turn a false claim into a compileable theorem about a different proposition.

Candidate systems from the recent research include **Leanify**, **PaperFormalizer** and **AutoformBot**. Their exact executable versions, upstream revisions, model settings and code availability must be discovered and pinned **before** a benchmark receipt is valid; this document does not invent those pins or assume equivalent outputs.

## Versioned corpus (retain original LaTeX, gold statement and proof obligations)

| Suite | Instances | What faithful translation preserves |
| --- | --- | --- |
| Elementary | quantified definitions, integral/rational identities, sums, recurrence domains | Quantifier order, type coercions, scopes, nonzero denominators |
| Research spectral | commuting involutions, joint eigenspace sign, central interpolation identity, selector rowspace | Exact group action, equality vs congruence, rank vs row norm, integer measurement assumptions |
| Algorithmic | recursive mode expansion, \(p\)-adic truncation, packing inequalities, complexity recurrences | Bounded sums, termination/decreasing measure, source parameters and bit complexity model |
| Adversarial | false equalities, missing invertibility, invalid group factorization, changed quantifiers, overbroad asymptotics | **Reject** false or under-specified inputs; no auto-repair that silently changes the problem |

The benchmark must preserve a challenge ID, gold human-checked proposition, known theorem/counterexample, source blob identity and a list of semantic invariants. Partition by *mathematical family* before evaluation so that template-memorizing a fixture does not count as generalization. Keep a held-out collection with fresh symbol names and equivalent but structurally different formulations.

## Faithfulness gate

A proposed Lean statement may pass parsing and typechecking while proving the wrong theorem. Compare the following independently:

1. Free variables, binders and quantifier order; type and domain of each symbol.
2. Missing or strengthened hypotheses, including \(p>0\), quotient-ring characteristic, invertibility, source-valid packing and finite support.
3. Equality vs congruence; modular precision; existential vs constructive output; uniform vs instance-specific asymptotic constants.
4. Definitional identities, aliases, tuple indexing, source-dependent routing and number of groups.
5. Imported axioms, `sorry`, `admit`, opaque constants and `noncomputable` use; audit with `#print axioms` and source closure analysis.
6. Intentional falsity: if the original counterexample is false in a small finite model, translation must not pass by inserting new hypotheses, weakening the conclusion or changing the universe.

Use a kernel-checked, independent statement-equivalence proof where practicable; otherwise report **faithfulness unverified**, even if the candidate compiles. Never score compilation as semantic equivalence.

## Reproducibility and cost

Capture per candidate: LaTeX source ID/hash, gold Lean statement hash, tool repository and immutable revision, model provider/model version, prompting and token budget, decoding seed/temperature, Lean/Mathlib versions, generated code hashes, kernel result, axiom audit, complete diagnostics, time, input/output token counts and estimated/actual provider cost. Report refusal separately from invalid or faithful-but-unproved outputs. No background external solver or unpinned internet retrieval during the acceptance test.

Primary metrics: **faithful-proposition rate**, **kernel-checked proof rate conditional on faithfulness**, **false-claim rejection rate**, **unauthorized-assumption rate**, median and tail time/cost, and regression robustness on held-out transformations. A strong false-claim test should deliberately negate the expected conclusion or remove an invertibility hypothesis and check that the system declines or produces a counterexample, not a bogus theorem.

## Initial ETH target suite

- Pair swaps: prove \(W\) eigenvalue \(j\) and \(V\) sign \((-1)^j\) on joint eigenspaces; falsify by making swaps noncommuting.
- Group coupling: reject a rank-one decomposition for \(\bigl[\begin{smallmatrix}1&1/2\\1/2&3/8\end{smallmatrix}\bigr]\) (determinant \(1/8\)).
- Weighted cutoff: prove omission of modes with weight \(\ge p\) **only** in the algebra satisfying \(2^p=0\).
- Source packet routing: preserve two active groups, crossing ports, label/copy provenance and bounded child size; mutate one route to force a failed proof.
- Hermite recovery: distinguish units from nonunits modulo \(2^p\) and retain necessary precision.
- Resource theorem: require a uniform bit-work/space bound over all inputs, not a fast result on sample parameter values.

A successful translated lemma should be integrated into the *actual* source-facing Lean theorem hierarchy in [two-adic recursion](two-adic-recursion.md), not kept as an unrelated toy lemma. For source-refinement claims, require separate independent original-Lean/Rust execution checks described in [compiler acceptance](lean-rust-acceptance.md).
