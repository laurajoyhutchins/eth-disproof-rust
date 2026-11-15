# External-source LaTeX translation benchmark

This corpus tests two existing frontends against mathematics published independently of this repository.
It does not estimate general mathematical understanding. The sources are publicly available
and may appear in model training data.

## Source groups and frozen input

- **Overlap discovery:** OpenStax *College Algebra 2e*, section 1.1, real-number identities O01–O07.
- **Author/publisher holdout:** NIST DLMF 1.2.3, 1.2.7 and 1.2.37: D01–D03.
- **Author/publisher holdout:** Nicholson *Linear Algebra with Applications*, section 2.1, N01–N02.

The source snapshot is commit `a0d26681cee5d7af46e5b2d8b172fd1c3bf5c428`.
`lock.json` records exact Git blob hashes. `validate.mjs` checks them, every source
equation, author-group assignment, case inventory and source URL. Runtime receipts also
record SHA-256 independently.

The Leanify artifact generator now restores its temporary Lake registration after
building. The source-oracle runner also accepts an already registered target
only when its exact source directory and module glob match expectations.

These are transcribed mathematical equations, **not raw publisher TeX bytes**.
Each case has a minimal LaTeX document wrapper. OpenStax's real-number domain is
made explicit as quantified variables. The manifest documents transcription changes.
No parser receives a different copy or a post-hoc simplified formula.

## Measurements

1. Existing receipt checks independently validate source, tool, generated modules and logs.
2. The cross-frontend comparator checks definitional equivalence only if both backends
   accept exactly one corresponding claim. Failed `rfl` remains unresolved.
3. The reference layer independently elaborates `oracle/ExternalGold.lean` *before*
   candidate modules are imported, then checks each parsed claim using a generated
   `by rfl` theorem against its source-specific typed reference proposition.
4. The report keeps parsing, backend overlap, reference-proposition shape matching,
   semantic-faithfulness review and proof completion separate.

**The source-oracle transcriptions are not independently human-audited.**
Matching them definitionally is useful machine-checkable evidence, but not
automatic proof of source-faithfulness. Proving arbitrary `P ↔ Q` is inadequate
because unrelated statements can both be true.

D02's generalized binomial coefficient over complex arguments has no independently
validated typed oracle here. We report `oracle_not_formalized`, never substitute
the natural-number binomial coefficient.

## Reproduction

The gated `.github/workflows/latex-unified-contract.yml` deep job produces the
original corpus reports and additionally `external-coverage.json`,
`external-summary.json`, and `external-oracle/summary.json` with archived Lean
probe sources and execution logs. For local source checks:

```bash
node benchmark/latex-to-lean/external/validate.mjs
node --test benchmark/latex-to-lean/external/*.test.mjs benchmark/latex-to-lean/external/oracle/*.test.mjs
```

Do not tune either parser on the reserved source groups and then continue reporting
them as held out. Any such tuning requires a fresh source-family holdout.

## Frozen CI evidence and regression gate

The pinned reference run [#43704510203](https://github.com/laurajoyhutchins/eth-disproof-rust/actions/runs/43704510203) passed the full toolchain and source-oracle integration at commit `5f37179b8af7aff78e66a43acb68545c8ceea365`.
The original 12 research and six synthetic holdout coverage counts remain unchanged.
The historical external corpus yielded seven accepted cases, five dual-frontend
translations, four kernel-checked **definitional** matches, and eleven out of
twelve accepted translations matching a separately written Lean reference
proposition **definitionally**. A subsequent examination of the fifth overlapping
case found a difference between unary negation and subtraction from zero.
The new comparator records a separate, kernel-checked `zero_sub` normalization
proof if it succeeds. It never relabels this as definitional equivalence or
retroactively changes the original `rfl` evidence.
All five external author/publisher holdout cases remain unsupported.

`baseline.json` records **observed engineering results**, not source-faithfulness
or theorem-truth labels. The deep CI job runs `assert-baseline.mjs` after every
stage. A changed count, a missing case, invented proof/source-review credit, or
source-identity mismatch fails the job. Updating a baseline should require
reviewing the full new evidence and preserving the previous observation.

Ordinary pushes and pull requests run the fast checkpoint tests only. A push
commit containing `[deep]` or an explicit workflow dispatch enables complete
integration. Checkpoint concurrency cannot cancel an active deep run, and both
jobs check out the exact commit head. Only the dedicated deep lane runs pinned
Lean, Mathlib, Leanify and the external corpus.

## Source cross-check and limited mathematical normalization

The artifact from [deep CI #43706737530](https://github.com/laurajoyhutchins/eth-disproof-rust/actions/runs/43706737530)
shows that OpenStax case O07 produced two distinct representations:
`a + (-a) = 0` and `a + (0 - a) = 0`. The original `by rfl` comparison
failed, and the independently defined real-valued reference was a definitional
match for Leanify but not the structural translation.

A *second*, separately archived Lean proof uses only the explicit `zero_sub`
rewrite and `iff_self`, never a general tactic such as `tauto` that might
prove unrelated true propositions equivalent. The output status is
`propositionally_equivalent`, with `definitional_equivalence = false`.
Changed quantifiers, hypotheses and types remain negative Lean fixtures.

`source-crosscheck.json` documents a model-assisted inspection of the cited
primary-source text. The algebra identities agree with the OpenStax real-number
properties table; DLMF 1.2.3, 1.2.7 and 1.2.37 contain the displayed binomial
and transpose identities; Nicholson §2.1 Theorem 2 contains the transpose
involution and additivity statements. The inspection does **not** constitute an
independent human audit. Domain specialization also matters: DLMF's matrix
identity is represented over `ℂ`, while Nicholson's two are represented over
`ℝ`. Neither choice establishes a universal-field correspondence. DLMF 1.2.7
still has no typed oracle. No source-faithfulness or proof-completion credit
is awarded merely from this cross-check.

The updated `baseline.json` preserves the preceding deep run as a historical
observation. The new acceptance distinguishes four definitional matches from
one expected normalized equivalence, rather than raising the definitional
match count to five.
