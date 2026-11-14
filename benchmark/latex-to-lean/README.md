# LaTeX-to-Lean upstream acceptance experiment

This **isolated branch** compares programs on the exact, original mathematical LaTeX of 32 fixed fixtures; eight each in elementary, research, algorithmic, and adversarial groups. The input is not altered to fit one vendor's grammar.

### How to reproduce

The workflow at `.github/workflows/latex-to-lean-pilot.yml` checks out fully pinned vendor revisions, builds Leanify with its native Lean 4.34.0 and pinned Mathlib, runs `check --claims --defined` on all 32 original LaTeX files, and records raw stdout/stderr/exit/time for every case. The `summarize.mjs` importer rejects missing case receipts, inconsistent claim counts and unexpected vendor commits. It classifies compiled statements, unsupported prose, diagnostic rejections, and tool failures separately.

Independent `MathlibExactPilot.lean` and `MathlibAdversarial.lean` test known mathematical facts, counterexamples, and prohibited semantic transformations. Those oracles are NEVER provided to the candidate formalizer. Kernel proofs here are not vendor proof-completion results.

PaperFormalizer and AutoformBot currently run **installation/CLI smoke tests only**, not agent-led formalization. They are not scored as zero and no absent results are invented. Agent model tokens and subscription usage require a distinct authorized experiment.

### Initial native-parser baseline

[Full 32-case upstream run](https://github.com/laurajoyhutchins/eth-disproof-rust/actions/runs/43630277740) on the pinned Leanify revision:

| Family | Statement compiled | Diagnosed rejection | Unread/unsupported | Crash |
|---|---:|---:|---:|---:|
| Elementary | 4 | 2 | 2 | 0 |
| Research | 0 | 0 | 8 | 0 |
| Algorithmic | 0 | 1 | 7 | 0 |
| Adversarial | 3 | 1 | 4 | 0 |

Total: 7 compiled, 4 meaningful diagnostics, 21 unread. Later runs add explicit definedness observations.

### Correct measurement boundaries

- A process exit code of zero **does not mean** a theorem was compiled, proven, or correct.
- Source-preserving parser coverage, semantically faithful elaboration, proof generation, refutation, and issue diagnosis are different metrics.
- An unsupported/refused statement may be safe, but does not earn correctness or refutation credit.
- The 32 original cases are not a statistically adequate estimate for arbitrary papers and do not prove performance across all mathematical notation.
- AI-driven tools require separately tracked model credentials, model versions, independent runs, token usage and failure rates.

Do not merge experimental jobs into `main` without reconciling repository scope and CI costs.
