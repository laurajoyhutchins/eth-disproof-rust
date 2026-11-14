# LaTeX-to-Lean research mathematics extension (2026-11-14)

This is an **executable experiment**, not an accuracy claim about arbitrary research papers.

## Reproducibility

- Original immutable research cases: `benchmark/latex-to-lean/research/cases/` (12 LaTeX files).
- Reference mathematics: `benchmark/latex-to-lean/research/oracle/ResearchGold.lean`.
- Explicit fixture manifest: `benchmark/latex-to-lean/research/manifest.json`.
- Fail-closed evidence parser: `benchmark/latex-to-lean/research/summarize.mjs`; tests: `summarize.test.mjs`.
- CI: `.github/workflows/latex-to-lean-research.yml`.
- Pinned Leanify: `134da59ae02e9fffc011a5ea89acf4320268d220` (Lean 4.34.0; its pinned Mathlib commit).
- **Verified successful run:** https://github.com/laurajoyhutchins/eth-disproof-rust/actions/runs/43638678862
- Raw evidence artifact: https://github.com/laurajoyhutchins/eth-disproof-rust/actions/runs/43638678862/artifacts/14130973617

## Measured results (statement parsing only)

| Subsystem | Compiled | Diagnosed rejection | Unread | Tool error |
| --- | ---: | ---: | ---: | ---: |
| Group actions (RG01–RG04) | 2 | 2 | 0 | 0 |
| Spectral algebra (RS01–RS04) | 3 | 1 | 0 | 0 |
| Combinatorial counting (RC01–RC04) | 3 | 0 | 1 | 0 |
| **Total** | **8/12** | **3** | **1** | **0** |

Details:
- RG01 and RG03 compile. The full-vector swap definitions in RG02/RG04 are rejected as type mismatches.
- RS02–RS04 compile, including even/odd spectral projections and their identities. The matrix-environment statement RS01 is not recognized.
- RC01–RC03 compile, including the general binomial sum identity. Free-form natural-language RC04 is not read.
- The stderr/stdout, source SHA-256s, exit statuses, process CPU/memory measurements, and machine-readable summary are preserved in the artifact.
- LaTeX check time after the one-time checker build was about 1.06–1.11 seconds per case in the first full run. This includes per-process startup and is **not** an end-to-end proof/LLM time.

## Independent kernel oracles

Eleven Lean proofs cover pair-swap involution, commuting disjoint swaps, simultaneous dot-product invariance, the *actual* 2×2 swap matrix square, even/odd spectral reconstruction and idempotence, fixed binomial values, the general binomial sum theorem, and binary-word counting.

All 11 check under the pinned Mathlib toolchain. The axiom audit reports only `propext`, `Classical.choice`, `Quot.sound` (or none); no `sorryAx`. These are reference theorems, **not proofs produced by the LaTeX compiler**.

## Strict interpretation

Passing `leanify check` does **not** mean a result is proved or the generated proposition has been independently shown equivalent to the paper's meaning. No research cases have yet passed a generated-Lean semantics-equivalence audit or `leanify audit`. The older elementary/adversarial pilot's equivalence proofs remain separate.

PaperFormalizer and AutoformBot remain at verified install/CLI smoke level only, with no agent-run accuracy, token, or cost measurements. No three-way ranking is justified.

## Recommended next acceptance gate

On supported research cases RG01 and RS02, run `leanify init`, build the generated `Article.lean`, run `leanify audit`, and prove each generated claim equivalent to a source-authored gold Lean statement. Only then give formalization-faithfulness credit. Repeat across independently sourced published papers, not only this synthetic development set.
