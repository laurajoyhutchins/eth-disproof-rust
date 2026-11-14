# Structural LaTeX backend: verified research extension

Status: **bounded structural fragment, tested on actual sources and hold-outs, no theorem-solving claim**.

## Reproduction
- Rust crate: `benchmark/latex-to-lean/structural/`.
- End-to-end workflow: `.github/workflows/latex-structural-backend.yml`.
- Rust 1.99.1, standard library only, frozen `Cargo.lock`.
- Lean 4.34.0 and exact Mathlib revision `5ed2965256430c3649e86755f9576b54eca72435`.
- Leanify source revision `134da59ae02e9fffc011a5ea89acf4320268d220` is used **only as a pinned Lean/Mathlib environment** for structural-backend verification.
- Verification of the four originals and held-outs: https://github.com/laurajoyhutchins/eth-disproof-rust/actions/runs/43644843335
- Narrow-import equivalence and performance measurement: https://github.com/laurajoyhutchins/eth-disproof-rust/actions/runs/43645484295

## Test coverage and semantics
- The untouched research-math benchmark first establishes **8/12** accepted by pinned upstream Leanify. This figure has not been rewritten.
- The independent structural frontend adds support for all **four** original cases Leanify rejected: product-valued maps `RG02`, commuting maps `RG04`, matrix involution `RS01`, and finite binary word counting `RC04`.
- The combined two-backend corpus covers **12/12**, but does **not** mean Leanify alone supports 12/12, nor that a combined router has been implemented.
- **16/16** Rust parser/typechecker tests passed, including dimension sweeps 2–16, word bases 2–8 and lengths 1–10.
- Six separate held-out articles were compiled, including vector dimension 5, a 3x3 matrix, different domain/codomain arities, and ternary cardinality.
- Three invalid articles were explicitly refused: unbound symbol, matrix dimension mismatch, and vector-map codomain mismatch.
- Independently written Lean proof suite checked 15 statements: four original meaning correspondences, four original mathematical proofs, further hold-out correspondences and proofs, and explicit refutations of two false claims.
- The Lean kernel reported only `propext`, `Classical.choice`, and `Quot.sound` for those theorems, with **no `sorryAx`**.

## Performance (single run per configuration, not confidence intervals)

| Phase | Broad `import Mathlib` | Targeted imports |
|---|---:|---:|
| Lean verification wall clock | 5.88 s | 2.01 s |
| Lean verification peak RSS | 7,329,608 KiB | 2,058,536 KiB |
| Checked proof receipts | 15 | 15 |

Relative improvement is approximately 66% lower wall time and 72% lower RSS. The phase imports Mathlib modules and runs all fifteen proof checks; environment bootstrap is excluded.

The Rust native six-article parse batch had peak RSS 2,408 KiB with an elapsed time printed at hundredths precision as 0:00.00; the cold Rust release binary build took 1.32 s and peaked at 270,160 KiB RSS. Sub-centisecond timing is not sufficiently precise to claim a numeric throughput advantage.

## Limitations and next boundaries
- Separate Leanify and Rust engines have separate coverage receipts; no source-faithful decision procedure automatically chooses between them yet.
- The new source language is deliberately restricted to finite real vectors, rectangular real matrices, and finite-word cardinality with explicit domains. It is not an arbitrary LaTeX formalizer.
- The Rust compiler is not itself verified in Lean. The independent Lean reference correspondences establish semantic preservation on the exercised articles only.
- A proof success is not attributed to the generated output: the proof oracles are independent.
- PaperFormalizer and AutoformBot still do not have authenticated mathematical test runs, so no valid comparative ranking exists.

Build further capabilities as type-directed extensions, then test on independent held-outs, metamorphic perturbations, and false statements. Never translate unsupported structures into vacuous or weakened claims.
