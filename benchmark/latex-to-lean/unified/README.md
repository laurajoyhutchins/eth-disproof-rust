# One source contract for LaTeX → Lean (experimental)

This is a **single user-facing workflow**, not yet one source-language semantics engine. It invokes two deterministic, pinned frontends on **identical original bytes**. A successful parse is **not a proof**.

## Reproducible command

From the ETH repository root, build the std-only structural crate and the exact Leanify checkout:

```bash
cd benchmark/latex-to-lean/structural
cargo +1.99.1 build --release --offline --locked
cd ../../../..
git clone https://github.com/Corrram/leanify.git vendor/leanify
git -C vendor/leanify checkout --detach 134da59ae02e9fffc011a5ea89acf4320268d220
cd vendor/leanify && lake exe cache get && lake build leanify && cd ../..
node benchmark/latex-to-lean/unified/run.mjs \
  --source benchmark/latex-to-lean/research/cases/RG03.tex \
  --out /tmp/latex-unified-rg03 \
  --structural-bin "$PWD/benchmark/latex-to-lean/structural/target/release/structural-latex" \
  --leanify-dir "$PWD/vendor/leanify"
```

The driver probes both parsers, without an ID-based router. It checks pinned Leanify revision, source SHA-256 before and after each backend, subprocess results, source and generated-output hashes, and generated native Lean modules. Generated Leanify `Article.lean` and `Compiled.lean` are built using the native Lake project and copied to the receipt directory; the temporary source module is deleted. The structural backend also emits its own complete Lean module.

## Selection and verification states

| State | Behavior |
|---|---|
| Only one parser accepts | Record its generated source as `translation_requires_kernel_review` |
| Both accept | Preserve both and return `conflict_requires_equivalence`; never arbitrarily select |
| Neither accepts | Record `unsupported` with original diagnostics |
| Any tool crashes, times out or emits inconsistent results | Return `incomplete`, not a fallback success |
| Proof or semantic-equivalence verification | **Never claimed by this driver**. Requires separate Lean kernel receipts |

Exit codes: `0` for normal observations (including genuinely unsupported input), `2` for infrastructure/tool failure, `3` for a conflicting pair of unverified translations, `1` for bad arguments, untrusted input or invalid checkout. A conflict is intentional, not a tool crash.

Inspect `receipt.json`, its source identity, `generated` entries and the four backend stdout/stderr files. When Leanify accepted, also inspect its `init` and `build` logs. `verify.mjs` independently checks these receipts, the source bytes, generated modules and original command logs across any directory of `.tex` files:

```bash
node benchmark/latex-to-lean/unified/verify.mjs SOURCE_DIR RECEIPTS_DIR coverage.json --require-coverage
```

## Baseline and limits

The pinned upstream Leanify parser covers **8/12** original research cases. The distinct Rust structural backend covers the remaining four, with 16 Rust typechecker tests, held-out dimension/alphabet sweeps and fifteen independent kernel proof/refutation checks. A previously verified focused-Mathlib import reduced kernel check memory and wall time relative to `import Mathlib`. **The union of parser capabilities is not one verified unified semantic compiler.**

The initial integrated run executes both frontends on all twelve original research cases and six independently held-out synthetic cases. A source-to-claim equivalence judgment is not inferred from parser output, matching words, proof success on a different statement, or a zero exit code. Previously verified Mathlib equivalences and Leanify's self-audit remain separate evidence.

## Next architectural step

**Do not add another mathematical parser.** Expose a common typed IR from *both* existing parsers. The minimum term vocabulary must carry typed variables, binders and quantifier order; proposition connectives; explicit real/natural casts; applications; products and finite vectors; matrices; finite-set cardinalities; and reference identities for definitions. Preserve source spans and all hypotheses. Do not construct a fake typed term from Leanify's printed claims: extract from the actual Lean elaborator/compiler IR. A certified equivalence check of two IR terms is required before selecting when both backends parse.

For generalization, freeze a genuinely independent mathematical-paper corpus, stratify by notation and claim type, hold out entire authors/documents, and measure semantic accuracy separately from parsing, proof completion, diagnostics, model cost and performance. The existing twelve research cases and six synthetic heldouts are regression coverage, **not** evidence of general mathematical understanding.

## CI

Run the Node contract tests and the existing research scorer tests on ordinary pushes; run the pinned, more expensive two-toolchain acceptance job on `workflow_dispatch` or a commit explicitly labeled `[deep]`. The full CI archives every source-linked result and never assigns automatic mathematical proof credit.
