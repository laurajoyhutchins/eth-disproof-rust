# Rust port notes

Start with [what runs](evidence.md) and [what is missing](remaining-lean-port.md). The historical chapters explain how individual fragments were constructed; they do not update the executable status of `main` by themselves.

## Read for a specific problem

**Machine execution:** [frontend](m2-runnable-frontend.md), [query table](compiled-query-table.md), [original Lean differential](independent-differential-and-accounting.md), [primitive TM2 resources](m3-tm2-resource-evidence.md).

**Lean compilation:** [compiler IR](compiler-ir-backend.md), [core expression residualization](core-expr-residualizer.md), [codegen agreement](two-path-acceptance-contract.md), [generalization](lean-to-rust-generalization.md).

**Mathematical cost:** [worst-case parameters and polynomial overhead](worst-case-and-polynomial-overhead.md), [finite fallback](m2-finite-fallback-decision.md), [research notebook](../../../research/README.md).

**History:** [the reconstructed Git reading guide](reading-the-history.md) and [test-accuracy audit](tdd-accuracy-audit.md).

The [stage registry](../src/remaining/registry.rs) is the executable inventory. Do not maintain a competing manual status table.

## Older experiments

These notes are useful when reproducing a specific fragment or recovering a design decision. Read the version in the filename literally.

### Cache and physical frames

[Integer cache v0.10](integer-cache-port-v0.10.md) · [H-cache v0.11](h-cache-iteration-v0.11.0.md) · [Integer cache v0.12](integer-cache-v0.12.0.md) · [Bootstrap v0.13](bootstrap-v0.13.0.md) · [Loader v0.14](native-signature-loader-frames-v0.14.0.md) · [Pair expansion v0.15](pair-expansion-v0.15.0.md) · [Difference pairs v0.16](difference-pairs-v0.16.0.md) · [Head support](head-support-port.md)

### Signature and query construction

[Signature frames v0.17](signature-frames-v0.17.0.md) · [Generator v0.18](signature-generator-v0.18.0.md) · [Rescan v0.19](signature-rescan-v0.19.0.md) · [Keys v0.20](signature-key-stages-v0.20.0.md) · [Arithmetic v0.21](signature-arithmetic-v0.21.0.md) · [Attained rescan v0.22](attained-signature-rescan-v0.22.0.md) · [Signed signature pipeline](signed-signature-pipeline.md)

[Signed pair preparation](m1-signed-pair-preparation.md) · [Physical pair sign](m1-physical-pair-sign.md) · [Table codegen](lean-table-codegen-experiment.md)

### Frontend, normalization, terminal cases

[Frontend boundaries](m2-frontend-boundaries.md) · [Outer I/O](m2-outer-io-boundaries.md) · [Literal cleanup](m2-normalization-literal-cleanup.md) · [Tautologies](m2-tautology-source.md) · [Full normalization](m2-full-source-normalization.md) · [Terminal classifier](m2-terminal-classifier-source.md) · [Terminal count](m2-terminal-count-source.md)

Source identity is pinned in [the manifest](../reference/source-manifest.json). Rust tests, original-Lean correspondence and primitive-machine complexity remain separate kinds of evidence.
