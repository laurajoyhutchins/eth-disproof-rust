# Source-derived Lean refinement experiment

This isolated Rust crate **includes the actual production coefficient toggle**, with
`#[path = "../../../src/checked_toggle.rs"]`. Its callable `checked_flip` invokes
the same `flip_checked` function used by `affine_cert.rs`.

The pipeline is:

1. Rust toolchain compiles this crate, checking the source path is live.
2. **Charon** extracts LLBC from this exact crate.
3. **Aeneas** translates LLBC into Lean and reports any unmodeled external dependencies.
4. Later: prove the generated Lean function corresponds to the existing
   `IndependentAffineIndexToggle.lean` specification.

Toolchain: Aeneas `2e3d4488280bb8a95411db81019a7854a784861f`,
its pinned Charon `9e193f0317dacc822cc864c1798b117c70dcf7df`,
Lean 4.36.0 (separate from the ETH proof suite's Lean 4.34.1).

**Scope:** A successful Rust build is not a verified translation. Charon extraction
is not an Aeneas theorem. Aeneas-generated code is not a completed refinement until
its generated functions, dependencies, external models, and **Lean kernel-checked
theorem** are verified. Do not assume a successful `cargo test` or `LLBC` file
discharges any of those obligations.

The expected output is a generated-data artifact from the CI probe, not
checked-in hand-written Lean standing in for source-derived semantics.
See the notebook study `affine-checker-universal-refinement`.
