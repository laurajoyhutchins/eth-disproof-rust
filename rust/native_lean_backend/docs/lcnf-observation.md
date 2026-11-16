# Inspecting final impure LCNF

Lean **4.34.1** already saves ownership-lowered LCNF immediately before
converting it to `Lean.IR`. The experiment reads those saved declarations
directly through `Lean.Compiler.LCNF.getLocalImpureDecl?`.

**No new `@[cpass]`, alternative lowering, or serialized executable IR is
needed.** The canonical in-process emitter still consumes `Lean.IR.Decl`.

```
Lean source -> LCNF base -> LCNF mono -> LCNF impure
                                           |
                                           +-> saveImpure -> local LCNF snapshot
                                           |                     |
                                           |                  read only
                                           v                     v
                                        Lean.IR ----------> diagnostic report
                                           |
                                           v
                                    canonical Rust Reader -> Rust
```

`LCNFCapture.report` requires both the process-local saved impure declaration
and matching executable `Lean.IR`. It fails closed if imported IR is present
but the final impure LCNF body is unavailable. It doesn't reconstruct
compiler state, infer unsupported source semantics, or modify compiler IR.

## Run

After building the existing backend and setting `NATIVE_LIB`, `LEAN_PREFIX`,
and `LEAN_PATH` as in `scripts/check.sh`:

```sh
bash scripts/check-lcnf-capture.sh
```

The test compiles the same source before and after importing the diagnostic
module. It demands byte-identical Rust emission, executes the scalar branch
and direct-call fixture, and writes `artifacts/lcnf-capture.json` for three
original Lean declarations. `List Nat` is **capture-only**, not an admission
of arbitrary heap semantics into the Rust backend.

**What this establishes if CI passes:** real saved LCNF can be inspected
without modifying Lean's compilation pipeline, while canonical Rust behavior
remains unchanged on the tested inputs. It does **not** prove general compiler
correctness, imported-program LCNF capture, or physical reference-count parity.

Pinned sources:
- [Lean's existing `saveImpure` pass](https://github.com/leanprover/lean4/blob/v4.34.1/src/Lean/Compiler/LCNF/Passes.lean)
- [Saved final impure declarations](https://github.com/leanprover/lean4/blob/v4.34.1/src/Lean/Compiler/LCNF/PhaseExt.lean)
