# Observing final impure LCNF

Lean **4.34.1** exposes the ownership-lowered compiler representation immediately
before conversion to `Lean.IR`. `LCNFCapture.lean` installs a read-only
`@[cpass]` observer **after `saveImpure`**. It does not reimplement any
compiler pass, and the Rust emitter still consumes `Lean.IR.Decl` in-process.

```
Lean source -> LCNF base -> LCNF mono -> LCNF impure
                                           |
                                           +-> saveImpure -> observer
                                           |                  |
                                           |                  +-> saved local LCNF
                                           |                       snapshot (JSON)
                                           v
                                        Lean.IR -> canonical Rust Reader -> Rust
```

The hook records declaration names only. Reporting retrieves the actual saved
impure LCNF from Lean's local compiler environment, pretty-prints it, and
refuses a root if the hook did not observe its compilation or the matching
compiler IR is absent. This is deliberately **not** an alternative lowering
or a serialized executable IR. Captured LCNF is process-local, so an imported
`.olean` whose compiler IR is already present is not silently described as
captured.

## Run

After building the existing backend and setting `NATIVE_LIB`, `LEAN_PREFIX`,
and `LEAN_PATH` as in `scripts/check.sh`:

```sh
bash scripts/check-lcnf-capture.sh
```

The test uses the same declarations with and without the observer. It requires
byte-identical Rust emission, executes the Rust branch/join and call fixture,
and writes `artifacts/lcnf-capture.json` for three original Lean declarations.
The `List Nat` fixture is **capture-only**: it exercises ownership-lowered
LCNF without pretending that the Rust backend supports its entire heap model.

**What this establishes:** a real, nonmutating observation point for final
impure LCNF and unchanged behavior on the tested scalar IR. **What remains
open:** equivalence for every LCNF/IR instruction, imported declaration capture,
physical heap/reference-count correspondence, and a general semantic refinement
theorem. None follows from an observational hook alone.

Pinned implementation references:
- [Lean compiler passes](https://github.com/leanprover/lean4/blob/v4.34.1/src/Lean/Compiler/LCNF/Passes.lean)
- [`PassInstaller.installAfter`](https://github.com/leanprover/lean4/blob/v4.34.1/src/Lean/Compiler/LCNF/PassManager.lean)
- [Saved final impure declarations](https://github.com/leanprover/lean4/blob/v4.34.1/src/Lean/Compiler/LCNF/PhaseExt.lean)
