# Lean C as a reference for the Rust emitter

Lean 4.34.1 generates C from **impure LCNF**, while our canonical
in-process Rust backend consumes **Lean.IR.Decl**. These are distinct
intermediate representations. We should copy semantics, not replace
our existing Rust backend with a C-text translator.

Relevant upstream code: [LCNF passes](https://github.com/leanprover/lean4/blob/v4.34.1/src/Lean/Compiler/LCNF/Passes.lean),
[LCNF driver](https://github.com/leanprover/lean4/blob/v4.34.1/src/Lean/Compiler/LCNF/Main.lean),
[C emitter](https://github.com/leanprover/lean4/blob/v4.34.1/src/Lean/Compiler/LCNF/EmitC.lean),
[IR declarations](https://github.com/leanprover/lean4/blob/v4.34.1/src/Lean/Compiler/IR/Basic.lean).

| Upstream C behavior | Rust obligation |
| --- | --- |
| Constructor allocation, projection and field writes | Preserve layouts, tags and values |
| `lean_is_exclusive`, `lean_ctor_release` | Preserve unique reuse and live aliases |
| `lean_inc`, `lean_dec`, `lean_del_object` | Account for physically observable RC effects |
| `lean_alloc_closure`, `lean_apply_*` | Preserve capture/argument ownership and arity |
| Tail-call assignments, cases and join labels | Preserve evaluation and control flow |

## Same-source executable comparison

`examples/MutKernels.lean` is the *unchanged* constructor program previously
declared directly in `MutFixture.lean`. Both Lean's real C compiler and
our Rust compiler consume this module. `MutCDriver.lean` and
`mut_c_driver.rs` only parse identical input Nat pairs and print results;
they do not reimplement the functions being tested.

`scripts/check-c-emitter-mut.sh`, invoked by `scripts/check.sh`,
compares original Lean evaluation, a freshly compiled Lean C binary,
and the in-process-IR-generated Rust binary byte for byte. It covers
unique and shared constructor updates and inputs beyond machine words.
The receipt is `artifacts/c-emitter-mut/receipt.txt`.

This proves only finite **returned-value parity** for exercised cases.
It is not a proof of matching reference-count traces, pointer identity,
allocation complexity, or general Lean/Rust equivalence. In particular,
`Rc` ownership observations and noncomputable ETH source remain separate
unresolved obligations. Fail closed on unsupported programs.
