# Canonical native Lean IR compiler

The executable-IR backend is `compiler` (Lean 4.34.1, Rust 1.99.1). The public `eth-compiler` CLI delegates to its existing [multi-root Lake-project compiler](../../compiler/scripts/compile-project.sh), which consumes genuine borrowed `Lean.IR.Decl` objects in the Lean process and emits a standalone Rust Cargo package.

This is **one** production Rust emitter. Its current emitted Rust includes the existing GMP/`Rc` value runtime for a bounded supported subset. That is an implementation fact, not evidence that its physical ownership traces match Lean C. A generated-Rust target linked through a pinned Lean C execution-runtime adapter is the next acceptance baseline; native Rust runtime replacement follows only after that comparison. The experimental leanfran adapter and the separate Lungo compiler-bootstrap probe are not alternate production code generators. Missing IR and unsupported runtime semantics refuse without switching backends.

See the [architecture](../../compiler/docs/backend-first-architecture.md), [runtime seam](../../compiler/docs/execution-runtime-contract.md) and [current status](../../compiler/docs/compiler-status.md).

## Use it on an unchanged Lake project

Build with a pinned Lean 4.34.1 installation, Rust 1.99.1, Linux x86-64, and the system GMP library. A source checkout must have a committed `lean-toolchain` and the original module. In this repository, the small source-pinned fixture is `compiler/fixtures/CompilerCli`.

```sh
export LEAN_PREFIX=/absolute/path/to/lean-4.34.1
fixture="$PWD/compiler/fixtures/CompilerCli"

cargo run --locked --offline -p lean-eth-reference --bin eth-compiler -- compile \
  --backend compiler-ir \
  --source-repo "$PWD" \
  --source-revision "$(git rev-parse HEAD)" \
  --source-path compiler/fixtures/CompilerCli/Sample.lean \
  --source-toolchain-path compiler/fixtures/CompilerCli/lean-toolchain \
  --lake-root "$fixture" \
  --module Sample \
  --root Sample.inc --root Sample.twice --root Sample.choose \
  --output "$PWD/compiler/artifacts/compiled-cli-example" \
  --receipt "$PWD/compiler/artifacts/compiled-cli-example.receipt.json"
```

`--output` is a **new Cargo package directory**, not a loose `.rs` file. The directory must not exist before compilation. It contains `Cargo.toml`, `src/lib.rs`, and the original native compiler's `receipt.txt`. The unified acceptance receipt is stored separately at `--receipt`.

The original Lake project is built without rewriting its declarations. Its requested executable IR is passed to the native backend with shared closure deduplication. A generated Cargo test runs under the existing native script. **No default output is certified semantically equivalent to original Lean**; only the finite source-oracle tests in the native conformance suite establish equality for exercised programs.

## Reverify without compiling again

```sh
cargo run --locked --offline -p lean-eth-reference --bin eth-compiler -- verify \
  --backend compiler-ir \
  --source-repo "$PWD" \
  --source-revision "$(git rev-parse HEAD)" \
  --source-path compiler/fixtures/CompilerCli/Sample.lean \
  --source-toolchain-path compiler/fixtures/CompilerCli/lean-toolchain \
  --module Sample \
  --root Sample.inc --root Sample.twice --root Sample.choose \
  --artifact "$PWD/compiler/artifacts/compiled-cli-example" \
  --receipt "$PWD/compiler/artifacts/compiled-cli-example.receipt.json"
```

Verification rechecks the original file and toolchain's Git blobs, exact selected roots and source revision, native project receipt, generated library hash, Cargo manifest hash, and the acceptance metadata. Any mismatch refuses and invalidates the acceptance receipt. The native compiler's project receipt explicitly records that the complete transitive imported-source manifest is **not captured**.

The checked semantics of each Lean IR instruction and the original ETH machine still require their independent source-level obligations. Generated Rust does not establish original Lean program correspondence merely because it compiled.

## Distinct symbolic path

`--backend residual-expr` emits a non-executable shared Lean core-`Expr` DAG with a strict syntax, provenance and refusal contract. It does **not** generate the same Cargo package, automatically repair missing compiler IR, or authorize a replacement #SAT algorithm.

The ETH-specific structured `BitProgram` source lowering remains a separate specialization. Its labels, ports, physical state transitions, cost and Lean-to-Rust equivalence must be validated independently before any common backend can supersede it.

## Remaining release obligations

The compiled interface now handles several roots for an unchanged Lake project. The G1 release still requires three **substantial** independent unchanged projects through that very path, complete source closure provenance, ABI and ownership correctness, and integrated exact-head CI. G2 adds lazy semantics-preserving residual consumption plus the complete original query, leaf, DFS and outer counting program with independent full-state and primitive-resource correspondence.

See [checklist #193](https://github.com/laurajoyhutchins/eth-disproof-rust/issues/193), [G1 semantics](../../compiler/SEMANTICS.md), and [Lean/Rust acceptance](../../research/lean-rust-acceptance.md).
