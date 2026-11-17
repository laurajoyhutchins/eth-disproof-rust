# Excession-guided native compiler refactor

## Revisions and scope

This is a structure-only extraction from `src/lib.rs`. `src/names.rs` owns canonical Lean.Name text encoding and injective generated Rust symbol names. `src/primitives.rs` owns the shared primitive whitelist and both tab-separated registry lookups. Original functions and lookup tables are moved, not rewritten. IR decoding, construction, the canonical GMP/Rc runtime, Lean ABI entrypoints and G2 residualization are unchanged.

The critical invariant is that *dependency discovery and expression lowering consult the same primitive classifications*. An unsupported primitive must be refused, never approximated or delegated to a substitute host implementation.

## Evidence and commands

The pull request runs the pinned Excession CLI (commit `21d2e0fd52b6099bb88eae1456bfe3a4681b963d`) against the compiler's actual Git base and head:

```sh
excession agent locate --repo . --rev BASE --task 'Lean compiler primitive registry and source name encoding' --index-segments 256 --json
excession agent context --repo . --rev BASE --focus compiler/src/lib.rs,compiler/primitive-registry.tsv,compiler/runtime-primitive-registry.tsv
excession agent verify --repo . --base BASE --candidate HEAD
```

Source identity, changed paths, candidate impact and unresolved obligations are uploaded as separate Excession artifacts. Their job is to prevent accidental scope changes and retain a replayable review of the refactor, *not* to certify that Lean and Rust behave identically.

Excession's ordinary static dependency analyzer does not yet establish Rust call-graph completeness. A Rust-only repository can report `NO_SUPPORTED_STATIC_MODULE_INDEX`. Such a gap is not a clean bill of health. The existing exact-head native Lean IR and generated Rust differential CI must still pass, especially constructor families, persistent arrays, GMP Nat, closures and original external projects.

## Acceptance

1. The original `lib.rs` name and primitive tests continue to pass, along with new distinct-namespace and unsupported-primitive tests.
2. `scripts/check.sh` and the full `native-lean-rust.yml` job pass on the exact candidate SHA.
3. Excession context and verification reports are tied to the same base and candidate commits, with unsupported relationship coverage visible.
4. No new compiler path, runtime representation, fallback or ETH counting claim is introduced.
