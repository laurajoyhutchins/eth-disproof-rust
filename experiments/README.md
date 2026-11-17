# Isolated experiments

The Lungo experiment lives in
[lean-compiler-bootstrap](lean-compiler-bootstrap/README.md). It
compiles a bounded subset of original Lean compiler declarations
to Rust and records independent Lean-oracle results.

It is not the canonical Lean compiler IR emitter. Missing original
runtime externs remain refused, and neither stage-zero compilation
nor a self-hosted compiler would by itself establish backend
ownership semantics or the ETH #SAT execution theorem.

Experiment code must not become a fallback from `compiler/`. Keep
its pinned dependencies and CI separate.
