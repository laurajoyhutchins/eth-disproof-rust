# Isolated experiments

The Lungo experiment lives in
[lean-compiler-bootstrap](lean-compiler-bootstrap/README.md). It
compiles a bounded subset of original Lean compiler declarations
to Rust and records independent Lean-oracle results.

The [egg contraction optimizer](egg-contraction-optimizer/README.md)
is a separately pinned Rust equality-saturation experiment over exact
integer polynomial DAGs. It cannot yet optimize the source ETH
contraction or certify an original Lean theorem.

Experiments are not the canonical Lean compiler IR emitter, and
experiment code must never silently become a fallback from `compiler/`
or the source-pinned ETH counting implementation. Keep their pinned
dependencies and CI separate.
