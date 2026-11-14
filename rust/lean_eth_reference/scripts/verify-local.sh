#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
# Fast stdlib-only tests of the imported-Lean evidence gate; no Mathlib required.
python3 -m unittest discover -s scripts/tests
cargo fmt --check
cargo test --offline
cargo clippy --offline --all-targets -- -D warnings
