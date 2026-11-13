#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
cargo fmt --check
cargo test --offline
cargo clippy --offline --all-targets -- -D warnings
