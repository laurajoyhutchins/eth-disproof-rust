//! Strict Lean 4.34.1 compiler-IR reader and source-to-Rust lowering.
//! FFI object access is separate from semantics; no unverified fallbacks.
use super::*;
use std::collections::BTreeSet;
use std::fmt::Write;

pub(super) struct Reader;

mod decode;
mod expr;
mod cases;
mod body;
mod module;
