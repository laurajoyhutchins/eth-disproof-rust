//! Strict Lean 4.34.1 compiler-IR reader and source-to-Rust lowering.
//! FFI object access is separate from semantics; no unverified fallbacks.
use super::*;
use crate::names::internal_closure_name;
use crate::primitives::{is_nat_primitive, is_primitive, primitive_spec, runtime_primitive_spec};
use std::collections::BTreeSet;
use std::fmt::Write;

pub(super) struct Reader;

mod body;
mod borrow;
mod cases;
mod decode;
mod expr;
mod expr_call;
mod expr_value;
mod module;
mod ownership;
mod usage;
mod view;

use ownership::OwnershipSummary;
use view::{AltView, FnBodyView};
