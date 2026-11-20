//! Shared production error type, compiled without duplication by the source-linked proof harness.

use std::fmt;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Error {
    Invalid(String),
    Capacity(String),
    Overflow,
    /// An explicit unfinished source-defined command, never a successful halt.
    NotImplemented(&'static str),
}
impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Invalid(s) => write!(f, "invalid formula: {s}"),
            Self::Capacity(s) => write!(f, "capacity refusal: {s}"),
            Self::Overflow => write!(f, "exact count overflow"),
            Self::NotImplemented(symbol) => write!(f, "unimplemented Lean source stage: {symbol}"),
        }
    }
}
impl std::error::Error for Error {}
