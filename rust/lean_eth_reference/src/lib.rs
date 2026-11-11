//! Source-grounded **finite semantic layer** from OpenAI's ETH Lean formalization.
//!
//! `openai/math` revision 4eaee87548250b2682affda7d05d947c05554bae:
//! - `SAT.lean`: Literal/CNF semantics, `removeTautologies`, `absorb`, `normalize`
//! - `Encoding.lean`: `encodeNat`, `frame`, `encodeList`, `encodeCNF`
//! - `SqrtLogSpace/DisjointSparsify.lean`: selected/petals/childA/childB
//! - `SqrtLogSpace/DisjointReuse/SparsePriority.lean`: candidates/select
//! - `SqrtLogSpace/DisjointReuse/SparseCountProgram.lean`: State/step/run
//!
//! Not the compiled `BitProgram` of `SqrtLogSpace/Final.lean`. In particular,
//! the `SAT.count` leaf below is deliberately **exponential**; no subexponential
//! bit-complexity claim is transferred. The finite fallback in upstream
//! `FiniteFallback.lean` is noncomputable and is not implemented here.

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

/// A Lean `SAT.Literal (Fin n)`, with `variable` indexed from zero.
/// Its `Ord` is the `Encoding.literalCode` order: variable, false before true.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Literal {
    pub variable: usize,
    pub positive: bool,
}
impl Literal {
    pub fn from_dimacs(value: i64, variables: usize) -> Result<Self, Error> {
        let unsigned = value.unsigned_abs();
        if unsigned == 0 || unsigned > variables as u64 {
            return Err(Error::Invalid(format!(
                "literal {value} outside 1..={variables}"
            )));
        }
        Ok(Self {
            variable: unsigned as usize - 1,
            positive: value > 0,
        })
    }
    pub fn negate(self) -> Self {
        Self {
            positive: !self.positive,
            ..self
        }
    }
    pub fn code(self) -> usize {
        self.variable * 2 + usize::from(self.positive)
    }
    pub fn eval(self, assignment: u128) -> bool {
        assert!(
            self.variable < 128,
            "literal exceeds u128 assignment representation"
        );
        ((assignment >> self.variable) & 1 != 0) == self.positive
    }
}

/// Finset representation; every clause is a sorted/deduplicated set of literals.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Clause(Vec<Literal>);
impl Clause {
    pub fn new(mut literals: Vec<Literal>) -> Self {
        literals.sort_unstable();
        literals.dedup();
        Self(literals)
    }
    /// Canonical, sorted and deduplicated literals, matching Lean's Finset.
    pub fn literals(&self) -> &[Literal] {
        &self.0
    }
    pub fn is_subset_of(&self, other: &Self) -> bool {
        // Sets are sorted by Lean's `literalCode`.
        let mut j = 0;
        for needle in &self.0 {
            while j < other.0.len() && other.0[j] < *needle {
                j += 1;
            }
            if j == other.0.len() || other.0[j] != *needle {
                return false;
            }
            j += 1;
        }
        true
    }
    pub fn is_tautology(&self) -> bool {
        self.0
            .iter()
            .any(|l| self.0.binary_search(&l.negate()).is_ok())
    }
    pub fn eval(&self, assignment: u128) -> bool {
        self.0.iter().any(|lit| lit.eval(assignment))
    }
}

/// Upstream `SAT.CNF (Fin n)` is a *Finset* of clauses, not implicitly normalized.
/// The declared universe is retained, including unused variables.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Cnf {
    variables: usize,
    clauses: Vec<Clause>,
}
impl Cnf {
    pub fn new(variables: usize, mut clauses: Vec<Clause>) -> Result<Self, Error> {
        // Recanonicalize internal raw clauses before operations that assume Finset order.
        for clause in &mut clauses {
            clause.0.sort_unstable();
            clause.0.dedup();
        }
        if clauses
            .iter()
            .flat_map(|c| &c.0)
            .any(|l| l.variable >= variables)
        {
            return Err(Error::Invalid("literal exceeds declared Fin n".into()));
        }
        if clauses
            .iter()
            .flat_map(|c| &c.0)
            .any(|l| l.variable > (usize::MAX - 1) / 2)
        {
            return Err(Error::Overflow);
        }
        clauses.sort_unstable();
        clauses.dedup();
        Ok(Self { variables, clauses })
    }
    pub fn from_signed(variables: usize, clauses: &[&[i64]]) -> Result<Self, Error> {
        let rows = clauses
            .iter()
            .map(|row| {
                row.iter()
                    .map(|v| Literal::from_dimacs(*v, variables))
                    .collect::<Result<Vec<_>, _>>()
                    .map(Clause::new)
            })
            .collect::<Result<Vec<_>, _>>()?;
        Self::new(variables, rows)
    }
    pub fn variables(&self) -> usize {
        self.variables
    }
    pub fn clauses(&self) -> &[Clause] {
        &self.clauses
    }
    /// Bounded truth valuation. A native `u128` mask is not a full Lean
    /// assignment once the variable universe exceeds 128; refuse explicitly.
    pub fn eval_mask_checked(&self, assignment: u128) -> Result<bool, Error> {
        if self.variables > 128 {
            return Err(Error::Capacity(
                "u128 assignment cannot represent >128 variables".into(),
            ));
        }
        if self.variables < 128 && assignment >= (1u128 << self.variables) {
            return Err(Error::Invalid(
                "assignment outside declared Boolean cube".into(),
            ));
        }
        Ok(self.clauses.iter().all(|clause| clause.eval(assignment)))
    }
    /// Convenience for already validated bounded masks. Never silently give
    /// an answer when the Boolean universe exceeds the mask representation.
    pub fn eval(&self, assignment: u128) -> bool {
        self.eval_mask_checked(assignment)
            .expect("invalid or unrepresentable assignment")
    }
    pub fn remove_tautologies(&self) -> Self {
        let clauses = self
            .clauses
            .iter()
            .filter(|c| !c.is_tautology())
            .cloned()
            .collect();
        Self {
            variables: self.variables,
            clauses,
        }
    }
    pub fn absorb(&self) -> Self {
        // Exact SAT.absorb: remove C when any other D is a strict subset of C.
        let clauses = self
            .clauses
            .iter()
            .filter(|c| {
                !self
                    .clauses
                    .iter()
                    .any(|d| d != *c && d.0.len() < c.0.len() && d.is_subset_of(c))
            })
            .cloned()
            .collect();
        Self {
            variables: self.variables,
            clauses,
        }
    }
    pub fn normalize(&self) -> Self {
        self.remove_tautologies().absorb()
    }

    /// `Encoding.encodeCNF`: **not** DIMACS, no implicit normalization.
    pub fn encode_lean(&self) -> String {
        let mut out = encode_nat(self.variables);
        out.push_str(&encode_list(self.clauses.iter().map(|clause| {
            encode_list(clause.0.iter().map(|lit| encode_nat(lit.code())))
        })));
        out
    }

    /// Strict inverse of the nested Lean `encodeCNF` syntax. Rejects duplicate,
    /// out-of-order, and out-of-range finite-set encodings instead of silently
    /// normalizing them into a different source formula.
    pub fn decode_lean(word: &str) -> Result<Self, Error> {
        let mut cursor = BitCursor::new(word)?;
        let variables = cursor.nat()?;
        let rows = cursor.list(|row_bits| {
            let mut row = BitCursor::new(row_bits)?;
            let codes = row.list(|nat_bits| {
                let mut nat = BitCursor::new(nat_bits)?;
                let result = nat.nat()?;
                nat.finish()?;
                Ok(result)
            })?;
            row.finish()?;
            if codes.windows(2).any(|pair| pair[0] >= pair[1]) {
                return Err(Error::Invalid(
                    "out-of-order or duplicate Lean literals".into(),
                ));
            }
            let bound = variables.checked_mul(2).ok_or_else(|| {
                Error::Invalid("Lean variable count overflows literal code".into())
            })?;
            codes
                .into_iter()
                .map(|code| {
                    if code >= bound {
                        Err(Error::Invalid(
                            "Lean literal code outside declared Fin n".into(),
                        ))
                    } else {
                        Ok(Literal {
                            variable: code / 2,
                            positive: code % 2 == 1,
                        })
                    }
                })
                .collect::<Result<Vec<_>, _>>()
                .map(Clause)
        })?;
        cursor.finish()?;
        if rows.windows(2).any(|pair| pair[0] >= pair[1]) {
            return Err(Error::Invalid(
                "out-of-order or duplicate Lean clauses".into(),
            ));
        }
        Cnf::new(variables, rows)
    }
}

/// Iterative `Encoding.readNat`/`readFrame` inverse with checked input bounds.
struct BitCursor<'a> {
    bits: &'a [u8],
    offset: usize,
}
impl<'a> BitCursor<'a> {
    fn new(word: &'a str) -> Result<Self, Error> {
        if !word.bytes().all(|b| b == b'0' || b == b'1') {
            return Err(Error::Invalid(
                "Lean word contains a non-bit character".into(),
            ));
        }
        Ok(Self {
            bits: word.as_bytes(),
            offset: 0,
        })
    }
    fn bit(&mut self) -> Result<bool, Error> {
        let value = *self
            .bits
            .get(self.offset)
            .ok_or_else(|| Error::Invalid("truncated Lean bit word".into()))?;
        self.offset += 1;
        Ok(value == b'1')
    }
    fn nat(&mut self) -> Result<usize, Error> {
        let mut result = 0usize;
        while self.bit()? {
            result = result
                .checked_add(1)
                .ok_or_else(|| Error::Invalid("unary Lean integer overflow".into()))?;
        }
        Ok(result)
    }
    fn frame(&mut self) -> Result<String, Error> {
        let mut frame = String::new();
        while self.bit()? {
            frame.push(if self.bit()? { '1' } else { '0' });
        }
        Ok(frame)
    }
    fn list<T>(
        &mut self,
        mut decode: impl FnMut(&str) -> Result<T, Error>,
    ) -> Result<Vec<T>, Error> {
        let mut items = Vec::new();
        while self.bit()? {
            items.push(decode(&self.frame()?)?);
        }
        Ok(items)
    }
    fn finish(&self) -> Result<(), Error> {
        if self.offset != self.bits.len() {
            return Err(Error::Invalid("trailing bits inside Lean encoding".into()));
        }
        Ok(())
    }
}

fn encode_nat(n: usize) -> String {
    let mut s = "1".repeat(n);
    s.push('0');
    s
}
fn frame(bits: &str) -> String {
    let mut out = String::with_capacity(bits.len() * 2 + 1);
    for c in bits.chars() {
        out.push('1');
        out.push(c);
    }
    out.push('0');
    out
}
fn encode_list(items: impl IntoIterator<Item = String>) -> String {
    let mut out = String::new();
    for item in items {
        out.push('1');
        out.push_str(&frame(&item));
    }
    out.push('0');
    out
}

mod semantic_count;
pub use semantic_count::{
    CountState, CountStats, Entry, EnumeratingLeaf, LeafCounter, Limits, count_cnf, count_step,
    disjoint_children, priority_select, selected,
};

/// Strict DIMACS parser for a complete finite formula. Not Lean's input encoding.
pub fn parse_dimacs(text: &str) -> Result<Cnf, Error> {
    let mut header = None;
    let mut rows = Vec::new();
    let mut current = Vec::new();
    for line in text.lines() {
        let line = line.trim();
        if line.is_empty() || line.starts_with('c') {
            continue;
        }
        if header.is_none() {
            let parts: Vec<_> = line.split_whitespace().collect();
            if parts.len() != 4 || parts[0] != "p" || parts[1] != "cnf" {
                return Err(Error::Invalid(
                    "expected p cnf <variables> <clauses>".into(),
                ));
            }
            let n = parts[2]
                .parse::<usize>()
                .map_err(|_| Error::Invalid("bad variable count".into()))?;
            let m = parts[3]
                .parse::<usize>()
                .map_err(|_| Error::Invalid("bad clause count".into()))?;
            header = Some((n, m));
            continue;
        }
        let (n, m) = header.expect("header present");
        for token in line.split_whitespace() {
            if rows.len() >= m {
                return Err(Error::Invalid("extra clause data".into()));
            }
            let value = token
                .parse::<i64>()
                .map_err(|_| Error::Invalid("bad literal".into()))?;
            if value == 0 {
                rows.push(Clause::new(std::mem::take(&mut current)));
            } else {
                current.push(Literal::from_dimacs(value, n)?);
            }
        }
    }
    let (n, m) = header.ok_or_else(|| Error::Invalid("missing DIMACS header".into()))?;
    if !current.is_empty() || rows.len() != m {
        return Err(Error::Invalid("unterminated or missing clauses".into()));
    }
    Cnf::new(n, rows)
}

pub mod bit_program;
pub mod native_high;
pub mod native_tuple;

pub mod finite_fallback;
pub mod native_ambient;
pub mod native_answer;
/// Source-defined post-normalization body placement and ambient header suffix.
pub mod native_frontend_tail;
pub mod native_layout;
pub mod native_nodes;
pub mod native_pair_setup;
pub mod native_query_prefix;

/// Literal cleanup across framed clauses on original 13x11 machine.
pub mod native_literal_cleanup;
/// Actual nested literal deduplication on source 10x8 machine.
pub mod native_literal_dedup;
/// Source-defined preserving unary-polarity complement query.
pub mod native_negated_query;
/// Exact source prefix: physical clause-wise literal cleanup then tautology removal.
pub mod native_normalization_prefix;
/// Source-native finite unary polarity, frame writer and record reversal.
pub mod native_normalization_primitives;
/// Physical complementary-literal search inside one encoded clause.
pub mod native_tautology_core;
/// Original nested formula-wide tautology filter and record-order restoration.
pub mod native_tautology_filter;

/// Preserving equivalence scans and last-occurrence clause deduplication.
pub mod native_clause_dedup;
/// Source fixed-master strict-subset filtering of clause records.
pub mod native_clause_filter;
/// Three-mode encoded formula relation scanner.
pub mod native_clause_relation_scan;
/// Source physical clause subset and dual-direction relation kernel.
pub mod native_clause_relations;
/// Complete original physical Native.frontendCommand on the 80x1220 machine.
pub mod native_frontend;
/// Source-fixed unary header reader and binary length initializer.
pub mod native_frontend_header;
pub mod native_membership;
/// Complete source-defined CNF normalization command on 15x16 machine.
pub mod native_normalization_full;
/// Original 80x1220 lift of the source-normalizing 15x16 machine.
pub mod native_outer_normalization;
pub mod native_terminal;

/// Exact framed-record iteration and fixed-control membership program.
pub mod native_record_membership;

/// Source physical terminal classification and guarded 80x1220 output.
pub mod native_terminal_classifier;
/// Bounded source-physical terminal CNF counter; nonterminal cases refuse.
pub mod native_terminal_count;

/// Source-defined generic terminal/nonterminal branch dispatcher; no leaf oracle.
pub mod native_leaf_dispatch;

/// Explicit, source-pinned remainder of the native ETH program.
pub mod remaining;

pub mod native_bootstrap;
pub mod native_integer_cache;

pub mod native_cache_iteration;

/// Source-refined fixed-width flattening and executable integer cache.
pub mod native_flatten;

/// Source-defined fixed-width H-cache normalization and signed flattening.
pub mod native_cache_normalize;

/// Physical source ABI import/export around the pending signature-head local matrix.
pub mod native_loader_frames;

/// Source-defined pruned difference-pair streaming controller.
pub mod native_difference_pairs;

pub mod native_head_scatter;
pub mod native_head_support;
/// Strict source-pinned importer and interpreter bridge for genuine Lean query tables.
pub mod native_query_table;
/// Physical source-defined attained-signature controller and level initializer.
pub mod native_signature_tuple;

/// Source-defined signed pair accumulator preparation; signed update pending.
pub mod native_pair_accumulator;

/// Source-defined physical mask parity, not signed accumulation.
pub mod native_pair_sign;

#[cfg(test)]
mod canonical_clause_tests {
    use super::*;

    #[test]
    fn cnf_new_recanonicalizes_internal_rows_before_set_operations() {
        let x = Literal {
            variable: 0,
            positive: true,
        };
        let y = Literal {
            variable: 1,
            positive: false,
        };
        // The raw Clause constructor is unavailable to external callers.
        let f = Cnf::new(2, vec![Clause(vec![y, x, y])]).unwrap();
        assert_eq!(f.clauses()[0].literals(), &[x, y]);
        assert!(Clause::new(vec![x]).is_subset_of(&f.clauses()[0]));
        assert_eq!(
            f.encode_lean(),
            Cnf::from_signed(2, &[&[1, -2]]).unwrap().encode_lean()
        );
    }
}
