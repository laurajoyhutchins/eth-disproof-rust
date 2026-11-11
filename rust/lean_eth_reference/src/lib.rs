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

use std::collections::VecDeque;
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
pub struct Clause(pub Vec<Literal>);
impl Clause {
    pub fn new(mut literals: Vec<Literal>) -> Self {
        literals.sort_unstable();
        literals.dedup();
        Self(literals)
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
        if clauses
            .iter()
            .flat_map(|c| &c.0)
            .any(|l| l.variable >= variables)
        {
            return Err(Error::Invalid("literal exceeds declared Fin n".into()));
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

/// `DisjointBranch.selected` and `petals`, preserving raw Finset semantics.
pub fn selected(f: &Cnf, width: usize, core: &Clause) -> Vec<Clause> {
    f.clauses
        .iter()
        .filter(|c| c.0.len() == width && core.is_subset_of(c))
        .cloned()
        .collect()
}

/// Lean's `childA` and `childB` use `absorb`, **not** `normalize`.
/// For every assignment, `F = A OR B` and `A AND B = false`.
pub fn disjoint_children(f: &Cnf, width: usize, core: &Clause) -> (Cnf, Cnf) {
    let mut a = Vec::new();
    let mut b = Vec::new();
    for clause in &f.clauses {
        if clause.0.len() == width && core.is_subset_of(clause) {
            b.push(Clause::new(
                clause
                    .0
                    .iter()
                    .copied()
                    .filter(|lit| core.0.binary_search(lit).is_err())
                    .collect(),
            ));
        } else {
            a.push(clause.clone());
            b.push(clause.clone());
        }
    }
    a.push(core.clone());
    for lit in &core.0 {
        b.push(Clause::new(vec![lit.negate()]));
    }
    (
        Cnf::new(f.variables, a).expect("valid subset").absorb(),
        Cnf::new(f.variables, b).expect("valid subset").absorb(),
    )
}

#[derive(Debug, Clone, Copy)]
pub struct Limits {
    pub max_nodes: usize,
    pub max_candidates_per_node: usize,
    pub max_depth: usize,
    pub max_leaf_variables: usize,
}
impl Default for Limits {
    fn default() -> Self {
        Self {
            max_nodes: 4096,
            max_candidates_per_node: 1_000_000,
            max_depth: 512,
            max_leaf_variables: 20,
        }
    }
}

/// Lean `SparsePriority.select`: enumerate source-ordered clauses and subsets,
/// choose the smallest width and largest core (first candidate breaks ties).
/// No arithmetic overflow: compare `threshold^(width-core_size)` with degree
/// by a saturating product stopped at `degree + 1`.
pub fn priority_select(
    f: &Cnf,
    threshold: usize,
    limits: Limits,
) -> Result<Option<(usize, Clause)>, Error> {
    if threshold < 2 {
        return Err(Error::Invalid("threshold M must be >= 2".into()));
    }
    let mut best: Option<(usize, Clause)> = None;
    let mut candidates = 0usize;
    for clause in &f.clauses {
        let width = clause.0.len();
        if width < 2 {
            continue;
        }
        let subset_count = 1usize.checked_shl(width as u32).ok_or_else(|| {
            Error::Capacity("width too large for exhaustive core enumeration".into())
        })?;
        candidates = candidates
            .checked_add(subset_count)
            .ok_or_else(|| Error::Capacity("candidate count overflow".into()))?;
        if candidates > limits.max_candidates_per_node {
            return Err(Error::Capacity("candidate enumeration limit".into()));
        }
        // `orderedClauses C.powerset` sorts by lexicographic literal codes.
        let mut subsets: Vec<Clause> = (0..subset_count)
            .map(|mask| {
                Clause(
                    clause
                        .0
                        .iter()
                        .enumerate()
                        .filter_map(|(i, lit)| ((mask >> i) & 1 == 1).then_some(*lit))
                        .collect(),
                )
            })
            .collect();
        subsets.sort_unstable();
        for core in subsets {
            if core.0.is_empty() || core.0.len() == width {
                continue;
            }
            if let Some((old_width, old_core)) = &best
                && (width > *old_width || (width == *old_width && core.0.len() < old_core.0.len()))
            {
                continue;
            }
            let degree = f
                .clauses
                .iter()
                .filter(|other| other.0.len() == width && core.is_subset_of(other))
                .count();
            let mut required = 1usize;
            for _ in 0..(width - core.0.len()) {
                required = required.saturating_mul(threshold);
                if required > degree {
                    break;
                }
            }
            if required <= degree
                && best
                    .as_ref()
                    .is_none_or(|(w, h)| width < *w || (width == *w && core.0.len() > h.0.len()))
            {
                best = Some((width, core));
            }
        }
    }
    Ok(best)
}

/// Extensible semantic leaf callback, **not** the upstream native leaf program.
pub trait LeafCounter {
    fn count(&mut self, formula: &Cnf) -> Result<u128, Error>;
}

/// Upstream `SAT.count` semantic specification, using explicit assignments.
/// Exponential, bounded, and unsuitable as evidence of ETH's running time.
pub struct EnumeratingLeaf {
    pub max_variables: usize,
}
impl LeafCounter for EnumeratingLeaf {
    fn count(&mut self, f: &Cnf) -> Result<u128, Error> {
        if f.variables > self.max_variables || f.variables >= 128 {
            return Err(Error::Capacity(format!(
                "SAT.count leaf has {} variables, maximum {}",
                f.variables,
                self.max_variables.min(127)
            )));
        }
        Ok((0..(1u128 << f.variables))
            .filter(|mask| f.eval(*mask))
            .count() as u128)
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Entry {
    pub formula: Cnf,
    pub depth: usize,
}

/// `SparseCountProgram.State`, with the top at `VecDeque`'s front.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CountState {
    pub pending: VecDeque<Entry>,
    pub total: u128,
}
impl CountState {
    pub fn initial(f: Cnf) -> Self {
        Self {
            pending: VecDeque::from([Entry {
                formula: f,
                depth: 0,
            }]),
            total: 0,
        }
    }
    /// `reference/lean_native_trace.lean`: unary total and framed pending entries.
    /// This *trace encoding* differs from the source's own `encodeState`.
    pub fn trace_bits(&self) -> Result<String, Error> {
        let n = usize::try_from(self.total).map_err(|_| Error::Overflow)?;
        let mut out = encode_nat(n);
        out.push_str(&encode_list(self.pending.iter().map(|e| {
            format!("{}{}", encode_nat(e.depth), e.formula.encode_lean())
        })));
        Ok(out)
    }
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct CountStats {
    pub nodes: usize,
    pub leaves: usize,
    pub peak_frontier: usize,
    pub max_depth: usize,
}

/// One direct `SparseCountProgram.step` transition.
pub fn count_step<L: LeafCounter>(
    s: &mut CountState,
    m: usize,
    leaf: &mut L,
    limits: Limits,
    stats: &mut CountStats,
) -> Result<bool, Error> {
    if s.pending.is_empty() {
        return Ok(false);
    }
    if stats.nodes >= limits.max_nodes {
        return Err(Error::Capacity("node visit limit".into()));
    }
    // Important: on refusal, the node remains pending; there is no false count.
    let node = s.pending.front().expect("nonempty").clone();
    let choice = priority_select(&node.formula, m, limits)?;
    if choice.is_some() && node.depth >= limits.max_depth {
        return Err(Error::Capacity("sparsification depth limit".into()));
    }
    let (new_total, children) = match choice {
        None => {
            if node.formula.variables() > limits.max_leaf_variables {
                return Err(Error::Capacity("semantic leaf variable limit".into()));
            }
            let count = leaf.count(&node.formula)?;
            let sum = s.total.checked_add(count).ok_or(Error::Overflow)?;
            (sum, None)
        }
        Some((width, core)) => {
            let (a, b) = disjoint_children(&node.formula, width, &core);
            (s.total, Some((a, b)))
        }
    };
    s.pending.pop_front();
    if let Some((a, b)) = children {
        s.pending.push_front(Entry {
            formula: b,
            depth: node.depth + 1,
        });
        s.pending.push_front(Entry {
            formula: a,
            depth: node.depth + 1,
        });
        stats.peak_frontier = stats.peak_frontier.max(s.pending.len());
        stats.max_depth = stats.max_depth.max(node.depth + 1);
    } else {
        stats.leaves += 1;
    }
    s.total = new_total;
    stats.nodes += 1;
    Ok(true)
}

/// Semantic exact count with explicit admission; **not** `Native.countingProgram`.
pub fn count_cnf<L: LeafCounter>(
    f: Cnf,
    m: usize,
    leaf: &mut L,
    limits: Limits,
) -> Result<(u128, CountStats), Error> {
    let mut s = CountState::initial(f);
    let mut stats = CountStats {
        peak_frontier: 1,
        ..Default::default()
    };
    while count_step(&mut s, m, leaf, limits, &mut stats)? {}
    Ok((s.total, stats))
}

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

pub mod native_layout;
pub mod native_nodes;
pub mod native_pair_setup;
pub mod native_query_prefix;
pub mod finite_fallback;
pub mod native_answer;
pub mod native_ambient;
/// Source-defined post-normalization body placement and ambient header suffix.
pub mod native_frontend_tail;

/// Source-native finite unary polarity, frame writer and record reversal.
pub mod native_normalization_primitives;
/// Actual nested literal deduplication on source 10x8 machine.
pub mod native_literal_dedup;
/// Literal cleanup across framed clauses on original 13x11 machine.
pub mod native_literal_cleanup;
/// Source-defined preserving unary-polarity complement query.
pub mod native_negated_query;
/// Physical complementary-literal search inside one encoded clause.
pub mod native_tautology_core;
/// Original nested formula-wide tautology filter and record-order restoration.
pub mod native_tautology_filter;
/// Exact source prefix: physical clause-wise literal cleanup then tautology removal.
pub mod native_normalization_prefix;

/// Source physical clause subset and dual-direction relation kernel.
pub mod native_clause_relations;
/// Three-mode encoded formula relation scanner.
pub mod native_clause_relation_scan;
/// Preserving equivalence scans and last-occurrence clause deduplication.
pub mod native_clause_dedup;
/// Source fixed-master strict-subset filtering of clause records.
pub mod native_clause_filter;
/// Complete source-defined CNF normalization command on 15x16 machine.
pub mod native_normalization_full;
/// Source-fixed unary header reader and binary length initializer.
pub mod native_frontend_header;
pub mod native_terminal;
pub mod native_membership;

/// Exact framed-record iteration and fixed-control membership program.
pub mod native_record_membership;

/// Source physical terminal classification and guarded 80x1220 output.
pub mod native_terminal_classifier;

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

/// Physical source-defined attained-signature controller and level initializer.
pub mod native_signature_tuple;
pub mod native_head_scatter;
pub mod native_head_support;
