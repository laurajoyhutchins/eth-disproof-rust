//! Finite sparse-disjoint counting reference for the Lean semantic model.
//! Its bounded enumerating leaf remains exponential and is not the native ETH machine.

use crate::{Clause, Cnf, Error, encode_list, encode_nat};
use std::collections::VecDeque;

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
