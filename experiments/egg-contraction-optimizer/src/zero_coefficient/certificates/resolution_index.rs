//! Source-derived, per-frontier clause constraints for final exact #SAT.
//!
//! This experiment compiles bounded source-clause resolvents *once* for a
//! fixed set of future source factors. Every indexed rule is verified through
//! an independently written source-and-resolution proof replay before use.
//! A rule can reject a boundary mask only if every variable in the proven
//! clause is present on the current retained boundary and all its literals
//! are false under that mask.
//!
//! The resulting state is a contextual final-#SAT object. It is not a
//! reusable processed-prefix polynomial. No index, clause or certificate
//! survives crossing to another frontier with different future factors.

use super::*;
use std::time::Instant;

#[path = "resolution_index/prejoin.rs"]
pub mod prejoin;

const MAX_SOURCE_CLAUSES: usize = 64;
const MIN_SUPPORT_TO_COMPILE: usize = 8;
const MAX_DERIVED_CLAUSES: usize = 48;
const MAX_PAIR_SCANS_PER_FRONTIER: u64 = 2_000;
const MAX_RESOLVENT_WIDTH: usize = 3;
const MAX_RESOLUTION_DEPTH: u8 = 2;
const MAX_PATTERN_CHECKS_PER_CASE: u64 = 200_000;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum IndexMode {
    SourceBoundaryClauses,
    CheckedResolution,
}

impl IndexMode {
    pub const ALL: [Self; 2] = [
        Self::SourceBoundaryClauses,
        Self::CheckedResolution,
    ];

    pub fn name(self) -> &'static str {
        match self {
            Self::SourceBoundaryClauses => "indexed-source-clauses",
            Self::CheckedResolution => "indexed-checked-resolution",
        }
    }
}

#[derive(Clone, Debug)]
enum Origin {
    Source { factor: usize, constraint: usize },
    Resolve {
        left: usize,
        right: usize,
        pivot: String,
        left_positive: bool,
    },
}

#[derive(Clone, Debug)]
struct Node {
    clause: Clause,
    origin: Origin,
    depth: u8,
}

#[derive(Clone, Copy, Debug)]
struct ForbiddenPattern {
    assigned_bits: usize,
    required_false_bits: usize,
}

#[derive(Default, Clone, Debug)]
pub struct IndexWork {
    pub source_clause_collections: u64,
    pub collected_clauses: u64,
    pub collected_literals: u64,
    pub source_nodes_checked: u64,
    pub source_reason_literals_checked: u64,
    pub pair_scans: u64,
    pub pivot_candidate_reads: u64,
    pub resolution_constructed: u64,
    pub resolution_tautology_refusals: u64,
    pub resolution_width_refusals: u64,
    pub resolution_duplicate_refusals: u64,
    pub resolution_budget_refusals: u64,
    pub derived_nodes_checked: u64,
    pub replay_literal_reads: u64,
    pub verified_patterns: u64,
    pub direct_patterns: u64,
    pub derived_patterns: u64,
    pub pattern_mask_comparisons: u64,
    pub rejected_boundary_entries: u64,
    pub frontier_compilations: u64,
    pub skipped_small_support: u64,
    pub skipped_large_source: u64,
    pub peak_source_nodes: usize,
    pub peak_derived_nodes: usize,
    pub peak_patterns: usize,
    /// Minimum representation bytes for proof nodes, compiled masks and
    /// retained strings; not actual map/allocator/BigUint peak memory.
    pub peak_encoded_index_bytes_lower_bound: usize,
    pub exact: Metrics,
}

#[derive(Debug)]
pub struct Receipt {
    pub case: Case,
    pub mode: IndexMode,
    pub order: Vec<usize>,
    pub final_count: BigUint,
    pub expected_count: BigUint,
    pub elapsed_ns: u128,
    pub same_case_sparse_elapsed_ns: u128,
    pub same_case_uncached_unit_elapsed_ns: u128,
    pub sparse_multiplications: u64,
    pub unit_multiplications: u64,
    pub work: IndexWork,
    pub oracle: &'static str,
}

fn normalized_source_clause(raw: &Clause) -> Option<Clause> {
    let mut normalized = BTreeMap::<String, bool>::new();
    for (name, desired) in raw {
        if matches!(normalized.insert(name.clone(), *desired), Some(old) if old != *desired) {
            // A tautological clause is true under every assignment.
            return None;
        }
    }
    Some(normalized.into_iter().collect())
}

fn source_nodes(
    factors: &[Factor],
    order: &[usize],
    step: usize,
    work: &mut IndexWork,
) -> Result<Vec<Node>, String> {
    work.source_clause_collections += 1;
    let mut nodes = Vec::new();
    for &factor in &order[step + 1..] {
        for (constraint, c) in factors[factor].constraints.iter().enumerate() {
            let Constraint::Clause(original) = c else {
                return Err("unsupported non-CNF future source for resolution index".into());
            };
            work.collected_clauses += 1;
            work.collected_literals += original.len() as u64;
            if let Some(clause) = normalized_source_clause(original) {
                nodes.push(Node {
                    clause,
                    origin: Origin::Source { factor, constraint },
                    depth: 0,
                });
            }
        }
    }
    Ok(nodes)
}

/// Candidate generator. This function is deliberately separate from the
/// replay checker below. The generator never grants permission to prune.
fn derive_clause(
    left: &Clause,
    right: &Clause,
    pivot: &str,
    left_positive: bool,
    work: &mut IndexWork,
) -> Option<Clause> {
    let mut values = BTreeMap::<String, bool>::new();
    for (name, sign) in left.iter().chain(right.iter()) {
        if name == pivot { continue; }
        work.pivot_candidate_reads += 1;
        if matches!(values.insert(name.clone(), *sign), Some(old) if old != *sign) {
            work.resolution_tautology_refusals += 1;
            return None;
        }
    }
    if !left.contains(&(pivot.to_owned(), left_positive)) ||
       !right.contains(&(pivot.to_owned(), !left_positive))
    {
        return None;
    }
    Some(values.into_iter().collect())
}

fn add_bounded_resolvents(nodes: &mut Vec<Node>, work: &mut IndexWork) {
    let mut known = nodes.iter().map(|n| n.clause.clone())
        .collect::<BTreeSet<_>>();
    let source_len = nodes.len();
    let mut budget_exhausted = false;
    let mut frontier_pair_scans = 0u64;
    'rounds: for round in 1..=MAX_RESOLUTION_DEPTH {
        let limit = nodes.len();
        for left in 0..limit {
            for right in (left + 1)..limit {
                let depth = nodes[left].depth.max(nodes[right].depth) + 1;
                if depth != round { continue; }
                if frontier_pair_scans >= MAX_PAIR_SCANS_PER_FRONTIER {
                    budget_exhausted = true;
                    break 'rounds;
                }
                work.pair_scans += 1;
                frontier_pair_scans += 1;
                // Inspect every complementary pivot, not only the first.
                let possible = nodes[left].clause.clone();
                for (pivot, sign) in possible {
                    work.pivot_candidate_reads += nodes[right].clause.len() as u64;
                    if !nodes[right].clause.contains(&(pivot.clone(), !sign)) {
                        continue;
                    }
                    let Some(resolvent) = derive_clause(
                        &nodes[left].clause, &nodes[right].clause,
                        &pivot, sign, work,
                    ) else { continue };
                    if resolvent.len() > MAX_RESOLVENT_WIDTH {
                        work.resolution_width_refusals += 1;
                        continue;
                    }
                    if !known.insert(resolvent.clone()) {
                        work.resolution_duplicate_refusals += 1;
                        continue;
                    }
                    nodes.push(Node {
                        clause: resolvent,
                        origin: Origin::Resolve {
                            left, right, pivot, left_positive: sign,
                        },
                        depth,
                    });
                    work.resolution_constructed += 1;
                    if nodes.len() - source_len >= MAX_DERIVED_CLAUSES {
                        budget_exhausted = true;
                        break 'rounds;
                    }
                }
            }
        }
    }
    if budget_exhausted {
        work.resolution_budget_refusals += 1;
    }
}

/// Independent proof replay. Source leaves are checked by original factor
/// and constraint *identity*. Derived nodes are re-evaluated from validated
/// parent nodes by a separate literal-set union implementation, without
/// calling derive_clause, accepting pivot absence, or accepting tautologies.
fn check_nodes(
    nodes: &[Node], factors: &[Factor],
    allowed_future: &BTreeSet<usize>, work: &mut IndexWork,
) -> Result<(), String> {
    for (i, node) in nodes.iter().enumerate() {
        let expected = match &node.origin {
            Origin::Source { factor, constraint } => {
                if !allowed_future.contains(factor) {
                    return Err("source proof clause is absent from current future frontier".into());
                }
                let Some(Constraint::Clause(original)) = factors.get(*factor)
                    .and_then(|f| f.constraints.get(*constraint))
                else { return Err("source witness points outside original CNF".into()); };
                let mut members = BTreeSet::<Literal>::new();
                for lit in original {
                    work.source_reason_literals_checked += 1;
                    members.insert(lit.clone());
                }
                if members.iter().any(|(name, sign)|
                    members.contains(&(name.clone(), !sign)))
                {
                    return Err("tautological original clause must not be indexed".into());
                }
                work.source_nodes_checked += 1;
                members
            }
            Origin::Resolve {
                left, right, pivot, left_positive,
            } => {
                if *left >= i || *right >= i {
                    return Err("resolution witness has forward or missing dependency".into());
                }
                let l = &nodes[*left].clause;
                let r = &nodes[*right].clause;
                if !l.contains(&(pivot.clone(), *left_positive)) ||
                    !r.contains(&(pivot.clone(), !*left_positive))
                {
                    return Err("witness lacks complementary original pivot".into());
                }
                let mut members = BTreeSet::<Literal>::new();
                for lit in l.iter().filter(|(name, _)| name != pivot)
                    .chain(r.iter().filter(|(name, _)| name != pivot))
                {
                    work.replay_literal_reads += 1;
                    members.insert(lit.clone());
                }
                if members.iter().any(|(name, sign)|
                    members.contains(&(name.clone(), !sign)))
                {
                    return Err("resolution checker rejects tautological resolvent".into());
                }
                work.derived_nodes_checked += 1;
                members
            }
        };
        if expected.into_iter().collect::<Clause>() != node.clause {
            return Err(format!("source-resolution witness mismatch at node {i}"));
        }
    }
    Ok(())
}

fn indexed_patterns(
    nodes: &[Node], ports: &[String], work: &mut IndexWork,
) -> Result<Vec<ForbiddenPattern>, String> {
    let mut seen = BTreeSet::<(usize, usize)>::new();
    let mut rules = Vec::new();
    for node in nodes {
        let mut assigned_bits = 0usize;
        let mut false_bits = 0usize;
        let mut all_present = true;
        for (name, sign) in &node.clause {
            let Ok(index) = ports.binary_search(name) else {
                all_present = false;
                break;
            };
            let bit = 1usize.checked_shl(index as u32)
                .ok_or("boundary mask exceeds machine word")?;
            assigned_bits |= bit;
            if !sign { false_bits |= bit; }
        }
        if all_present && seen.insert((assigned_bits, false_bits)) {
            rules.push(ForbiddenPattern {
                assigned_bits, required_false_bits: false_bits,
            });
            work.verified_patterns += 1;
            match node.origin {
                Origin::Source { .. } => work.direct_patterns += 1,
                Origin::Resolve { .. } => work.derived_patterns += 1,
            }
        }
    }
    Ok(rules)
}

fn index_bytes(nodes: &[Node], rules: &[ForbiddenPattern]) -> usize {
    nodes.iter().map(|n| {
        std::mem::size_of::<Node>() +
        n.clause.iter().map(|(s, _)| s.len() +
            std::mem::size_of::<(String, bool)>()).sum::<usize>() +
        match &n.origin {
            Origin::Source { .. } => 0,
            Origin::Resolve { pivot, .. } => pivot.len(),
        }
    }).sum::<usize>() + rules.len() * std::mem::size_of::<ForbiddenPattern>()
}

fn filter(
    state: &mut Stage, factors: &[Factor], order: &[usize],
    step: usize, mode: IndexMode, work: &mut IndexWork,
) -> Result<(), String> {
    if state.entries() < MIN_SUPPORT_TO_COMPILE {
        work.skipped_small_support += 1;
        return Ok(());
    }
    let mut nodes = source_nodes(factors, order, step, work)?;
    if nodes.is_empty() { return Ok(()); }
    if nodes.len() > MAX_SOURCE_CLAUSES {
        work.skipped_large_source += 1;
        return Ok(());
    }
    let source_count = nodes.len();
    if mode == IndexMode::CheckedResolution {
        add_bounded_resolvents(&mut nodes, work);
    }
    // No candidate is trusted until all its parent source references and
    // resolution steps are independently rechecked.
    let allowed_future = order[step + 1..].iter().copied().collect::<BTreeSet<_>>();
    check_nodes(&nodes, factors, &allowed_future, work)?;
    let rules = indexed_patterns(&nodes, &state.ports, work)?;
    work.frontier_compilations += 1;
    work.peak_source_nodes = work.peak_source_nodes.max(source_count);
    work.peak_derived_nodes =
        work.peak_derived_nodes.max(nodes.len() - source_count);
    work.peak_patterns = work.peak_patterns.max(rules.len());
    work.peak_encoded_index_bytes_lower_bound =
        work.peak_encoded_index_bytes_lower_bound.max(index_bytes(&nodes, &rules));
    if rules.is_empty() { return Ok(()); }
    let Values::Sparse(values) = &mut state.values else {
        return Err("precompiled source clauses require sparse exact support".into());
    };
    let mut removed = Vec::new();
    for &mask in values.keys() {
        for rule in &rules {
            if work.pattern_mask_comparisons >= MAX_PATTERN_CHECKS_PER_CASE {
                // A budget refusal simply stops optional pruning.
                break;
            }
            work.pattern_mask_comparisons += 1;
            if (mask & rule.assigned_bits) == rule.required_false_bits {
                removed.push(mask);
                break;
            }
        }
        if work.pattern_mask_comparisons >= MAX_PATTERN_CHECKS_PER_CASE {
            break;
        }
    }
    for mask in removed {
        if values.remove(&mask).is_none() {
            return Err("duplicate forbidden boundary assignment".into());
        }
        work.rejected_boundary_entries += 1;
    }
    Ok(())
}

fn run_with_reference(
    case: Case, mode: IndexMode, source: &[Factor],
    baseline: &super::super::Receipt, unit: &super::Receipt,
) -> Result<Receipt, String> {
    let order = baseline.order.clone();
    let started = Instant::now();
    let mut work = IndexWork::default();
    let mut leaves = Vec::new();
    for factor in source {
        leaves.push(Stage::leaf(factor, Strategy::IndexedSupport, &mut work.exact)?);
    }
    let mut state = leaves[order[0]].clone();
    filter(&mut state, source, &order, 0, mode, &mut work)?;
    for (step, &index) in order.iter().enumerate().skip(1) {
        let kept = kept_after(
            source, &order, step, &state.ports, &leaves[index].ports, &[],
        );
        state = state.merge_sparse(
            &leaves[index], &kept, &mut work.exact,
        )?;
        filter(&mut state, source, &order, step, mode, &mut work)?;
    }
    if !state.ports.is_empty() {
        return Err("source index expected a closed #SAT boundary".into());
    }
    let result = state.get(0);
    if result != baseline.source_satisfying_count ||
        result != unit.satisfying_count
    {
        return Err(format!(
            "indexed source resolution changed #SAT for {}: {} != {}",
            case.label(), result, baseline.source_satisfying_count,
        ));
    }
    let sparse = baseline.variants.iter()
        .find(|r| r.strategy == Strategy::IndexedSupport)
        .ok_or("missing sparse verified reference")?;
    Ok(Receipt {
        case, mode, order, final_count: result,
        expected_count: baseline.source_satisfying_count.clone(),
        elapsed_ns: started.elapsed().as_nanos(),
        same_case_sparse_elapsed_ns: sparse.elapsed_ns,
        same_case_uncached_unit_elapsed_ns: unit.elapsed_ns,
        sparse_multiplications: sparse.work.multiplications,
        unit_multiplications: unit.work.exact_arithmetic.multiplications,
        work, oracle: "checked",
    })
}

pub fn run_modes(case: Case) -> Result<Vec<Receipt>, String> {
    let baseline = super::super::run_case(case)?;
    let original = adaptive::source_case(case)?;
    let unit = super::run_with_baseline(case, Mode::Unit, &baseline, &original)?;
    IndexMode::ALL.into_iter().map(|mode|
        run_with_reference(case, mode, &original, &baseline, &unit)).collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    fn factor(ports: &[&str], clauses: &[&[(&str, bool)]]) -> Factor {
        Factor {
            ports: ports.iter().map(|v| (*v).to_string()).collect(),
            constraints: clauses.iter().map(|clause| Constraint::Clause(
                clause.iter().map(|(name, sign)|
                    (name.to_string(), *sign)).collect(),
            )).collect(),
        }
    }

    #[test]
    fn derived_boundary_clause_rejects_before_source_unit_query() {
        // Future has (p∨x) and (q∨¬x); resolving x produces (p∨q).
        // Under p=q=false, source clauses force both x values.
        // Direct indexing alone cannot reject because x is unbound.
        let factors = vec![
            factor(&["p", "q", "r"], &[]),
            factor(&["p", "x"], &[&[("p", true), ("x", true)]]),
            factor(&["q", "x"], &[&[("q", true), ("x", false)]]),
        ];
        let order = [0, 1, 2];
        let mut m = Metrics::default();
        let source = Stage::leaf(&factors[0], Strategy::IndexedSupport, &mut m)
            .unwrap();
        let mut direct = source.clone();
        let mut derived = source;
        let mut control = IndexWork::default();
        let mut indexed = IndexWork::default();
        filter(&mut direct, &factors, &order, 0,
            IndexMode::SourceBoundaryClauses, &mut control).unwrap();
        filter(&mut derived, &factors, &order, 0,
            IndexMode::CheckedResolution, &mut indexed).unwrap();
        // Eight assignments in the source boundary, two bad p=q=0
        // assignments, differing only on irrelevant r.
        assert_eq!(direct.entries(), 8);
        assert_eq!(derived.entries(), 6);
        assert_eq!(indexed.rejected_boundary_entries, 2);
        assert!(indexed.derived_nodes_checked > 0);
        assert!(indexed.derived_patterns > 0);
    }

    #[test]
    fn forged_resolvent_cannot_be_indexed() {
        let factors = vec![
            factor(&["p", "x"], &[&[("p", true), ("x", true)]]),
            factor(&["q", "x"], &[&[("q", true), ("x", false)]]),
        ];
        let nodes = vec![
            Node {
                clause: vec![("p".into(), true), ("x".into(), true)],
                origin: Origin::Source { factor: 0, constraint: 0 },
                depth: 0,
            },
            Node {
                clause: vec![("q".into(), true), ("x".into(), false)],
                origin: Origin::Source { factor: 1, constraint: 0 },
                depth: 0,
            },
            Node {
                clause: vec![("p".into(), false), ("q".into(), true)],
                origin: Origin::Resolve {
                    left: 0, right: 1, pivot: "x".into(), left_positive: true,
                },
                depth: 1,
            },
        ];
        assert!(check_nodes(&nodes, &factors, &BTreeSet::from([0, 1]),
            &mut IndexWork::default()).is_err());
    }

    #[test]
    fn source_proof_from_previous_frontier_cannot_be_replayed() {
        let factors = vec![
            factor(&["p"], &[&[("p", true)]]),
            factor(&["q"], &[&[("q", true)]]),
        ];
        let forged_source = vec![Node {
            clause: vec![("p".into(), true)],
            origin: Origin::Source { factor: 0, constraint: 0 },
            depth: 0,
        }];
        let err = check_nodes(&forged_source, &factors,
            &BTreeSet::from([1]), &mut IndexWork::default()).unwrap_err();
        assert!(err.contains("absent from current future frontier"));
    }

    #[test]
    fn no_rule_for_unfixed_future_variable() {
        // A source clause containing x cannot be tested on a boundary
        // that retains only p. It is NOT a contradiction for p=false.
        let factors = vec![
            factor(&["p", "q", "r"], &[]),
            factor(&["p", "x"], &[&[("p", true), ("x", true)]]),
        ];
        let order = [0, 1];
        let mut m = Metrics::default();
        let mut stage = Stage::leaf(&factors[0], Strategy::IndexedSupport, &mut m)
            .unwrap();
        let mut work = IndexWork::default();
        filter(&mut stage, &factors, &order, 0,
            IndexMode::CheckedResolution, &mut work).unwrap();
        assert_eq!(stage.entries(), 8);
        assert!(work.source_nodes_checked > 0);
        assert_eq!(work.verified_patterns, 0);
    }

    #[test]
    fn source_future_clause_is_supported_but_not_falsified_when_satisfied() {
        let factors = vec![
            factor(&["p","q","r"], &[]),
            factor(&["p","q"], &[&[("p", true), ("q", true)]]),
        ];
        let order = [0, 1];
        let mut m = Metrics::default();
        let mut stage = Stage::leaf(&factors[0], Strategy::IndexedSupport, &mut m)
            .unwrap();
        filter(&mut stage, &factors, &order, 0,
            IndexMode::SourceBoundaryClauses, &mut IndexWork::default()).unwrap();
        assert_eq!(stage.entries(), 6);
    }

    #[test]
    fn unsupported_future_factor_fails_closed() {
        let factors = vec![
            factor(&["p", "q", "r"], &[]),
            Factor {
                ports: vec!["p".into()],
                constraints: vec![Constraint::Parity(vec!["p".into()], true)],
            },
        ];
        let mut m = Metrics::default();
        let mut stage = Stage::leaf(&factors[0], Strategy::IndexedSupport, &mut m)
            .unwrap();
        let err = filter(&mut stage, &factors, &[0, 1], 0,
            IndexMode::CheckedResolution, &mut IndexWork::default()).unwrap_err();
        assert!(err.contains("non-CNF"));
        assert_eq!(stage.entries(), 8);
    }
}
