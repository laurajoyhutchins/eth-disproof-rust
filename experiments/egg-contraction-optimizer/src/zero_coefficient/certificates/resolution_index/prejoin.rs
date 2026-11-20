//! Apply original future clauses to compatible support pairs BEFORE
//! their exact BigUint product, instead of building then rejecting a
//! nonzero output coefficient. The controls use *the same* compiled
//! source clauses at *the same* factor-admission frontiers.
//!
//! Correctness depends on two independent facts:
//!  1. Every indexed clause is an ORIGINAL unprocessed source clause,
//!     independently replayed by source factor and constraint ID.
//!  2. Every indexed clause variable is retained in the OUTPUT boundary
//!     of this merge. Hence every compatible join pair producing the same
//!     boundary key makes the same clause-violation decision.
//!
//! A contextual pruning state preserves only the final exact #SAT, not
//! the standalone processed-prefix count or full violation histogram.

use super::*;
use std::time::Instant;

#[path = "prejoin/memo.rs"]
pub mod memo;

const MIN_LEFT_SUPPORT: usize = 8;
const MAX_SOURCE_NODES: usize = 64;
const MAX_MASK_TESTS_PER_CASE: u64 = 200_000;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Placement {
    PostJoin,
    BeforeProduct,
}

impl Placement {
    pub const ALL: [Self; 2] = [Self::PostJoin, Self::BeforeProduct];
    pub fn name(self) -> &'static str {
        match self {
            Self::PostJoin => "postjoin-source-mask",
            Self::BeforeProduct => "preproduct-source-mask",
        }
    }
}

#[derive(Default, Clone, Debug)]
pub struct Work {
    pub source: IndexWork,
    pub exact: Metrics,
    pub compiled_frontiers: u64,
    pub skipped_low_support: u64,
    pub skipped_large_source: u64,
    pub candidate_pairs_visited: u64,
    pub mask_tests_before_product: u64,
    pub mask_tests_after_join: u64,
    pub candidate_products_refused: u64,
    pub final_outputs_refused: u64,
    pub budget_refusals: u64,
    pub proof_checked_original_clauses: u64,
    pub source_provenance_literal_reads: u64,
    pub peak_rules: usize,
    pub peak_rule_payload_bytes_lower_bound: usize,
    pub memo_lookup_requests: u64,
    pub memo_hits_forbidden: u64,
    pub memo_hits_allowed: u64,
    pub memo_misses: u64,
    pub memo_inserts: u64,
    pub memo_capacity_refusals: u64,
    pub memo_incomplete_refusals: u64,
    pub memo_peak_entries: usize,
    pub memo_peak_payload_bytes_lower_bound: usize,
}

#[derive(Debug)]
pub struct Receipt {
    pub case: Case,
    pub placement: Placement,
    pub order: Vec<usize>,
    pub final_count: BigUint,
    pub expected_count: BigUint,
    pub elapsed_ns: u128,
    pub same_case_unpruned_sparse_ns: u128,
    pub same_case_old_postjoin_ns: u128,
    pub same_case_unpruned_mult: u64,
    pub same_case_old_postjoin_mult: u64,
    pub work: Work,
    pub oracle: &'static str,
}

/// Compilation is done after choosing the merge's actual retained
/// output, using only *strictly later* source factors. Source provenance
/// and frontier membership are checked independently at every frontier.
///
/// This gate deliberately depends only on the incoming left support:
/// the two strategies therefore compile identical rules whenever
/// their incoming state agrees, and neither strategy obtains an easier
/// policy from inspecting the output that it is about to calculate.
fn compile(
    source: &[Factor], order: &[usize], step: usize, kept: &[String],
    left_entries: usize, work: &mut Work,
) -> Result<Vec<ForbiddenPattern>, String> {
    if left_entries < MIN_LEFT_SUPPORT {
        work.skipped_low_support += 1;
        return Ok(Vec::new());
    }
    let nodes = source_nodes(source, order, step, &mut work.source)?;
    if nodes.len() > MAX_SOURCE_NODES {
        work.skipped_large_source += 1;
        return Ok(Vec::new());
    }
    if nodes.is_empty() { return Ok(Vec::new()); }
    let allowed_future = order[step + 1..].iter()
        .copied().collect::<BTreeSet<_>>();
    check_nodes(&nodes, source, &allowed_future, &mut work.source)?;
    // All rules are original clauses. This experiment does NOT use
    // derived resolution closure or unverified inferred clauses.
    if nodes.iter().any(|node| !matches!(node.origin, Origin::Source { .. })) {
        return Err("prejoin compiler unexpectedly contains derived resolution".into());
    }
    let patterns = indexed_patterns(&nodes, kept, &mut work.source)?;
    work.compiled_frontiers += 1;
    work.proof_checked_original_clauses += nodes.len() as u64;
    work.source_provenance_literal_reads +=
        nodes.iter().map(|node| node.clause.len() as u64).sum::<u64>();
    work.peak_rules = work.peak_rules.max(patterns.len());
    work.peak_rule_payload_bytes_lower_bound =
        work.peak_rule_payload_bytes_lower_bound.max(
            index_bytes(&nodes, &patterns));
    Ok(patterns)
}

fn rejected(
    mask: usize, patterns: &[ForbiddenPattern],
    before_product: bool, work: &mut Work,
) -> bool {
    for pattern in patterns {
        let attempted = work.mask_tests_before_product
            + work.mask_tests_after_join;
        if attempted >= MAX_MASK_TESTS_PER_CASE {
            work.budget_refusals += 1;
            // A work refusal is NEVER proof of impossibility.
            return false;
        }
        if before_product {
            work.mask_tests_before_product += 1;
        } else {
            work.mask_tests_after_join += 1;
        }
        if (mask & pattern.assigned_bits) == pattern.required_false_bits {
            return true;
        }
    }
    false
}

fn remove_after_merge(
    stage: &mut Stage, patterns: &[ForbiddenPattern], work: &mut Work,
) -> Result<(), String> {
    let Values::Sparse(map) = &mut stage.values else {
        return Err("postjoin source mask requires sparse output".into());
    };
    let to_remove = map.keys().copied()
        .filter(|&mask| rejected(mask, patterns, false, work))
        .collect::<Vec<_>>();
    for mask in to_remove {
        if map.remove(&mask).is_none() {
            return Err("duplicate original-clause rejection".into());
        }
        work.final_outputs_refused += 1;
    }
    Ok(())
}

/// A direct copy of the *same* indexed sparse join topology. The
/// distinction is exactly one operation boundary: after determining
/// a compatible union assignment and its retained output key, check
/// an independently verified future source clause BEFORE multiplying
/// exact coefficients.
fn merge_preproduct(
    left: &Stage, right: &Stage, kept: &[String],
    patterns: &[ForbiddenPattern], work: &mut Work,
) -> Result<Stage, String> {
    merge_preproduct_with_memo(left, right, kept, patterns, work, None)
}

fn merge_preproduct_with_memo(
    left: &Stage, right: &Stage, kept: &[String],
    patterns: &[ForbiddenPattern], work: &mut Work,
    mut memo: Option<&mut memo::DecisionCache>,
) -> Result<Stage, String> {
    let (Values::Sparse(a), Values::Sparse(b)) = (&left.values, &right.values)
    else { return Err("pre-product source check requires sparse inputs".into()); };
    let union = union_ports(&left.ports, &right.ports);
    let shared = left.ports.iter()
        .filter(|name| right.ports.binary_search(name).is_ok())
        .cloned().collect::<Vec<_>>();
    let mut index = BTreeMap::<usize, Vec<(usize, &BigUint)>>::new();
    for (&mask, count) in b {
        let key = project(mask, &right.ports, &shared);
        index.entry(key).or_default().push((mask, count));
        work.exact.support_index_insertions += 1;
    }
    let mut dest = BTreeMap::<usize, BigUint>::new();
    for (&left_mask, left_count) in a {
        work.exact.left_entry_scans += 1;
        let key = project(left_mask, &left.ports, &shared);
        work.exact.support_group_lookups += 1;
        let Some(rights) = index.get(&key) else { continue; };
        for &(right_mask, right_count) in rights {
            work.candidate_pairs_visited += 1;
            work.exact.compatible_pair_visits += 1;
            if work.exact.compatible_pair_visits > MAX_JOIN_PAIRS {
                return Err("preproduct join exceeded hard pair budget".into());
            }
            let union_mask = embed(left_mask, &left.ports, &union)
                | embed(right_mask, &right.ports, &union);
            let output = project(union_mask, &union, kept);
            let forbidden = match memo.as_deref_mut() {
                Some(cache) => cache.check(output, patterns, work),
                None => rejected(output, patterns, true, work),
            };
            if forbidden {
                work.candidate_products_refused += 1;
                continue;
            }
            let product = measured_product(left_count, right_count, &mut work.exact);
            let sum = dest.entry(output).or_default();
            measured_add_assign(sum, &product, &mut work.exact);
        }
    }
    Ok(Stage { ports: kept.to_vec(), values: Values::Sparse(dest) })
}

fn fold(
    source: &[Factor], order: &[usize], placement: Placement,
) -> Result<(BigUint, Work, u128), String> {
    fold_with_memo(source, order, placement, None)
}

fn fold_with_memo(
    source: &[Factor], order: &[usize], placement: Placement,
    memo_mode: Option<memo::MemoMode>,
) -> Result<(BigUint, Work, u128), String> {
    validate_order(source, order)?;
    let start = Instant::now();
    let mut work = Work::default();
    let mut leaves = Vec::with_capacity(source.len());
    for factor in source {
        leaves.push(Stage::leaf(
            factor, Strategy::IndexedSupport, &mut work.exact,
        )?);
    }
    let mut stage = leaves[order[0]].clone();
    // The initial leaf is the same between the two strategies.
    let original = compile(source, order, 0, &stage.ports, stage.entries(), &mut work)?;
    remove_after_merge(&mut stage, &original, &mut work)?;

    for (step, &factor) in order.iter().enumerate().skip(1) {
        let kept = kept_after(
            source, order, step, &stage.ports, &leaves[factor].ports, &[],
        );
        let constraints = compile(
            source, order, step, &kept, stage.entries(), &mut work,
        )?;
        stage = match placement {
            Placement::PostJoin => {
                let mut merged = stage.merge_sparse(
                    &leaves[factor], &kept, &mut work.exact,
                )?;
                remove_after_merge(&mut merged, &constraints, &mut work)?;
                merged
            },
            Placement::BeforeProduct => {
                // A fresh cache belongs to exactly one checked future
                // clause set; never carry decisions to the next frontier.
                let mut cache = memo_mode.map(memo::DecisionCache::new);
                merge_preproduct_with_memo(
                    &stage, &leaves[factor], &kept, &constraints,
                    &mut work, cache.as_mut(),
                )?
            },
        };
    }
    if !stage.ports.is_empty() {
        return Err("pre-product #SAT study expected closed final boundary".into());
    }
    Ok((stage.get(0), work, start.elapsed().as_nanos()))
}

pub fn run_modes(case: Case) -> Result<Vec<Receipt>, String> {
    let baseline = super::super::super::run_case(case)?;
    let source = adaptive::source_case(case)?;
    let unit = super::super::run_with_baseline(
        case, Mode::Unit, &baseline, &source,
    )?;
    let old_post = super::run_with_reference(
        case, IndexMode::SourceBoundaryClauses, &source, &baseline, &unit,
    )?;
    let reference_sparse = baseline.variants.iter()
        .find(|v| v.strategy == Strategy::IndexedSupport)
        .ok_or("missing independently checked sparse reference")?;
    Placement::ALL.into_iter().map(|placement| {
        let (answer, work, elapsed_ns) = fold(&source, &baseline.order, placement)?;
        if answer != baseline.source_satisfying_count ||
           answer != reference_sparse.satisfying_count ||
           answer != old_post.final_count
        {
            return Err(format!(
                "{} preproduct/pruned source count {} differs from {}",
                case.label(), answer, baseline.source_satisfying_count,
            ));
        }
        Ok(Receipt {
            case, placement, order: baseline.order.clone(),
            final_count: answer,
            expected_count: baseline.source_satisfying_count.clone(),
            elapsed_ns,
            same_case_unpruned_sparse_ns: reference_sparse.elapsed_ns,
            same_case_old_postjoin_ns: old_post.elapsed_ns,
            same_case_unpruned_mult: reference_sparse.work.multiplications,
            same_case_old_postjoin_mult: old_post.work.exact.multiplications,
            work, oracle: "checked",
        })
    }).collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    fn free(ports: &[&str]) -> Factor {
        Factor {
            ports: ports.iter().map(|x| (*x).to_owned()).collect(),
            constraints: Vec::new(),
        }
    }

    fn clause(ports: &[&str], literals: &[(&str, bool)]) -> Factor {
        Factor {
            ports: ports.iter().map(|x| (*x).to_owned()).collect(),
            constraints: vec![Constraint::Clause(literals.iter()
                .map(|(v, value)| (v.to_string(), *value))
                .collect())],
        }
    }

    #[test]
    fn future_clause_rejects_two_join_pairs_before_products() {
        // x and z are dead at this join; p is retained because
        // the original future source clause is (p). Each p key
        // receives four distinct (x,z) completions. Unlike an
        // artificially forced compile, this fixture has eight
        // incoming nonzero left entries and meets the real gate.
        let factors = vec![
            free(&["p", "x", "z"]),
            free(&["x"]),
            clause(&["p"], &[("p", true)]),
        ];
        let order = [0, 1, 2];
        let mut m = Metrics::default();
        let left = Stage::leaf(
            &factors[0], Strategy::IndexedSupport, &mut m,
        ).unwrap();
        let right = Stage::leaf(
            &factors[1], Strategy::IndexedSupport, &mut m,
        ).unwrap();
        let kept = kept_after(
            &factors, &order, 1, &left.ports, &right.ports, &[],
        );
        assert_eq!(kept, vec!["p"]);
        let mut before = Work::default();
        let mut after = Work::default();
        let compiled_before = compile(
            &factors, &order, 1, &kept, left.entries(), &mut before,
        ).unwrap();
        let compiled_after = compile(
            &factors, &order, 1, &kept, left.entries(), &mut after,
        ).unwrap();
        let first = merge_preproduct(
            &left, &right, &kept, &compiled_before, &mut before,
        ).unwrap();
        let mut second = left.merge_sparse(
            &right, &kept, &mut after.exact,
        ).unwrap();
        remove_after_merge(&mut second, &compiled_after, &mut after).unwrap();
        for mask in [0, 1] {
            assert_eq!(first.get(mask), second.get(mask));
        }
        assert_eq!(first.get(0), BigUint::default());
        assert_eq!(first.get(1), BigUint::from(4u8));
        assert_eq!(before.exact.multiplications, 4);
        assert_eq!(after.exact.multiplications, 8);
        assert_eq!(before.candidate_products_refused, 4);
        // After the final clause the original source has four
        // satisfying assignments: x and z are both hidden and free.
        let expected = source_oracle(&factors, &[], 0).unwrap().count_at_zero();
        assert_eq!(expected, BigUint::from(4u8));
    }

    #[test]
    fn clause_with_unbound_future_variable_cannot_refuse_a_pair() {
        let factors = vec![
            free(&["p", "x", "z"]),
            free(&["x"]),
            clause(&["p", "y"], &[("p", true), ("y", true)]),
        ];
        let order = [0, 1, 2];
        let kept = vec!["p".to_owned()];
        let mut work = Work::default();
        let rules = compile(&factors, &order, 1, &kept, 8, &mut work).unwrap();
        assert!(rules.is_empty());
        assert_eq!(work.proof_checked_original_clauses, 1);
    }

    #[test]
    fn postjoin_and_preproduct_agree_on_generated_source() {
        for case in [
            Case { kind: adaptive::CaseKind::Random3Cnf,
                variables: 8, clauses: 16, seed: 21_101 },
            Case { kind: adaptive::CaseKind::Planted3Cnf,
                variables: 8, clauses: 32, seed: 21_113 },
            Case { kind: adaptive::CaseKind::FrustratedXor3Cnf,
                variables: 6, clauses: 24, seed: 0 },
        ] {
            let out = run_modes(case).unwrap();
            assert_eq!(out.len(), 2);
            assert_eq!(out[0].final_count, out[1].final_count);
        }
    }

    #[test]
    fn unsupported_future_source_refuses_before_any_join_mutation() {
        let factors = vec![
            free(&["p", "x", "z"]),
            Factor {
                ports: vec!["p".to_owned()],
                constraints: vec![Constraint::Parity(vec!["p".into()], true)],
            },
        ];
        let mut work = Work::default();
        let result = compile(
            &factors, &[0, 1], 0,
            &factors[0].ports, 8, &mut work,
        );
        assert!(result.unwrap_err().contains("non-CNF"));
    }

    #[test]
    fn source_proof_must_be_in_future() {
        let factors = vec![
            clause(&["p"], &[("p", true)]),
            free(&["q"]),
        ];
        let invalid = vec![Node {
            clause: vec![("p".to_owned(), true)],
            origin: Origin::Source { factor: 0, constraint: 0 },
            depth: 0,
        }];
        let result = check_nodes(
            &invalid, &factors, &BTreeSet::from([1]),
            &mut IndexWork::default(),
        );
        assert!(result.unwrap_err().contains("absent from current future frontier"));
    }
}
