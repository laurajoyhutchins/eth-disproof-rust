//! Two machine-word bitsets per frontier for *complete checked*
//! source-clause guard decisions, optionally admitted by a strictly
//! pre-join structural estimate. No runtime SAT claims are cached.
//!
//! Truth of a negative result means only "no indexed ORIGINAL
//! future clause was falsified". Budget-interrupted scans are never
//! entered into either bitset. Each merge owns a fresh cache.

use super::*;

/// At most 256 possible retained output keys. Two 4-word arrays
/// occupy 64 bytes regardless of how many keys have been seen.
const MAX_OUTPUT_PORTS: usize = 8;
const WORDS: usize = 4;

/// *Heuristic* not a theorem or certified estimate:
/// E[compatible pairs] ≈ |support(A)| |support(B)| / 2^|shared|.
/// Permit the optional cache only if this estimate is at least
/// twice the number of retained output masks, at least 8 pairs,
/// and the union has at least one eliminated variable.
/// No source-oracle results or observed pair visits feed the gate.
const MIN_ESTIMATED_PAIRS: u128 = 8;
const MIN_ESTIMATED_PAIRS_PER_OUTPUT: u128 = 2;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Policy {
    AlwaysSmallBitset,
    PredictedRepeatedFiber,
}
impl Policy {
    pub const ALL: [Self; 2] = [
        Self::AlwaysSmallBitset, Self::PredictedRepeatedFiber,
    ];
    pub fn name(self) -> &'static str {
        match self {
            Self::AlwaysSmallBitset => "bitset-all-small",
            Self::PredictedRepeatedFiber => "bitset-predicted-fiber",
        }
    }
}

pub(super) struct DecisionBits {
    known: [u64; WORDS],
    forbidden: [u64; WORDS],
    entries: usize,
}

impl DecisionBits {
    pub(super) fn prepare(
        left: &Stage, right: &Stage, kept: &[String],
        patterns: &[ForbiddenPattern], policy: Policy, work: &mut Work,
    ) -> Option<Self> {
        if patterns.is_empty() {
            return None;
        }
        work.bitset_gate_calls += 1;
        if kept.len() > MAX_OUTPUT_PORTS {
            work.bitset_declined_width += 1;
            return None;
        }
        if policy == Policy::PredictedRepeatedFiber {
            // All values come from source scopes or already-present
            // input support lengths, before scanning compatible pairs.
            let union = union_ports(&left.ports, &right.ports);
            let shared = left.ports.iter()
                .filter(|name| right.ports.binary_search(name).is_ok())
                .count();
            work.bitset_gate_port_reads +=
                (left.ports.len() + right.ports.len() + kept.len()) as u64;
            let pairs = (left.entries() as u128)
                .saturating_mul(right.entries() as u128)
                .checked_shr(shared as u32).unwrap_or(0);
            let domain = 1u128 << kept.len();
            let eliminated = union.len().saturating_sub(kept.len());
            work.bitset_estimated_compatible_pairs =
                work.bitset_estimated_compatible_pairs.saturating_add(pairs);
            work.bitset_estimated_excess_pairs =
                work.bitset_estimated_excess_pairs.saturating_add(
                    pairs.saturating_sub(domain),
                );
            if eliminated == 0 ||
                pairs < MIN_ESTIMATED_PAIRS ||
                pairs < domain * MIN_ESTIMATED_PAIRS_PER_OUTPUT
            {
                work.bitset_declined_estimate += 1;
                return None;
            }
        }
        work.bitset_admitted_frontiers += 1;
        work.bitset_peak_state_bytes =
            work.bitset_peak_state_bytes.max(std::mem::size_of::<Self>());
        Some(Self {
            known: [0; WORDS],
            forbidden: [0; WORDS],
            entries: 0,
        })
    }

    pub(super) fn check(
        &mut self, output: usize, patterns: &[ForbiddenPattern], work: &mut Work,
    ) -> bool {
        if patterns.is_empty() {
            return false;
        }
        // All projected masks fit in at most eight retained ports.
        // For an out-of-domain key, preserve the exact checked guard.
        let word = output / 64;
        if word >= WORDS {
            work.bitset_fallback_out_of_range += 1;
            return rejected(output, patterns, true, work);
        }
        let bit = 1u64 << (output % 64);
        work.memo_lookup_requests += 1;
        if self.known[word] & bit != 0 {
            let is_forbidden = self.forbidden[word] & bit != 0;
            if is_forbidden {
                work.memo_hits_forbidden += 1;
            } else {
                work.memo_hits_allowed += 1;
            }
            return is_forbidden;
        }
        work.memo_misses += 1;
        let before = work.budget_refusals;
        let is_forbidden = rejected(output, patterns, true, work);
        if work.budget_refusals != before {
            work.memo_incomplete_refusals += 1;
            return false;
        }
        self.known[word] |= bit;
        if is_forbidden { self.forbidden[word] |= bit; }
        self.entries += 1;
        work.memo_inserts += 1;
        work.memo_peak_entries = work.memo_peak_entries.max(self.entries);
        work.memo_peak_payload_bytes_lower_bound =
            work.memo_peak_payload_bytes_lower_bound.max(
                std::mem::size_of::<Self>()
            );
        is_forbidden
    }
}

#[derive(Debug)]
pub struct Receipt {
    pub case: Case,
    pub policy_name: &'static str,
    pub order: Vec<usize>,
    pub final_count: BigUint,
    pub source_count: BigUint,
    pub elapsed_ns: u128,
    pub direct_ns: u128,
    pub tree_ns: u128,
    pub sparse_ns: u128,
    pub direct_mask_tests: u64,
    pub tree_mask_tests: u64,
    pub direct_mult: u64,
    pub tree_mult: u64,
    pub sparse_mult: u64,
    pub work: Work,
    pub oracle: &'static str,
}

pub fn run_modes(case: Case) -> Result<Vec<Receipt>, String> {
    // The inherited reference runs independent name-based original
    // source enumeration, the full-polynomial zero-coefficient
    // differential pass, exact sparse counting, original preproduct
    // counting and tree-cache checks on the *same* source.
    let references = memo::run_modes(case)?;
    let tree = references.iter().find(|r|
        r.mode == memo::MemoMode::CompleteDecisions
    ).ok_or("missing prior exact tree-cache reference")?;
    let source = adaptive::source_case(case)?;
    let mut receipts = Vec::new();
    for policy in Policy::ALL {
        let (count, work, elapsed_ns) = fold_with_bitset(
            &source, &tree.order, policy,
        )?;
        if count != tree.source_count ||
            work.exact.multiplications != tree.direct_multiplications ||
            work.exact.additions != tree.work.exact.additions ||
            work.candidate_products_refused != tree.work.candidate_products_refused
        {
            return Err(format!(
                "bitset {:?} changed exact checked #SAT or arithmetic for {}",
                policy, case.label(),
            ));
        }
        receipts.push(Receipt {
            case, policy_name: policy.name(), order: tree.order.clone(),
            final_count: count, source_count: tree.source_count.clone(),
            elapsed_ns, direct_ns: tree.direct_preproduct_elapsed_ns,
            tree_ns: tree.elapsed_ns, sparse_ns: tree.sparse_elapsed_ns,
            direct_mask_tests: tree.direct_mask_tests,
            tree_mask_tests: tree.work.mask_tests_before_product,
            direct_mult: tree.direct_multiplications,
            tree_mult: tree.work.exact.multiplications,
            sparse_mult: tree.sparse_multiplications,
            work, oracle: "checked",
        });
    }
    // Expose the independently verified existing BTreeMap baseline in
    // the same result set, without re-running it.
    receipts.push(Receipt {
        case, policy_name: "tree-complete",
        order: tree.order.clone(), final_count: tree.result.clone(),
        source_count: tree.source_count.clone(),
        elapsed_ns: tree.elapsed_ns,
        direct_ns: tree.direct_preproduct_elapsed_ns,
        tree_ns: tree.elapsed_ns,
        sparse_ns: tree.sparse_elapsed_ns,
        direct_mask_tests: tree.direct_mask_tests,
        tree_mask_tests: tree.work.mask_tests_before_product,
        direct_mult: tree.direct_multiplications,
        tree_mult: tree.work.exact.multiplications,
        sparse_mult: tree.sparse_multiplications,
        work: clone_work_for_receipt(&tree.work),
        oracle: "checked",
    });
    Ok(receipts)
}

// The existing Work retains only exact metric POD fields and source
// vectors are absent. Keep the original tree reference counters intact.
fn clone_work_for_receipt(work: &Work) -> Work {
    Work {
        source: work.source.clone(), exact: work.exact.clone(),
        compiled_frontiers: work.compiled_frontiers,
        skipped_low_support: work.skipped_low_support,
        skipped_large_source: work.skipped_large_source,
        candidate_pairs_visited: work.candidate_pairs_visited,
        mask_tests_before_product: work.mask_tests_before_product,
        mask_tests_after_join: work.mask_tests_after_join,
        candidate_products_refused: work.candidate_products_refused,
        final_outputs_refused: work.final_outputs_refused,
        budget_refusals: work.budget_refusals,
        proof_checked_original_clauses: work.proof_checked_original_clauses,
        source_provenance_literal_reads: work.source_provenance_literal_reads,
        peak_rules: work.peak_rules,
        peak_rule_payload_bytes_lower_bound: work.peak_rule_payload_bytes_lower_bound,
        memo_lookup_requests: work.memo_lookup_requests,
        memo_hits_forbidden: work.memo_hits_forbidden,
        memo_hits_allowed: work.memo_hits_allowed,
        memo_misses: work.memo_misses,
        memo_inserts: work.memo_inserts,
        memo_capacity_refusals: work.memo_capacity_refusals,
        memo_incomplete_refusals: work.memo_incomplete_refusals,
        memo_peak_entries: work.memo_peak_entries,
        memo_peak_payload_bytes_lower_bound: work.memo_peak_payload_bytes_lower_bound,
        ..Work::default()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    fn patterns() -> Vec<ForbiddenPattern> {
        vec![ForbiddenPattern {
            assigned_bits: 1, required_false_bits: 0,
        }]
    }

    fn free(ports: &[&str]) -> Factor {
        Factor {
            ports: ports.iter().map(|s| (*s).to_owned()).collect(),
            constraints: Vec::new(),
        }
    }
    fn unit(name: &str) -> Factor {
        Factor {
            ports: vec![name.to_owned()],
            constraints: vec![
                Constraint::Clause(vec![(name.to_owned(), true)]),
            ],
        }
    }

    #[test]
    fn bitset_negative_and_positive_reuse_are_both_checked() {
        let left = Stage {
            ports: vec!["p".into()],
            values: Values::Sparse(BTreeMap::new()),
        };
        let mut work = Work::default();
        let mut bits = DecisionBits::prepare(
            &left, &left, &left.ports,
            &patterns(), Policy::AlwaysSmallBitset, &mut work,
        ).unwrap();
        for key in [0, 1, 0, 1] {
            assert_eq!(bits.check(key, &patterns(), &mut work), key == 0);
        }
        assert_eq!(work.memo_hits_forbidden, 1);
        assert_eq!(work.memo_hits_allowed, 1);
        assert_eq!(work.memo_inserts, 2);
        assert_eq!(work.mask_tests_before_product, 2);
    }

    #[test]
    fn predictor_rejects_no_hidden_fiber_without_scanning_pairs() {
        let mut counts = BTreeMap::new();
        for m in 0..8 { counts.insert(m, BigUint::from(1u8)); }
        let left = Stage {
            ports: vec!["p".into(), "x".into(), "z".into()],
            values: Values::Sparse(counts),
        };
        let right = Stage {
            ports: vec!["p".into(), "x".into(), "z".into()],
            values: left.values.clone(),
        };
        let mut work = Work::default();
        assert!(DecisionBits::prepare(
            &left, &right, &left.ports, &patterns(),
            Policy::PredictedRepeatedFiber, &mut work,
        ).is_none());
        assert_eq!(work.bitset_admitted_frontiers, 0);
        assert_eq!(work.bitset_declined_estimate, 1);
    }

    #[test]
    fn predictor_admits_repeated_hidden_fibers_and_preserves_source_count() {
        let source = vec![
            free(&["w", "x", "z"]),
            free(&["p", "x"]),
            unit("p"),
        ];
        let order = [0, 1, 2];
        let (direct, direct_work, _) = fold_with_memo(
            &source, &order, Placement::BeforeProduct, None,
        ).unwrap();
        let (predicted, predicted_work, _) = fold_with_bitset(
            &source, &order, Policy::PredictedRepeatedFiber,
        ).unwrap();
        assert_eq!(direct, BigUint::from(8u8));
        assert_eq!(direct, predicted);
        assert_eq!(direct_work.exact.multiplications,
            predicted_work.exact.multiplications);
        assert_eq!(predicted_work.bitset_admitted_frontiers, 1);
        assert_eq!(predicted_work.memo_hits_forbidden, 7);
        assert_eq!(predicted_work.memo_hits_allowed, 7);
        assert_eq!(predicted_work.mask_tests_before_product, 2);
        let independent = source_oracle(&source, &[], 0).unwrap().count_at_zero();
        assert_eq!(direct, independent);
    }

    #[test]
    fn direct_address_declines_nine_port_boundary() {
        let ports = (0..9).map(|i| format!("x{i}")).collect::<Vec<_>>();
        let stage = Stage {
            ports: ports.clone(),
            values: Values::Sparse(BTreeMap::new()),
        };
        let mut work = Work::default();
        let result = DecisionBits::prepare(
            &stage, &stage, &ports, &patterns(),
            Policy::AlwaysSmallBitset, &mut work,
        );
        assert!(result.is_none());
        assert_eq!(work.bitset_declined_width, 1);
        assert_eq!(work.bitset_admitted_frontiers, 0);
    }

    #[test]
    fn structural_pair_estimate_is_not_a_sound_repeat_certificate() {
        // The gate assumes roughly uniform shared-port occupancy,
        // but the actual positive supports may be anticorrelated.
        // It is allowed to spend time on a bad prediction; it must
        // never use this estimate to reject source assignments.
        let mut a = BTreeMap::new();
        for m in 0..16usize {
            if m & 2 == 0 { a.insert(m, BigUint::from(1u8)); }
        }
        let mut b = BTreeMap::new();
        for m in 0..8usize {
            if m & 2 != 0 { b.insert(m, BigUint::from(1u8)); }
        }
        let left = Stage {
            ports: vec!["p".into(), "s".into(), "x".into(), "z".into()],
            values: Values::Sparse(a),
        };
        let right = Stage {
            ports: vec!["q".into(), "s".into(), "x".into()],
            values: Values::Sparse(b),
        };
        let kept = vec!["p".into(), "q".into()];
        let mut work = Work::default();
        assert!(DecisionBits::prepare(
            &left, &right, &kept, &patterns(),
            Policy::PredictedRepeatedFiber, &mut work,
        ).is_some());
        // Structural estimate: 8*4 / 2^2 = 8 pairs.
        assert_eq!(work.bitset_estimated_compatible_pairs, 8);
        // Actual compatible pairs: 0, because left always has
        // s=0 while right always has s=1.
        let shared = vec!["s".to_owned(), "x".to_owned()];
        let Values::Sparse(a) = &left.values else { unreachable!() };
        let Values::Sparse(b) = &right.values else { unreachable!() };
        let matched = a.keys().flat_map(|&m| {
            b.keys().filter(move |&&n| {
                project(m, &left.ports, &shared) ==
                    project(n, &right.ports, &shared)
            })
        }).count();
        assert_eq!(matched, 0);
    }

    #[test]
    fn interrupted_scan_cannot_become_cached_negative() {
        let left = Stage {
            ports: vec!["p".into()],
            values: Values::Sparse(BTreeMap::new()),
        };
        let mut work = Work::default();
        let mut bits = DecisionBits::prepare(
            &left, &left, &left.ports,
            &patterns(), Policy::AlwaysSmallBitset, &mut work,
        ).unwrap();
        work.mask_tests_before_product = MAX_MASK_TESTS_PER_CASE;
        assert!(!bits.check(1, &patterns(), &mut work));
        assert_eq!(work.memo_incomplete_refusals, 1);
        assert_eq!(work.memo_inserts, 0);
        assert!(!bits.check(1, &patterns(), &mut work));
        assert_eq!(work.memo_hits_allowed, 0);
    }

    #[test]
    fn no_source_guard_means_no_cache() {
        let mut work = Work::default();
        let a = Stage {
            ports: vec!["p".into()],
            values: Values::Sparse(BTreeMap::new()),
        };
        assert!(DecisionBits::prepare(
            &a, &a, &a.ports, &[], Policy::AlwaysSmallBitset, &mut work
        ).is_none());
        assert_eq!(work.bitset_admitted_frontiers, 0);
    }
}
