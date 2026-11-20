//! Bounded, frontier-local memoization of checked source-clause decisions.
//!
//! This is an experiment in cost amortization, NOT a new SAT inference rule.
//! Decisions depend only on the projected retained-output mask AND the
//! fixed original future source-clause set verified at this frontier.
//! A fresh cache is created at *every* merge; no entry survives a change
//! in source clauses, retained port list, or factor admission.
//!
//! A positive decision is a checked impossibility witness from source
//! clauses. A negative decision says only that no *compiled* clause was
//! falsified, NOT that the formula is satisfiable. Cache negative results
//! only when every current pattern was examined (never on budget refusal).

use super::*;

const MAX_MEMO_KEYS_PER_FRONTIER: usize = 64;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum MemoMode {
    ForbiddenOnly,
    CompleteDecisions,
}
impl MemoMode {
    pub const ALL: [Self; 2] = [Self::ForbiddenOnly, Self::CompleteDecisions];
    pub fn name(self) -> &'static str {
        match self {
            Self::ForbiddenOnly => "memo-forbidden-only",
            Self::CompleteDecisions => "memo-both-decisions",
        }
    }
}

pub(super) struct DecisionCache {
    mode: MemoMode,
    decisions: BTreeMap<usize, bool>,
}

impl DecisionCache {
    pub(super) fn new(mode: MemoMode) -> Self {
        Self { mode, decisions: BTreeMap::new() }
    }

    pub(super) fn check(
        &mut self, output_mask: usize, patterns: &[ForbiddenPattern],
        work: &mut Work,
    ) -> bool {
        if patterns.is_empty() {
            return false;
        }

        // The real BTreeMap lookup runs inside the measured fold. This
        // count includes hits and misses; the allocator/node costs are
        // not modeled as a fictitious constant number of comparisons.
        work.memo_lookup_requests += 1;
        if let Some(&forbidden) = self.decisions.get(&output_mask) {
            if forbidden {
                work.memo_hits_forbidden += 1;
            } else {
                work.memo_hits_allowed += 1;
            }
            return forbidden;
        }
        work.memo_misses += 1;

        let budget_before = work.budget_refusals;
        let forbidden = rejected(output_mask, patterns, true, work);
        if work.budget_refusals != budget_before {
            // The interrupted scan makes no negative claim and cannot
            // be used to initialize a trusted cache entry.
            work.memo_incomplete_refusals += 1;
            return false;
        }
        if !forbidden && self.mode == MemoMode::ForbiddenOnly {
            return false;
        }
        if self.decisions.len() >= MAX_MEMO_KEYS_PER_FRONTIER {
            work.memo_capacity_refusals += 1;
            return forbidden;
        }
        self.decisions.insert(output_mask, forbidden);
        work.memo_inserts += 1;
        work.memo_peak_entries = work.memo_peak_entries.max(self.decisions.len());
        // A strict lower bound on logical key/value payload. Excludes
        // BTreeMap's B-tree node, element storage capacity and allocator.
        work.memo_peak_payload_bytes_lower_bound =
            work.memo_peak_payload_bytes_lower_bound.max(
                self.decisions.len() *
                    (std::mem::size_of::<usize>() + std::mem::size_of::<bool>()),
            );
        forbidden
    }
}

#[derive(Debug)]
pub struct Receipt {
    pub case: Case,
    pub mode: MemoMode,
    pub order: Vec<usize>,
    pub result: BigUint,
    pub source_count: BigUint,
    pub elapsed_ns: u128,
    pub direct_preproduct_elapsed_ns: u128,
    pub sparse_elapsed_ns: u128,
    pub direct_multiplications: u64,
    pub sparse_multiplications: u64,
    pub work: Work,
    pub oracle: &'static str,
}

/// Comparison on the *same* source case: original source enumeration,
/// full polynomial zero-coefficient oracle, existing sparse baseline,
/// original direct-preproduct control, then two memoization policies.
pub fn run_modes(case: Case) -> Result<Vec<Receipt>, String> {
    let references = super::run_modes(case)?;
    let direct = references.iter()
        .find(|r| r.placement == Placement::BeforeProduct)
        .ok_or("missing original certified preproduct reference")?;
    let source = adaptive::source_case(case)?;
    MemoMode::ALL.into_iter().map(|mode| {
        let (result, work, elapsed_ns) =
            fold_with_memo(&source, &direct.order, Placement::BeforeProduct, Some(mode))?;
        if result != direct.final_count || result != direct.expected_count {
            return Err(format!(
                "memo result for {} differs from independent source count",
                case.label(),
            ));
        }
        // Reusing exact decisions may save mask comparisons, but must
        // never silently change the exact arithmetic on a case where
        // neither path hit its optional source-rule budget.
        if work.budget_refusals == 0 &&
            direct.work.budget_refusals == 0 &&
            (work.exact.multiplications != direct.work.exact.multiplications ||
             work.exact.additions != direct.work.exact.additions)
        {
            return Err(format!(
                "memo changed matched certified arithmetic for {} without budget refusals",
                case.label(),
            ));
        }
        Ok(Receipt {
            case, mode, order: direct.order.clone(),
            result, source_count: direct.expected_count.clone(),
            elapsed_ns,
            direct_preproduct_elapsed_ns: direct.elapsed_ns,
            sparse_elapsed_ns: direct.same_case_unpruned_sparse_ns,
            direct_multiplications: direct.work.exact.multiplications,
            sparse_multiplications: direct.same_case_unpruned_mult,
            work, oracle: "checked",
        })
    }).collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    fn pattern(assigned_bits: usize, required_false_bits: usize) -> ForbiddenPattern {
        ForbiddenPattern { assigned_bits, required_false_bits }
    }

    #[test]
    fn cache_decisions_agree_with_checked_patterns_on_both_values() {
        let patterns = [pattern(1, 0)];
        for mode in MemoMode::ALL {
            let mut work = Work::default();
            let mut memo = DecisionCache::new(mode);
            for key in [0, 1, 0, 1] {
                assert_eq!(memo.check(key, &patterns, &mut work), key == 0);
            }
            assert_eq!(work.memo_hits_forbidden, 1);
            if mode == MemoMode::CompleteDecisions {
                assert_eq!(work.memo_hits_allowed, 1);
                assert_eq!(work.memo_inserts, 2);
                assert_eq!(work.mask_tests_before_product, 2);
            } else {
                assert_eq!(work.memo_hits_allowed, 0);
                assert_eq!(work.memo_inserts, 1);
                assert_eq!(work.mask_tests_before_product, 3);
            }
        }
    }

    #[test]
    fn changing_future_patterns_requires_a_new_frontier_cache() {
        let mut work = Work::default();
        let mut first = DecisionCache::new(MemoMode::CompleteDecisions);
        assert!(first.check(0, &[pattern(1, 0)], &mut work));
        assert_eq!(first.decisions.get(&0), Some(&true));

        // A later frontier has different original source clauses, so
        // reusing the old memo would be unsound. The actual fold creates
        // a new cache for each factor admission.
        let mut second = DecisionCache::new(MemoMode::CompleteDecisions);
        assert!(!second.check(0, &[pattern(1, 1)], &mut work));
        assert_eq!(second.decisions.get(&0), Some(&false));
    }

    #[test]
    fn never_store_an_unchecked_open_on_budget_exhaustion() {
        let mut work = Work::default();
        work.mask_tests_before_product = MAX_MASK_TESTS_PER_CASE;
        let mut memo = DecisionCache::new(MemoMode::CompleteDecisions);
        let patterns = [pattern(1, 0), pattern(2, 0)];
        assert!(!memo.check(3, &patterns, &mut work));
        assert!(memo.decisions.is_empty());
        assert_eq!(work.memo_incomplete_refusals, 1);
        assert_eq!(work.budget_refusals, 1);
        assert!(!memo.check(3, &patterns, &mut work));
        assert_eq!(work.memo_incomplete_refusals, 2);
    }

    #[test]
    fn memo_capacity_refusal_keeps_real_checked_decisions() {
        let mut work = Work::default();
        let mut memo = DecisionCache::new(MemoMode::CompleteDecisions);
        let patterns = [pattern(1, 0)];
        for key in 0..(MAX_MEMO_KEYS_PER_FRONTIER + 2) {
            assert_eq!(memo.check(key, &patterns, &mut work), key & 1 == 0);
        }
        assert_eq!(memo.decisions.len(), MAX_MEMO_KEYS_PER_FRONTIER);
        assert_eq!(work.memo_capacity_refusals, 2);
        assert_eq!(work.memo_peak_entries, MAX_MEMO_KEYS_PER_FRONTIER);
    }

    fn free(ports: &[&str]) -> Factor {
        Factor {
            ports: ports.iter().map(|s| s.to_string()).collect(),
            constraints: Vec::new(),
        }
    }
    fn unit_clause(variable: &str) -> Factor {
        Factor {
            ports: vec![variable.to_owned()],
            constraints: vec![Constraint::Clause(vec![(variable.to_owned(), true)])],
        }
    }

    #[test]
    fn duplicate_hidden_fibers_reuse_forbidden_and_allowed_results() {
        // First leaf deliberately lacks p. A checked future (p)
        // clause cannot reject its eight x,z,w states yet. The next
        // leaf introduces p and x, creating 16 compatible join pairs,
        // with eight hidden completions for each retained p output.
        let source = vec![
            free(&["w", "x", "z"]),
            free(&["p", "x"]),
            unit_clause("p"),
        ];
        let order = [0, 1, 2];
        let (direct, raw, _) =
            fold_with_memo(&source, &order, Placement::BeforeProduct, None).unwrap();
        let (cached, memo, _) =
            fold_with_memo(
                &source, &order, Placement::BeforeProduct,
                Some(MemoMode::CompleteDecisions),
            ).unwrap();
        assert_eq!(cached, direct);
        assert_eq!(cached, BigUint::from(8u8));
        assert_eq!(memo.exact.multiplications, raw.exact.multiplications);
        assert_eq!(memo.candidate_products_refused, 8);
        assert_eq!(memo.memo_hits_forbidden, 7);
        assert_eq!(memo.memo_hits_allowed, 7);
        assert_eq!(raw.mask_tests_before_product, 16);
        assert_eq!(memo.mask_tests_before_product, 2);
        assert_eq!(memo.memo_misses, 2);
        assert_eq!(memo.memo_inserts, 2);
        let expected = source_oracle(&source, &[], 0).unwrap().count_at_zero();
        assert_eq!(cached, expected);
    }

    #[test]
    fn fully_open_future_clause_must_not_create_a_false_refutation() {
        let source = vec![
            free(&["p", "x", "z"]),
            free(&["x"]),
            Factor {
                ports: vec!["p".into(), "y".into()],
                constraints: vec![Constraint::Clause(vec![
                    ("p".into(), true), ("y".into(), true),
                ])],
            },
        ];
        let order = [0, 1, 2];
        let (direct, _, _) =
            fold_with_memo(&source, &order, Placement::BeforeProduct, None).unwrap();
        let (cached, work, _) =
            fold_with_memo(
                &source, &order, Placement::BeforeProduct,
                Some(MemoMode::CompleteDecisions),
            ).unwrap();
        assert_eq!(cached, direct);
        assert_eq!(work.memo_inserts, 0);
        assert_eq!(work.candidate_products_refused, 0);
    }
}
