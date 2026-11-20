//! Source-provenance-bound unit refutations amortized over boundary entries.
//!
//! Exact #SAT is preserved for the FINAL fixed source formula only. A learned
//! nogood is a *partial* boundary assignment whose original-clause-indexed
//! unit-refutation has been checked independently. Every superset of the
//! partial assignment is impossible for the same future source clauses.
//!
//! Cache scope is deliberately one frontier. Future clauses change at every
//! factor admission; a certificate is NEVER reused across frontiers. This
//! avoids smuggling a stale clause into a later continuation.
//!
//! The cached proof is checked once at insertion, including original source
//! provenance. Cache hits need only a literal-subset check, with every such
//! comparison charged. No learned nogood is shared between test cases.

use super::*;

const MAX_CACHED_PER_FRONTIER: usize = 64;
const MAX_NOGOOD_WIDTH: usize = 12;
const MAX_MINIMIZATION_ATTEMPTS: u64 = 256;
const MAX_LOOKUP_LITERAL_CHECKS: u64 = 200_000;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum CacheMode {
    FullAssignment,
    MinimizedAssumptions,
}

impl CacheMode {
    pub const ALL: [Self; 2] = [Self::FullAssignment, Self::MinimizedAssumptions];
    pub fn name(self) -> &'static str {
        match self {
            Self::FullAssignment => "nogood-full-assignment",
            Self::MinimizedAssumptions => "nogood-minimized",
        }
    }
}

#[derive(Clone, Debug)]
struct SavedNogood {
    // Every source name/value in this list is a *necessary* assumption
    // for the checked witness, but the set need not be globally minimal.
    assumptions: Vec<(String, bool)>,
    // (factor index, constraint index) for every used original clause.
    used_source_clauses: Vec<(usize, usize)>,
    // Original future source-clause indices, never clause text guessed
    // or manufactured independently of the source.
    proof: UnitRefutation,
    frontier_step: usize,
}

#[derive(Default, Clone, Debug)]
pub struct CacheWork {
    pub baseline: CertificateWork,
    pub lookup_attempts: u64,
    pub lookup_literal_reads: u64,
    pub cache_hits: u64,
    pub cache_inserts: u64,
    pub cache_full_refusals: u64,
    pub minimized_attempts: u64,
    pub minimized_removed_assumptions: u64,
    pub minimization_budget_refusals: u64,
    pub independent_proof_checks: u64,
    pub proof_replay_literal_reads: u64,
    pub source_provenance_checks: u64,
    pub source_provenance_literal_reads: u64,
    pub peak_cache_entries: usize,
    pub peak_cached_assumptions: usize,
    pub peak_cached_proof_steps: usize,
    /// Source-key/value payload + indexing lower bound, not allocator RSS.
    pub peak_cache_payload_bytes_lower_bound: usize,
}

#[derive(Clone, Debug)]
pub struct Receipt {
    pub case: Case,
    pub mode: CacheMode,
    pub order: Vec<usize>,
    pub final_count: BigUint,
    pub expected_count: BigUint,
    pub elapsed_ns: u128,
    pub same_case_uncached_unit_elapsed_ns: u128,
    pub same_case_sparse_elapsed_ns: u128,
    pub same_case_uncached_exact_mult: u64,
    pub same_case_sparse_exact_mult: u64,
    pub work: CacheWork,
    pub oracle: &'static str,
}

fn provenance(factors: &[Factor], order: &[usize], step: usize,
    clauses: &[Clause], cost: &mut CacheWork,
) -> Result<Vec<(usize, usize)>, String> {
    let mut indices = Vec::new();
    for &factor_index in &order[step + 1..] {
        for (constraint_index, constraint) in
            factors[factor_index].constraints.iter().enumerate()
        {
            if let Constraint::Clause(_) = constraint {
                indices.push((factor_index, constraint_index));
            } else {
                return Err("unsupported future non-CNF source".into());
            }
        }
    }
    if indices.len() != clauses.len() {
        return Err("source-clause provenance length mismatch".into());
    }
    // Source identity mapping is checked against the original factor table
    // *once* per frontier; the rest of the proof uses those indices.
    for (idx, &(f, c)) in indices.iter().enumerate() {
        let Constraint::Clause(original) = &factors[f].constraints[c] else {
            return Err("cached source clause ID refers to non-clause".into());
        };
        cost.source_provenance_checks += 1;
        cost.source_provenance_literal_reads += original.len() as u64;
        if *original != clauses[idx] {
            return Err("original source clause does not match proof input".into());
        }
    }
    Ok(indices)
}

/// Check the source-indexed unit reasons with an independent reason checker
/// *after* assumption minimization. Reject invalid traces, budget overflows,
/// and provenance that does not identify the actual remaining factor set.
fn replay_checked(
    clauses: &[Clause], assumption: &BTreeMap<String, bool>,
    proof: &UnitRefutation, work: &mut CacheWork,
) -> Result<(), String> {
    let mut local = CertificateWork::default();
    let result = check_refutation(clauses, assumption, proof, &mut local);
    work.independent_proof_checks += 1;
    work.proof_replay_literal_reads += local.checked_reason_literals;
    result
}

fn trial_minimize(
    clauses: &[Clause], original: &BTreeMap<String, bool>,
    proof: &UnitRefutation, mode: CacheMode, work: &mut CacheWork,
) -> Result<BTreeMap<String, bool>, String> {
    let mut reduced = original.clone();
    if mode != CacheMode::MinimizedAssumptions {
        return Ok(reduced);
    }
    if reduced.len() > MAX_NOGOOD_WIDTH {
        work.minimization_budget_refusals += 1;
        return Ok(reduced);
    }
    // This is proof-only minimization. It does NOT re-run UP under each
    // subset, so the reductions are cheaper than finding new proofs.
    // Failed proof replay means *retain* that original assumption.
    for name in original.keys() {
        if work.minimized_attempts >= MAX_MINIMIZATION_ATTEMPTS {
            work.minimization_budget_refusals += 1;
            break;
        }
        let prior = reduced.remove(name).ok_or("missing initial assumption")?;
        work.minimized_attempts += 1;
        if replay_checked(clauses, &reduced, proof, work).is_ok() {
            work.minimized_removed_assumptions += 1;
        } else {
            reduced.insert(name.clone(), prior);
        }
    }
    Ok(reduced)
}

fn checked_source_reasons(
    proof: &UnitRefutation, index: &[(usize, usize)],
    factors: &[Factor], work: &mut CacheWork,
) -> Result<Vec<(usize, usize)>, String> {
    let mut used = Vec::with_capacity(proof.forced.len() + 1);
    for pos in proof.forced.iter().map(|s| s.reason)
        .chain(std::iter::once(proof.empty_reason))
    {
        let &(source_factor, clause_index) = index.get(pos)
            .ok_or("proof points beyond future source clause table")?;
        // This identity is carried into the cache. Compare source by ID,
        // not a derived textual fingerprint that might collide.
        if !matches!(
            factors[source_factor].constraints.get(clause_index),
            Some(Constraint::Clause(_))
        ) {
            return Err("proof provenance does not name an original clause".into());
        }
        work.source_provenance_checks += 1;
        used.push((source_factor, clause_index));
    }
    Ok(used)
}

fn cache_footprint(nogoods: &[SavedNogood]) -> usize {
    nogoods.iter().map(|ng| {
        std::mem::size_of::<SavedNogood>() +
        ng.assumptions.iter().map(|(name, _)| name.len() +
            std::mem::size_of::<(String, bool)>()).sum::<usize>() +
        ng.used_source_clauses.len() * std::mem::size_of::<(usize, usize)>() +
        ng.proof.forced.iter().map(|s| std::mem::size_of::<Step>() +
            s.variable.len()).sum::<usize>()
    }).sum()
}

/// Literal-subset matching is all that is needed to reuse a *checked*
/// refutation. It is valid even if the extra assignments would prevent
/// the literal-by-literal proof checker from replaying the original steps.
fn matches(
    ng: &SavedNogood, fixed: &BTreeMap<String, bool>,
    step: usize, work: &mut CacheWork,
) -> bool {
    if ng.frontier_step != step { return false; }
    for (name, value) in &ng.assumptions {
        if work.lookup_literal_reads >= MAX_LOOKUP_LITERAL_CHECKS {
            return false;
        }
        work.lookup_literal_reads += 1;
        if fixed.get(name) != Some(value) { return false; }
    }
    true
}

/// A cache is local to the *current* future-CNF frontier. It is discarded
/// before any further source factor is absorbed.
fn filter_with_cache(stage: &mut Stage, factors: &[Factor],
    order: &[usize], step: usize, mode: CacheMode,
    work: &mut CacheWork,
) -> Result<(), String> {
    let clauses = future_clauses(factors, order, step, &mut work.baseline)?;
    if clauses.is_empty() { return Ok(()); }
    if clauses.len() > MAX_FUTURE_CLAUSES {
        work.baseline.budget_skips += 1;
        return Ok(());
    }
    let ids = provenance(factors, order, step, &clauses, work)?;
    let Values::Sparse(support) = &mut stage.values else {
        return Err("source nogood requires indexed sparse support".into());
    };
    let mut nogoods = Vec::<SavedNogood>::new();
    let mut rejected = Vec::new();
    for &mask in support.keys() {
        let initial = stage.ports.iter().enumerate()
            .map(|(i, name)| (name.clone(), mask & (1 << i) != 0))
            .collect::<BTreeMap<_, _>>();
        work.lookup_attempts += 1;
        if nogoods.iter().any(|ng| matches(ng, &initial, step, work)) {
            work.cache_hits += 1;
            rejected.push(mask);
            continue;
        }
        if work.baseline.queries >= MAX_QUERIES ||
            work.baseline.clause_visits >= MAX_CLAUSE_VISITS
        {
            work.baseline.budget_skips += 1;
            break;
        }
        work.baseline.queries += 1;
        let Some(Witness::Unit(proof)) =
            detect(&clauses, &initial, Mode::Unit, &mut work.baseline)
        else { continue };
        // Source-based independent replay on full assumptions BEFORE
        // pruning, whether or not the proof will later be cached.
        check_witness(&clauses, &initial, &Witness::Unit(proof.clone()),
            &mut work.baseline)?;
        work.baseline.unit_refutations += 1;
        rejected.push(mask);

        if nogoods.len() == MAX_CACHED_PER_FRONTIER {
            work.cache_full_refusals += 1;
            continue;
        }
        let reduced = trial_minimize(&clauses, &initial, &proof, mode, work)?;
        replay_checked(&clauses, &reduced, &proof, work)?;
        let source = checked_source_reasons(&proof, &ids, factors, work)?;
        let ng = SavedNogood {
            assumptions: reduced.into_iter().collect(),
            used_source_clauses: source,
            proof,
            frontier_step: step,
        };
        nogoods.push(ng);
        work.cache_inserts += 1;
        work.peak_cache_entries = work.peak_cache_entries.max(nogoods.len());
        work.peak_cached_assumptions = work.peak_cached_assumptions.max(
            nogoods.iter().map(|x| x.assumptions.len()).sum());
        work.peak_cached_proof_steps = work.peak_cached_proof_steps.max(
            nogoods.iter().map(|x| x.proof.forced.len() + 1).sum());
        work.peak_cache_payload_bytes_lower_bound =
            work.peak_cache_payload_bytes_lower_bound.max(cache_footprint(&nogoods));
    }
    for mask in rejected {
        if support.remove(&mask).is_none() {
            return Err("source-certified nogood was already removed".into());
        }
        work.baseline.removed_entries += 1;
    }
    Ok(())
}

fn run_with_baseline(
    case: Case, mode: CacheMode, reference: &super::super::Receipt,
    source: &[Factor], unguarded_unit: &super::Receipt,
) -> Result<Receipt, String> {
    let order = reference.order.clone();
    let start = Instant::now();
    let mut work = CacheWork::default();
    let mut leaves = Vec::with_capacity(source.len());
    for factor in source {
        leaves.push(Stage::leaf(
            factor, Strategy::IndexedSupport, &mut work.baseline.exact_arithmetic,
        )?);
    }
    let mut state = leaves[order[0]].clone();
    filter_with_cache(&mut state, source, &order, 0, mode, &mut work)?;
    for (step, &index) in order.iter().enumerate().skip(1) {
        let kept = kept_after(source, &order, step, &state.ports,
            &leaves[index].ports, &[]);
        state = state.merge_sparse(
            &leaves[index], &kept, &mut work.baseline.exact_arithmetic,
        )?;
        filter_with_cache(&mut state, source, &order, step, mode, &mut work)?;
    }
    if !state.ports.is_empty() { return Err("nogood study expected closed output".into()); }
    let answer = state.get(0);
    let unguarded_sparse = reference.variants.iter()
        .find(|r| r.strategy == Strategy::IndexedSupport)
        .ok_or("missing independently checked sparse reference")?;
    if answer != reference.source_satisfying_count ||
        answer != unguarded_unit.satisfying_count ||
        answer != unguarded_sparse.satisfying_count
    {
        return Err(format!("cached source refutation changed exact #SAT for {}",
            case.label()));
    }
    Ok(Receipt {
        case, mode, order, final_count: answer,
        expected_count: reference.source_satisfying_count.clone(),
        elapsed_ns: start.elapsed().as_nanos(),
        same_case_uncached_unit_elapsed_ns: unguarded_unit.elapsed_ns,
        same_case_sparse_elapsed_ns: unguarded_sparse.elapsed_ns,
        same_case_uncached_exact_mult:
            unguarded_unit.work.exact_arithmetic.multiplications,
        same_case_sparse_exact_mult:
            unguarded_sparse.work.multiplications,
        work, oracle: "checked",
    })
}

pub fn run_modes(case: Case) -> Result<Vec<Receipt>, String> {
    let reference = super::super::run_case(case)?;
    let source = adaptive::source_case(case)?;
    let uncached = super::run_with_baseline(
        case, Mode::Unit, &reference, &source)?;
    CacheMode::ALL.into_iter().map(|mode|
        run_with_baseline(case, mode, &reference, &source, &uncached)).collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    fn factor(ports: &[&str], clauses: &[&[(&str, bool)]]) -> Factor {
        let constraints = clauses.iter().map(|clause| Constraint::Clause(
            clause.iter().map(|(name, sign)| ((*name).into(), *sign)).collect()
        )).collect();
        Factor {
            ports: ports.iter().map(|s| (*s).into()).collect(),
            constraints,
        }
    }

    #[test]
    fn checked_two_literal_nogood_reused_under_extra_assumptions() {
        // Under p=0,q=0 the future forces x and ~x. The original
        // boundary includes r, which the source proof does not need.
        let factors = vec![
            factor(&["p", "q", "r"], &[]),
            factor(&["p", "q", "x"], &[&[
                ("p", true), ("q", true), ("x", true),
            ]]),
            factor(&["p", "q", "x"], &[&[
                ("p", true), ("q", true), ("x", false),
            ]]),
        ];
        let order = [0, 1, 2];
        let mut m = Metrics::default();
        let original = Stage::leaf(&factors[0], Strategy::IndexedSupport, &mut m)
            .unwrap();
        let mut full = original.clone();
        let mut shrunk = original;
        let mut cost_full = CacheWork::default();
        let mut cost_shrunk = CacheWork::default();
        filter_with_cache(&mut full, &factors, &order, 0,
            CacheMode::FullAssignment, &mut cost_full).unwrap();
        filter_with_cache(&mut shrunk, &factors, &order, 0,
            CacheMode::MinimizedAssumptions, &mut cost_shrunk).unwrap();
        assert_eq!(full.entries(), 6);
        assert_eq!(shrunk.entries(), 6);
        assert_eq!(cost_full.cache_hits, 0);
        assert!(cost_shrunk.cache_hits > 0);
        assert!(cost_shrunk.minimized_removed_assumptions > 0);
        for mask in 0..8 {
            assert_eq!(full.get(mask), shrunk.get(mask));
        }
    }

    #[test]
    fn reused_proof_cannot_escape_its_future_source_scope() {
        // p=false is impossible only while the two source clauses
        // are BOTH in the future. After one is absorbed, no
        // contradiction may be sourced from a stale previous frontier.
        let factors = vec![
            factor(&["p"], &[]),
            factor(&["p", "x"], &[&[("p", true), ("x", true)]]),
            factor(&["p", "x"], &[&[("p", true), ("x", false)]]),
        ];
        let mut metrics = Metrics::default();
        let original = Stage::leaf(&factors[0], Strategy::IndexedSupport, &mut metrics)
            .unwrap();
        let mut first = original.clone();
        let mut first_work = CacheWork::default();
        filter_with_cache(&mut first, &factors, &[0, 1, 2], 0,
            CacheMode::MinimizedAssumptions, &mut first_work).unwrap();
        assert_eq!(first.entries(), 1);
        let mut later = original;
        let mut later_work = CacheWork::default();
        filter_with_cache(&mut later, &factors, &[0, 1, 2], 1,
            CacheMode::MinimizedAssumptions, &mut later_work).unwrap();
        assert_eq!(later.entries(), 2);
        assert_eq!(later_work.cache_hits, 0);
    }

    #[test]
    fn invalid_cached_proof_fails_independent_replay() {
        let clauses = vec![
            vec![("x".into(), true), ("y".into(), false)],
        ];
        let lie = UnitRefutation {
            forced: vec![Step {
                reason: 0, variable: "x".into(), value: true,
            }],
            empty_reason: 0,
        };
        let mut metrics = CacheWork::default();
        assert!(replay_checked(&clauses, &BTreeMap::new(), &lie, &mut metrics)
            .is_err());
    }

    #[test]
    fn no_source_certificate_means_no_pruning() {
        let factors = vec![
            factor(&["p", "q"], &[]),
            factor(&["p", "q"], &[&[
                ("p", true), ("q", true),
            ]]),
        ];
        let mut metrics = Metrics::default();
        let mut stage = Stage::leaf(&factors[0], Strategy::IndexedSupport,
            &mut metrics).unwrap();
        let mut work = CacheWork::default();
        filter_with_cache(&mut stage, &factors, &[0, 1], 0,
            CacheMode::MinimizedAssumptions, &mut work).unwrap();
        assert_eq!(stage.entries(), 4);
        assert_eq!(work.baseline.removed_entries, 0);
    }
}
