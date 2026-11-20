//! Early source-derived CNF contradiction certificates during exact #SAT.
//!
//! The witness is a replayable chain of unit implications with original
//! source-clause indices followed by an all-false clause. A bounded
//! one-variable split accepts only when *both* branches have such traces.
//! Witnesses are checked by a separate reason checker before any pruning.
//!
//! This is a contextual #SAT optimization: the pruned intermediate support
//! is intentionally NOT the exact processed-prefix boundary function.
//! It is exact for the FINAL formula only because every omitted entry has
//! a checked contradiction in future source clauses under its retained
//! boundary assignment. Never reuse such a stage as a standalone prefix
//! polynomial or for positive-energy optimization.

use super::*;
use std::time::Instant;

const MAX_CLAUSE_VISITS: u64 = 100_000;
const MAX_QUERIES: u64 = 4_096;
const MAX_FUTURE_CLAUSES: usize = 64;
const MAX_SPLIT_PROBES: usize = 1;

type Literal = (String, bool);
type Clause = Vec<Literal>;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Mode {
    Unit,
    OneSplit,
}

impl Mode {
    pub const ALL: [Self; 2] = [Self::Unit, Self::OneSplit];
    pub fn name(self) -> &'static str {
        match self { Self::Unit => "unit-refutation", Self::OneSplit => "one-split-refutation" }
    }
}

#[derive(Clone, Debug)]
struct Step {
    reason: usize,
    variable: String,
    value: bool,
}

#[derive(Clone, Debug)]
struct UnitRefutation {
    forced: Vec<Step>,
    empty_reason: usize,
}

#[derive(Clone, Debug)]
enum Witness {
    Unit(UnitRefutation),
    Split {
        variable: String,
        false_branch: UnitRefutation,
        true_branch: UnitRefutation,
    },
}

#[derive(Clone, Debug, Default)]
pub struct CertificateWork {
    pub queries: u64,
    pub future_clause_collections: u64,
    pub source_clause_copies: u64,
    pub copied_literal_instances: u64,
    pub clause_visits: u64,
    pub literal_reads: u64,
    pub derived_units: u64,
    pub split_probes: u64,
    pub source_leaf_assignments: u64,
    pub checked_reason_literals: u64,
    pub checked_steps: u64,
    pub independently_checked_witnesses: u64,
    pub unit_refutations: u64,
    pub two_branch_refutations: u64,
    pub removed_entries: u64,
    pub source_rejects: u64,
    pub budget_skips: u64,
    pub unsupported_refusals: u64,
    pub exact_merges: u64,
    pub exact_arithmetic: Metrics,
}

#[derive(Clone, Debug)]
pub struct Receipt {
    pub case: Case,
    pub mode: Mode,
    pub order: Vec<usize>,
    pub elapsed_ns: u128,
    pub satisfying_count: BigUint,
    pub unguarded_sparse_count: BigUint,
    pub work: CertificateWork,
    pub independent_oracle: &'static str,
}

enum Search {
    Open,
    Budget,
    Refuted(UnitRefutation),
}

fn future_clauses(factors: &[Factor], order: &[usize], step: usize,
    m: &mut CertificateWork) -> Result<Vec<Clause>, String>
{
    m.future_clause_collections += 1;
    let mut clauses = Vec::new();
    for &idx in &order[step + 1..] {
        for constraint in &factors[idx].constraints {
            match constraint {
                Constraint::Clause(literals) => {
                    m.source_clause_copies += 1;
                    m.copied_literal_instances += literals.len() as u64;
                    clauses.push(literals.clone());
                },
                Constraint::Parity(_, _) =>
                    return Err("source UP adapter refuses non-CNF parity factors".into()),
            }
        }
    }
    Ok(clauses)
}

/// One deterministic unit-resolution run. It may return "open", but
/// open is NEVER interpreted as satisfiability. Budget exhaustion also
/// means "no pruning"; it cannot change the exact count.
fn derive(clauses: &[Clause], seed: &BTreeMap<String, bool>, m: &mut CertificateWork)
    -> Search
{
    let mut known = seed.clone();
    let mut forced = Vec::new();
    loop {
        let mut next = None;
        for (reason, clause) in clauses.iter().enumerate() {
            if m.clause_visits >= MAX_CLAUSE_VISITS { return Search::Budget; }
            m.clause_visits += 1;
            let mut satisfied = false;
            let mut unbound = 0usize;
            let mut last_open = None;
            for (name, desired) in clause {
                m.literal_reads += 1;
                match known.get(name) {
                    Some(value) if *value == *desired => {
                        satisfied = true;
                        break;
                    }
                    Some(_) => (),
                    None => {
                        unbound += 1;
                        last_open = Some((name.clone(), *desired));
                    }
                }
            }
            if satisfied { continue; }
            if unbound == 0 {
                return Search::Refuted(UnitRefutation {
                    forced, empty_reason: reason,
                });
            }
            if unbound == 1 {
                let (variable, value) = last_open.expect("one unbound literal");
                next = Some(Step { reason, variable, value });
                break;
            }
        }
        let Some(step) = next else { return Search::Open };
        // A derived step must have exactly one unbound literal, hence it
        // cannot override an existing assignment.
        known.insert(step.variable.clone(), step.value);
        m.derived_units += 1;
        forced.push(step);
    }
}

/// Independent certificate checker: original source clauses are re-evaluated
/// only at the explicit reason indices, without calling the searcher's
/// "unit" classifier or trusting its cached resulting assignments.
fn check_refutation(
    clauses: &[Clause], seed: &BTreeMap<String, bool>,
    trace: &UnitRefutation, m: &mut CertificateWork,
) -> Result<(), String> {
    let mut values = seed.clone();
    for step in &trace.forced {
        let clause = clauses.get(step.reason)
            .ok_or("invalid original clause index in unit witness")?;
        let mut open = 0usize;
        let mut only_open = None;
        let mut has_true = false;
        for (name, sign) in clause {
            m.checked_reason_literals += 1;
            match values.get(name) {
                Some(v) if *v == *sign => has_true = true,
                Some(_) => (),
                None => {
                    open += 1;
                    only_open = Some((name.as_str(), *sign));
                }
            }
        }
        if has_true || open != 1 ||
            only_open != Some((step.variable.as_str(), step.value)) ||
            values.contains_key(&step.variable)
        {
            return Err("invalid unit-propagation reason in certificate".into());
        }
        values.insert(step.variable.clone(), step.value);
        m.checked_steps += 1;
    }
    let empty = clauses.get(trace.empty_reason)
        .ok_or("invalid empty-clause source index")?;
    for (name, sign) in empty {
        m.checked_reason_literals += 1;
        if values.get(name).is_none_or(|value| *value == *sign) {
            return Err("terminal clause is not false under certified assignments".into());
        }
    }
    m.independently_checked_witnesses += 1;
    Ok(())
}

fn check_witness(
    clauses: &[Clause], initial: &BTreeMap<String, bool>,
    witness: &Witness, m: &mut CertificateWork,
) -> Result<(), String> {
    match witness {
        Witness::Unit(trace) => check_refutation(clauses, initial, trace, m),
        Witness::Split { variable, false_branch, true_branch } => {
            m.checked_reason_literals += clauses.iter().map(|c| c.len() as u64).sum::<u64>();
            if initial.contains_key(variable) ||
                !clauses.iter().flatten().any(|(name, _)| name == variable)
            {
                return Err("invalid split variable or already assigned".into());
            }
            let mut left = initial.clone();
            left.insert(variable.clone(), false);
            check_refutation(clauses, &left, false_branch, m)?;
            let mut right = initial.clone();
            right.insert(variable.clone(), true);
            check_refutation(clauses, &right, true_branch, m)
        }
    }
}

fn highest_frequency_unfixed(
    clauses: &[Clause], fixed: &BTreeMap<String, bool>,
    m: &mut CertificateWork,
) -> Option<String> {
    let mut frequency = BTreeMap::<String, usize>::new();
    for clause in clauses {
        for (name, _) in clause {
            m.literal_reads += 1;
            if !fixed.contains_key(name) {
                *frequency.entry(name.clone()).or_default() += 1;
            }
        }
    }
    frequency.into_iter()
        .max_by(|(a, ac), (b, bc)| ac.cmp(bc).then_with(|| b.cmp(a)))
        .map(|(name, _)| name)
}

/// A source-only contradiction certificate with a fixed probe budget.
/// When probing does not produce both branch refutations, no state is
/// removed. Failure to prove unsat is NEVER treated as a proof of sat.
fn detect(
    clauses: &[Clause], initial: &BTreeMap<String, bool>,
    mode: Mode, m: &mut CertificateWork,
) -> Option<Witness> {
    match derive(clauses, initial, m) {
        Search::Refuted(trace) => return Some(Witness::Unit(trace)),
        Search::Open if mode == Mode::Unit => return None,
        Search::Budget => { m.budget_skips += 1; return None; }
        Search::Open => (),
    }
    let Some(var) = highest_frequency_unfixed(clauses, initial, m) else { return None; };
    for _ in 0..MAX_SPLIT_PROBES {
        let mut assumptions = initial.clone();
        assumptions.insert(var.clone(), false);
        m.split_probes += 1;
        let Search::Refuted(false_branch) = derive(clauses, &assumptions, m)
            else { return None; };
        assumptions.insert(var.clone(), true);
        m.split_probes += 1;
        let Search::Refuted(true_branch) = derive(clauses, &assumptions, m)
            else { return None; };
        return Some(Witness::Split {
            variable: var, false_branch, true_branch,
        });
    }
    None
}

fn filter_stage(
    stage: &mut Stage, factors: &[Factor], order: &[usize], step: usize,
    mode: Mode, m: &mut CertificateWork,
) -> Result<(), String> {
    let clauses = future_clauses(factors, order, step, m)?;
    if clauses.is_empty() { return Ok(()); }
    if clauses.len() > MAX_FUTURE_CLAUSES {
        m.budget_skips += 1;
        return Ok(());
    }
    let Values::Sparse(support) = &mut stage.values else {
        return Err("early contradiction checker requires sparse exact support".into());
    };
    let mut rejected = Vec::new();
    for &mask in support.keys() {
        if m.queries >= MAX_QUERIES || m.clause_visits >= MAX_CLAUSE_VISITS {
            m.budget_skips += 1;
            break;
        }
        let initial = stage.ports.iter().enumerate()
            .map(|(i, var)| (var.clone(), mask & (1 << i) != 0))
            .collect::<BTreeMap<_, _>>();
        m.queries += 1;
        let Some(witness) = detect(&clauses, &initial, mode, m) else {
            continue;
        };
        // A failed check is a correctness error, never permission to prune.
        check_witness(&clauses, &initial, &witness, m)?;
        match witness {
            Witness::Unit(_) => m.unit_refutations += 1,
            Witness::Split { .. } => m.two_branch_refutations += 1,
        }
        rejected.push(mask);
    }
    for mask in rejected {
        if support.remove(&mask).is_none() {
            return Err("already deleted certified support entry".into());
        }
        m.removed_entries += 1;
    }
    Ok(())
}

/// The resulting stage is only required to preserve the FINAL global #SAT
/// count. Intermediate stages intentionally discard processed-prefix
/// solutions incompatible with future factors.
fn run_with_baseline(
    case: Case, mode: Mode, baseline: &super::Receipt, original: &[Factor],
) -> Result<Receipt, String> {
    let order = baseline.order.clone();
    let start = Instant::now();
    let mut m = CertificateWork::default();
    let mut leaves = Vec::new();
    for factor in original {
        leaves.push(Stage::leaf(
            factor, Strategy::IndexedSupport, &mut m.exact_arithmetic,
        )?);
    }
    m.source_leaf_assignments = m.exact_arithmetic.source_leaf_assignments;
    m.source_rejects = m.exact_arithmetic.source_leaf_rejections;
    let mut stage = leaves[order[0]].clone();
    filter_stage(&mut stage, &original, &order, 0, mode, &mut m)?;
    for (step, &index) in order.iter().enumerate().skip(1) {
        let kept = kept_after(
            &original, &order, step, &stage.ports, &leaves[index].ports, &[],
        );
        stage = stage.merge_sparse(
            &leaves[index], &kept, &mut m.exact_arithmetic,
        )?;
        m.exact_merges += 1;
        filter_stage(&mut stage, &original, &order, step, mode, &mut m)?;
    }
    if !stage.ports.is_empty() {
        return Err("certificate experiment expected a closed boundary".into());
    }
    let count = stage.get(0);
    if count != baseline.source_satisfying_count {
        return Err(format!(
            "source certificate pruning changed exact count: {} expected {} for {}",
            count, baseline.source_satisfying_count, case.label()
        ));
    }
    let elapsed_ns = start.elapsed().as_nanos();
    let unguarded_sparse_count = baseline.variants.iter()
        .find(|v| v.strategy == Strategy::IndexedSupport)
        .ok_or("no unguarded support baseline")?.satisfying_count.clone();
    Ok(Receipt {
        case, mode, order, elapsed_ns, satisfying_count: count,
        unguarded_sparse_count, work: m, independent_oracle: "checked",
    })
}

/// Reuse one independently checked source/full-polynomial baseline for both
/// certificate modes; neither source oracle nor full polynomial is part
/// of the measured certificate variant's fold time.
pub fn run_modes(case: Case) -> Result<Vec<Receipt>, String> {
    let baseline = super::run_case(case)?;
    let original = adaptive::source_case(case)?;
    Mode::ALL.into_iter().map(|mode|
        run_with_baseline(case, mode, &baseline, &original)).collect()
}

pub fn run_case(case: Case, mode: Mode) -> Result<Receipt, String> {
    let baseline = super::run_case(case)?;
    let original = adaptive::source_case(case)?;
    run_with_baseline(case, mode, &baseline, &original)
}

#[cfg(test)]
mod tests {
    use super::*;
    fn factor(ports: &[&str], clauses: &[&[(&str, bool)]]) -> Factor {
        let ports = ports.iter().map(|s| (*s).to_owned()).collect();
        let constraints = clauses.iter().map(|clause| Constraint::Clause(
            clause.iter().map(|(name, value)| (name.to_string(), *value)).collect(),
        )).collect();
        Factor { ports, constraints }
    }

    #[test]
    fn direct_unit_conflict_is_checked_and_prunes_before_counting() {
        // Under p=false, (p∨x) and (p∨¬x) cannot both hold.
        let factors = vec![
            factor(&["p"], &[]),
            factor(&["p", "x"], &[&[("p", true), ("x", true)]]),
            factor(&["p", "x"], &[&[("p", true), ("x", false)]]),
        ];
        let order = vec![0, 1, 2];
        let mut metrics = Metrics::default();
        let mut stage = Stage::leaf(&factors[0], Strategy::IndexedSupport, &mut metrics).unwrap();
        let mut cert = CertificateWork::default();
        filter_stage(&mut stage, &factors, &order, 0, Mode::Unit, &mut cert).unwrap();
        assert_eq!(cert.removed_entries, 1);
        assert_eq!(cert.unit_refutations, 1);
        assert_eq!(stage.get(0), BigUint::default());
        assert_eq!(stage.get(1), BigUint::from(1u8));
    }

    #[test]
    fn two_branch_proof_detects_unsat_without_initial_units() {
        // Under p=false these four clauses form the classical unsat
        // two-variable four-clause core. No initial UP step exists, but
        // either x value yields opposite forced y values.
        let factors = vec![
            factor(&["p"], &[]),
            factor(&["p", "x", "y"], &[&[("p", true), ("x", true), ("y", true)]]),
            factor(&["p", "x", "y"], &[&[("p", true), ("x", true), ("y", false)]]),
            factor(&["p", "x", "y"], &[&[("p", true), ("x", false), ("y", true)]]),
            factor(&["p", "x", "y"], &[&[("p", true), ("x", false), ("y", false)]]),
        ];
        let order = vec![0, 1, 2, 3, 4];
        let mut m = Metrics::default();
        let mut unit = Stage::leaf(&factors[0], Strategy::IndexedSupport, &mut m).unwrap();
        let mut split = unit.clone();
        let mut unit_stats = CertificateWork::default();
        let mut split_stats = CertificateWork::default();
        filter_stage(&mut unit, &factors, &order, 0, Mode::Unit, &mut unit_stats).unwrap();
        filter_stage(&mut split, &factors, &order, 0, Mode::OneSplit, &mut split_stats).unwrap();
        assert_eq!(unit_stats.removed_entries, 0);
        assert_eq!(split_stats.removed_entries, 1);
        assert_eq!(split_stats.two_branch_refutations, 1);
        assert_eq!(split.get(0), BigUint::default());
        assert_eq!(split.get(1), BigUint::from(1u8));
    }

    #[test]
    fn fabricated_certificate_is_rejected() {
        let clauses = vec![vec![("x".into(), true), ("y".into(), true)]];
        let fake = Witness::Unit(UnitRefutation {
            forced: vec![Step {
                reason: 0, variable: "x".into(), value: true,
            }],
            empty_reason: 0,
        });
        let mut m = CertificateWork::default();
        assert!(check_witness(&clauses, &BTreeMap::new(), &fake, &mut m).is_err());
    }

    #[test]
    fn checked_predictions_preserve_original_oracle_on_generated_cases() {
        for case in [
            Case { kind: adaptive::CaseKind::Random3Cnf,
                variables: 6, clauses: 12, seed: 1009 },
            Case { kind: adaptive::CaseKind::Planted3Cnf,
                variables: 6, clauses: 24, seed: 13009 },
            Case { kind: adaptive::CaseKind::FrustratedXor3Cnf,
                variables: 6, clauses: 24, seed: 0 },
        ] {
            for mode in Mode::ALL {
                let r = run_case(case, mode).unwrap();
                assert_eq!(r.satisfying_count, r.unguarded_sparse_count);
            }
        }
    }
}
