//! Online factor-admission ordering, using the same exact executor as the
//! three-representation study. Candidate previews belong to the planner's cost.
//!
//! A bounded pilot, not an asymptotic improvement or a generic treewidth
//! optimizer. The min-fill baseline measures induced fill for dead-port
//! elimination in a LEFT fold (not a general elimination-tree search).

use super::*;
use std::time::Instant;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Policy {
    Sequential,
    MinFillAdmission,
    TropicalZeroSupport,
    ExactPreview,
}

impl Policy {
    pub fn name(self) -> &'static str {
        match self {
            Self::Sequential => "sequential",
            Self::MinFillAdmission => "min-fill-admission",
            Self::TropicalZeroSupport => "tropical-zero-support",
            Self::ExactPreview => "exact-preview",
        }
    }

    pub const ALL: [Self; 4] = [
        Self::Sequential, Self::MinFillAdmission,
        Self::TropicalZeroSupport, Self::ExactPreview,
    ];
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum CaseKind {
    Random3Cnf,
    Planted3Cnf,
    FrustratedXor3Cnf,
}

impl CaseKind {
    pub fn name(self) -> &'static str {
        match self {
            Self::Random3Cnf => "random-3cnf",
            Self::Planted3Cnf => "planted-3cnf",
            Self::FrustratedXor3Cnf => "frustrated-xor3-cnf",
        }
    }
}

#[derive(Clone, Copy, Debug)]
pub struct Case {
    pub kind: CaseKind,
    pub variables: usize,
    pub clauses: usize,
    pub seed: u64,
}

impl Case {
    pub fn label(self) -> String {
        format!("{}-v{}-c{}-s{}", self.kind.name(),
            self.variables, self.clauses, self.seed)
    }
}

/// Fixed split, committed before viewing benchmark outcomes. No heuristic
/// parameter fitting or instance-selection based on held-out results.
pub fn held_out_cases() -> Vec<Case> {
    let mut cases = Vec::new();
    for variables in [6, 8, 10] {
        for seed in [1009, 2027] {
            for kind in [CaseKind::Random3Cnf, CaseKind::Planted3Cnf] {
                cases.push(Case { kind, variables, clauses: variables * 2, seed });
            }
        }
    }
    for variables in [4, 6, 8, 10] {
        cases.push(Case {
            kind: CaseKind::FrustratedXor3Cnf,
            variables,
            clauses: variables * 4,
            seed: 0,
        });
    }
    cases
}

#[derive(Clone, Debug)]
struct Lcg(u64);

impl Lcg {
    fn next(&mut self) -> u64 {
        self.0 = self.0.wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        self.0 ^ (self.0 >> 29)
    }

    fn choose(&mut self, upper: usize) -> usize {
        (self.next() % upper as u64) as usize
    }

    fn bit(&mut self) -> bool { self.next() & 1 != 0 }
}

fn source_case(case: Case) -> Result<Vec<Factor>, String> {
    if case.kind == CaseKind::FrustratedXor3Cnf {
        if case.clauses != case.variables * 4 || case.seed != 0 {
            return Err("invalid frustrated-ring case specification".into());
        }
        return generate(StudyFamily::FrustratedXor3Cnf, case.variables);
    }
    if !(4..=12).contains(&case.variables)
        || case.clauses < case.variables
        || case.clauses > case.variables * 4
    {
        return Err("random CNF specification outside bounded domain".into());
    }
    let mut rng = Lcg(case.seed ^ 0xD1B5_4A32_D192_ED03);
    let planted = (0..case.variables).map(|i| {
        (case.seed.rotate_left((i % 63) as u32) ^ i as u64).count_ones() & 1 != 0
    }).collect::<Vec<_>>();
    let mut factors = Vec::new();
    for i in 0..case.clauses {
        // First n clauses explicitly cover all declared variables. No
        // unseen or accidentally duplicated variable in the oracle domain.
        let mut ids = vec![i % case.variables];
        while ids.len() < 3 {
            let next = rng.choose(case.variables);
            if !ids.contains(&next) { ids.push(next); }
        }
        let mut literals = ids.iter().map(|&id| {
            (format!("x{id}"), rng.bit())
        }).collect::<Vec<_>>();
        if case.kind == CaseKind::Planted3Cnf
            && !ids.iter().enumerate().any(|(k, &id)| literals[k].1 == planted[id])
        {
            let k = rng.choose(3);
            literals[k].1 = planted[ids[k]];
        }
        let ports = literals.iter().map(|(name, _)| name.clone())
            .collect::<BTreeSet<_>>().into_iter().collect();
        let factor = Factor { ports, constraints: vec![Constraint::Clause(literals)] };
        factor.validate()?;
        factors.push(factor);
    }
    Ok(factors)
}

#[derive(Clone, Debug)]
struct TropicalStage {
    ports: Vec<String>,
    values: Vec<Option<Leading>>,
}

impl TropicalStage {
    fn from_leaf(t: &Tables) -> Self {
        Self { ports: t.ports.clone(), values: t.tropical.clone() }
    }

    fn merge(&self, other: &Self, kept: &[String], work: &mut Work)
        -> Result<Self, String>
    {
        let union = union_ports(&self.ports, &other.ports);
        let mut values = vec![None; count_masks(kept.len())?];
        for mask in 0..count_masks(union.len())? {
            let left = project(mask, &union, &self.ports);
            let right = project(mask, &union, &other.ports);
            let dest = project(mask, &union, kept);
            let product = tropical_mul(&self.values[left], &other.values[right], work)?;
            values[dest] = tropical_add(values[dest].take(), product, work);
        }
        Ok(Self { ports: kept.to_vec(), values })
    }

    fn zero_energy_cells(&self) -> usize {
        self.values.iter().flatten().filter(|v| v.energy == 0).count()
    }
}

#[derive(Clone, Debug)]
struct ExactStage {
    ports: Vec<String>,
    values: Vec<Polynomial>,
}

impl ExactStage {
    fn from_leaf(t: &Tables) -> Self {
        Self { ports: t.ports.clone(), values: t.exact.clone() }
    }

    fn merge(&self, other: &Self, kept: &[String], work: &mut Work)
        -> Result<Self, String>
    {
        let union = union_ports(&self.ports, &other.ports);
        let mut values = vec![Polynomial::default(); count_masks(kept.len())?];
        for mask in 0..count_masks(union.len())? {
            let left = project(mask, &union, &self.ports);
            let right = project(mask, &union, &other.ports);
            let dest = project(mask, &union, kept);
            let product = self.values[left].mul(&other.values[right], work);
            values[dest] = values[dest].add(&product, work);
        }
        Ok(Self { ports: kept.to_vec(), values })
    }

    fn coefficient_slots(&self) -> usize {
        self.values.iter().map(|x| x.0.len()).sum()
    }

    fn bit_payload_bytes(&self) -> usize {
        self.values.iter().flat_map(|poly| poly.0.iter())
            .map(|x| x.bits().div_ceil(8) as usize).sum()
    }
}

#[derive(Debug)]
struct Candidate {
    factor: usize,
    kept: Vec<String>,
    score: (u128, u128, u128, usize),
    exact: Option<ExactStage>,
    tropical: Option<TropicalStage>,
}

fn cliques(scope: &[String], graph: &mut BTreeMap<String, BTreeSet<String>>) {
    for v in scope {
        graph.entry(v.clone()).or_default();
    }
    for (i, a) in scope.iter().enumerate() {
        for b in scope.iter().skip(i + 1) {
            graph.entry(a.clone()).or_default().insert(b.clone());
            graph.entry(b.clone()).or_default().insert(a.clone());
        }
    }
}

/// Actual graph fill-in introduced by eliminating newly dead variables,
/// given the current accumulator clique and all remaining factor cliques.
fn fill_edges(
    active: &[String], remaining: &BTreeSet<usize>,
    leaves: &[Tables], kept: &[String], candidate: usize,
) -> usize {
    let mut graph = BTreeMap::<String, BTreeSet<String>>::new();
    cliques(active, &mut graph);
    for &index in remaining { cliques(&leaves[index].ports, &mut graph); }
    let union = union_ports(active, &leaves[candidate].ports);
    let dead = union.iter().filter(|v| kept.binary_search(v).is_err())
        .cloned().collect::<Vec<_>>();
    let mut fill = 0;
    for var in dead {
        let neighbors = graph.remove(&var).unwrap_or_default()
            .into_iter().collect::<Vec<_>>();
        for a in &neighbors {
            if let Some(adjacency) = graph.get_mut(a) { adjacency.remove(&var); }
        }
        for (i, a) in neighbors.iter().enumerate() {
            for b in neighbors.iter().skip(i + 1) {
                if !graph[a].contains(b) {
                    fill += 1;
                    graph.get_mut(a).expect("neighbor exists").insert(b.clone());
                    graph.get_mut(b).expect("neighbor exists").insert(a.clone());
                }
            }
        }
    }
    fill
}

fn add_work(total: &mut Work, more: &Work) {
    total.additions += more.additions;
    total.multiplications += more.multiplications;
    total.bit_work_proxy += more.bit_work_proxy;
    total.max_coefficient_bits = total.max_coefficient_bits.max(more.max_coefficient_bits);
}

#[derive(Debug)]
struct Plan {
    order: Vec<usize>,
    work: Work,
    candidates_examined: usize,
    planned_ns: u128,
    peak_preview_payload_bytes: usize,
}

fn make_plan(factors: &[Factor], policy: Policy) -> Result<Plan, String> {
    let clock = Instant::now();
    let leaves = factors.iter().map(Tables::from_factor)
        .collect::<Result<Vec<_>, _>>()?;
    let mut order = vec![0usize];
    let mut remaining = (1..leaves.len()).collect::<BTreeSet<_>>();
    let mut ports = leaves[0].ports.clone();
    let mut tropical = TropicalStage::from_leaf(&leaves[0]);
    let tropical_leaves = leaves.iter().map(TropicalStage::from_leaf)
        .collect::<Vec<_>>();
    let mut exact = ExactStage::from_leaf(&leaves[0]);
    let exact_leaves = leaves.iter().map(ExactStage::from_leaf)
        .collect::<Vec<_>>();
    let mut work = Work::default();
    let mut candidates_examined = 0usize;
    let mut peak_preview_payload_bytes = 0usize;
    let empty_output = BTreeSet::new();

    while !remaining.is_empty() {
        let mut best: Option<Candidate> = None;
        for &index in &remaining {
            candidates_examined += 1;
            let future = remaining.iter().filter(|&&j| j != index)
                .flat_map(|&j| leaves[j].ports.iter().cloned())
                .collect::<BTreeSet<_>>();
            let active = ports.iter().cloned().collect::<BTreeSet<_>>();
            let next = leaves[index].ports.iter().cloned().collect::<BTreeSet<_>>();
            let kept = affine_orders::kept_port_set(&active, &next, &future, &empty_output)
                .into_iter().collect::<Vec<_>>();
            let union = union_ports(&ports, &leaves[index].ports);
            let union_cells = count_masks(union.len())? as u128;
            let kept_cells = count_masks(kept.len())? as u128;

            let mut candidate_exact = None;
            let mut candidate_tropical = None;
            let score = match policy {
                Policy::Sequential => (index as u128, 0, 0, index),
                Policy::MinFillAdmission => (
                    fill_edges(&ports, &remaining, &leaves, &kept, index) as u128,
                    kept_cells, union_cells, index,
                ),
                Policy::TropicalZeroSupport => {
                    let mut preview = Work::default();
                    let next = tropical.merge(&tropical_leaves[index], &kept, &mut preview)?;
                    add_work(&mut work, &preview);
                    // The 4:1 penalty was fixed before evaluating held-out
                    // cases. Positive minimum energy may discard ZERO-only
                    // contributions, but not the entire exact polynomial.
                    let zero_cells = next.zero_energy_cells() as u128;
                    let score = (kept_cells + 4 * zero_cells, union_cells,
                        preview.multiplications as u128, index);
                    candidate_tropical = Some(next);
                    score
                }
                Policy::ExactPreview => {
                    let mut preview = Work::default();
                    let next = exact.merge(&exact_leaves[index], &kept, &mut preview)?;
                    add_work(&mut work, &preview);
                    peak_preview_payload_bytes = peak_preview_payload_bytes.max(
                        exact.bit_payload_bytes() + next.bit_payload_bytes());
                    // Exact-only baseline pays for every discarded candidate
                    // full-polynomial preview and does not use tropical data.
                    let score = (
                        preview.bit_work_proxy,
                        next.coefficient_slots() as u128,
                        union_cells, index,
                    );
                    candidate_exact = Some(next);
                    score
                }
            };
            let replacement = best.as_ref().is_none_or(|previous| score < previous.score);
            if replacement {
                best = Some(Candidate {
                    factor: index, kept, score,
                    exact: candidate_exact, tropical: candidate_tropical,
                });
            }
        }
        let winner = best.ok_or("planner has no legal candidate")?;
        remaining.remove(&winner.factor);
        order.push(winner.factor);
        ports = winner.kept;
        if let Some(stage) = winner.exact { exact = stage; }
        if let Some(stage) = winner.tropical { tropical = stage; }
    }

    Ok(Plan {
        order, work, candidates_examined,
        planned_ns: clock.elapsed().as_nanos(),
        peak_preview_payload_bytes,
    })
}

#[derive(Debug)]
pub struct AdaptiveReceipt {
    pub case: Case,
    pub policy: Policy,
    pub order: Vec<usize>,
    pub candidates_examined: usize,
    pub planning_elapsed_ns: u128,
    pub planning_work: Work,
    pub peak_preview_coefficient_payload_bytes: usize,
    pub exact_elapsed_ns: u128,
    pub exact: Receipt,
}

pub fn evaluate(case: Case, policy: Policy) -> Result<AdaptiveReceipt, String> {
    let factors = source_case(case)?;
    let plan = make_plan(&factors, policy)?;
    let started = Instant::now();
    let exact = execute_order(&factors, case.kind.name(), factors.len(),
        policy.name(), &plan.order, &[])?;
    let exact_elapsed_ns = started.elapsed().as_nanos();
    Ok(AdaptiveReceipt {
        case, policy, order: plan.order,
        candidates_examined: plan.candidates_examined,
        planning_elapsed_ns: plan.planned_ns,
        planning_work: plan.work,
        peak_preview_coefficient_payload_bytes: plan.peak_preview_payload_bytes,
        exact_elapsed_ns, exact,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn held_out_split_is_fixed_and_distinct() {
        let cases = held_out_cases();
        assert_eq!(cases.len(), 16);
        assert_eq!(cases.iter().map(|c| c.label()).collect::<BTreeSet<_>>().len(), 16);
        assert!(cases.iter().filter(|c| c.kind != CaseKind::FrustratedXor3Cnf)
            .all(|c| c.seed >= 1000));
    }

    #[test]
    fn all_policies_compute_same_source_count_on_small_instances() {
        for case in [
            Case { kind: CaseKind::Random3Cnf, variables: 6, clauses: 12, seed: 1009 },
            Case { kind: CaseKind::Planted3Cnf, variables: 6, clauses: 12, seed: 2027 },
            Case { kind: CaseKind::FrustratedXor3Cnf, variables: 6, clauses: 24, seed: 0 },
        ] {
            let values = Policy::ALL.map(|p| evaluate(case, p).unwrap());
            for trace in values.iter().skip(1) {
                assert_eq!(trace.exact.minimum_energy, values[0].exact.minimum_energy);
                assert_eq!(trace.exact.minimum_count, values[0].exact.minimum_count);
                assert_eq!(trace.exact.satisfying_count, values[0].exact.satisfying_count);
                assert_eq!(trace.order.len(), trace.exact.size);
                assert_eq!(trace.order.iter().copied().collect::<BTreeSet<_>>().len(),
                    trace.order.len());
            }
            assert!(values[2].planning_work.multiplications > 0);
            assert!(values[3].planning_work.multiplications > 0);
            assert_eq!(values[1].planning_work.multiplications, 0);
        }
    }
}
