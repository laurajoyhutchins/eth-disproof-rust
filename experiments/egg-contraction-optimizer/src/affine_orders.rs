//! Reproducible, fail-closed contraction-order experiments for exact affine
//! interfaces. D and B describe *this explicit representation*, not the
//! smallest possible circuit and not a general #SAT complexity theorem.
//!
//! Only ports absent from every remaining factor and from the chosen output
//! may be eliminated. Reordering without that liveness rule is unsound.

use crate::affine::{AffineRegion, Equation};
use crate::affine_planner::{Stage, StageMetrics};
use num_bigint::BigUint;
use std::collections::{BTreeMap, BTreeSet};

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Family {
    Chain,
    CirculantXor3,
}

impl Family {
    pub fn name(self) -> &'static str {
        match self {
            Self::Chain => "chain-equality",
            Self::CirculantXor3 => "circulant-xor3",
        }
    }
}

/// A factorized family with exact affine equations. The generator does not
/// assert that the circulant family is an expander.
pub fn generate(family: Family, size: usize) -> Result<Vec<AffineRegion>, String> {
    if !(3..=256).contains(&size) {
        return Err("size must be between 3 and 256".into());
    }
    let mut factors = Vec::with_capacity(size);
    for i in 0..size {
        let (scope, rhs) = match family {
            Family::Chain => (
                vec![format!("x{i}"), format!("x{}", i + 1)],
                false,
            ),
            Family::CirculantXor3 => {
                let stride = (size / 2).max(2);
                let indices = [i, (i + 1) % size, (i + stride) % size];
                let rhs = indices.iter().fold(false, |acc, &j| acc ^ (j % 3 == 0));
                (indices.iter().map(|j| format!("x{j}")).collect(), rhs)
            }
        };
        factors.push(AffineRegion {
            internal: Vec::new(),
            boundary: scope.clone(),
            equations: vec![Equation { variables: scope, rhs }],
        });
    }
    Ok(factors)
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Schedule {
    Sequential,
    Reverse,
    EvenFirst,
}

impl Schedule {
    pub fn name(self) -> &'static str {
        match self {
            Self::Sequential => "sequential",
            Self::Reverse => "reverse",
            Self::EvenFirst => "even-first",
        }
    }

    pub fn indices(self, size: usize) -> Vec<usize> {
        match self {
            Self::Sequential => (0..size).collect(),
            Self::Reverse => (0..size).rev().collect(),
            Self::EvenFirst => (0..size).step_by(2)
                .chain((1..size).step_by(2)).collect(),
        }
    }
}

#[derive(Clone, Debug)]
pub struct Limits {
    pub max_factors: usize,
    pub max_merge_cells: usize,
    pub max_total_merge_cells: usize,
}

impl Default for Limits {
    fn default() -> Self {
        Self {
            max_factors: 256,
            max_merge_cells: 2_000_000,
            max_total_merge_cells: 16_000_000,
        }
    }
}

#[derive(Clone, Debug)]
pub struct Step {
    pub index: usize,
    pub absorbed_factor: usize,
    pub metrics: StageMetrics,
    /// Number of cells in the newly constructed dense logical matrix.
    /// This is a proxy for input footprint, not peak RSS or bit operations.
    pub merge_matrix_cells: usize,
    pub cumulative_merge_cells: usize,
    pub cumulative_xors: usize,
    pub cumulative_replay_steps: usize,
}

#[derive(Clone, Debug)]
pub struct Trace {
    pub schedule: Option<Schedule>,
    pub steps: Vec<Step>,
    pub stage: Stage,
    pub peak_d: usize,
    pub peak_b: usize,
    pub sum_d: usize,
    pub sum_merge_matrix_cells: usize,
    pub sum_xors: usize,
    pub sum_replay_steps: usize,
}

/// Exact left-fold for an explicit permutation of the same factor network.
/// The permutation changes work and transient representation, not semantics.
pub fn fold(
    factors: &[AffineRegion],
    order: &[usize],
    output: &[String],
    limits: &Limits,
) -> Result<Trace, String> {
    if factors.len() < 2 || factors.len() > limits.max_factors {
        return Err("factor count outside configured limits".into());
    }
    if order.len() != factors.len() {
        return Err("schedule does not cover every factor".into());
    }
    let mut covered = vec![false; factors.len()];
    for &i in order {
        if i >= covered.len() || covered[i] {
            return Err("invalid or repeated factor index in schedule".into());
        }
        covered[i] = true;
    }

    // The same leaf interfaces are reused mathematically for all schedules.
    // Leaf construction and verification cost is not included in merge costs.
    let mut leaves = Vec::with_capacity(factors.len());
    let mut declared_ports = BTreeSet::new();
    for factor in factors {
        let leaf = Stage::from_region(factor)?;
        declared_ports.extend(leaf.interface.boundary.iter().cloned());
        leaves.push(leaf);
    }
    let outputs: BTreeSet<_> = output.iter().cloned().collect();
    if outputs.len() != output.len() || !outputs.is_subset(&declared_ports) {
        return Err("output must be a unique subset of declared ports".into());
    }

    let mut stage = leaves[order[0]].clone();
    let mut peak_d = stage.metrics.d;
    let mut peak_b = stage.metrics.b;
    let mut sum_d = stage.metrics.d;
    let (mut sum_cells, mut sum_xors, mut sum_steps) = (0usize, 0usize, 0usize);
    let mut steps = vec![Step {
        index: 0, absorbed_factor: order[0],
        metrics: stage.metrics.clone(), merge_matrix_cells: 0,
        cumulative_merge_cells: 0, cumulative_xors: 0, cumulative_replay_steps: 0,
    }];

    for (step_index, &leaf_index) in order.iter().enumerate().skip(1) {
        let leaf = &leaves[leaf_index];
        let mut live = outputs.clone();
        // A port is live if any not-yet-merged factor needs it, even when
        // the two currently merged regions share that port.
        for &remaining in &order[step_index + 1..] {
            live.extend(leaves[remaining].interface.boundary.iter().cloned());
        }
        let union = stage.interface.boundary.iter()
            .chain(&leaf.interface.boundary)
            .cloned().collect::<BTreeSet<_>>();
        let kept = union.intersection(&live).cloned().collect::<Vec<_>>();

        let rows = stage.interface.residual.len()
            .checked_add(leaf.interface.residual.len())
            .ok_or("row count overflow")?;
        let cols = union.len().checked_add(1).ok_or("matrix width overflow")?;
        let cells = rows.checked_mul(cols).ok_or("matrix cell count overflow")?;
        if cells > limits.max_merge_cells {
            return Err(format!("merge matrix cell limit exceeded at step {step_index}"));
        }
        sum_cells = sum_cells.checked_add(cells).ok_or("cumulative matrix cell overflow")?;
        if sum_cells > limits.max_total_merge_cells {
            return Err(format!("cumulative matrix cell limit exceeded at step {step_index}"));
        }
        stage = stage.merge(leaf, &kept)?;
        sum_xors = sum_xors.checked_add(stage.metrics.elimination_xors)
            .ok_or("cumulative XOR overflow")?;
        sum_steps = sum_steps.checked_add(stage.metrics.certificate_steps)
            .ok_or("cumulative replay-step overflow")?;
        sum_d = sum_d.checked_add(stage.metrics.d).ok_or("cumulative D overflow")?;
        peak_d = peak_d.max(stage.metrics.d);
        peak_b = peak_b.max(stage.metrics.b);
        steps.push(Step {
            index: step_index, absorbed_factor: leaf_index,
            metrics: stage.metrics.clone(), merge_matrix_cells: cells,
            cumulative_merge_cells: sum_cells,
            cumulative_xors: sum_xors, cumulative_replay_steps: sum_steps,
        });
    }
    let final_ports = stage.interface.boundary.iter().cloned().collect::<BTreeSet<_>>();
    if final_ports != outputs {
        return Err("final live boundary differs from requested output".into());
    }
    Ok(Trace {
        schedule: [Schedule::Sequential, Schedule::Reverse, Schedule::EvenFirst]
            .into_iter().find(|candidate| candidate.indices(factors.len()) == order),
        steps, stage, peak_d, peak_b, sum_d,
        sum_merge_matrix_cells: sum_cells, sum_xors, sum_replay_steps: sum_steps,
    })
}

/// Independent Boolean enumeration of the *original* input equations.
/// Explicitly bounded to small examples, never a hidden execution fallback.
pub fn oracle(
    factors: &[AffineRegion],
    output: &BTreeMap<String, bool>,
    max_variables: usize,
) -> Result<BigUint, String> {
    let mut variables = BTreeSet::new();
    for f in factors {
        variables.extend(f.internal.iter().cloned());
        variables.extend(f.boundary.iter().cloned());
    }
    if !output.keys().all(|k| variables.contains(k)) {
        return Err("oracle output contains unknown variable".into());
    }
    let fixed: BTreeSet<_> = output.keys().cloned().collect();
    let free = variables.difference(&fixed).cloned().collect::<Vec<_>>();
    if free.len() > max_variables || free.len() >= usize::BITS as usize {
        return Err("oracle enumeration limit exceeded".into());
    }
    let mut count = BigUint::from(0u8);
    for mask in 0..(1usize << free.len()) {
        let mut values = output.clone();
        for (i, name) in free.iter().enumerate() {
            values.insert(name.clone(), mask & (1 << i) != 0);
        }
        let satisfied = factors.iter().flat_map(|f| &f.equations).all(|eq| {
            eq.variables.iter().fold(false, |acc, name| acc ^ values[name.as_str()]) == eq.rhs
        });
        if satisfied { count += 1u8; }
    }
    Ok(count)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn compare(family: Family, n: usize, output: &[String]) {
        let factors = generate(family, n).unwrap();
        let limits = Limits::default();
        let traces = [
            Schedule::Sequential, Schedule::Reverse, Schedule::EvenFirst,
        ].map(|schedule| {
            fold(&factors, &schedule.indices(n), output, &limits).unwrap()
        });
        let contexts = 1usize << output.len();
        for mask in 0..contexts {
            let assignment = output.iter().enumerate()
                .map(|(i, x)| (x.clone(), mask & (1 << i) != 0))
                .collect::<BTreeMap<_, _>>();
            let expected = oracle(&factors, &assignment, 14).unwrap();
            for trace in &traces {
                assert_eq!(trace.stage.count_at(&assignment).unwrap(), expected,
                    "{family:?} n={n} {:?} assignment={assignment:?}", trace.schedule);
                assert_eq!(trace.steps.len(), n);
                assert_eq!(trace.steps.last().unwrap().metrics,
                    trace.stage.metrics);
            }
        }
    }

    #[test]
    fn small_networks_exact_across_three_orders_and_outer_contexts() {
        for n in 3..=9 {
            compare(Family::Chain, n, &[]);
            compare(Family::Chain, n, &["x0".into(), format!("x{n}")]);
            compare(Family::CirculantXor3, n, &[]);
            compare(Family::CirculantXor3, n, &["x0".into(), "x1".into()]);
        }
    }

    #[test]
    fn deliberately_bad_chain_order_grows_transient_representation() {
        let n = 24;
        let factors = generate(Family::Chain, n).unwrap();
        let good = fold(&factors, &Schedule::Sequential.indices(n), &[], &Limits::default()).unwrap();
        let poor = fold(&factors, &Schedule::EvenFirst.indices(n), &[], &Limits::default()).unwrap();
        assert_eq!(good.stage.count_at(&BTreeMap::new()).unwrap(), 2u8.into());
        assert_eq!(poor.stage.count_at(&BTreeMap::new()).unwrap(), 2u8.into());
        assert!(poor.peak_d > good.peak_d, "good={}, poor={}", good.peak_d, poor.peak_d);
        assert!(poor.sum_d > good.sum_d);
        assert_eq!(good.stage.metrics.d, poor.stage.metrics.d);
    }

    #[test]
    fn exactness_survives_larger_cyclic_parity_networks() {
        for n in [12, 24, 48] {
            let factors = generate(Family::CirculantXor3, n).unwrap();
            let a = fold(&factors, &Schedule::Sequential.indices(n), &[], &Limits::default()).unwrap();
            let b = fold(&factors, &Schedule::EvenFirst.indices(n), &[], &Limits::default()).unwrap();
            let c = fold(&factors, &Schedule::Reverse.indices(n), &[], &Limits::default()).unwrap();
            let count = a.stage.count_at(&BTreeMap::new()).unwrap();
            assert!(count > BigUint::from(0u8)); // Witness baked into RHS.
            assert_eq!(b.stage.count_at(&BTreeMap::new()).unwrap(), count);
            assert_eq!(c.stage.count_at(&BTreeMap::new()).unwrap(), count);
        }
    }

    #[test]
    fn invalid_orders_outputs_and_budgets_refuse() {
        let factors = generate(Family::Chain, 6).unwrap();
        let limits = Limits::default();
        assert!(fold(&factors, &[0, 1, 2, 3, 4, 4], &[], &limits).is_err());
        assert!(fold(&factors, &[0, 1, 2, 3, 4], &[], &limits).is_err());
        assert!(fold(&factors, &Schedule::Sequential.indices(6), &["bad".into()], &limits).is_err());
        let tight = Limits { max_merge_cells: 1, ..Limits::default() };
        assert!(fold(&factors, &Schedule::Sequential.indices(6), &[], &tight)
            .unwrap_err().contains("limit"));
        assert!(oracle(&factors, &BTreeMap::new(), 1).is_err());
    }
}
