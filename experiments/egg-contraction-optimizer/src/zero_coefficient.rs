//! Exact #SAT constant-coefficient contraction: dense, skipped-zero and
//! indexed sparse support, under the SAME min-fill factor-admission schedule.
//!
//! Mathematical correctness follows from [t^0](P Q) = [t^0]P [t^0]Q
//! and finite sum distributivity. The checked Lean theorem in
//! IndependentZeroCoefficientPruning.lean specifies these equations; Rust
//! correspondence is independently tested, not universally proved.
//!
//! Source factors have nonnegative clause-violation energies. A zero state
//! means that every completion of the already absorbed source factors
//! violates at least one constraint for that boundary assignment. That
//! "no repair" certificate justifies skipping zero multiplicands.
//!
//! Sparse support indexing avoids enumerating full unions but pays for
//! BTreeMap grouping, key projections, and compatible pair joins.
//! It does not assert a bound on worst-case sparse support growth.

use super::*;
use crate::representation_study::adaptive::{self, Case, Policy};
use std::time::Instant;

const MAX_JOIN_PAIRS: u64 = 5_000_000;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Strategy {
    Dense,
    DenseSkipZero,
    IndexedSupport,
}

impl Strategy {
    pub const ALL: [Self; 3] = [
        Self::Dense, Self::DenseSkipZero, Self::IndexedSupport,
    ];
    pub fn name(self) -> &'static str {
        match self {
            Self::Dense => "dense-zero",
            Self::DenseSkipZero => "dense-zero-pruned",
            Self::IndexedSupport => "indexed-support",
        }
    }
}

#[derive(Default, Clone, Debug)]
pub struct Metrics {
    pub additions: u64,
    pub multiplications: u64,
    pub bit_work_proxy: u128,
    pub full_union_mask_visits: u64,
    pub certified_zero_skips: u64,
    pub source_leaf_assignments: u64,
    pub source_leaf_rejections: u64,
    pub support_index_insertions: u64,
    pub support_group_lookups: u64,
    pub compatible_pair_visits: u64,
    pub left_entry_scans: u64,
    pub peak_nonzero_boundary_entries: usize,
    pub peak_stored_boundary_slots: usize,
    /// Lower-bound byte proxy, excluding BTreeMap node/allocator overhead.
    pub peak_encoded_boundary_bytes: usize,
    pub max_coefficient_bits: u64,
}

fn measured_product(a: &BigUint, b: &BigUint, m: &mut Metrics) -> BigUint {
    m.multiplications += 1;
    m.bit_work_proxy += u128::from(a.bits().max(1)) * u128::from(b.bits().max(1));
    let result = a * b;
    m.max_coefficient_bits = m.max_coefficient_bits.max(result.bits());
    result
}

fn measured_add_assign(out: &mut BigUint, value: &BigUint, m: &mut Metrics) {
    m.additions += 1;
    m.bit_work_proxy += u128::from(out.bits().max(value.bits()).max(1));
    *out += value;
    m.max_coefficient_bits = m.max_coefficient_bits.max(out.bits());
}

fn embed(mask: usize, from: &[String], union: &[String]) -> usize {
    from.iter().enumerate().fold(0, |bits, (i, name)| {
        let index = union.binary_search(name).expect("union contains child");
        bits | (((mask >> i) & 1) << index)
    })
}

#[derive(Clone)]
enum Values {
    Dense(Vec<BigUint>),
    Sparse(BTreeMap<usize, BigUint>),
}

#[derive(Clone)]
struct Stage {
    ports: Vec<String>,
    values: Values,
}

impl Stage {
    fn entries(&self) -> usize {
        match &self.values {
            Values::Dense(v) => v.iter().filter(|x| **x != BigUint::default()).count(),
            Values::Sparse(v) => v.len(),
        }
    }

    fn slots(&self) -> usize {
        match &self.values {
            Values::Dense(v) => v.len(),
            Values::Sparse(v) => v.len(),
        }
    }

    fn get(&self, mask: usize) -> BigUint {
        match &self.values {
            Values::Dense(v) => v[mask].clone(),
            Values::Sparse(v) => v.get(&mask).cloned().unwrap_or_default(),
        }
    }

    fn encoded_bytes_lower_bound(&self) -> usize {
        let base = std::mem::size_of::<Stage>()
            + self.ports.capacity() * std::mem::size_of::<String>()
            + self.ports.iter().map(String::len).sum::<usize>();
        base + match &self.values {
            Values::Dense(v) => v.capacity() * std::mem::size_of::<BigUint>()
                + v.iter().map(|x| x.bits().div_ceil(8) as usize).sum::<usize>(),
            Values::Sparse(v) => v.len()
                * (std::mem::size_of::<usize>() + std::mem::size_of::<BigUint>())
                + v.values().map(|x| x.bits().div_ceil(8) as usize).sum::<usize>(),
        }
    }

    fn record(&self, m: &mut Metrics, leaves: usize, previous: usize) {
        m.peak_nonzero_boundary_entries =
            m.peak_nonzero_boundary_entries.max(self.entries());
        m.peak_stored_boundary_slots = m.peak_stored_boundary_slots.max(self.slots());
        m.peak_encoded_boundary_bytes = m.peak_encoded_boundary_bytes.max(
            leaves + previous + self.encoded_bytes_lower_bound(),
        );
        match &self.values {
            Values::Dense(v) => {
                m.max_coefficient_bits = m.max_coefficient_bits.max(
                    v.iter().map(BigUint::bits).max().unwrap_or(0));
            }
            Values::Sparse(v) => {
                m.max_coefficient_bits = m.max_coefficient_bits.max(
                    v.values().map(BigUint::bits).max().unwrap_or(0));
            }
        }
    }

    fn leaf(factor: &Factor, strategy: Strategy, m: &mut Metrics) -> Result<Self, String> {
        let n = count_masks(factor.ports.len())?;
        m.source_leaf_assignments += n as u64;
        let mut dense = Vec::with_capacity(n);
        let mut sparse = BTreeMap::new();
        for mask in 0..n {
            let satisfied = factor.energy(mask) == 0;
            if !satisfied { m.source_leaf_rejections += 1; }
            if strategy == Strategy::IndexedSupport {
                if satisfied { sparse.insert(mask, BigUint::from(1u8)); }
            } else {
                dense.push(BigUint::from(if satisfied { 1u8 } else { 0u8 }));
            }
        }
        Ok(Self {
            ports: factor.ports.clone(),
            values: if strategy == Strategy::IndexedSupport {
                Values::Sparse(sparse)
            } else {
                Values::Dense(dense)
            },
        })
    }

    fn merge_dense(&self, next: &Self, kept: &[String], strategy: Strategy,
        metrics: &mut Metrics) -> Result<Self, String>
    {
        let union = union_ports(&self.ports, &next.ports);
        let mut dest = vec![BigUint::default(); count_masks(kept.len())?];
        for mask in 0..count_masks(union.len())? {
            metrics.full_union_mask_visits += 1;
            let a = self.get(project(mask, &union, &self.ports));
            let b = next.get(project(mask, &union, &next.ports));
            if strategy == Strategy::DenseSkipZero
                && (a == BigUint::default() || b == BigUint::default())
            {
                metrics.certified_zero_skips += 1;
                continue;
            }
            let product = measured_product(&a, &b, metrics);
            let i = project(mask, &union, kept);
            measured_add_assign(&mut dest[i], &product, metrics);
        }
        Ok(Self { ports: kept.to_vec(), values: Values::Dense(dest) })
    }

    fn merge_sparse(&self, next: &Self, kept: &[String],
        m: &mut Metrics) -> Result<Self, String>
    {
        let (Values::Sparse(left), Values::Sparse(right)) = (&self.values, &next.values)
        else { return Err("sparse merge received non-sparse input".into()); };
        let union = union_ports(&self.ports, &next.ports);
        // Project just the common port values into a compact lookup key.
        let shared = self.ports.iter().filter(|p| next.ports.binary_search(p).is_ok())
            .cloned().collect::<Vec<_>>();
        let mut index = BTreeMap::<usize, Vec<(usize, &BigUint)>>::new();
        for (&mask, count) in right {
            let key = project(mask, &next.ports, &shared);
            index.entry(key).or_default().push((mask, count));
            m.support_index_insertions += 1;
        }
        let mut dest = BTreeMap::<usize, BigUint>::new();
        for (&a_mask, a) in left {
            m.left_entry_scans += 1;
            let key = project(a_mask, &self.ports, &shared);
            m.support_group_lookups += 1;
            let Some(matches) = index.get(&key) else { continue };
            for &(b_mask, b) in matches {
                m.compatible_pair_visits += 1;
                if m.compatible_pair_visits > MAX_JOIN_PAIRS {
                    return Err("sparse support join exceeds hard pair budget".into());
                }
                let union_mask = embed(a_mask, &self.ports, &union)
                    | embed(b_mask, &next.ports, &union);
                let output = project(union_mask, &union, kept);
                let product = measured_product(a, b, m);
                let sum = dest.entry(output).or_default();
                measured_add_assign(sum, &product, m);
            }
        }
        Ok(Self { ports: kept.to_vec(), values: Values::Sparse(dest) })
    }
}

#[derive(Clone, Debug)]
pub struct VariantReceipt {
    pub strategy: Strategy,
    pub work: Metrics,
    pub elapsed_ns: u128,
    pub satisfying_count: BigUint,
    /// All requested boundary assignments, not only mask zero. This
    /// remains a bounded explicit table for the experimental oracle.
    pub boundary_counts: Vec<BigUint>,
    pub output_ports: Vec<String>,
}

fn validate_order(factors: &[Factor], order: &[usize]) -> Result<(), String> {
    if factors.len() < 2 || order.len() != factors.len() {
        return Err("zero study requires a complete nonempty order".into());
    }
    let mut seen = vec![false; factors.len()];
    for &index in order {
        if index >= seen.len() || seen[index] { return Err("invalid factor order".into()); }
        seen[index] = true;
    }
    Ok(())
}

fn kept_after(factors: &[Factor], order: &[usize], step: usize,
    current: &[String], next: &[String], output: &[String]) -> Vec<String>
{
    let future = order[step + 1..].iter().flat_map(|&i| factors[i].ports.iter().cloned())
        .collect::<BTreeSet<_>>();
    affine_orders::kept_port_set(
        &current.iter().cloned().collect(),
        &next.iter().cloned().collect(),
        &future, &output.iter().cloned().collect(),
    ).into_iter().collect()
}

fn fold(factors: &[Factor], order: &[usize], output: &[String],
    strategy: Strategy) -> Result<VariantReceipt, String>
{
    validate_order(factors, order)?;
    let start = Instant::now();
    let mut work = Metrics::default();
    let mut leaves = Vec::with_capacity(factors.len());
    for factor in factors { leaves.push(Stage::leaf(factor, strategy, &mut work)?); }
    let leaf_bytes = leaves.iter().map(Stage::encoded_bytes_lower_bound).sum::<usize>();
    let mut stage = leaves[order[0]].clone();
    stage.record(&mut work, leaf_bytes, 0);
    for (step, &index) in order.iter().enumerate().skip(1) {
        let kept = kept_after(
            factors, order, step, &stage.ports, &leaves[index].ports, output,
        );
        let merged = match strategy {
            Strategy::Dense | Strategy::DenseSkipZero =>
                stage.merge_dense(&leaves[index], &kept, strategy, &mut work)?,
            Strategy::IndexedSupport =>
                stage.merge_sparse(&leaves[index], &kept, &mut work)?,
        };
        merged.record(&mut work, leaf_bytes, stage.encoded_bytes_lower_bound());
        stage = merged;
    }
    if stage.ports != output { return Err("zero study output boundary mismatch".into()); }
    let boundary_counts = (0..count_masks(stage.ports.len())?)
        .map(|mask| stage.get(mask)).collect::<Vec<_>>();
    let satisfying_count = boundary_counts[0].clone();
    Ok(VariantReceipt {
        strategy, work, elapsed_ns: start.elapsed().as_nanos(),
        satisfying_count, boundary_counts, output_ports: stage.ports,
    })
}

/// A separate differential pass compares every intermediate boundary cell
/// with the full polynomial's constant coefficient, not just final #SAT.
/// This verification cost is outside the measured three-variant work.
fn verify_every_boundary(factors: &[Factor], order: &[usize]) -> Result<(), String> {
    validate_order(factors, order)?;
    let mut poly_work = Work::default();
    let mut tropical_work = Work::default();
    let leaves = factors.iter().map(Tables::from_factor)
        .collect::<Result<Vec<_>, _>>()?;
    let mut full = leaves[order[0]].clone();
    let mut dense_metrics = Metrics::default();
    let mut sparse_metrics = Metrics::default();
    let dense_leaves = factors.iter().map(|f|
        Stage::leaf(f, Strategy::DenseSkipZero, &mut dense_metrics))
        .collect::<Result<Vec<_>, _>>()?;
    let sparse_leaves = factors.iter().map(|f|
        Stage::leaf(f, Strategy::IndexedSupport, &mut sparse_metrics))
        .collect::<Result<Vec<_>, _>>()?;
    let mut dense = dense_leaves[order[0]].clone();
    let mut sparse = sparse_leaves[order[0]].clone();

    for step in 0..order.len() {
        if step > 0 {
            let index = order[step];
            let kept = kept_after(
                factors, order, step, &full.ports, &leaves[index].ports, &[],
            );
            full = full.merge(&leaves[index], &kept,
                &mut poly_work, &mut tropical_work)?;
            full.verify_shadow()?;
            dense = dense.merge_dense(
                &dense_leaves[index], &kept, Strategy::DenseSkipZero, &mut dense_metrics)?;
            sparse = sparse.merge_sparse(
                &sparse_leaves[index], &kept, &mut sparse_metrics)?;
        }
        if dense.ports != full.ports || sparse.ports != full.ports {
            return Err(format!("zero/full port mismatch at source step {step}"));
        }
        for mask in 0..count_masks(full.ports.len())? {
            let expected = full.exact[mask].count_at_zero();
            if dense.get(mask) != expected || sparse.get(mask) != expected {
                return Err(format!(
                    "zero coefficient/full polynomial mismatch at source step {step} cell {mask}",
                ));
            }
        }
    }
    Ok(())
}

#[derive(Debug)]
pub struct Receipt {
    pub case: Case,
    pub order: Vec<usize>,
    pub full_polynomial_multiplications: u64,
    pub full_polynomial_bit_work_proxy: u128,
    pub full_polynomial_peak_encoded_bytes: usize,
    pub source_satisfying_count: BigUint,
    pub variants: Vec<VariantReceipt>,
    pub independent_oracle: &'static str,
}

/// All three variants must match the separately enumerated source Boolean
/// formula and all full-polynomial intermediate cells. The min-fill order is
/// chosen once, before viewing a single zero-only outcome.
pub fn run_case(case: Case) -> Result<Receipt, String> {
    let full = adaptive::evaluate(case, Policy::MinFillAdmission)?;
    let factors = adaptive::source_case(case)?;
    let mut variants = Vec::new();
    for strategy in Strategy::ALL {
        let value = fold(&factors, &full.order, &[], strategy)?;
        if value.satisfying_count != full.exact.satisfying_count {
            return Err(format!(
                "wrong #SAT for {} under {:?}: expected {}, got {}",
                case.label(), strategy,
                full.exact.satisfying_count, value.satisfying_count,
            ));
        }
        variants.push(value);
    }
    verify_every_boundary(&factors, &full.order)?;
    Ok(Receipt {
        case, order: full.order,
        full_polynomial_multiplications: full.exact.exact_work.multiplications,
        full_polynomial_bit_work_proxy: full.exact.exact_work.bit_work_proxy,
        full_polynomial_peak_encoded_bytes: full.exact.peak_live_encoded_bytes,
        source_satisfying_count: full.exact.satisfying_count,
        variants,
        independent_oracle: "checked",
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn open_boundaries_agree_with_full_polynomial() {
        let factors = generate(StudyFamily::EqualityChain, 4).unwrap();
        let order = Schedule::EvenFirst.indices(factors.len());
        let all_ports = factors.iter().flat_map(|f| f.ports.iter().cloned())
            .collect::<BTreeSet<_>>();
        let output = ["x0".to_owned(), "x4".to_owned()].to_vec();
        assert!(output.iter().all(|x| all_ports.contains(x)));
        for strategy in Strategy::ALL {
            let result = fold(&factors, &order, &output, strategy).unwrap();
            assert_eq!(result.output_ports, output);
            let exact = execute_order(&factors, "chain", factors.len(), "test",
                &order, &output).unwrap();
            // The two retained endpoint variables must agree. Check all
            // four assignments independently, not only output mask zero.
            assert_eq!(result.satisfying_count, exact.satisfying_count);
            for mask in 0..count_masks(output.len()).unwrap() {
                let original = source_oracle(&factors, &output, mask).unwrap();
                assert_eq!(result.boundary_counts[mask], original.count_at_zero());
            }
        }
    }

    #[test]
    fn final_and_intermediate_closed_boundary_oracles() {
        for case in [
            Case { kind: adaptive::CaseKind::Random3Cnf,
                variables: 6, clauses: 12, seed: 1009 },
            Case { kind: adaptive::CaseKind::Planted3Cnf,
                variables: 6, clauses: 24, seed: 5003 },
            Case { kind: adaptive::CaseKind::FrustratedXor3Cnf,
                variables: 6, clauses: 24, seed: 0 },
        ] {
            let r = run_case(case).unwrap();
            assert_eq!(r.variants.len(), 3);
            assert_eq!(r.independent_oracle, "checked");
            assert!(r.variants.iter().all(|v|
                v.satisfying_count == r.source_satisfying_count));
            assert!(r.variants[1].work.certified_zero_skips > 0);
        }
    }


    #[test]
    fn dense_support_is_not_a_general_sparse_growth_bound() {
        // Every source assignment satisfies these free-amplifier factors,
        // so the support index must carry all leaf assignments. There is
        // no promised sparsity or exponential compression.
        for size in [4, 6, 8] {
            let factors = generate(StudyFamily::FreeAmplifier, size).unwrap();
            let order = Schedule::Sequential.indices(factors.len());
            let dense = fold(&factors, &order, &[], Strategy::DenseSkipZero).unwrap();
            let sparse = fold(&factors, &order, &[], Strategy::IndexedSupport).unwrap();
            let expected = BigUint::from(1u8) << (2 * size);
            assert_eq!(dense.satisfying_count, expected);
            assert_eq!(sparse.satisfying_count, expected);
            assert_eq!(dense.work.certified_zero_skips, 0);
            assert!(sparse.work.support_index_insertions > 0);
            assert!(sparse.work.compatible_pair_visits > 0);
        }
    }

    #[test]
    fn contradictory_ring_does_not_require_minimum_energy_recovery() {
        let factors = generate(StudyFamily::FrustratedXor3Cnf, 8).unwrap();
        let order = Schedule::Sequential.indices(factors.len());
        let dense = fold(&factors, &order, &[], Strategy::DenseSkipZero).unwrap();
        let sparse = fold(&factors, &order, &[], Strategy::IndexedSupport).unwrap();
        assert_eq!(dense.satisfying_count, BigUint::default());
        assert_eq!(sparse.satisfying_count, BigUint::default());
        // For #SAT the zero certificate is sufficient, without computing
        // that the true minimum violated-clause count is exactly one.
        assert!(dense.work.certified_zero_skips > 0);
    }

    #[test]
    fn duplicate_or_missing_factor_order_is_rejected() {
        let factors = generate(StudyFamily::EqualityChain, 3).unwrap();
        assert!(fold(&factors, &[0, 0, 2], &[], Strategy::Dense).is_err());
        assert!(fold(&factors, &[0, 1], &[], Strategy::IndexedSupport).is_err());
    }
}
