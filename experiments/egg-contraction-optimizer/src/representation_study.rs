//! Three representations, one ordered contraction plan, one source-level oracle.
//!
//! This is deliberately bounded experimental infrastructure, not a SAT solver
//! with an asymptotic resource guarantee. Exact polynomial tables retain every
//! violation coefficient; tropical tables retain only the first nonzero term;
//! factored circuits retain every coefficient *symbolically*, with explicit
//! summation binders and a separately measured forcing cost.

use crate::affine_orders::{self, Family, Schedule};
use crate::tropical_orders::Leading;
use num_bigint::BigUint;
use std::collections::{BTreeMap, BTreeSet};

const MAX_WIDTH: usize = 16;
const MAX_CACHE_STATES: usize = 200_000;
const MAX_COUNTED_WORK: u64 = 4_000_000;

#[derive(Clone, Copy, Debug)]
pub enum StudyFamily {
    EqualityChain,
    CirculantXor3,
    FreeAmplifier,
    Overlapping3Cnf,
    FrustratedXor3Cnf,
}

impl StudyFamily {
    pub fn name(self) -> &'static str {
        match self {
            Self::EqualityChain => "equality-chain",
            Self::CirculantXor3 => "circulant-xor3",
            Self::FreeAmplifier => "free-amplifier",
            Self::Overlapping3Cnf => "overlapping-3cnf",
            Self::FrustratedXor3Cnf => "frustrated-xor3-cnf",
        }
    }
}

#[derive(Clone, Debug)]
enum Constraint {
    Parity(Vec<String>, bool),
    Clause(Vec<(String, bool)>),
}

#[derive(Clone, Debug)]
struct Factor {
    ports: Vec<String>,
    constraints: Vec<Constraint>,
}

impl Factor {
    fn energy(&self, mask: usize) -> usize {
        self.constraints.iter().filter(|constraint| match constraint {
            Constraint::Parity(vars, rhs) => {
                vars.iter().fold(false, |acc, v| {
                    let bit = self.ports.binary_search(v).expect("validated source");
                    acc ^ (mask & (1 << bit) != 0)
                }) != *rhs
            }
            Constraint::Clause(lits) => !lits.iter().any(|(v, sign)| {
                let bit = self.ports.binary_search(v).expect("validated source");
                (mask & (1 << bit) != 0) == *sign
            }),
        }).count()
    }

    fn validate(&self) -> Result<(), String> {
        if self.ports.iter().collect::<BTreeSet<_>>().len() != self.ports.len()
            || self.ports.windows(2).any(|w| w[0] >= w[1])
        {
            return Err("unsorted or duplicate source ports".into());
        }
        for constraint in &self.constraints {
            let vars = match constraint {
                Constraint::Parity(names, _) => names.iter().collect::<Vec<_>>(),
                Constraint::Clause(literals) => literals.iter().map(|(v, _)| v).collect(),
            };
            if vars.iter().any(|v| self.ports.binary_search(v).is_err()) {
                return Err("constraint refers to unknown source port".into());
            }
        }
        Ok(())
    }
}

fn generate(family: StudyFamily, size: usize) -> Result<Vec<Factor>, String> {
    if !(3..=64).contains(&size) {
        return Err("size outside finite study family".into());
    }
    let factors = match family {
        StudyFamily::EqualityChain | StudyFamily::CirculantXor3 |
        StudyFamily::FreeAmplifier => {
            let kind = match family {
                StudyFamily::EqualityChain => Family::Chain,
                StudyFamily::CirculantXor3 => Family::CirculantXor3,
                StudyFamily::FreeAmplifier => Family::FreeAmplifiers,
                StudyFamily::Overlapping3Cnf | StudyFamily::FrustratedXor3Cnf => unreachable!(),
            };
            affine_orders::generate(kind, size)?.into_iter().map(|region| {
                let ports = region.internal.iter().chain(&region.boundary)
                    .cloned().collect::<BTreeSet<_>>().into_iter().collect();
                let constraints = region.equations.into_iter().map(|eq| {
                    Constraint::Parity(eq.variables, eq.rhs)
                }).collect();
                Factor { ports, constraints }
            }).collect()
        }
        StudyFamily::Overlapping3Cnf => (0..size).map(|i| {
            let stride = (size / 2).max(2);
            let ids = [i, (i + 1) % size, (i + stride) % size];
            let names = ids.map(|j| format!("x{j}"));
            let ports = names.iter().cloned().collect::<BTreeSet<_>>()
                .into_iter().collect();
            let literals = names.into_iter().enumerate().map(|(k, name)| {
                (name, (i + k + (i / 3)) % 2 == 0)
            }).collect();
            Factor { ports, constraints: vec![Constraint::Clause(literals)] }
        }).collect(),
        StudyFamily::FrustratedXor3Cnf => {
            if size < 4 || size % 2 != 0 {
                return Err("frustrated XOR3-CNF requires even size at least four".into());
            }
            (0..size).map(|i| {
                // Summing the n parity equations cancels each cycle variable
                // twice and the hub n times. The one odd charge is impossible.
                let vars = [
                    format!("x{i}"), format!("x{}", (i + 1) % size), "h".into(),
                ];
                let ports = vars.iter().cloned().collect::<BTreeSet<_>>()
                    .into_iter().collect();
                let rhs = i == 0;
                let constraints = (0..8usize).filter_map(|mask| {
                    let assignment = [mask & 1 != 0, mask & 2 != 0, mask & 4 != 0];
                    if assignment.iter().fold(false, |p, bit| p ^ *bit) == rhs {
                        None
                    } else {
                        // A canonical three-literal clause forbids exactly
                        // the given assignment. Four clauses encode XOR3.
                        Some(Constraint::Clause(vars.iter().cloned()
                            .zip(assignment.iter().map(|bit| !*bit)).collect()))
                    }
                }).collect();
                Factor { ports, constraints }
            }).collect()
        }
    };
    let factors: Vec<Factor> = factors;
    for factor in &factors { factor.validate()?; }
    Ok(factors)
}

fn count_masks(width: usize) -> Result<usize, String> {
    if width > MAX_WIDTH || width >= usize::BITS as usize {
        Err(format!("explicit study refuses boundary width {width}"))
    } else {
        Ok(1usize << width)
    }
}

fn union_ports(left: &[String], right: &[String]) -> Vec<String> {
    left.iter().chain(right).cloned().collect::<BTreeSet<_>>()
        .into_iter().collect()
}

fn project(mask: usize, from: &[String], to: &[String]) -> usize {
    to.iter().enumerate().fold(0, |out, (i, name)| {
        let j = from.binary_search(name).expect("subset of union");
        out | (((mask >> j) & 1) << i)
    })
}

fn expand(
    keep_mask: usize, kept: &[String], eliminated_mask: usize,
    eliminated: &[String], union: &[String],
) -> usize {
    union.iter().enumerate().fold(0, |out, (i, v)| {
        let value = match kept.binary_search(v) {
            Ok(j) => (keep_mask >> j) & 1,
            Err(_) => (eliminated_mask >> eliminated.binary_search(v)
                .expect("partition of union")) & 1,
        };
        out | (value << i)
    })
}

#[derive(Default, Clone, Debug)]
pub struct Work {
    pub additions: u64,
    pub multiplications: u64,
    pub max_coefficient_bits: u64,
}

#[derive(Clone, Default, Debug, Eq, PartialEq)]
struct Polynomial(Vec<BigUint>);

impl Polynomial {
    fn monomial(degree: usize) -> Self {
        let mut c = vec![BigUint::default(); degree + 1];
        c[degree] = BigUint::from(1u8);
        Self(c)
    }

    fn add(&self, other: &Self, work: &mut Work) -> Self {
        let mut out = vec![BigUint::default(); self.0.len().max(other.0.len())];
        for (i, c) in out.iter_mut().enumerate() {
            if let Some(x) = self.0.get(i) { *c += x; work.additions += 1; }
            if let Some(y) = other.0.get(i) { *c += y; work.additions += 1; }
            work.max_coefficient_bits = work.max_coefficient_bits.max(c.bits());
        }
        while out.last().is_some_and(|c| *c == BigUint::default()) {
            out.pop();
        }
        Self(out)
    }

    fn mul(&self, other: &Self, work: &mut Work) -> Self {
        if self.0.is_empty() || other.0.is_empty() { return Self::default(); }
        let mut out = vec![BigUint::default(); self.0.len() + other.0.len() - 1];
        for (i, x) in self.0.iter().enumerate() {
            if *x == BigUint::default() { continue; }
            for (j, y) in other.0.iter().enumerate() {
                if *y == BigUint::default() { continue; }
                out[i + j] += x * y;
                work.additions += 1;
                work.multiplications += 1;
                work.max_coefficient_bits = work.max_coefficient_bits.max(out[i + j].bits());
            }
        }
        while out.last().is_some_and(|c| *c == BigUint::default()) {
            out.pop();
        }
        Self(out)
    }

    fn leading(&self) -> Option<Leading> {
        self.0.iter().enumerate().find(|(_, c)| **c != BigUint::default())
            .map(|(energy, count)| Leading { energy, count: count.clone() })
    }

    fn nonzero_terms(&self) -> usize {
        self.0.iter().filter(|c| **c != BigUint::default()).count()
    }

    fn count_at_zero(&self) -> BigUint {
        self.0.first().cloned().unwrap_or_default()
    }
}

fn tropical_add(a: Option<Leading>, b: Option<Leading>, work: &mut Work)
    -> Option<Leading>
{
    work.additions += 1;
    match (a, b) {
        (None, x) | (x, None) => x,
        (Some(a), Some(b)) if a.energy < b.energy => Some(a),
        (Some(a), Some(b)) if b.energy < a.energy => Some(b),
        (Some(a), Some(b)) => {
            let count = a.count + b.count;
            work.max_coefficient_bits = work.max_coefficient_bits.max(count.bits());
            Some(Leading { energy: a.energy, count })
        }
    }
}

fn tropical_mul(a: &Option<Leading>, b: &Option<Leading>, work: &mut Work)
    -> Result<Option<Leading>, String>
{
    work.multiplications += 1;
    match (a, b) {
        (Some(a), Some(b)) => {
            let count = &a.count * &b.count;
            work.max_coefficient_bits = work.max_coefficient_bits.max(count.bits());
            Ok(Some(Leading {
                energy: a.energy.checked_add(b.energy).ok_or("energy overflow")?,
                count,
            }))
        }
        _ => Ok(None),
    }
}

#[derive(Clone, Debug)]
struct Tables {
    ports: Vec<String>,
    exact: Vec<Polynomial>,
    tropical: Vec<Option<Leading>>,
}

impl Tables {
    fn from_factor(factor: &Factor) -> Result<Self, String> {
        let exact = (0..count_masks(factor.ports.len())?)
            .map(|mask| Polynomial::monomial(factor.energy(mask))).collect::<Vec<_>>();
        let tropical = exact.iter().map(Polynomial::leading).collect();
        Ok(Self { ports: factor.ports.clone(), exact, tropical })
    }

    fn merge(
        &self, next: &Self, kept: &[String], exact_work: &mut Work,
        tropical_work: &mut Work,
    ) -> Result<Self, String> {
        let union = union_ports(&self.ports, &next.ports);
        let mut exact = vec![Polynomial::default(); count_masks(kept.len())?];
        let mut tropical = vec![None; count_masks(kept.len())?];
        for mask in 0..count_masks(union.len())? {
            let left = project(mask, &union, &self.ports);
            let right = project(mask, &union, &next.ports);
            let dest = project(mask, &union, kept);
            let product = self.exact[left].mul(&next.exact[right], exact_work);
            exact[dest] = exact[dest].add(&product, exact_work);
            let product = tropical_mul(&self.tropical[left], &next.tropical[right], tropical_work)?;
            tropical[dest] = tropical_add(tropical[dest].take(), product, tropical_work);
        }
        Ok(Self { ports: kept.to_vec(), exact, tropical })
    }

    fn verify_shadow(&self) -> Result<(), String> {
        for (i, poly) in self.exact.iter().enumerate() {
            if poly.leading() != self.tropical[i] {
                return Err(format!("tropical does not match exact at boundary cell {i}"));
            }
        }
        Ok(())
    }
}

#[derive(Clone, Debug)]
enum NodeKind {
    Leaf(usize),
    Merge {
        left: usize,
        right: usize,
        union: Vec<String>,
        eliminated: Vec<String>,
    },
}

#[derive(Clone, Debug)]
struct Node {
    ports: Vec<String>,
    kind: NodeKind,
}

struct Evaluator<'a> {
    nodes: &'a [Node],
    factors: &'a [Factor],
    cache: BTreeMap<(usize, usize), Polynomial>,
    cached_coefficient_slots: usize,
    work: Work,
}

impl<'a> Evaluator<'a> {
    fn eval(&mut self, id: usize, mask: usize) -> Result<Polynomial, String> {
        if let Some(hit) = self.cache.get(&(id, mask)) { return Ok(hit.clone()); }
        if self.cache.len() >= MAX_CACHE_STATES {
            return Err("factored forcing cache budget exceeded".into());
        }
        let node = &self.nodes[id];
        let result = match &node.kind {
            NodeKind::Leaf(index) => Polynomial::monomial(self.factors[*index].energy(mask)),
            NodeKind::Merge { left, right, union, eliminated } => {
                let mut result = Polynomial::default();
                for bits in 0..count_masks(eliminated.len())? {
                    let combined = expand(mask, &node.ports, bits, eliminated, union);
                    let left_mask = project(combined, union, &self.nodes[*left].ports);
                    let right_mask = project(combined, union, &self.nodes[*right].ports);
                    let a = self.eval(*left, left_mask)?;
                    let b = self.eval(*right, right_mask)?;
                    let product = a.mul(&b, &mut self.work);
                    result = result.add(&product, &mut self.work);
                    if self.work.additions + self.work.multiplications > MAX_COUNTED_WORK {
                        return Err("factored forcing arithmetic budget exceeded".into());
                    }
                }
                result
            }
        };
        self.cached_coefficient_slots += result.0.len();
        self.work.max_coefficient_bits = self.work.max_coefficient_bits.max(
            result.0.iter().map(BigUint::bits).max().unwrap_or(0));
        self.cache.insert((id, mask), result.clone());
        Ok(result)
    }
}

/// Direct enumeration of *source factors*, independent of all three folds.
fn source_oracle(factors: &[Factor], output: &[String], output_mask: usize)
    -> Result<Polynomial, String>
{
    let universe = factors.iter().flat_map(|f| f.ports.iter().cloned())
        .collect::<BTreeSet<_>>().into_iter().collect::<Vec<_>>();
    let hidden = universe.iter().filter(|v| output.binary_search(v).is_err())
        .cloned().collect::<Vec<_>>();
    let mut coeff = vec![BigUint::default();
        1 + factors.iter().map(|f| f.constraints.len()).sum::<usize>()];
    for bits in 0..count_masks(hidden.len())? {
        let assignment = expand(output_mask, output, bits, &hidden, &universe);
        let energy: usize = factors.iter().map(|f| {
            f.energy(project(assignment, &universe, &f.ports))
        }).sum();
        coeff[energy] += 1u8;
    }
    while coeff.last().is_some_and(|c| *c == BigUint::default()) {
        coeff.pop();
    }
    Ok(Polynomial(coeff))
}

#[derive(Clone, Debug)]
pub struct Receipt {
    pub family: &'static str,
    pub size: usize,
    pub schedule: &'static str,
    pub peak_boundary_ports: usize,
    pub peak_table_cells: usize,
    pub peak_exact_coefficient_slots: usize,
    pub peak_exact_nonzero_coefficients: usize,
    pub exact_work: Work,
    pub tropical_work: Work,
    pub tropical_positive_energy_cells: usize,
    pub staged_tropical_cells: usize,
    pub staged_positive_energy_cells: usize,
    pub symbolic_nodes: usize,
    pub symbolic_port_name_occurrences: usize,
    pub symbolic_eliminated_binders: usize,
    pub forced_cache_entries: usize,
    pub forced_cache_coefficient_slots: usize,
    pub symbolic_work: Work,
    pub minimum_energy: usize,
    pub minimum_count: BigUint,
    pub satisfying_count: BigUint,
}

pub fn run(family: StudyFamily, size: usize, schedule: Schedule,
    output: &[String]) -> Result<Receipt, String>
{
    let factors = generate(family, size)?;
    if output.iter().collect::<BTreeSet<_>>().len() != output.len()
        || output.windows(2).any(|w| w[0] >= w[1])
    {
        return Err("output ports must be sorted and unique".into());
    }
    let all_ports = factors.iter().flat_map(|f| f.ports.iter().cloned())
        .collect::<BTreeSet<_>>();
    if output.iter().any(|p| !all_ports.contains(p)) {
        return Err("unknown requested output port".into());
    }
    let leaves = factors.iter().map(Tables::from_factor)
        .collect::<Result<Vec<_>, _>>()?;
    let mut nodes = factors.iter().enumerate().map(|(i, f)| Node {
        ports: f.ports.clone(), kind: NodeKind::Leaf(i),
    }).collect::<Vec<_>>();
    let order = schedule.indices(factors.len());
    let mut stage = leaves[order[0]].clone();
    let mut root = order[0];
    let mut peak_boundary_ports = stage.ports.len();
    let mut peak_table_cells = stage.exact.len();
    let mut peak_exact_coefficient_slots: usize = stage.exact.iter().map(|p| p.0.len()).sum();
    let mut peak_exact_nonzero_coefficients: usize = stage.exact.iter()
        .map(Polynomial::nonzero_terms).sum();
    let mut staged_tropical_cells = stage.tropical.len();
    let mut staged_positive_energy_cells = stage.tropical.iter().flatten()
        .filter(|c| c.energy > 0).count();
    let mut exact_work = Work::default();
    let mut tropical_work = Work::default();
    let output_set = output.iter().cloned().collect::<BTreeSet<_>>();
    let mut symbolic_eliminated_binders = 0;
    for (step, &index) in order.iter().enumerate().skip(1) {
        let future = order[step + 1..].iter().flat_map(|&i| leaves[i].ports.iter().cloned())
            .collect::<BTreeSet<_>>();
        let active = stage.ports.iter().cloned().collect::<BTreeSet<_>>();
        let next = leaves[index].ports.iter().cloned().collect::<BTreeSet<_>>();
        let kept = affine_orders::kept_port_set(&active, &next, &future, &output_set);
        let kept = kept.into_iter().collect::<Vec<_>>();
        let union = union_ports(&stage.ports, &leaves[index].ports);
        let eliminated = union.iter().filter(|p| kept.binary_search(p).is_err())
            .cloned().collect::<Vec<_>>();
        symbolic_eliminated_binders += eliminated.len();
        nodes.push(Node {
            ports: kept.clone(),
            kind: NodeKind::Merge { left: root, right: index, union, eliminated },
        });
        root = nodes.len() - 1;
        stage = stage.merge(&leaves[index], &kept, &mut exact_work, &mut tropical_work)?;
        stage.verify_shadow()?;
        staged_tropical_cells += stage.tropical.len();
        staged_positive_energy_cells += stage.tropical.iter().flatten()
            .filter(|c| c.energy > 0).count();
        peak_boundary_ports = peak_boundary_ports.max(stage.ports.len());
        peak_table_cells = peak_table_cells.max(stage.exact.len());
        peak_exact_coefficient_slots = peak_exact_coefficient_slots.max(
            stage.exact.iter().map(|p| p.0.len()).sum());
        peak_exact_nonzero_coefficients = peak_exact_nonzero_coefficients.max(
            stage.exact.iter().map(Polynomial::nonzero_terms).sum());
    }
    if stage.ports != output {
        return Err("computed output differs from requested output".into());
    }
    // Nodes alone undercount the factored representation: merge nodes retain
    // explicit sorted union/retained/eliminated port lists.
    let symbolic_port_name_occurrences = nodes.iter().map(|node| {
        node.ports.len() + match &node.kind {
            NodeKind::Leaf(_) => 0,
            NodeKind::Merge { union, eliminated, .. } =>
                union.len() + eliminated.len(),
        }
    }).sum();
    let mut evaluator = Evaluator {
        nodes: &nodes, factors: &factors, cache: BTreeMap::new(),
        cached_coefficient_slots: 0, work: Work::default(),
    };
    for mask in 0..count_masks(output.len())? {
        let forced = evaluator.eval(root, mask)?;
        if forced != stage.exact[mask] {
            return Err(format!("factored circuit differs from explicit table at {mask}"));
        }
        let oracle = source_oracle(&factors, output, mask)?;
        if oracle != forced {
            return Err(format!("source oracle differs from exact circuit at {mask}"));
        }
    }
    let root_poly = &stage.exact[0];
    let leading = root_poly.leading().ok_or("empty source polynomial")?;
    let tropical_positive_energy_cells = stage.tropical.iter().filter(|v| {
        v.as_ref().is_some_and(|c| c.energy > 0)
    }).count();
    exact_work.max_coefficient_bits = exact_work.max_coefficient_bits.max(
        stage.exact.iter().flat_map(|p| p.0.iter()).map(BigUint::bits).max().unwrap_or(0));
    tropical_work.max_coefficient_bits = tropical_work.max_coefficient_bits.max(
        stage.tropical.iter().flatten().map(|c| c.count.bits()).max().unwrap_or(0));
    Ok(Receipt {
        family: family.name(), size, schedule: schedule.name(),
        peak_boundary_ports, peak_table_cells, peak_exact_coefficient_slots,
        peak_exact_nonzero_coefficients, exact_work, tropical_work,
        tropical_positive_energy_cells, staged_tropical_cells,
        staged_positive_energy_cells, symbolic_nodes: nodes.len(),
        symbolic_port_name_occurrences,
        symbolic_eliminated_binders, forced_cache_entries: evaluator.cache.len(),
        forced_cache_coefficient_slots: evaluator.cached_coefficient_slots,
        symbolic_work: evaluator.work, minimum_energy: leading.energy,
        minimum_count: leading.count, satisfying_count: root_poly.count_at_zero(),
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn all_three_representations_agree_with_source_enumeration() {
        for family in [
            StudyFamily::EqualityChain, StudyFamily::CirculantXor3,
            StudyFamily::FreeAmplifier, StudyFamily::Overlapping3Cnf,
        ] {
            for size in 3..=6 {
                let traces = [
                    Schedule::Sequential, Schedule::Reverse, Schedule::EvenFirst,
                ].map(|schedule| run(family, size, schedule, &[]).unwrap());
                for r in &traces {
                    assert_eq!(r.minimum_energy == 0,
                        r.satisfying_count != BigUint::default());
                }
                assert!(traces.windows(2).all(|w| {
                    w[0].minimum_energy == w[1].minimum_energy
                        && w[0].minimum_count == w[1].minimum_count
                        && w[0].satisfying_count == w[1].satisfying_count
                }));
            }
        }
    }

    #[test]
    fn open_boundary_functions_and_refusal_are_explicit() {
        for family in [StudyFamily::EqualityChain, StudyFamily::Overlapping3Cnf] {
            for schedule in [
                Schedule::Sequential, Schedule::Reverse, Schedule::EvenFirst,
            ] {
                run(family, 5, schedule, &["x0".into(), "x1".into()]).unwrap();
            }
        }
        assert!(run(StudyFamily::EqualityChain, 17, Schedule::EvenFirst, &[]).is_err());
        assert!(run(StudyFamily::EqualityChain, 3, Schedule::Sequential,
            &["unknown".into()]).is_err());
    }

    #[test]
    fn contradictory_cnf_has_exact_positive_minimum_and_no_solutions() {
        for size in [4, 6, 8] {
            for schedule in [
                Schedule::Sequential, Schedule::Reverse, Schedule::EvenFirst,
            ] {
                let r = run(StudyFamily::FrustratedXor3Cnf, size, schedule, &[])
                    .unwrap();
                assert_eq!(r.minimum_energy, 1);
                assert_eq!(r.satisfying_count, BigUint::default());
                assert_eq!(r.minimum_count, BigUint::from(4 * size));
                assert!(r.staged_positive_energy_cells > 0);
            }
        }
    }

    #[test]
    fn tropical_agreement_does_not_imply_equal_polynomials() {
        let a = Polynomial(vec![BigUint::from(1u8), BigUint::default()]);
        let b = Polynomial(vec![BigUint::from(1u8), BigUint::from(5u8)]);
        assert_eq!(a.leading(), b.leading());
        assert_ne!(a, b);
        // Multiplying and summing in the positive semiring still preserves
        // the leading pair. Recovering higher coefficients is impossible.
        let mut work = Work::default();
        assert_eq!(a.mul(&b, &mut work).leading(), a.leading());
    }
}
