//! Explicit bounded tropical shadow of the *existing* affine factor families.
//!
//! Each cell is an exact minimum-violation energy and its multiplicity.
//! This table implementation intentionally enumerates boundary assignments;
//! its measurements cannot establish efficient compression or bit complexity.

use crate::affine::AffineRegion;
use crate::affine_orders::{generate, kept_port_set, Family, Limits, Schedule};
use num_bigint::BigUint;
use std::collections::{BTreeMap, BTreeSet};

const MAX_PORTS: usize = 16;
const MAX_ORACLE_VARIABLES: usize = 16;

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Leading {
    pub energy: usize,
    pub count: BigUint,
}

#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct OperationCounts {
    pub multiplications: u64,
    pub additions: u64,
    pub leading_ties: u64,
}

type Cell = Option<Leading>; // None is the additive zero.

fn add_cell(left: Cell, right: Cell, ops: &mut OperationCounts) -> Cell {
    ops.additions += 1;
    match (left, right) {
        (None, b) => b,
        (a, None) => a,
        (Some(a), Some(b)) => {
            if a.energy < b.energy {
                Some(a)
            } else if b.energy < a.energy {
                Some(b)
            } else {
                ops.leading_ties += 1;
                Some(Leading {
                    energy: a.energy,
                    count: a.count + b.count,
                })
            }
        }
    }
}

fn mul_cell(left: &Cell, right: &Cell, ops: &mut OperationCounts) -> Result<Cell, String> {
    ops.multiplications += 1;
    match (left, right) {
        (Some(a), Some(b)) => Ok(Some(Leading {
            energy: a.energy.checked_add(b.energy).ok_or("energy overflow")?,
            count: &a.count * &b.count,
        })),
        _ => Ok(None),
    }
}

fn port_count(width: usize) -> Result<usize, String> {
    if width > MAX_PORTS || width >= usize::BITS as usize {
        return Err(format!("explicit tropical table refuses {width} ports"));
    }
    Ok(1usize << width)
}

fn projected_mask(mask: usize, from: &[String], to: &[String]) -> Result<usize, String> {
    let mut result = 0;
    for (bit, name) in to.iter().enumerate() {
        let position = from.binary_search(name)
            .map_err(|_| format!("missing shared port {name}"))?;
        if mask & (1 << position) != 0 {
            result |= 1 << bit;
        }
    }
    Ok(result)
}

#[derive(Clone, Debug)]
pub struct Interface {
    pub ports: Vec<String>,
    pub cells: Vec<Cell>,
}

impl Interface {
    fn from_region(region: &AffineRegion) -> Result<Self, String> {
        let ports = region.internal.iter().chain(&region.boundary)
            .cloned().collect::<BTreeSet<_>>().into_iter().collect::<Vec<_>>();
        if ports.len() != region.internal.len() + region.boundary.len() {
            return Err("duplicate source port".into());
        }
        let mut cells = Vec::with_capacity(port_count(ports.len())?);
        for mask in 0..port_count(ports.len())? {
            let value = |name: &String| -> Result<bool, String> {
                let bit = ports.binary_search(name)
                    .map_err(|_| format!("undeclared equation port {name}"))?;
                Ok(mask & (1 << bit) != 0)
            };
            let mut energy = 0usize;
            for eq in &region.equations {
                let mut parity = false;
                for name in &eq.variables {
                    parity ^= value(name)?;
                }
                if parity != eq.rhs {
                    energy += 1;
                }
            }
            cells.push(Some(Leading { energy, count: BigUint::from(1u8) }));
        }
        Ok(Self { ports, cells })
    }

    fn merge_and_project(
        &self,
        next: &Self,
        keep: &BTreeSet<String>,
        ops: &mut OperationCounts,
    ) -> Result<Self, String> {
        let ports = self.ports.iter().chain(&next.ports)
            .cloned().collect::<BTreeSet<_>>().into_iter().collect::<Vec<_>>();
        if !keep.is_subset(&ports.iter().cloned().collect()) {
            return Err("retained port absent from input factors".into());
        }
        let output = keep.iter().cloned().collect::<Vec<_>>();
        let mut cells = vec![None; port_count(output.len())?];
        for mask in 0..port_count(ports.len())? {
            let left = projected_mask(mask, &ports, &self.ports)?;
            let right = projected_mask(mask, &ports, &next.ports)?;
            let output_mask = projected_mask(mask, &ports, &output)?;
            let product = mul_cell(&self.cells[left], &next.cells[right], ops)?;
            let previous = cells[output_mask].take();
            cells[output_mask] = add_cell(previous, product, ops);
        }
        Ok(Self { ports: output, cells })
    }
}

#[derive(Clone, Debug)]
pub struct Receipt {
    pub schedule: Schedule,
    pub peak_boundary_ports: usize,
    pub peak_table_cells: usize,
    pub final_distinct_energies: usize,
    pub max_multiplicity_bits: u64,
    pub operations: OperationCounts,
    pub final_interface: Interface,
}

pub fn fold(
    factors: &[AffineRegion],
    schedule: Schedule,
    output: &[String],
) -> Result<Receipt, String> {
    if factors.len() < 2 {
        return Err("need two or more factors".into());
    }
    let order = schedule.indices(factors.len());
    let leaves = factors.iter().map(Interface::from_region)
        .collect::<Result<Vec<_>, _>>()?;
    let outputs = output.iter().cloned().collect::<BTreeSet<_>>();
    if outputs.len() != output.len() {
        return Err("duplicate output ports".into());
    }
    let output = outputs;
    let all_ports = leaves.iter().flat_map(|f| f.ports.iter().cloned())
        .collect::<BTreeSet<_>>();
    if !output.is_subset(&all_ports) {
        return Err("unknown output port".into());
    }
    let mut stage = leaves[order[0]].clone();
    let mut peak_boundary_ports = stage.ports.len();
    let mut peak_table_cells = stage.cells.len();
    let mut max_multiplicity_bits = 1;
    let mut operations = OperationCounts::default();
    for (step, &index) in order.iter().enumerate().skip(1) {
        let future = order[step + 1..].iter().flat_map(|&i| leaves[i].ports.iter().cloned())
            .collect::<BTreeSet<_>>();
        let active = stage.ports.iter().cloned().collect::<BTreeSet<_>>();
        let next = leaves[index].ports.iter().cloned().collect::<BTreeSet<_>>();
        let retained = kept_port_set(&active, &next, &future, &output);
        stage = stage.merge_and_project(&leaves[index], &retained, &mut operations)?;
        peak_boundary_ports = peak_boundary_ports.max(stage.ports.len());
        peak_table_cells = peak_table_cells.max(stage.cells.len());
        for value in stage.cells.iter().flatten() {
            max_multiplicity_bits = max_multiplicity_bits.max(value.count.bits());
        }
    }
    if stage.ports.iter().cloned().collect::<BTreeSet<_>>() != output {
        return Err("final boundary not equal to specified output".into());
    }
    let final_distinct_energies = stage.cells.iter().flatten()
        .map(|cell| cell.energy).collect::<BTreeSet<_>>().len();
    Ok(Receipt {
        schedule, peak_boundary_ports, peak_table_cells, final_distinct_energies,
        max_multiplicity_bits, operations, final_interface: stage,
    })
}

/// Independent source-level enumeration, retaining *every* coefficient.
/// Never called by the contraction algorithm. Exponential and bounded.
pub fn polynomial_oracle(
    factors: &[AffineRegion],
    boundary: &BTreeMap<String, bool>,
) -> Result<Vec<BigUint>, String> {
    let all = factors.iter()
        .flat_map(|f| f.internal.iter().chain(&f.boundary).cloned())
        .collect::<BTreeSet<_>>();
    if !boundary.keys().all(|name| all.contains(name)) {
        return Err("oracle has unknown boundary port".into());
    }
    let free = all.difference(&boundary.keys().cloned().collect())
        .cloned().collect::<Vec<_>>();
    if free.len() > MAX_ORACLE_VARIABLES {
        return Err("oracle enumeration limit exceeded".into());
    }
    let mut histogram = vec![BigUint::from(0u8); factors.iter()
        .map(|f| f.equations.len()).sum::<usize>() + 1];
    for mask in 0..(1usize << free.len()) {
        let mut assignment = boundary.clone();
        for (i, name) in free.iter().enumerate() {
            assignment.insert(name.clone(), mask & (1 << i) != 0);
        }
        let energy = factors.iter().flat_map(|f| &f.equations)
            .filter(|eq| {
                eq.variables.iter().fold(false, |parity, name| parity ^ assignment[name]) != eq.rhs
            }).count();
        histogram[energy] += 1u8;
    }
    Ok(histogram)
}

pub fn leading_of_polynomial(coeffs: &[BigUint]) -> Cell {
    coeffs.iter().enumerate().find(|(_, c)| **c != BigUint::from(0u8))
        .map(|(energy, count)| Leading { energy, count: count.clone() })
}

pub fn trial(family: Family, size: usize) -> Result<Vec<Receipt>, String> {
    let factors = generate(family, size)?;
    [Schedule::Sequential, Schedule::Reverse, Schedule::EvenFirst]
        .into_iter().map(|order| fold(&factors, order, &[])).collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::affine_orders;

    fn assert_equivalent(family: Family, size: usize, output: &[String]) {
        let factors = generate(family, size).unwrap();
        let traces = [Schedule::Sequential, Schedule::Reverse, Schedule::EvenFirst]
            .map(|schedule| fold(&factors, schedule, output).unwrap());
        for mask in 0..(1usize << output.len()) {
            let fixed = output.iter().enumerate().map(|(i, name)| {
                (name.clone(), mask & (1 << i) != 0)
            }).collect::<BTreeMap<_, _>>();
            let full = polynomial_oracle(&factors, &fixed).unwrap();
            let expected = leading_of_polynomial(&full);
            for trace in &traces {
                let idx = projected_mask(mask, output, &trace.final_interface.ports).unwrap();
                assert_eq!(trace.final_interface.cells[idx], expected,
                    "family={family:?} size={size} schedule={:?} fixed={fixed:?}",
                    trace.schedule);
            }
            // An independent, non-enumerating GF(2) affine evaluator verifies
            // the degree-zero coefficient, not the higher-energy histogram.
            let exact_count = affine_orders::fold(
                &factors, &Schedule::Sequential.indices(size), output,
                &Limits::default()).unwrap().stage.count_at(&fixed).unwrap();
            assert_eq!(full[0], exact_count);
        }
    }

    #[test]
    fn tropical_boundary_matches_full_polynomial_and_affine_counts() {
        for size in 3..=5 {
            assert_equivalent(Family::Chain, size, &[]);
            assert_equivalent(Family::Chain, size, &["x0".into(), format!("x{size}")]);
            assert_equivalent(Family::CirculantXor3, size, &[]);
            assert_equivalent(Family::CirculantXor3, size, &["x0".into(), "x1".into()]);
            assert_equivalent(Family::FreeAmplifiers, size, &[]);
        }
    }

    #[test]
    fn same_tropical_summary_can_hide_different_past_work() {
        let factors = generate(Family::Chain, 10).unwrap();
        let a = fold(&factors, Schedule::Sequential, &[]).unwrap();
        let b = fold(&factors, Schedule::EvenFirst, &[]).unwrap();
        assert_eq!(a.final_interface.cells, b.final_interface.cells);
        assert!(b.peak_boundary_ports > a.peak_boundary_ports);
    }

    #[test]
    fn inconsistent_constraints_count_minimizers_not_solutions() {
        use crate::affine::Equation;
        let factors = [false, true].map(|rhs| AffineRegion {
            internal: Vec::new(),
            boundary: vec!["x".to_string()],
            equations: vec![Equation { variables: vec!["x".to_string()], rhs }],
        });
        let trace = fold(&factors, Schedule::Sequential, &[]).unwrap();
        let polynomial = polynomial_oracle(&factors, &BTreeMap::new()).unwrap();
        assert_eq!(polynomial, vec![BigUint::from(0u8), BigUint::from(2u8), BigUint::from(0u8)]);
        assert_eq!(trace.final_interface.cells, vec![Some(Leading {
            energy: 1,
            count: BigUint::from(2u8),
        })]);
        let satisfying = affine_orders::fold(
            &factors, &Schedule::Sequential.indices(2), &[], &Limits::default()
        ).unwrap().stage.count_at(&BTreeMap::new()).unwrap();
        assert_eq!(satisfying, BigUint::from(0u8));
    }

    #[test]
    fn refusal_and_tie_counts_are_explicit() {
        let factors = generate(Family::FreeAmplifiers, 3).unwrap();
        let trace = fold(&factors, Schedule::Sequential, &[]).unwrap();
        assert_eq!(trace.final_interface.cells, vec![Some(Leading {
            energy: 0, count: BigUint::from(64u8),
        })]);
        assert!(trace.operations.leading_ties > 0);
        assert!(trial(Family::Chain, 17).is_err()); // Explicit table cap.
    }
}
