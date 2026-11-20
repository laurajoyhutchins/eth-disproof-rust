//! Reproducible bounded tropical order study. This is an explicit-table
//! comparison, not a compact general-SAT contraction implementation.

use egg_contraction_experiment::affine_orders::{generate, Family, Schedule};
use egg_contraction_experiment::tropical_orders::{
    fold, leading_of_polynomial, polynomial_oracle,
};
use std::collections::BTreeMap;
use std::time::Instant;

fn main() -> Result<(), String> {
    let sizes = [3usize, 5, 8];
    for family in [Family::Chain, Family::CirculantXor3, Family::FreeAmplifiers] {
        for &size in &sizes {
            let factors = generate(family, size)?;
            let oracle = polynomial_oracle(&factors, &BTreeMap::new())?;
            let expected = leading_of_polynomial(&oracle);
            for schedule in [Schedule::Sequential, Schedule::Reverse, Schedule::EvenFirst] {
                let start = Instant::now();
                let receipt = fold(&factors, schedule, &[])?;
                let elapsed_ns = start.elapsed().as_nanos();
                let actual = &receipt.final_interface.cells[0];
                if actual != &expected {
                    return Err(format!("tropical/full-polynomial disagreement for {} size={size} order={}",
                        family.name(), schedule.name()));
                }
                let (energy, optimal_count) = actual.as_ref()
                    .map(|a| (a.energy.to_string(), a.count.to_string()))
                    .unwrap_or_else(|| ("null".to_string(), "0".to_string()));
                println!(
                    "{{\"family\":\"{}\",\"size\":{},\"order\":\"{}\",\"oracle\":\"checked\",\"minimum_energy\":{},\"optimal_count\":\"{}\",\"peak_boundary_ports\":{},\"peak_table_cells\":{},\"distinct_final_energies\":{},\"leading_ties\":{},\"additions\":{},\"multiplications\":{},\"max_multiplicity_bits\":{},\"elapsed_ns\":{}}}",
                    family.name(), size, schedule.name(), energy, optimal_count,
                    receipt.peak_boundary_ports, receipt.peak_table_cells,
                    receipt.final_distinct_energies, receipt.operations.leading_ties,
                    receipt.operations.additions, receipt.operations.multiplications,
                    receipt.max_multiplicity_bits, elapsed_ns,
                );
            }
        }
    }
    Ok(())
}
