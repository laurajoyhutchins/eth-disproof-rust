//! Reproducible JSONL receipts for three exact SAT representations.
//! All three folds share factors, order and live-port policy. The direct
//! Boolean source enumeration is an independent, bounded correctness oracle.

use egg_contraction_experiment::affine_orders::Schedule;
use egg_contraction_experiment::representation_study::{run, StudyFamily};

fn main() -> Result<(), String> {
    for family in [
        StudyFamily::EqualityChain,
        StudyFamily::CirculantXor3,
        StudyFamily::FreeAmplifier,
        StudyFamily::Overlapping3Cnf,
        StudyFamily::FrustratedXor3Cnf,
    ] {
        let sizes: &[usize] = match family {
            StudyFamily::Overlapping3Cnf => &[3, 5, 8, 10],
            StudyFamily::FrustratedXor3Cnf => &[4, 6, 8, 10],
            _ => &[3, 5, 8],
        };
        for &size in sizes {
            for order in [
                Schedule::Sequential, Schedule::Reverse, Schedule::EvenFirst,
            ] {
                let r = run(family, size, order, &[])?;
                println!(
                    concat!(
                        "{{\"family\":\"{}\",\"size\":{},\"order\":\"{}\",",
                        "\"oracle\":\"checked\",",
                        "\"minimum_energy\":{},\"optimal_count\":\"{}\",",
                        "\"satisfying_count\":\"{}\",",
                        "\"peak_boundary_ports\":{},\"peak_table_cells\":{},",
                        "\"exact_peak_coefficient_slots\":{},",
                        "\"exact_peak_nonzero_coefficients\":{},",
                        "\"exact_additions\":{},\"exact_multiplications\":{},",
                        "\"exact_max_coefficient_bits\":{},",
                        "\"tropical_additions\":{},\"tropical_multiplications\":{},",
                        "\"tropical_max_count_bits\":{},",
                        "\"tropical_positive_energy_final_cells\":{},",
                        "\"tropical_staged_cells\":{},",
                        "\"tropical_staged_positive_energy_cells\":{},",
                        "\"factored_ast_nodes\":{},\"factored_port_name_occurrences\":{},",
                        "\"factored_elimination_binders\":{},",
                        "\"factored_forced_cached_states\":{},",
                        "\"factored_forced_cached_coefficient_slots\":{},",
                        "\"factored_forced_additions\":{},",
                        "\"factored_forced_multiplications\":{},",
                        "\"factored_forced_max_coefficient_bits\":{}}}"
                    ),
                    r.family, r.size, r.schedule,
                    r.minimum_energy, r.minimum_count, r.satisfying_count,
                    r.peak_boundary_ports, r.peak_table_cells,
                    r.peak_exact_coefficient_slots, r.peak_exact_nonzero_coefficients,
                    r.exact_work.additions, r.exact_work.multiplications,
                    r.exact_work.max_coefficient_bits,
                    r.tropical_work.additions, r.tropical_work.multiplications,
                    r.tropical_work.max_coefficient_bits,
                    r.tropical_positive_energy_cells,
                    r.staged_tropical_cells, r.staged_positive_energy_cells,
                    r.symbolic_nodes, r.symbolic_port_name_occurrences,
                    r.symbolic_eliminated_binders,
                    r.forced_cache_entries, r.forced_cache_coefficient_slots,
                    r.symbolic_work.additions, r.symbolic_work.multiplications,
                    r.symbolic_work.max_coefficient_bits,
                );
            }
        }
    }
    Ok(())
}
