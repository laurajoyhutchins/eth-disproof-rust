//! Bounded per-frontier original-clause resolution index for exact #SAT.
//!
//! 56 previously examined controls, 16 new validation formulas. Modes and
//! budgets were frozen before inspecting the new seeds. Each case computes
//! its original source oracle/full polynomial, unpruned sparse executor,
//! and source-unit reference independently of the indexed alternatives.

use egg_contraction_experiment::representation_study::adaptive::{
    held_out_cases, Case, CaseKind,
};
use egg_contraction_experiment::representation_study::zero_coefficient::
    certificates::resolution_index::run_modes;
use std::process::Command;

const PRIOR_NOGOOD_SEEDS: [u64; 2] = [18_013, 18_029];
const NEW_RESOLUTION_SEEDS: [u64; 2] = [21_101, 21_113];

fn cases() -> Vec<Case> {
    let mut cases = held_out_cases();
    for seed in PRIOR_NOGOOD_SEEDS.into_iter().chain(NEW_RESOLUTION_SEEDS) {
        for variables in [8, 10] {
            for density in [2, 4] {
                for kind in [CaseKind::Random3Cnf, CaseKind::Planted3Cnf] {
                    cases.push(Case {
                        kind, variables, clauses: variables * density, seed,
                    });
                }
            }
        }
    }
    cases
}

fn parse_kind(s: &str) -> Result<CaseKind, String> {
    match s {
        "random-3cnf" => Ok(CaseKind::Random3Cnf),
        "planted-3cnf" => Ok(CaseKind::Planted3Cnf),
        "frustrated-xor3-cnf" => Ok(CaseKind::FrustratedXor3Cnf),
        _ => Err(format!("unknown source case kind: {s}")),
    }
}

fn peak_case_rss() -> Option<u64> {
    std::fs::read_to_string("/proc/self/status").ok()?
        .lines().find(|line| line.starts_with("VmHWM:"))?
        .split_whitespace().nth(1)?.parse().ok()
}

fn single(case: Case) -> Result<(), String> {
    let variants = run_modes(case)?;
    let cohort = if NEW_RESOLUTION_SEEDS.contains(&case.seed) {
        "fresh-validation"
    } else { "previously-examined" };
    let rss = peak_case_rss().map_or("null".into(), |r| r.to_string());
    for v in variants {
        let m = v.work;
        println!(concat!(
            "{{\"case\":\"{}\",\"cohort\":\"{}\",\"kind\":\"{}\",",
            "\"variables\":{},\"clauses\":{},\"seed\":{},",
            "\"mode\":\"{}\",\"oracle\":\"{}\",",
            "\"source_count\":\"{}\",\"final_count\":\"{}\",",
            "\"order\":{:?},\"elapsed_ns\":{},",
            "\"same_case_sparse_elapsed_ns\":{},",
            "\"same_case_uncached_unit_elapsed_ns\":{},",
            "\"sparse_mult\":{},\"uncached_unit_mult\":{},",
            "\"exact_mult\":{},\"exact_bit_work\":{},",
            "\"source_clause_collections\":{},",
            "\"collected_clauses\":{},\"collected_literals\":{},",
            "\"source_nodes_checked\":{},\"source_reason_literals_checked\":{},",
            "\"pair_scans\":{},\"pivot_candidate_reads\":{},",
            "\"resolution_constructed\":{},",
            "\"resolution_tautology_refusals\":{},",
            "\"resolution_width_refusals\":{},",
            "\"resolution_duplicate_refusals\":{},",
            "\"resolution_budget_refusals\":{},",
            "\"derived_nodes_checked\":{},\"replay_literal_reads\":{},",
            "\"verified_patterns\":{},\"direct_patterns\":{},",
            "\"derived_patterns\":{},\"pattern_mask_comparisons\":{},",
            "\"rejected_boundary_entries\":{},",
            "\"frontier_compilations\":{},",
            "\"skipped_small_support\":{},\"skipped_large_source\":{},",
            "\"peak_source_nodes\":{},\"peak_derived_nodes\":{},",
            "\"peak_patterns\":{},\"peak_encoded_index_bytes_lower_bound\":{},",
            "\"compatible_pairs\":{},\"source_leaf_assignments\":{},",
            "\"shared_case_rss_peak_kib\":{}}}"
        ),
            case.label(), cohort, case.kind.name(),
            case.declared_variables(), case.clauses, case.seed,
            v.mode.name(), v.oracle, v.expected_count, v.final_count,
            v.order, v.elapsed_ns,
            v.same_case_sparse_elapsed_ns, v.same_case_uncached_unit_elapsed_ns,
            v.sparse_multiplications, v.unit_multiplications,
            m.exact.multiplications, m.exact.bit_work_proxy,
            m.source_clause_collections, m.collected_clauses,
            m.collected_literals, m.source_nodes_checked,
            m.source_reason_literals_checked,
            m.pair_scans, m.pivot_candidate_reads,
            m.resolution_constructed, m.resolution_tautology_refusals,
            m.resolution_width_refusals, m.resolution_duplicate_refusals,
            m.resolution_budget_refusals, m.derived_nodes_checked,
            m.replay_literal_reads, m.verified_patterns,
            m.direct_patterns, m.derived_patterns,
            m.pattern_mask_comparisons, m.rejected_boundary_entries,
            m.frontier_compilations, m.skipped_small_support,
            m.skipped_large_source, m.peak_source_nodes,
            m.peak_derived_nodes, m.peak_patterns,
            m.peak_encoded_index_bytes_lower_bound,
            m.exact.compatible_pair_visits, m.exact.source_leaf_assignments,
            rss,
        );
    }
    Ok(())
}

fn run() -> Result<(), String> {
    let args = std::env::args().collect::<Vec<_>>();
    if args.len() == 6 && args[1] == "--single" {
        return single(Case {
            kind: parse_kind(&args[2])?,
            variables: args[3].parse().map_err(|_| "invalid variable count")?,
            clauses: args[4].parse().map_err(|_| "invalid clause count")?,
            seed: args[5].parse().map_err(|_| "invalid seed")?,
        });
    }
    if args.len() != 1 {
        return Err("usage: frontier-resolution-study [--single kind n m seed]".into());
    }
    let prepared = cases();
    if prepared.len() != 72 ||
        prepared.iter().filter(|case| NEW_RESOLUTION_SEEDS.contains(&case.seed)).count() != 16
    {
        return Err("cohort split changed after policy was frozen".into());
    }
    let exe = std::env::current_exe()
        .map_err(|e| format!("cannot access executable path: {e}"))?;
    for case in prepared {
        let child = Command::new(&exe).args([
            "--single", case.kind.name(), &case.variables.to_string(),
            &case.clauses.to_string(), &case.seed.to_string(),
        ]).output().map_err(|e| format!("source study spawn: {e}"))?;
        if !child.status.success() {
            return Err(format!("source study {} failed: {}",
                case.label(), String::from_utf8_lossy(&child.stderr)));
        }
        let output = String::from_utf8(child.stdout)
            .map_err(|_| "invalid UTF8 source index output")?;
        if output.lines().count() != 2 ||
            output.lines().any(|line| !line.contains("\"oracle\":\"checked\""))
        {
            return Err(format!("source index receipt missing for {}", case.label()));
        }
        print!("{output}");
    }
    Ok(())
}

fn main() {
    if let Err(e) = run() {
        eprintln!("{e}");
        std::process::exit(1);
    }
}
