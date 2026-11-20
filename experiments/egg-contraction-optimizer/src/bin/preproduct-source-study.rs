//! Original-source necessary constraints checked before BigUint products.
//! 72 prior controls plus 16 newly fixed seed instances, two identical
//! compilation policies differing only in pre/post multiplication placement.

use egg_contraction_experiment::representation_study::adaptive::{
    held_out_cases, Case, CaseKind,
};
use egg_contraction_experiment::representation_study::zero_coefficient::
    certificates::resolution_index::prejoin::run_modes;
use std::process::Command;

const OLD_CACHE_SEEDS: [u64; 2] = [18_013, 18_029];
const OLD_RESOLUTION_SEEDS: [u64; 2] = [21_101, 21_113];
const NEW_PREPRODUCT_SEEDS: [u64; 2] = [23_039, 23_053];

fn cases() -> Vec<Case> {
    let mut cases = held_out_cases();
    for seed in OLD_CACHE_SEEDS.into_iter()
        .chain(OLD_RESOLUTION_SEEDS)
        .chain(NEW_PREPRODUCT_SEEDS)
    {
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

fn kind(s: &str) -> Result<CaseKind, String> {
    match s {
        "random-3cnf" => Ok(CaseKind::Random3Cnf),
        "planted-3cnf" => Ok(CaseKind::Planted3Cnf),
        "frustrated-xor3-cnf" => Ok(CaseKind::FrustratedXor3Cnf),
        _ => Err(format!("unknown CNF case kind {s}")),
    }
}

fn rss() -> Option<u64> {
    std::fs::read_to_string("/proc/self/status").ok()?
        .lines().find(|line| line.starts_with("VmHWM:"))?
        .split_whitespace().nth(1)?.parse().ok()
}

fn single(case: Case) -> Result<(), String> {
    let receipts = run_modes(case)?;
    let cohort = if NEW_PREPRODUCT_SEEDS.contains(&case.seed) {
        "fresh-validation"
    } else { "prior-controls" };
    let peak = rss().map_or("null".to_string(), |r| r.to_string());
    for r in receipts {
        let work = r.work;
        let ex = work.exact;
        let src = work.source;
        println!(concat!(
            "{{\"case\":\"{}\",\"cohort\":\"{}\",\"kind\":\"{}\",",
            "\"variables\":{},\"clauses\":{},\"seed\":{},",
            "\"placement\":\"{}\",\"oracle\":\"{}\",",
            "\"source_count\":\"{}\",\"final_count\":\"{}\",",
            "\"order\":{:?},\"elapsed_ns\":{},",
            "\"same_case_sparse_elapsed_ns\":{},",
            "\"same_case_old_postjoin_ns\":{},",
            "\"sparse_mult\":{},\"old_postjoin_mult\":{},",
            "\"exact_mult\":{},\"exact_add\":{},\"exact_bit_work\":{},",
            "\"compatible_pairs\":{},",
            "\"candidate_pairs_visited\":{},\"compiled_frontiers\":{},",
            "\"source_clause_collections\":{},",
            "\"collected_clauses\":{},\"collected_literals\":{},",
            "\"source_nodes_checked\":{},",
            "\"source_reason_literals_checked\":{},",
            "\"proof_checked_original_clauses\":{},",
            "\"source_provenance_literal_reads\":{},",
            "\"verified_patterns\":{},\"direct_patterns\":{},",
            "\"mask_tests_before_product\":{},",
            "\"mask_tests_after_join\":{},",
            "\"candidate_products_refused\":{},",
            "\"final_outputs_refused\":{},",
            "\"skipped_low_support\":{},\"skipped_large_source\":{},",
            "\"budget_refusals\":{},\"peak_rules\":{},",
            "\"peak_rule_payload_bytes_lower_bound\":{},",
            "\"index_inserts\":{},\"group_lookups\":{},",
            "\"source_leaf_assignments\":{},",
            "\"shared_case_peak_rss_kib\":{}}}"
        ),
            case.label(), cohort, case.kind.name(),
            case.declared_variables(), case.clauses, case.seed,
            r.placement.name(), r.oracle, r.expected_count, r.final_count,
            r.order, r.elapsed_ns, r.same_case_unpruned_sparse_ns,
            r.same_case_old_postjoin_ns,
            r.same_case_unpruned_mult, r.same_case_old_postjoin_mult,
            ex.multiplications, ex.additions, ex.bit_work_proxy,
            ex.compatible_pair_visits,
            work.candidate_pairs_visited, work.compiled_frontiers,
            src.source_clause_collections, src.collected_clauses,
            src.collected_literals, src.source_nodes_checked,
            src.source_reason_literals_checked,
            work.proof_checked_original_clauses,
            work.source_provenance_literal_reads,
            src.verified_patterns, src.direct_patterns,
            work.mask_tests_before_product,
            work.mask_tests_after_join,
            work.candidate_products_refused, work.final_outputs_refused,
            work.skipped_low_support, work.skipped_large_source,
            work.budget_refusals, work.peak_rules,
            work.peak_rule_payload_bytes_lower_bound,
            ex.support_index_insertions, ex.support_group_lookups,
            ex.source_leaf_assignments, peak,
        );
    }
    Ok(())
}

fn run() -> Result<(), String> {
    let args = std::env::args().collect::<Vec<_>>();
    if args.len() == 6 && args[1] == "--single" {
        return single(Case {
            kind: kind(&args[2])?,
            variables: args[3].parse().map_err(|_| "bad variable count")?,
            clauses: args[4].parse().map_err(|_| "bad clause count")?,
            seed: args[5].parse().map_err(|_| "bad seed")?,
        });
    }
    if args.len() != 1 {
        return Err("usage: preproduct-source-study [--single kind n m seed]".into());
    }
    let expected = cases();
    if expected.len() != 88 ||
        expected.iter().filter(|c| NEW_PREPRODUCT_SEEDS.contains(&c.seed)).count() != 16
    {
        return Err("fixed benchmark split changed".into());
    }
    let exe = std::env::current_exe().map_err(|e| format!("executable: {e}"))?;
    for case in expected {
        let child = Command::new(&exe).args([
            "--single", case.kind.name(), &case.variables.to_string(),
            &case.clauses.to_string(), &case.seed.to_string(),
        ]).output().map_err(|e| format!("subprocess: {e}"))?;
        if !child.status.success() {
            return Err(format!("case {} failed: {}",
                case.label(), String::from_utf8_lossy(&child.stderr)));
        }
        let output = String::from_utf8(child.stdout)
            .map_err(|_| "non-UTF8 benchmark output")?;
        if output.lines().count() != 2 ||
            output.lines().any(|line| !line.contains("\"oracle\":\"checked\""))
        {
            return Err(format!("missing source receipt for {}", case.label()));
        }
        print!("{output}");
    }
    Ok(())
}

fn main() {
    if let Err(error) = run() {
        eprintln!("{error}");
        std::process::exit(1);
    }
}
