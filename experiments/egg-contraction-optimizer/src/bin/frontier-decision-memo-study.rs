//! Compare the original certified pre-product clause check against
//! per-frontier memoization of forbidden-only or both Boolean decisions.
//!
//! New validation seeds are fixed in source before CI is examined.
//! Independent source enumeration, unguarded sparse, full-polynomial
//! coefficient checks and original direct-preproduct references are run
//! once per case; these costs are excluded from the measured memo fold.

use egg_contraction_experiment::representation_study::adaptive::{
    held_out_cases, Case, CaseKind,
};
use egg_contraction_experiment::representation_study::zero_coefficient::
    certificates::resolution_index::prejoin::memo::run_modes;
use std::process::Command;

const OLD_CACHE_SEEDS: [u64; 2] = [18_013, 18_029];
const OLD_RESOLUTION_SEEDS: [u64; 2] = [21_101, 21_113];
const OLD_PREPRODUCT_SEEDS: [u64; 2] = [23_039, 23_053];
const NEW_MEMO_SEEDS: [u64; 2] = [24_107, 24_131];

fn cases() -> Vec<Case> {
    let mut result = held_out_cases();
    for seed in OLD_CACHE_SEEDS.into_iter()
        .chain(OLD_RESOLUTION_SEEDS)
        .chain(OLD_PREPRODUCT_SEEDS)
        .chain(NEW_MEMO_SEEDS)
    {
        for variables in [8, 10] {
            for density in [2, 4] {
                for kind in [CaseKind::Random3Cnf, CaseKind::Planted3Cnf] {
                    result.push(Case {
                        kind, variables, clauses: variables * density, seed,
                    });
                }
            }
        }
    }
    result
}

fn kind(s: &str) -> Result<CaseKind, String> {
    match s {
        "random-3cnf" => Ok(CaseKind::Random3Cnf),
        "planted-3cnf" => Ok(CaseKind::Planted3Cnf),
        "frustrated-xor3-cnf" => Ok(CaseKind::FrustratedXor3Cnf),
        _ => Err(format!("unexpected source kind {s}")),
    }
}

fn peak_process_rss() -> Option<u64> {
    std::fs::read_to_string("/proc/self/status").ok()?
        .lines().find(|l| l.starts_with("VmHWM:"))?
        .split_whitespace().nth(1)?.parse().ok()
}

fn run_single(case: Case) -> Result<(), String> {
    let results = run_modes(case)?;
    let cohort = if NEW_MEMO_SEEDS.contains(&case.seed) {
        "fresh-validation"
    } else {
        "prior-controls"
    };
    let rss = peak_process_rss().map_or("null".to_string(), |value| value.to_string());
    for result in results {
        let work = result.work;
        let m = work.exact;
        let source = work.source;
        println!(concat!(
            "{{\"case\":\"{}\",\"cohort\":\"{}\",\"kind\":\"{}\",",
            "\"variables\":{},\"clauses\":{},\"seed\":{},",
            "\"mode\":\"{}\",\"oracle\":\"{}\",",
            "\"source_count\":\"{}\",\"final_count\":\"{}\",",
            "\"order\":{:?},\"elapsed_ns\":{},",
            "\"same_case_direct_preproduct_ns\":{},",
            "\"same_case_sparse_elapsed_ns\":{},",
            "\"sparse_multiplications\":{},\"direct_multiplications\":{},",
            "\"exact_multiplications\":{},\"exact_additions\":{},",
            "\"exact_bit_work_proxy\":{},",
            "\"compatible_pairs\":{},\"candidate_pairs_visited\":{},",
            "\"compiled_frontiers\":{},\"verified_source_clauses\":{},",
            "\"source_reason_literal_reads\":{},\"compiled_patterns\":{},",
            "\"preproduct_mask_tests\":{},\"candidate_products_refused\":{},",
            "\"memo_lookup_requests\":{},\"memo_hits_forbidden\":{},",
            "\"memo_hits_allowed\":{},\"memo_misses\":{},",
            "\"memo_inserts\":{},\"memo_capacity_refusals\":{},",
            "\"memo_incomplete_refusals\":{},",
            "\"memo_peak_entries\":{},",
            "\"memo_peak_payload_bytes_lower_bound\":{},",
            "\"budget_refusals\":{},",
            "\"peak_rule_payload_bytes_lower_bound\":{},",
            "\"source_leaf_assignments\":{},",
            "\"shared_case_peak_rss_kib\":{}}}"
        ),
            case.label(), cohort, case.kind.name(),
            case.declared_variables(), case.clauses, case.seed,
            result.mode.name(), result.oracle,
            result.source_count, result.result, result.order,
            result.elapsed_ns,
            result.direct_preproduct_elapsed_ns,
            result.sparse_elapsed_ns,
            result.sparse_multiplications,
            result.direct_multiplications,
            m.multiplications, m.additions, m.bit_work_proxy,
            m.compatible_pair_visits, work.candidate_pairs_visited,
            work.compiled_frontiers,
            work.proof_checked_original_clauses,
            work.source_provenance_literal_reads,
            source.verified_patterns,
            work.mask_tests_before_product,
            work.candidate_products_refused,
            work.memo_lookup_requests, work.memo_hits_forbidden,
            work.memo_hits_allowed, work.memo_misses,
            work.memo_inserts, work.memo_capacity_refusals,
            work.memo_incomplete_refusals, work.memo_peak_entries,
            work.memo_peak_payload_bytes_lower_bound,
            work.budget_refusals,
            work.peak_rule_payload_bytes_lower_bound,
            m.source_leaf_assignments,
            rss,
        );
    }
    Ok(())
}

fn run() -> Result<(), String> {
    let args = std::env::args().collect::<Vec<_>>();
    if args.len() == 6 && args[1] == "--single" {
        return run_single(Case {
            kind: kind(&args[2])?,
            variables: args[3].parse().map_err(|_| "invalid number of variables")?,
            clauses: args[4].parse().map_err(|_| "invalid number of clauses")?,
            seed: args[5].parse().map_err(|_| "invalid seed")?,
        });
    }
    if args.len() != 1 {
        return Err("usage: frontier-decision-memo-study [--single kind n m seed]".into());
    }
    let cases = cases();
    if cases.len() != 104 ||
        cases.iter().filter(|c| NEW_MEMO_SEEDS.contains(&c.seed)).count() != 16
    {
        return Err("fixed new validation cohort mismatch".into());
    }
    let exe = std::env::current_exe().map_err(|e| format!("executable lookup: {e}"))?;
    for case in cases {
        let child = Command::new(&exe).args([
            "--single", case.kind.name(),
            &case.variables.to_string(), &case.clauses.to_string(),
            &case.seed.to_string(),
        ]).output().map_err(|e| format!("child start: {e}"))?;
        if !child.status.success() {
            return Err(format!(
                "original source case {} refused: {}",
                case.label(), String::from_utf8_lossy(&child.stderr),
            ));
        }
        let output = String::from_utf8(child.stdout)
            .map_err(|_| "invalid UTF8 decision memo receipt")?;
        if output.lines().count() != 2 ||
            output.lines().any(|line| !line.contains("\"oracle\":\"checked\""))
        {
            return Err(format!("incomplete memo results for {}", case.label()));
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
