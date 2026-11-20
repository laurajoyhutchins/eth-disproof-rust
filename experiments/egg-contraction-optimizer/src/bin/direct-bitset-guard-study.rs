//! Fresh-cohort evaluation of a small direct-address output-guard
//! decision cache versus tree lookup and unconditionally direct checks.
//! All strategies use exactly the same source factor order and checked
//! original future-clause set. The cost gate examines no candidate pair.

use egg_contraction_experiment::representation_study::adaptive::{
    held_out_cases, Case, CaseKind,
};
use egg_contraction_experiment::representation_study::zero_coefficient::
    certificates::resolution_index::prejoin::bitset::run_modes;
use std::process::Command;

const OLD_SEEDS: [u64; 8] = [
    18_013, 18_029, 21_101, 21_113,
    23_039, 23_053, 24_107, 24_131,
];
const NEW_SEEDS: [u64; 2] = [25_117, 25_121];

fn cases() -> Vec<Case> {
    let mut cases = held_out_cases();
    for seed in OLD_SEEDS.into_iter().chain(NEW_SEEDS) {
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
        _ => Err(format!("unknown source case family {s}")),
    }
}

fn high_water_kib() -> Option<u64> {
    std::fs::read_to_string("/proc/self/status").ok()?
        .lines().find(|l| l.starts_with("VmHWM:"))?
        .split_whitespace().nth(1)?.parse().ok()
}

fn single(case: Case) -> Result<(), String> {
    let variants = run_modes(case)?;
    let cohort = if NEW_SEEDS.contains(&case.seed) {
        "fresh-validation"
    } else {
        "prior-controls"
    };
    let rss = high_water_kib().map_or("null".to_owned(), |v| v.to_string());
    for receipt in variants {
        let work = receipt.work;
        let m = work.exact;
        let source = work.source;
        println!(concat!(
            "{{\"case\":\"{}\",\"cohort\":\"{}\",\"kind\":\"{}\",",
            "\"variables\":{},\"clauses\":{},\"seed\":{},",
            "\"policy\":\"{}\",\"oracle\":\"{}\",",
            "\"source_count\":\"{}\",\"final_count\":\"{}\",",
            "\"order\":{:?},",
            "\"elapsed_ns\":{},\"direct_ns\":{},\"tree_ns\":{},\"sparse_ns\":{},",
            "\"direct_mask_tests\":{},\"tree_mask_tests\":{},",
            "\"sparse_mult\":{},\"direct_mult\":{},\"tree_mult\":{},",
            "\"exact_mult\":{},\"exact_add\":{},\"exact_bitwork\":{},",
            "\"candidate_pairs\":{},\"source_clauses_checked\":{},",
            "\"preproduct_mask_tests\":{},\"candidate_products_refused\":{},",
            "\"memo_lookups\":{},\"memo_true_hits\":{},\"memo_false_hits\":{},",
            "\"memo_misses\":{},\"memo_inserts\":{},",
            "\"memo_peak_entries\":{},\"memo_payload_bytes_lower_bound\":{},",
            "\"bitset_gate_calls\":{},\"bitset_gate_port_reads\":{},",
            "\"bitset_admitted\":{},\"bitset_declined_width\":{},",
            "\"bitset_declined_estimate\":{},",
            "\"bitset_estimated_pairs\":{},\"bitset_estimated_excess\":{},",
            "\"bitset_peak_state_bytes\":{},",
            "\"bitset_out_of_range\":{},\"memo_incomplete\":{},",
            "\"memo_capacity_refusals\":{},\"budget_refusals\":{},",
            "\"source_leaf_assignments\":{},",
            "\"shared_case_peak_rss_kib\":{}}}"
        ),
            case.label(), cohort, case.kind.name(),
            case.declared_variables(), case.clauses, case.seed,
            receipt.policy_name, receipt.oracle, receipt.source_count,
            receipt.final_count, receipt.order,
            receipt.elapsed_ns, receipt.direct_ns, receipt.tree_ns,
            receipt.sparse_ns, receipt.direct_mask_tests,
            receipt.tree_mask_tests, receipt.sparse_mult,
            receipt.direct_mult, receipt.tree_mult,
            m.multiplications, m.additions, m.bit_work_proxy,
            work.candidate_pairs_visited,
            work.proof_checked_original_clauses,
            work.mask_tests_before_product,
            work.candidate_products_refused,
            work.memo_lookup_requests,
            work.memo_hits_forbidden, work.memo_hits_allowed,
            work.memo_misses, work.memo_inserts,
            work.memo_peak_entries, work.memo_peak_payload_bytes_lower_bound,
            work.bitset_gate_calls, work.bitset_gate_port_reads,
            work.bitset_admitted_frontiers, work.bitset_declined_width,
            work.bitset_declined_estimate,
            work.bitset_estimated_compatible_pairs,
            work.bitset_estimated_excess_pairs,
            work.bitset_peak_state_bytes,
            work.bitset_fallback_out_of_range,
            work.memo_incomplete_refusals,
            work.memo_capacity_refusals, work.budget_refusals,
            m.source_leaf_assignments, rss,
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
        return Err("usage: direct-bitset-guard-study [--single kind n m seed]".into());
    }
    let list = cases();
    if list.len() != 120 ||
        list.iter().filter(|c| NEW_SEEDS.contains(&c.seed)).count() != 16
    {
        return Err("frozen direct-bitset benchmark cohort changed".into());
    }
    let exe = std::env::current_exe().map_err(|e| format!("executable path: {e}"))?;
    for case in list {
        let child = Command::new(&exe).args([
            "--single", case.kind.name(), &case.variables.to_string(),
            &case.clauses.to_string(), &case.seed.to_string(),
        ]).output().map_err(|e| format!("subprocess: {e}"))?;
        if !child.status.success() {
            return Err(format!(
                "source case {} failed: {}",
                case.label(), String::from_utf8_lossy(&child.stderr),
            ));
        }
        let output = String::from_utf8(child.stdout)
            .map_err(|_| "bad UTF-8 in source receipt")?;
        if output.lines().count() != 3 ||
            output.lines().any(|line| !line.contains("\"oracle\":\"checked\""))
        {
            return Err(format!("source receipts incomplete for {}", case.label()));
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
