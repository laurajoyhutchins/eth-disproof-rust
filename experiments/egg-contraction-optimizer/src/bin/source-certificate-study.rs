//! Reproducible, independently checked source contradiction-certificate pilot.
//!
//! Exact source-level checking and full polynomial verification run outside
//! each measured certified fold interval. Source clause copies, unit searches,
//! split probes, certificate replays, and the sparse count ARE in that interval.
//! Linux VmHWM is a shared case/process statistic, not a per-mode memory claim.

use egg_contraction_experiment::representation_study::adaptive::{
    held_out_cases, Case, CaseKind,
};
use egg_contraction_experiment::representation_study::zero_coefficient::certificates::run_modes;
use std::process::Command;

fn kind(s: &str) -> Result<CaseKind, String> {
    match s {
        "random-3cnf" => Ok(CaseKind::Random3Cnf),
        "planted-3cnf" => Ok(CaseKind::Planted3Cnf),
        "frustrated-xor3-cnf" => Ok(CaseKind::FrustratedXor3Cnf),
        _ => Err(format!("unknown kind: {s}")),
    }
}

fn peak_case_rss() -> Option<u64> {
    std::fs::read_to_string("/proc/self/status").ok()?
        .lines().find(|line| line.starts_with("VmHWM:"))?
        .split_whitespace().nth(1)?.parse().ok()
}

fn single(case: Case) -> Result<(), String> {
    let receipts = run_modes(case)?;
    let rss = peak_case_rss().map_or("null".into(), |x| x.to_string());
    for result in receipts {
        let m = result.work;
        let a = m.exact_arithmetic;
        println!(
            concat!(
                "{{\"case\":\"{}\",\"kind\":\"{}\",\"declared_variables\":{},",
                "\"clauses\":{},\"seed\":{},\"mode\":\"{}\",",
                "\"oracle\":\"{}\",\"source_count\":\"{}\",",
                "\"certified_count\":\"{}\",\"order\":{:?},",
                "\"same_case_sparse_baseline_elapsed_ns\":{},",
                "\"same_case_sparse_baseline_mult\":{},",
                "\"same_case_sparse_baseline_bit_work\":{},",
                "\"elapsed_ns\":{},\"queries\":{},\"future_clause_collections\":{},",
                "\"source_clause_copies\":{},\"copied_literal_instances\":{},",
                "\"clause_visits\":{},\"literal_reads\":{},\"derived_units\":{},",
                "\"split_probes\":{},\"checked_reason_literals\":{},",
                "\"checked_steps\":{},\"checked_witness_branches\":{},",
                "\"unit_refutations\":{},\"two_branch_refutations\":{},",
                "\"removed_entries\":{},\"budget_skips\":{},",
                "\"source_leaf_assignments\":{},\"source_rejects\":{},",
                "\"exact_merges\":{},\"exact_mult\":{},",
                "\"exact_bit_work_proxy\":{},\"compatible_pairs\":{},",
                "\"index_insertions\":{},\"index_lookups\":{},",
                "\"shared_case_peak_rss_kib\":{}}}"
            ),
            case.label(), case.kind.name(), case.declared_variables(),
            case.clauses, case.seed, result.mode.name(), result.independent_oracle,
            result.unguarded_sparse_count, result.satisfying_count, result.order,
            result.unguarded_sparse_elapsed_ns, result.unguarded_sparse_exact_mult,
            result.unguarded_sparse_bit_work_proxy,
            result.elapsed_ns, m.queries, m.future_clause_collections,
            m.source_clause_copies, m.copied_literal_instances,
            m.clause_visits, m.literal_reads, m.derived_units,
            m.split_probes, m.checked_reason_literals,
            m.checked_steps, m.independently_checked_witnesses,
            m.unit_refutations, m.two_branch_refutations,
            m.removed_entries, m.budget_skips, m.source_leaf_assignments,
            m.source_rejects, m.exact_merges, a.multiplications,
            a.bit_work_proxy, a.compatible_pair_visits,
            a.support_index_insertions, a.support_group_lookups, rss,
        );
    }
    Ok(())
}

fn run() -> Result<(), String> {
    let args = std::env::args().collect::<Vec<_>>();
    if args.len() == 6 && args[1] == "--single" {
        return single(Case {
            kind: kind(&args[2])?,
            variables: args[3].parse().map_err(|_| "invalid variables")?,
            clauses: args[4].parse().map_err(|_| "invalid clauses")?,
            seed: args[5].parse().map_err(|_| "invalid seed")?,
        });
    }
    if args.len() != 1 {
        return Err("usage: source-certificate-study [--single kind n m seed]".into());
    }
    let executable = std::env::current_exe()
        .map_err(|e| format!("cannot find current executable: {e}"))?;
    for case in held_out_cases() {
        let child = Command::new(&executable)
            .args([
                "--single", case.kind.name(),
                &case.variables.to_string(), &case.clauses.to_string(),
                &case.seed.to_string(),
            ]).output().map_err(|e| format!("spawn case: {e}"))?;
        if !child.status.success() {
            return Err(format!("case {} failed: {}", case.label(),
                String::from_utf8_lossy(&child.stderr)));
        }
        let lines = String::from_utf8(child.stdout)
            .map_err(|_| "non-UTF8 certificate receipts")?;
        if lines.lines().count() != 2 ||
            lines.lines().any(|line| !line.contains("\"oracle\":\"checked\""))
        {
            return Err(format!("invalid source certificate receipts for {}", case.label()));
        }
        print!("{lines}");
    }
    Ok(())
}

fn main() {
    if let Err(err) = run() {
        eprintln!("{err}");
        std::process::exit(1);
    }
}
