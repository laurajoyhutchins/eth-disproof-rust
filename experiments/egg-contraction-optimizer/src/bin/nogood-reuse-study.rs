//! Isolated, checked experiment for frontier-scoped nogood amortization.
//!
//! The cache policy (64 entries/frontier, 256 proof-only minimization trials,
//! 200,000 charged lookup-literal tests) was fixed before viewing the new
//! seeds. The 16 new source cases intentionally use seeds unseen in the
//! preceding unit-refutation study; the original 40 are calibration controls.

use egg_contraction_experiment::representation_study::adaptive::{
    held_out_cases, Case, CaseKind,
};
use egg_contraction_experiment::representation_study::zero_coefficient::
    certificates::nogood::run_modes;
use std::process::Command;

const FRESH_SEEDS: [u64; 2] = [18_013, 18_029];

fn cases() -> Vec<Case> {
    let mut cases = held_out_cases();
    for variables in [8, 10] {
        for seed in FRESH_SEEDS {
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
        _ => Err(format!("unknown case kind {s}")),
    }
}

fn peak_rss() -> Option<u64> {
    std::fs::read_to_string("/proc/self/status").ok()?
        .lines().find(|line| line.starts_with("VmHWM:"))?
        .split_whitespace().nth(1)?.parse().ok()
}

fn single(case: Case) -> Result<(), String> {
    let results = run_modes(case)?;
    let rss = peak_rss().map_or("null".to_owned(), |x| x.to_string());
    for r in results {
        let m = r.work;
        let b = m.baseline;
        let a = b.exact_arithmetic;
        let cohort = if FRESH_SEEDS.contains(&case.seed) {
            "fresh-validation"
        } else { "prior-controls" };
        println!(concat!(
            "{{\"case\":\"{}\",\"kind\":\"{}\",\"cohort\":\"{}\",",
            "\"declared_variables\":{},\"clauses\":{},\"seed\":{},",
            "\"mode\":\"{}\",\"oracle\":\"{}\",",
            "\"source_count\":\"{}\",\"certified_count\":\"{}\",",
            "\"order\":{:?},\"elapsed_ns\":{},",
            "\"same_case_sparse_elapsed_ns\":{},",
            "\"same_case_uncached_unit_elapsed_ns\":{},",
            "\"same_case_sparse_mult\":{},",
            "\"same_case_uncached_unit_mult\":{},",
            "\"exact_mult\":{},\"exact_bit_work_proxy\":{},",
            "\"queries\":{},\"clause_visits\":{},\"literal_reads\":{},",
            "\"copied_literal_instances\":{},",
            "\"source_provenance_checks\":{},",
            "\"source_provenance_literal_reads\":{},",
            "\"unit_refutations\":{},\"removed_entries\":{},",
            "\"cache_hits\":{},\"cache_inserts\":{},",
            "\"cache_full_refusals\":{},\"lookup_attempts\":{},",
            "\"lookup_literal_reads\":{},",
            "\"minimized_attempts\":{},",
            "\"minimized_removed_assumptions\":{},",
            "\"minimization_budget_refusals\":{},",
            "\"independent_proof_checks\":{},",
            "\"proof_replay_literal_reads\":{},",
            "\"peak_cache_entries\":{},\"peak_cached_assumptions\":{},",
            "\"peak_cached_proof_steps\":{},",
            "\"peak_cache_payload_bytes_lower_bound\":{},",
            "\"budget_skips\":{},\"compatible_pairs\":{},",
            "\"source_leaf_assignments\":{},",
            "\"shared_process_peak_rss_kib\":{}}}"
        ),
            case.label(), case.kind.name(), cohort,
            case.declared_variables(), case.clauses, case.seed,
            r.mode.name(), r.oracle, r.expected_count, r.final_count,
            r.order, r.elapsed_ns,
            r.same_case_sparse_elapsed_ns,
            r.same_case_uncached_unit_elapsed_ns,
            r.same_case_sparse_exact_mult,
            r.same_case_uncached_exact_mult,
            a.multiplications, a.bit_work_proxy,
            b.queries, b.clause_visits, b.literal_reads,
            b.copied_literal_instances,
            m.source_provenance_checks, m.source_provenance_literal_reads,
            b.unit_refutations, b.removed_entries,
            m.cache_hits, m.cache_inserts, m.cache_full_refusals,
            m.lookup_attempts, m.lookup_literal_reads,
            m.minimized_attempts, m.minimized_removed_assumptions,
            m.minimization_budget_refusals, m.independent_proof_checks,
            m.proof_replay_literal_reads,
            m.peak_cache_entries, m.peak_cached_assumptions,
            m.peak_cached_proof_steps, m.peak_cache_payload_bytes_lower_bound,
            b.budget_skips, a.compatible_pair_visits,
            a.source_leaf_assignments, rss,
        );
    }
    Ok(())
}

fn run() -> Result<(), String> {
    let args = std::env::args().collect::<Vec<_>>();
    if args.len() == 6 && args[1] == "--single" {
        return single(Case {
            kind: kind(&args[2])?,
            variables: args[3].parse().map_err(|_| "invalid n")?,
            clauses: args[4].parse().map_err(|_| "invalid m")?,
            seed: args[5].parse().map_err(|_| "invalid seed")?,
        });
    }
    if args.len() != 1 {
        return Err("usage: nogood-reuse-study [--single kind n m seed]".into());
    }
    let executable = std::env::current_exe()
        .map_err(|e| format!("current executable unavailable: {e}"))?;
    let prepared = cases();
    if prepared.len() != 56 ||
        prepared.iter().filter(|x| FRESH_SEEDS.contains(&x.seed)).count() != 16
    {
        return Err("cohort preparation violates fixed validation split".into());
    }
    for case in prepared {
        let output = Command::new(&executable).args([
            "--single", case.kind.name(), &case.variables.to_string(),
            &case.clauses.to_string(), &case.seed.to_string(),
        ]).output().map_err(|e| format!("spawn failed: {e}"))?;
        if !output.status.success() {
            return Err(format!("case {} failed: {}",
                case.label(), String::from_utf8_lossy(&output.stderr)));
        }
        let lines = String::from_utf8(output.stdout)
            .map_err(|_| "invalid UTF8 receipts")?;
        if lines.lines().count() != 2 ||
            lines.lines().any(|line| !line.contains("\"oracle\":\"checked\""))
        {
            return Err(format!("missing or bad receipt for {}", case.label()));
        }
        print!("{lines}");
    }
    Ok(())
}

fn main() {
    if let Err(error) = run() {
        eprintln!("{error}");
        std::process::exit(1);
    }
}
