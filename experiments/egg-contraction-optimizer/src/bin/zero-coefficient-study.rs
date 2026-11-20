//! Per-instance isolated exact #SAT comparison, with source-oracle receipts.
//! RSS includes verification and Rust allocation, never interpreted as a
//! representation-independent peak-space bound.

use egg_contraction_experiment::representation_study::adaptive::{
    held_out_cases, Case, CaseKind,
};
use egg_contraction_experiment::representation_study::zero_coefficient::run_case;
use std::process::Command;

fn kind(s: &str) -> Result<CaseKind, String> {
    match s {
        "random-3cnf" => Ok(CaseKind::Random3Cnf),
        "planted-3cnf" => Ok(CaseKind::Planted3Cnf),
        "frustrated-xor3-cnf" => Ok(CaseKind::FrustratedXor3Cnf),
        _ => Err(format!("unknown case kind: {s}")),
    }
}

fn vm_hwm() -> Option<u64> {
    std::fs::read_to_string("/proc/self/status").ok()?
        .lines().find(|s| s.starts_with("VmHWM:"))?
        .split_whitespace().nth(1)?.parse().ok()
}

fn single(case: Case) -> Result<(), String> {
    let result = run_case(case)?;
    let process_rss = vm_hwm().map_or("null".into(), |n| n.to_string());
    for variant in result.variants {
        let w = variant.work;
        println!(
            concat!(
                "{{\"case\":\"{}\",\"kind\":\"{}\",\"variables\":{},",
                "\"clauses\":{},\"seed\":{},\"strategy\":\"{}\",",
                "\"minfill_order\":{:?},\"oracle\":\"{}\",",
                "\"count\":\"{}\",\"full_poly_multiplications\":{},",
                "\"full_poly_bit_work_proxy\":{},",
                "\"full_poly_peak_encoded_bytes\":{},",
                "\"elapsed_ns\":{},\"additions\":{},\"multiplications\":{},",
                "\"bit_work_proxy\":{},\"mask_visits\":{},",
                "\"certified_zero_skips\":{},\"source_leaf_assignments\":{},",
                "\"source_leaf_rejections\":{},\"support_index_insertions\":{},",
                "\"support_group_lookups\":{},\"compatible_pair_visits\":{},",
                "\"left_entry_scans\":{},\"peak_nonzero_entries\":{},",
                "\"peak_stored_slots\":{},\"peak_encoded_bytes_lower_bound\":{},",
                "\"max_coefficient_bits\":{},\"peak_process_rss_kib\":{}}}"
            ),
            case.label(), case.kind.name(), case.declared_variables(),
            case.clauses, case.seed, variant.strategy.name(),
            result.order, result.independent_oracle, variant.satisfying_count,
            result.full_polynomial_multiplications,
            result.full_polynomial_bit_work_proxy,
            result.full_polynomial_peak_encoded_bytes,
            variant.elapsed_ns, w.additions, w.multiplications,
            w.bit_work_proxy, w.full_union_mask_visits,
            w.certified_zero_skips, w.source_leaf_assignments,
            w.source_leaf_rejections, w.support_index_insertions,
            w.support_group_lookups, w.compatible_pair_visits,
            w.left_entry_scans, w.peak_nonzero_boundary_entries,
            w.peak_stored_boundary_slots,
            w.peak_encoded_boundary_bytes, w.max_coefficient_bits,
            process_rss,
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
        return Err("usage: zero-coefficient-study [--single kind n m seed]".into());
    }
    let exe = std::env::current_exe().map_err(|e| format!("current exe: {e}"))?;
    for case in held_out_cases() {
        let result = Command::new(&exe)
            .args([
                "--single", case.kind.name(), &case.variables.to_string(),
                &case.clauses.to_string(), &case.seed.to_string(),
            ]).output().map_err(|e| format!("run child: {e}"))?;
        if !result.status.success() {
            return Err(format!(
                "{}: source/differential check failed: {}",
                case.label(), String::from_utf8_lossy(&result.stderr),
            ));
        }
        let lines = String::from_utf8(result.stdout)
            .map_err(|_| "non-UTF8 receipt")?;
        if lines.lines().count() != 3 ||
            lines.lines().any(|line| !line.contains("\"oracle\":\"checked\""))
        {
            return Err(format!("malformed receipt for {}", case.label()));
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
