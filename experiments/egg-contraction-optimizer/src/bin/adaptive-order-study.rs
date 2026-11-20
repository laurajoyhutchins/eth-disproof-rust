//! One process per held-out case/policy, so Linux VmHWM is attributable to
//! that case rather than the high-water mark of a previous comparison.
//! The CLI never treats RSS as a proof of asymptotic memory complexity.

use egg_contraction_experiment::representation_study::adaptive::{
    evaluate, held_out_cases, Case, CaseKind, Policy,
};
use std::process::Command;

fn kind_name(s: &str) -> Result<CaseKind, String> {
    match s {
        "random-3cnf" => Ok(CaseKind::Random3Cnf),
        "planted-3cnf" => Ok(CaseKind::Planted3Cnf),
        "frustrated-xor3-cnf" => Ok(CaseKind::FrustratedXor3Cnf),
        _ => Err(format!("unknown case kind: {s}")),
    }
}

fn policy_name(s: &str) -> Result<Policy, String> {
    match s {
        "sequential" => Ok(Policy::Sequential),
        "min-fill-admission" => Ok(Policy::MinFillAdmission),
        "tropical-zero-support" => Ok(Policy::TropicalZeroSupport),
        "exact-preview" => Ok(Policy::ExactPreview),
        _ => Err(format!("unknown planner policy: {s}")),
    }
}

/// The host reports maximum resident set size in KiB for this process.
/// It includes Rust runtime, source oracle, and all checked representations,
/// not just the exact table. Use per-case subprocess isolation.
fn linux_peak_rss_kib() -> Option<usize> {
    let status = std::fs::read_to_string("/proc/self/status").ok()?;
    let field = status.lines().find(|l| l.starts_with("VmHWM:"))?;
    field.split_whitespace().nth(1)?.parse().ok()
}

fn report(case: Case, policy: Policy) -> Result<(), String> {
    let result = evaluate(case, policy)?;
    let exact = &result.exact;
    let total_exact_and_preview_bit_proxy =
        exact.exact_work.bit_work_proxy + result.planning_work.bit_work_proxy;
    let rss = linux_peak_rss_kib()
        .map(|v| v.to_string()).unwrap_or("null".into());
    println!(
        concat!(
            "{{\"case\":\"{}\",\"kind\":\"{}\",\"variables\":{},\"clauses\":{},",
            "\"seed\":{},\"policy\":\"{}\",\"oracle\":\"checked\",",
            "\"order\":{:?},\"minimum_energy\":{},\"optimal_count\":\"{}\",",
            "\"satisfying_count\":\"{}\",",
            "\"planning_candidates\":{},\"planning_elapsed_ns\":{},",
            "\"planning_additions\":{},\"planning_multiplications\":{},",
            "\"planning_bit_work_proxy\":{},",
            "\"planning_peak_coefficient_payload_bytes\":{},",
            "\"exact_elapsed_ns\":{},\"exact_additions\":{},",
            "\"exact_multiplications\":{},\"exact_bit_work_proxy\":{},",
            "\"total_exact_plus_preview_bit_work_proxy\":{},",
            "\"exact_max_coefficient_bits\":{},\"peak_boundary_ports\":{},",
            "\"peak_table_cells\":{},\"peak_exact_coefficient_slots\":{},",
            "\"peak_live_encoded_bytes_proxy\":{},",
            "\"peak_process_rss_kib\":{}}}"
        ),
        case.label(), case.kind.name(), case.variables, case.clauses,
        case.seed, policy.name(),
        result.order, exact.minimum_energy, exact.minimum_count,
        exact.satisfying_count, result.candidates_examined,
        result.planning_elapsed_ns, result.planning_work.additions,
        result.planning_work.multiplications, result.planning_work.bit_work_proxy,
        result.peak_preview_coefficient_payload_bytes,
        result.exact_elapsed_ns, exact.exact_work.additions,
        exact.exact_work.multiplications, exact.exact_work.bit_work_proxy,
        total_exact_and_preview_bit_proxy, exact.exact_work.max_coefficient_bits,
        exact.peak_boundary_ports, exact.peak_table_cells,
        exact.peak_exact_coefficient_slots, exact.peak_live_encoded_bytes, rss,
    );
    Ok(())
}

fn run() -> Result<(), String> {
    let args = std::env::args().collect::<Vec<_>>();
    if args.len() == 7 && args[1] == "--single" {
        let case = Case {
            kind: kind_name(&args[2])?,
            variables: args[3].parse().map_err(|_| "invalid variable count")?,
            clauses: args[4].parse().map_err(|_| "invalid clause count")?,
            seed: args[5].parse().map_err(|_| "invalid seed")?,
        };
        return report(case, policy_name(&args[6])?);
    }
    if args.len() != 1 {
        return Err("usage: adaptive-order-study [--single kind n m seed policy]".into());
    }
    let executable = std::env::current_exe()
        .map_err(|e| format!("cannot find benchmark executable: {e}"))?;
    for case in held_out_cases() {
        for policy in Policy::ALL {
            let output = Command::new(&executable)
                .args([
                    "--single", case.kind.name(),
                    &case.variables.to_string(), &case.clauses.to_string(),
                    &case.seed.to_string(), policy.name(),
                ]).output().map_err(|e| format!("cannot invoke case: {e}"))?;
            if !output.status.success() {
                return Err(format!(
                    "case {} policy {} refused: {}",
                    case.label(), policy.name(),
                    String::from_utf8_lossy(&output.stderr),
                ));
            }
            let line = String::from_utf8(output.stdout)
                .map_err(|_| "case receipt not UTF-8")?;
            if line.lines().count() != 1 || !line.contains("\"oracle\":\"checked\"") {
                return Err(format!("invalid receipt for {}", case.label()));
            }
            print!("{line}");
        }
    }
    Ok(())
}

fn main() {
    if let Err(error) = run() {
        eprintln!("{error}");
        std::process::exit(1);
    }
}
