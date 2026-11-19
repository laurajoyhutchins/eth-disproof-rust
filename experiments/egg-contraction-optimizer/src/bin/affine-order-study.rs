//! Run exact GF(2) contraction-order experiments with per-stage JSONL receipts.
//! There is no arbitrary-CNF fallback or general complexity claim.

use egg_contraction_experiment::affine_orders::{
    fold, generate, oracle, Family, Limits, Schedule,
};
use egg_contraction_experiment::cnf_count::Refusal;
use std::collections::BTreeMap;
use std::time::Instant;

fn usage() -> &'static str {
    "usage: affine-order-study [--sizes 8,16,32] [--family chain|circulant|both] \
     [--max-merge-cells N] [--max-total-merge-cells N] [--summaries-only]\n\
     Prints JSON Lines, one record per stage and one summary per schedule. \
     For <=10 variables, the final count is independently checked by enumeration."
}

fn parse_sizes(s: &str) -> Result<Vec<usize>, String> {
    let numbers = s.split(',').map(|n| n.parse::<usize>()
        .map_err(|_| "invalid integer in --sizes".to_string())).collect::<Result<Vec<_>, _>>()?;
    if numbers.is_empty() || numbers.iter().any(|&n| !(3..=256).contains(&n)) {
        return Err("--sizes entries must be between 3 and 256".into());
    }
    Ok(numbers)
}

fn execute() -> Result<(), Refusal> {
    let mut args = std::env::args().skip(1);
    let mut sizes = vec![8, 16, 32];
    let mut families = vec![Family::Chain, Family::CirculantXor3];
    let mut limits = Limits::default();
    let mut summaries_only = false;
    while let Some(arg) = args.next() {
        if matches!(arg.as_str(), "--help" | "-h") {
            println!("{}", usage());
            return Ok(());
        }
        if arg == "--summaries-only" {
            summaries_only = true;
            continue;
        }
        let value = args.next().ok_or_else(|| Refusal::new(
            "input", "arguments", format!("missing value after {arg}"),
        ))?;
        match arg.as_str() {
            "--sizes" => sizes = parse_sizes(&value).map_err(|e| Refusal::new("input", "arguments", e))?,
            "--family" => families = match value.as_str() {
                "chain" => vec![Family::Chain],
                "circulant" => vec![Family::CirculantXor3],
                "both" => vec![Family::Chain, Family::CirculantXor3],
                _ => return Err(Refusal::new("input", "arguments", "unknown --family")),
            },
            "--max-merge-cells" => limits.max_merge_cells = value.parse()
                .map_err(|_| Refusal::new("input", "arguments", "invalid merge cell limit"))?,
            "--max-total-merge-cells" => limits.max_total_merge_cells = value.parse()
                .map_err(|_| Refusal::new("input", "arguments", "invalid total cell limit"))?,
            _ => return Err(Refusal::new("input", "arguments", format!("unknown flag {arg}"))),
        }
    }

    for family in families {
        for &n in &sizes {
            let factors = generate(family, n)
                .map_err(|e| Refusal::new("resource", "generate", e))?;
            let mut counts = Vec::new();
            for schedule in [Schedule::Sequential, Schedule::Reverse, Schedule::EvenFirst] {
                let start = Instant::now();
                let trace = fold(&factors, &schedule.indices(n), &[], &limits)
                    .map_err(|e| Refusal::new("resource", "contract", e))?;
                let count = trace.stage.count_at(&BTreeMap::new())
                    .map_err(|e| Refusal::new("verification", "reconstruct", e))?;
                let elapsed = start.elapsed().as_nanos();
                let oracle_status = if (family == Family::Chain && n <= 9)
                    || (family == Family::CirculantXor3 && n <= 10)
                {
                    let direct = oracle(&factors, &BTreeMap::new(), 12)
                        .map_err(|e| Refusal::new("resource", "oracle", e))?;
                    if count != direct {
                        return Err(Refusal::new(
                            "verification", "oracle", format!("count disagrees for {} n={n}", family.name()),
                        ));
                    }
                    "checked"
                } else {
                    "not-run"
                };
                counts.push(count.clone());
                if !summaries_only {
                    for step in &trace.steps {
                        println!(
                            concat!(
                                "{{\"kind\":\"stage\",\"family\":\"{}\",\"size\":{},\"order\":\"{}\",",
                                "\"step\":{},\"absorbed_factor\":{},\"d\":{},\"b_upper\":{},",
                                "\"ports\":{},\"residual_rows\":{},\"incidences\":{},",
                                "\"free_internal\":{},\"merge_matrix_cells\":{},",
                                "\"cumulative_merge_cells\":{},\"cumulative_xors\":{},",
                                "\"cumulative_replay_steps\":{}}}"
                            ),
                            family.name(), n, schedule.name(), step.index, step.absorbed_factor,
                            step.metrics.d, step.metrics.b, step.metrics.ports,
                            step.metrics.residual_rows, step.metrics.incidences,
                            step.metrics.free_internal, step.merge_matrix_cells,
                            step.cumulative_merge_cells, step.cumulative_xors,
                            step.cumulative_replay_steps,
                        );
                    }
                }
                println!(
                    concat!(
                        "{{\"kind\":\"summary\",\"family\":\"{}\",\"size\":{},\"order\":\"{}\",",
                        "\"count\":\"{}\",\"oracle\":\"{}\",\"peak_d\":{},\"peak_b_upper\":{},",
                        "\"sum_d\":{},\"sum_merge_matrix_cells\":{},\"sum_xors\":{},",
                        "\"sum_replay_steps\":{},\"elapsed_ns\":{}}}"
                    ),
                    family.name(), n, schedule.name(), count, oracle_status,
                    trace.peak_d, trace.peak_b, trace.sum_d,
                    trace.sum_merge_matrix_cells, trace.sum_xors,
                    trace.sum_replay_steps, elapsed,
                );
            }
            if counts.windows(2).any(|pair| pair[0] != pair[1]) {
                return Err(Refusal::new("verification", "compare",
                    format!("different contraction orders disagree for {} n={n}", family.name())));
            }
        }
    }
    Ok(())
}

fn main() {
    if let Err(e) = execute() {
        eprintln!("{}", e.to_json());
        std::process::exit(2);
    }
}
