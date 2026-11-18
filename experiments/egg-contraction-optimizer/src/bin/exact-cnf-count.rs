//! Exact #SAT for a narrowly recognized affine DIMACS fragment.
//! Usage: cargo run --bin exact-cnf-count -- [FILE|-] [--max-variables N] ...
use egg_contraction_experiment::cnf_count::{count_dimacs, Limits, Refusal};
use std::io::Read;

fn usage() -> &'static str {
    "usage: exact-cnf-count [FILE|-] [--max-input-bytes N] [--max-variables N] [--max-clauses N] [--max-literals N]\n\
     DIMACS from FILE or stdin. Accepts strict unit, empty, XOR2 and XOR3 parity clause blocks.\n\
     Outputs an exact-count JSON receipt or a refused JSON error on stderr (exit status 2)."
}

fn run() -> Result<(), Refusal> {
    let mut args = std::env::args().skip(1);
    let mut path: Option<String> = None;
    let mut limits = Limits::default();
    while let Some(arg) = args.next() {
        if arg == "--help" || arg == "-h" {
            println!("{}", usage());
            return Ok(());
        }
        let budget = match arg.as_str() {
            "--max-input-bytes" => Some(&mut limits.max_input_bytes),
            "--max-variables" => Some(&mut limits.max_variables),
            "--max-clauses" => Some(&mut limits.max_clauses),
            "--max-literals" => Some(&mut limits.max_literals),
            _ => None,
        };
        if let Some(slot) = budget {
            let next = args.next().ok_or_else(|| Refusal::new("input", "arguments",
                format!("missing value after {arg}")))?;
            *slot = next.parse::<usize>().map_err(|_| Refusal::new("input", "arguments",
                format!("invalid nonnegative limit after {arg}")))?;
        } else if arg.starts_with('-') && arg != "-" {
            return Err(Refusal::new("input", "arguments", format!("unknown flag {arg}")));
        } else if path.replace(arg).is_some() {
            return Err(Refusal::new("input", "arguments", "multiple input paths"));
        }
    }

    // Read at most one byte beyond the configured budget. Never read a
    // file of unbounded size just to learn that it exceeds the limit.
    let cap = (limits.max_input_bytes as u64).saturating_add(1);
    let path = path.unwrap_or_else(|| "-".into());
    let mut source = String::new();
    if path == "-" {
        std::io::stdin().take(cap).read_to_string(&mut source)
            .map_err(|e| Refusal::new("input", "read", e.to_string()))?;
    } else {
        std::fs::File::open(&path)
            .map_err(|e| Refusal::new("input", "read", e.to_string()))?
            .take(cap).read_to_string(&mut source)
            .map_err(|e| Refusal::new("input", "read", e.to_string()))?;
    }
    let report = count_dimacs(&source, &limits)?;
    println!("{}", report.to_json());
    Ok(())
}

fn main() {
    if let Err(refusal) = run() {
        eprintln!("{}", refusal.to_json());
        std::process::exit(2);
    }
}
