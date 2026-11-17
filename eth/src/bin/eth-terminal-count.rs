//! Exact source-native *terminal-family* counter, not a general #SAT solver.
use lean_eth_reference::bit_program::RunLimits;
use lean_eth_reference::native_terminal_count::{
    SOURCE_STAGES, count_terminal, count_word_decimal,
};
use lean_eth_reference::parse_dimacs;
use std::io::{self, Read};

fn run() -> Result<(), String> {
    let mut limits = RunLimits {
        max_steps: 20_000_000,
        max_stack_bits: 300_000,
    };
    let mut args = std::env::args().skip(1);
    while let Some(flag) = args.next() {
        if flag == "--help" || flag == "-h" {
            println!("Usage: eth-terminal-count [--max-steps N] [--max-stack-bits N] < input.cnf");
            println!("Runs physical Lean-source frontend, terminal counter and answer.");
            println!("Nonterminal formulas fail closed: the original leaf is not yet ported.");
            println!("Metrics are BitProgram instructions/live stack bits, NOT TM2 bounds.");
            return Ok(());
        }
        let value = args
            .next()
            .ok_or_else(|| format!("missing value for {flag}"))?;
        match flag.as_str() {
            "--max-steps" => limits.max_steps = value.parse().map_err(|_| "invalid step budget")?,
            "--max-stack-bits" => {
                limits.max_stack_bits = value.parse().map_err(|_| "invalid stack budget")?
            }
            _ => return Err(format!("unknown option {flag}")),
        }
    }
    let mut input = String::new();
    io::stdin()
        .read_to_string(&mut input)
        .map_err(|e| e.to_string())?;
    let cnf = parse_dimacs(&input).map_err(|e| e.to_string())?;
    let result = count_terminal(&cnf, limits).map_err(|e| e.to_string())?;
    let bits: String = result
        .count_lsb
        .iter()
        .map(|b| if *b { '1' } else { '0' })
        .collect();
    println!("status=terminal-count-complete");
    println!("count={}", count_word_decimal(&result.count_lsb));
    println!("count_bits_lsb={bits}");
    println!("answer={}", if result.positive { 1 } else { 0 });
    for (name, stats) in SOURCE_STAGES.iter().zip(result.stages.iter()) {
        println!(
            "stage={name} instructions={} peak_stack_bits={}",
            stats.instructions, stats.peak_stack_bits
        );
    }
    println!("source_instructions={}", result.total_instructions);
    println!("peak_live_stack_bits={}", result.peak_stack_bits);
    println!("resource_basis=BitProgram_source_instructions_not_TM2_microsteps");
    Ok(())
}
fn main() {
    if let Err(error) = run() {
        eprintln!("eth-terminal-count: {error}");
        std::process::exit(2);
    }
}
