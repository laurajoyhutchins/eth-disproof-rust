//! Run exactly the source-defined Native.frontendProgram, not a SAT oracle.
//! Input is DIMACS CNF on stdin, encoded using the crate's canonical Lean
//! Encoding.encodeCNF implementation. Output is the actual final bit stacks.
use lean_eth_reference::bit_program::RunLimits;
use lean_eth_reference::{native_frontend, parse_dimacs};
use std::io::{self, Read};

fn parse_limits() -> Result<Option<RunLimits>, String> {
    let mut limits = RunLimits::default();
    let mut args = std::env::args().skip(1);
    while let Some(flag) = args.next() {
        if flag == "--help" || flag == "-h" {
            println!("Usage: eth-frontend [--max-steps N] [--max-stack-bits N] < input.cnf");
            println!("Runs Lean Native.frontendProgram's physical Rust BitProgram port.");
            println!("Reports the preserved Lean encoding and normalized-body bit word.");
            println!("Does not compute #SAT or prove TM2 resource bounds.");
            return Ok(None);
        }
        let value = args
            .next()
            .ok_or_else(|| format!("missing value for {flag}"))?;
        match flag.as_str() {
            "--max-steps" => limits.max_steps = value.parse().map_err(|_| "invalid step cap")?,
            "--max-stack-bits" => {
                limits.max_stack_bits = value.parse().map_err(|_| "invalid stack-bit cap")?
            }
            _ => return Err(format!("unrecognized option: {flag}")),
        }
    }
    Ok(Some(limits))
}

fn bit_string(word: impl IntoIterator<Item = bool>) -> String {
    word.into_iter()
        .map(|b| if b { '1' } else { '0' })
        .collect()
}

fn run() -> Result<(), String> {
    let Some(limits) = parse_limits()? else {
        return Ok(());
    };
    let mut text = String::new();
    io::stdin()
        .read_to_string(&mut text)
        .map_err(|e| e.to_string())?;
    let formula = parse_dimacs(&text).map_err(|e| e.to_string())?;
    let original = formula.encode_lean();
    let p = native_frontend::program().map_err(|e| e.to_string())?;
    let mut c = p.initial(original.bytes().map(|b| b == b'1'));
    let stats = p.run(&mut c, limits).map_err(|e| e.to_string())?;
    if c.pc.is_some() {
        return Err("front-end did not reach its halt instruction".into());
    }
    let output = |port: usize| bit_string(c.stacks[port].iter().copied());
    // Do not report success unless these source ABI postconditions hold.
    if output(256) != original || !c.stacks[263].is_empty() {
        return Err("source ABI postcondition failed".into());
    }
    for i in 0..1220 {
        if ![256, 258, 265, 267].contains(&i) && !c.stacks[i].is_empty() {
            return Err(format!("source scratch stack {i} was not cleaned"));
        }
    }
    println!("status=frontend-completed");
    println!("instructions={}", stats.instructions);
    println!("peak_stack_bits={}", stats.peak_stack_bits);
    println!("original_encoding={}", output(256));
    println!("ambient_unary={}", output(258));
    println!("variables_binary_lsb={}", output(267));
    println!("normalized_body={}", output(265));
    Ok(())
}

fn main() {
    if let Err(error) = run() {
        eprintln!("eth-frontend: {error}");
        std::process::exit(2);
    }
}
