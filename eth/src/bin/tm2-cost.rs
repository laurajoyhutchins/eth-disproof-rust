//! Bounded primitive transition receipt for a real source-defined Rust stage.
//! This is finite-machine evidence, not an asymptotic complexity certificate.
use lean_eth_reference::native_high::branch_program;
use lean_eth_reference::tm2_resources::{PrimitiveLimits, run_primitive};

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let word = std::env::args().nth(1).unwrap_or_else(|| "1010".to_owned());
    if word.len() > 64 || !word.bytes().all(|b| b == b'0' || b == b'1') {
        return Err("expected at most 64 Boolean input bits (0/1)".into());
    }
    let input = word.bytes().map(|bit| bit == b'1');
    let program = branch_program()?;
    let mut machine = program.initial(input);
    let stats = run_primitive(&program, &mut machine, PrimitiveLimits::default())?;
    println!("source=openai/math@4eaee87548250b2682affda7d05d947c05554bae");
    println!("definition=HighIncidenceProgram.Branches.program");
    println!("source_steps={}", stats.source_steps);
    println!("tm2_microsteps={}", stats.tm2_microsteps);
    println!("primitive_steps={}", stats.primitive_steps);
    println!("head_moves={}", stats.head_moves);
    println!("writes={}", stats.writes);
    println!("visited_cells={}", stats.visited_cells);
    println!("peak_live_stack_bits={}", stats.peak_live_stack_bits);
    println!("peak_encoded_bits={}", stats.peak_encoded_bits);
    println!(
        "source_step_overhead_bound={}",
        stats.source_step_overhead_bound
    );
    println!("halted={}", machine.pc.is_none());
    println!("claim=finite_primitive_simulator_only");
    Ok(())
}
