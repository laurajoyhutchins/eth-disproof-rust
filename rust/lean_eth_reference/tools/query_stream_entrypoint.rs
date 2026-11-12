// Runtime entrypoint for the Lean-derived QueryStreamProgram machine.
// The generated preamble defines query() from the exact pinned source graph.
// Only a successfully compiled source graph may supply that preamble.
//
// This is the actual BitProgram, not a host-side #SAT oracle. The "run-bits"
// interface initializes only the source input stack. It does not establish
// the prepared-state hypotheses of the original count reconstruction theorem.
fn main() -> Result<(), Box<dyn std::error::Error>> {
    let program = query()?;
    let args: Vec<String> = std::env::args().skip(1).collect();
    match args.as_slice() {
        [command] if command == "abi" => {
            println!(
                "registers=40 stacks=896 labels={} entry={} input={} output={}",
                program.labels(),
                program.entry(),
                program.input_stack(),
                program.output_stack()
            );
        }
        [command, pc] if command == "instruction" => {
            let pc: usize = pc.parse()?;
            println!("{:?}", program.instruction_at(pc)?);
        }
        [command, bits, max_steps, max_stack_bits] if command == "run-bits" => {
            if bits.len() > 1_000_000 || !bits.bytes().all(|bit| bit == b'0' || bit == b'1') {
                return Err("input must be a bounded ASCII binary word".into());
            }
            let limits = RunLimits {
                max_steps: max_steps.parse()?,
                max_stack_bits: max_stack_bits.parse()?,
            };
            let mut config = program.initial(bits.bytes().map(|bit| bit == b'1'));
            let stats = program.run(&mut config, limits)?;
            let output: String = config.stacks[program.output_stack()]
                .iter()
                .map(|bit| if *bit { '1' } else { '0' })
                .collect();
            println!("HALT steps={} output_bits={}", stats.instructions, output);
        }
        _ => {
            return Err(
                "usage: query-stream abi | instruction <pc> | run-bits <bits> <max-steps> <max-stack-bits>"
                    .into(),
            );
        }
    }
    Ok(())
}
