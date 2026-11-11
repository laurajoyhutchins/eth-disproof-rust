//! Full source-instruction trace paired with imported upstream Lean.
//! See reference/lean_full_machine_trace.lean; it calls the original BitProgram.step.
use lean_eth_reference::native_high::branch_program;

fn word(bits: &std::collections::VecDeque<bool>) -> String {
    bits.iter().map(|b| if *b { '1' } else { '0' }).collect()
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let program = branch_program()?;
    for size in 0..=4_usize {
        for code in 0..(1_usize << size) {
            for dirty in [false, true] {
                let name = format!("{size}_{code}_{}", if dirty { "dirty" } else { "clean" });
                let input = (0..size).map(|i| (code >> i) & 1 != 0);
                let mut cfg = program.initial(input);
                if dirty {
                    cfg.regs = [true, true];
                    cfg.stacks[1].extend([true, false]);
                }
                let mut halted = false;
                for step in 0..512_usize {
                    let pc = cfg.pc.map_or("H".to_string(), |n| n.to_string());
                    let regs: String = cfg
                        .regs
                        .iter()
                        .map(|b| if *b { '1' } else { '0' })
                        .collect();
                    println!(
                        "machine|{name}|{step}|{pc}|{regs}|{}|{}",
                        word(&cfg.stacks[0]),
                        word(&cfg.stacks[1])
                    );
                    if cfg.pc.is_none() {
                        halted = true;
                        break;
                    }
                    program.step(&mut cfg)?;
                }
                if !halted {
                    return Err(format!("Rust fuel exhausted on {name}").into());
                }
            }
        }
    }
    Ok(())
}
