//! Machine-readable traces from the Rust port. Compare with unchanged Lean
//! source imports using `compare-traces --suite high`.

#[path = "trace/format.rs"]
mod trace_format;

use lean_eth_reference::bit_program::{Config, RunLimits};
use lean_eth_reference::native_high::{branch_program, initialize_program};

use trace_format::{bit_char, stack_bits};

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let branch = branch_program()?;
    let init = initialize_program()?;
    let cases: [(&str, &[bool]); 6] = [
        ("empty", &[]),
        ("zero", &[false]),
        ("one", &[true]),
        ("mixed", &[true, false, true]),
        ("alternate", &[false, true, false, true]),
        ("all", &[true, true, true, true]),
    ];
    for (name, mask) in cases {
        let mut b = branch.initial(mask.iter().copied());
        let bsteps = branch.run(&mut b, RunLimits::default())?;
        println!(
            "branch|{name}|{}|{}|{}|{}|{}",
            bsteps.instructions,
            stack_bits(&b, 0),
            stack_bits(&b, 1),
            bit_char(b.regs[0]),
            bit_char(b.regs[1]),
        );
        let mut s = init.initial(mask.iter().copied());
        let ssteps = init.run(&mut s, RunLimits::default())?;
        println!(
            "initialize|{name}|{}|{}|{}|{}|{}",
            ssteps.instructions,
            stack_bits(&s, 338),
            stack_bits(&s, 330),
            stack_bits(&s, 789),
            bit_char(s.regs[21]),
        );
    }
    Ok(())
}
