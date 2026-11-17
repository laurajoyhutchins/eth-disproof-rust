//! Machine-readable traces from the Rust port. Compare with unchanged Lean
//! source imports using `compare-traces --suite high`.
use lean_eth_reference::bit_program::{Config, RunLimits};
use lean_eth_reference::native_high::{branch_program, initialize_program};

fn word<const R: usize, const S: usize>(cfg: &Config<R, S>, port: usize) -> String {
    cfg.stacks[port]
        .iter()
        .map(|&b| if b { '1' } else { '0' })
        .collect()
}
fn bit(b: bool) -> char {
    if b { '1' } else { '0' }
}
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
            word(&b, 0),
            word(&b, 1),
            bit(b.regs[0]),
            bit(b.regs[1]),
        );
        let mut s = init.initial(mask.iter().copied());
        let ssteps = init.run(&mut s, RunLimits::default())?;
        println!(
            "initialize|{name}|{}|{}|{}|{}|{}",
            ssteps.instructions,
            word(&s, 338),
            word(&s, 330),
            word(&s, 789),
            bit(s.regs[21]),
        );
    }
    Ok(())
}
