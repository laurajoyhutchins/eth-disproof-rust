//! Physical trace paired with `reference/lean_native_layout_pair_trace.lean`.
//! This is only the Rust-side producer, not a Lean differential pass.

#[path = "trace/format.rs"]
mod trace_format;

use std::collections::VecDeque;

use lean_eth_reference::bit_program::{Config, RunLimits};
use lean_eth_reference::{native_layout, native_pair_setup};

use trace_format::{stack_bits};

fn flag(b: bool) -> &'static str {
    if b { "1" } else { "0" }
}
fn masters(d: &Config<40, 896>, start: usize) -> String {
    (start..start + 14)
        .map(|p| stack_bits(d, p))
        .collect::<Vec<_>>()
        .join(",")
}
fn put(d: &mut Config<40, 896>, port: usize, xs: &[bool]) {
    d.stacks[port] = VecDeque::from(xs.to_vec());
}
fn main() -> Result<(), Box<dyn std::error::Error>> {
    let layout = native_layout::program()?;
    let pair = native_pair_setup::setup_caller_program()?;
    for seed in 0..4 {
        let mut d = layout.initial(Vec::<bool>::new());
        for i in 730..744 {
            put(&mut d, i, &vec![(i + seed) % 2 == 0; (i - 730 + seed) % 4]);
        }
        for i in 128..142 {
            put(&mut d, i, &[true, false]);
        }
        put(&mut d, 684, &[true, false, true]);
        put(&mut d, 660, &[false, true]);
        put(&mut d, 665, &[true]);
        put(&mut d, 789, &[false, true]);
        for i in 0..40 {
            d.regs[i] = (i + seed) % 3 == 0;
        }
        let stats = layout.run(&mut d, RunLimits::default())?;
        println!(
            "layout|{seed}|{}|{}|{}|{}|{}|{}|{}|{}",
            stats.instructions,
            masters(&d, 128),
            masters(&d, 730),
            stack_bits(&d, 684),
            stack_bits(&d, 660),
            stack_bits(&d, 665),
            flag(d.regs[16]),
            flag(d.regs[39])
        );
        let mut d = pair.initial(Vec::<bool>::new());
        let m = (0..seed + 2)
            .map(|j| (j + seed) % 3 == 0)
            .collect::<Vec<_>>();
        put(&mut d, 338, &m);
        put(&mut d, 243, &[true, false, seed % 2 == 0]);
        for i in 325..330 {
            put(&mut d, i, &[true, false]);
        }
        put(&mut d, 832, &[false, true]);
        put(&mut d, 833, &[false]);
        put(&mut d, 834, &[true]);
        put(&mut d, 835, &[true, false]);
        put(&mut d, 789, &[true]);
        for i in 0..40 {
            d.regs[i] = (i + seed) % 3 == 0;
        }
        let stats = pair.run(&mut d, RunLimits::default())?;
        println!(
            "pair|{seed}|{}|{}|{}|{}|{}|{}|{}|{}|{}|{}",
            stats.instructions,
            stack_bits(&d, 338),
            stack_bits(&d, 243),
            stack_bits(&d, 832),
            stack_bits(&d, 833),
            (325..330)
                .map(|i| stack_bits(&d, i))
                .collect::<Vec<_>>()
                .join(","),
            stack_bits(&d, 834),
            stack_bits(&d, 835),
            flag(d.regs[9]),
            flag(d.regs[39])
        );
    }
    Ok(())
}
