//! Physical node-cursor trace corresponding to
//! `reference/lean_native_nodes_trace.lean` on the original Lean source.

#[path = "trace/format.rs"]
mod trace_format;

use std::collections::VecDeque;

use lean_eth_reference::bit_program::{Config, RunLimits};
use lean_eth_reference::native_nodes::{begin_node_program, nodes_entry_command};
use lean_eth_reference::native_tuple::encode_words;

use trace_format::{bit_char, stack_bits};

fn cases() -> Vec<(&'static str, Vec<Vec<bool>>)> {
    vec![
        ("empty", vec![]),
        ("zero", vec![vec![]]),
        ("one", vec![vec![true]]),
        ("two", vec![vec![false, true], vec![true]]),
        ("third", vec![vec![true, false, true], vec![false], vec![]]),
        (
            "mixed",
            vec![
                vec![false],
                vec![true, false],
                vec![false, true, true],
                vec![true],
            ],
        ),
    ]
}
fn snapshot(name: &str, entry: u64, read: u64, d: &Config<40, 896>) {
    println!(
        "nodes|{name}|{entry}|{read}|{}|{}|{}|{}|{}|{}|{}|{}|{}|{}|{}|{}|{}|{}",
        stack_bits(d, 300),
        stack_bits(d, 301),
        stack_bits(d, 302),
        stack_bits(d, 305),
        stack_bits(d, 307),
        stack_bits(d, 78),
        stack_bits(d, 850),
        stack_bits(d, 851),
        stack_bits(d, 863),
        stack_bits(d, 799),
        bit_char(d.regs[21]),
        bit_char(d.regs[37]),
        bit_char(d.regs[38]),
        bit_char(d.regs[39]),
    );
}
fn main() -> Result<(), Box<dyn std::error::Error>> {
    let entry = nodes_entry_command()?.compiled(300, 863)?;
    let read = begin_node_program()?;
    for (name, nodes) in cases() {
        let mut d = entry.initial(Vec::new());
        d.stacks[300] = VecDeque::from(encode_words(&nodes)?);
        for (port, content) in [
            (301, vec![true, false, true]),
            (302, vec![false, true]),
            (305, vec![true]),
            (307, vec![true, false]),
            (78, vec![false]),
            (850, vec![true, false]),
            (851, vec![false, true]),
            (863, vec![true]),
            (799, vec![true]),
        ] {
            d.stacks[port] = VecDeque::from(content);
        }
        d.regs[21] = true;
        d.regs[39] = true;
        let entry_stats = entry.run(&mut d, RunLimits::default())?;
        let mut read_steps = 0;
        if !nodes.is_empty() {
            d.pc = Some(read.entry());
            read_steps = read.run(&mut d, RunLimits::default())?.instructions;
        }
        snapshot(name, entry_stats.instructions, read_steps, &d);
    }
    Ok(())
}
