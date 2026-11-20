//! Physical query-prefix traces for differential comparison against the
//! ORIGINAL pinned Lean `HighQueryAdapter.prepareHighProgram` module.

#[path = "trace/format.rs"]
mod trace_format;

use std::collections::VecDeque;

use lean_eth_reference::bit_program::RunLimits;
use lean_eth_reference::native_query_prefix::prepare_high_program;
use lean_eth_reference::native_tuple::encode_words;

use trace_format::{bit_char, stack_bits};


fn cases() -> Vec<(&'static str, Vec<bool>, Vec<bool>)> {
    vec![
        ("empty", vec![], vec![]),
        ("none", vec![false, false], vec![]),
        ("first", vec![true, false, false], vec![true]),
        ("middle", vec![false, true, false], vec![true]),
        (
            "separated",
            vec![true, false, true, false],
            vec![true, false],
        ),
        ("all", vec![true, true, true], vec![false, true, false]),
    ]
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let program = prepare_high_program()?;
    for (name, mask, high) in cases() {
        let records: Vec<Vec<bool>> = high.iter().map(|&b| vec![b]).collect();
        let encoded = encode_words(&records)?;
        let mut cfg = program.initial(encoded);
        cfg.regs[21] = true;
        cfg.stacks[338] = VecDeque::from(mask);
        cfg.stacks[799] = VecDeque::from(vec![true]);
        for port in [702, 703, 680, 681, 682, 683, 684, 685] {
            cfg.stacks[port] = VecDeque::from(vec![false, true, false]);
        }
        let stats = program.run(
            &mut cfg,
            RunLimits {
                max_steps: 20_000,
                ..RunLimits::default()
            },
        )?;
        println!(
            "prepare|{name}|{}|{}|{}|{}|{}|{}|{}|{}|{}|{}|{}|{}|{}",
            stats.instructions,
            stack_bits(&cfg, 330),
            stack_bits(&cfg, 338),
            stack_bits(&cfg, 702),
            stack_bits(&cfg, 703),
            stack_bits(&cfg, 680),
            stack_bits(&cfg, 681),
            stack_bits(&cfg, 682),
            stack_bits(&cfg, 683),
            stack_bits(&cfg, 684),
            stack_bits(&cfg, 685),
            stack_bits(&cfg, 799),
            bit_char(cfg.regs[21])
        );
    }
    Ok(())
}
