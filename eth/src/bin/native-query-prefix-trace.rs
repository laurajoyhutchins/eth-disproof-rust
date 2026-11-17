//! Physical query-prefix traces for differential comparison against the
//! ORIGINAL pinned Lean `HighQueryAdapter.prepareHighProgram` module.
use lean_eth_reference::bit_program::RunLimits;
use lean_eth_reference::native_query_prefix::prepare_high_program;
use lean_eth_reference::native_tuple::encode_words;
use std::collections::VecDeque;

fn word(c: &lean_eth_reference::bit_program::Config<40, 896>, port: usize) -> String {
    c.stacks[port]
        .iter()
        .map(|b| if *b { '1' } else { '0' })
        .collect()
}
fn bit(value: bool) -> char {
    if value { '1' } else { '0' }
}

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
            word(&cfg, 330),
            word(&cfg, 338),
            word(&cfg, 702),
            word(&cfg, 703),
            word(&cfg, 680),
            word(&cfg, 681),
            word(&cfg, 682),
            word(&cfg, 683),
            word(&cfg, 684),
            word(&cfg, 685),
            word(&cfg, 799),
            bit(cfg.regs[21])
        );
    }
    Ok(())
}
