//! Machine-readable trace from the source-pinned Rust odometer and enumerator.
//! Compare against the imported upstream Lean implementation, not a generated
//! or Python-translated substitute.
use lean_eth_reference::bit_program::{Atom, Cmd, Config};
use lean_eth_reference::native_tuple::{
    CounterPorts, encode_words, enumerate_command, odometer_program,
};

fn bits(xs: &[bool]) -> String {
    xs.iter().map(|&b| if b { '1' } else { '0' }).collect()
}
fn word<const R: usize, const S: usize>(cfg: &Config<R, S>, port: usize) -> String {
    cfg.stacks[port]
        .iter()
        .map(|&b| if b { '1' } else { '0' })
        .collect()
}
fn bit(b: bool) -> char {
    if b { '1' } else { '0' }
}
fn cases() -> Vec<(&'static str, Vec<Vec<bool>>)> {
    vec![
        ("empty", vec![]),
        ("width0", vec![vec![]]),
        ("one", vec![vec![false]]),
        ("two", vec![vec![false, false]]),
        ("split", vec![vec![false], vec![false]]),
        ("three", vec![vec![false, false], vec![false]]),
    ]
}
type TraceResult<const R: usize, const S: usize> = (usize, Config<R, S>, Vec<Vec<bool>>);

fn run<const R: usize, const S: usize>(
    program: &lean_eth_reference::bit_program::Program<R, S>,
    input: &[bool],
    observe_at: Option<usize>,
    observed_port: usize,
) -> Result<TraceResult<R, S>, Box<dyn std::error::Error>> {
    let mut cfg = program.initial(input.iter().copied());
    let mut trace = Vec::new();
    let mut count = 0;
    while cfg.pc.is_some() {
        if count >= 10_000 {
            return Err("source trace fuel exhausted".into());
        }
        if cfg.pc == observe_at && observe_at.is_some() {
            trace.push(cfg.stacks[observed_port].iter().copied().collect());
        }
        program.step(&mut cfg)?;
        count += 1;
    }
    Ok((count, cfg, trace))
}
fn main() -> Result<(), Box<dyn std::error::Error>> {
    let odo = odometer_program()?;
    let ports = CounterPorts {
        registers: [0, 1, 2],
        counter: 0,
        scratch: 1,
    };
    let callback = Cmd::seq(
        Cmd::Atom(Atom::Set {
            dst: 3,
            value: true,
        }),
        Cmd::Atom(Atom::Push { stack: 2, src: 3 }),
    );
    let enumeration = enumerate_command::<4, 3>(ports, callback)?.compiled(0, 0)?;
    let mut odo_cases = cases();
    odo_cases.extend([
        ("carry", vec![vec![true, true], vec![false]]),
        ("overflow", vec![vec![true], vec![true]]),
    ]);
    for (name, words) in odo_cases {
        let input = encode_words(&words)?;
        let (steps, cfg, _) = run(&odo, &input, None, 0)?;
        println!(
            "odometer|{name}|{steps}|{}|{}|{}|{}|{}",
            word(&cfg, 0),
            word(&cfg, 1),
            bit(cfg.regs[0]),
            bit(cfg.regs[1]),
            bit(cfg.regs[2])
        );
    }
    for (name, words) in cases() {
        let input = encode_words(&words)?;
        let (steps, cfg, visits) = run(&enumeration, &input, Some(2), 0)?;
        let visit_bits = encode_words(&visits)?;
        println!(
            "enumerate|{name}|{steps}|{}|{}|{}|{}|{}|{}",
            word(&cfg, 0),
            word(&cfg, 1),
            word(&cfg, 2),
            bit(cfg.regs[2]),
            bit(cfg.regs[3]),
            bits(&visit_bits)
        );
    }
    Ok(())
}
