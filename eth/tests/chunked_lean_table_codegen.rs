//! Generated execution across compiler chunk boundaries, not table interpretation.
use lean_eth_reference::bit_program::{Instr, Program, RunLimits};

mod chunked {
    include!(concat!(env!("OUT_DIR"), "/chunked_fixture.rs"));
}

fn reference() -> Program<4, 3> {
    use Instr::*;
    let mut code = Vec::with_capacity(640);
    for pc in 0..640 {
        code.push(match pc {
            0 => Set {
                dst: 0,
                value: true,
                next: 1,
            },
            1 => Push {
                stack: 0,
                src: 0,
                next: 2,
            },
            2 => Peek {
                stack: 0,
                value: 1,
                present: 2,
                next: 3,
            },
            3 => Pop {
                stack: 0,
                value: 1,
                present: 2,
                next: 4,
            },
            4 => Branch {
                test: 2,
                yes: 5,
                no: 638,
            },
            638 => Pop {
                stack: 1,
                value: 0,
                present: 2,
                next: 639,
            },
            639 => Halt,
            _ => Goto { next: pc + 1 },
        });
    }
    Program::new(0, 2, 0, code).unwrap()
}

#[test]
fn generated_large_program_matches_reference_at_chunk_boundaries() {
    let reference = reference();
    assert_eq!(chunked::LABELS, reference.code().len());
    assert_eq!(chunked::ENTRY, reference.entry());
    assert_eq!(chunked::INPUT_STACK, reference.input_stack());
    assert_eq!(chunked::OUTPUT_STACK, reference.output_stack());
    for entry in [
        0usize, 1, 2, 3, 4, 5, 254, 255, 256, 257, 511, 512, 638, 639, 640,
    ] {
        for input in [false, true] {
            for bits in [0usize, 1, 2, 3] {
                for max_steps in [0, 1, 2, 4, 10, 128, 512] {
                    for max_stack_bits in [0, 1, 3] {
                        let mut a = reference.initial([]);
                        a.pc = Some(entry);
                        a.regs[0] = input;
                        a.stacks[1].extend(std::iter::repeat_n(true, bits));
                        let mut b = a.clone();
                        let limits = RunLimits {
                            max_steps,
                            max_stack_bits,
                        };
                        let ra = reference.run(&mut a, limits);
                        let rb = chunked::run(&mut b, limits);
                        assert_eq!(ra, rb, "result at {entry}, {input}, {bits}, {limits:?}");
                        assert_eq!(a, b, "state at {entry}, {input}, {bits}, {limits:?}");
                    }
                }
            }
        }
    }
}
