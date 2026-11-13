//! Differential tests for every mechanically extracted fixed original Lean table.
//! These check source-instruction semantics, not original Mathlib import or ETH.
use lean_eth_reference::bit_program::{Instr, Program, RunLimits};

#[allow(dead_code)]
mod catalog {
    include!(concat!(env!("OUT_DIR"), "/original_catalog.rs"));
}

fn parse<const R: usize, const S: usize>(table: &str) -> Program<R, S> {
    let lines: Vec<_> = table.lines().collect();
    let header: Vec<_> = lines[1].split('|').collect();
    assert_eq!(header[0], "PROGRAM");
    assert_eq!(header[2].parse::<usize>().unwrap(), R);
    assert_eq!(header[3].parse::<usize>().unwrap(), S);
    let labels = header[4].parse::<usize>().unwrap();
    assert_eq!(lines.len(), labels + 3);
    let parse_num = |x: &str| x.parse::<usize>().unwrap();
    let code = lines[2..labels + 2]
        .iter()
        .enumerate()
        .map(|(index, row)| {
            let record: Vec<_> = row.split('|').collect();
            assert_eq!(record[0], "CODE");
            assert_eq!(record[2].parse::<usize>().unwrap(), index);
            let parts: Vec<_> = record[3].split(':').collect();
            let n: Vec<_> = parts[1..].iter().map(|word| parse_num(word)).collect();
            match (parts[0], n.as_slice()) {
                ("halt", []) => Instr::Halt,
                ("goto", [next]) => Instr::Goto { next: *next },
                ("set", [dst, bit, next]) => Instr::Set {
                    dst: *dst,
                    value: *bit == 1,
                    next: *next,
                },
                ("copy", [dst, src, next]) => Instr::Copy {
                    dst: *dst,
                    src: *src,
                    next: *next,
                },
                ("not", [dst, src, next]) => Instr::Not {
                    dst: *dst,
                    src: *src,
                    next: *next,
                },
                ("and", [dst, left, right, next]) => Instr::And {
                    dst: *dst,
                    left: *left,
                    right: *right,
                    next: *next,
                },
                ("or", [dst, left, right, next]) => Instr::Or {
                    dst: *dst,
                    left: *left,
                    right: *right,
                    next: *next,
                },
                ("xor", [dst, left, right, next]) => Instr::Xor {
                    dst: *dst,
                    left: *left,
                    right: *right,
                    next: *next,
                },
                ("branch", [test, yes, no]) => Instr::Branch {
                    test: *test,
                    yes: *yes,
                    no: *no,
                },
                ("push", [stack, src, next]) => Instr::Push {
                    stack: *stack,
                    src: *src,
                    next: *next,
                },
                ("peek", [stack, value, present, next]) => Instr::Peek {
                    stack: *stack,
                    value: *value,
                    present: *present,
                    next: *next,
                },
                ("pop", [stack, value, present, next]) => Instr::Pop {
                    stack: *stack,
                    value: *value,
                    present: *present,
                    next: *next,
                },
                other => panic!("unsupported original finite instruction {other:?}"),
            }
        })
        .collect();
    Program::new(
        parse_num(header[6]),
        parse_num(header[7]),
        parse_num(header[5]),
        code,
    )
    .unwrap()
}

fn check<const R: usize, const S: usize>(
    table: &str,
    generated: fn(
        &mut lean_eth_reference::bit_program::Config<R, S>,
        RunLimits,
    )
        -> Result<lean_eth_reference::bit_program::RunStats, lean_eth_reference::Error>,
) {
    let reference = parse::<R, S>(table);
    for case in 0..8 {
        let input = (0..(case % 5)).map(|i| (i + case) % 2 == 0);
        let mut initial = reference.initial(input);
        for i in 0..R {
            initial.regs[i] = (i + case) % 2 == 0;
        }
        for (i, stack) in initial.stacks.iter_mut().enumerate() {
            if (i + case) % 17 == 0 && stack.is_empty() {
                stack.extend([case % 2 == 0, case % 3 == 0]);
            }
        }
        for max_steps in [0, 1, 2, 9, 30, 64] {
            for max_stack_bits in [0, 5, 60] {
                let limits = RunLimits {
                    max_steps,
                    max_stack_bits,
                };
                let mut expected = initial.clone();
                let mut actual = initial.clone();
                let left = reference.run(&mut expected, limits);
                let right = generated(&mut actual, limits);
                assert_eq!(left, right, "run result, case={case}, limits={limits:?}");
                assert_eq!(
                    expected, actual,
                    "physical state, case={case}, limits={limits:?}"
                );
            }
        }
    }
}

#[test]
fn every_generated_original_source_program_matches_reference_machine() {
    let text = include_str!("../tools/fixtures/original/all-literal.bundle");
    let mut tables: Vec<String> = text.split("\n\n").map(str::to_string).collect();
    assert_eq!(tables.len(), 65, "source program count");
    let (_, first) = tables[0].split_once('\n').unwrap();
    tables[0] = first.to_string();
    let last_index = tables.len() - 1;
    let (last, suffix) = tables[last_index]
        .split_once("\nEND_ORIGINAL_LEAN_LITERAL_BUNDLE|")
        .unwrap();
    assert_eq!(suffix.trim(), "65");
    tables[last_index] = last.to_string();
    check::<8, 3>(&tables[0], catalog::source_0::run);
    check::<8, 6>(&tables[1], catalog::source_1::run);
    check::<3, 2>(&tables[2], catalog::source_2::run);
    check::<3, 2>(&tables[3], catalog::source_3::run);
    check::<3, 3>(&tables[4], catalog::source_4::run);
    check::<3, 1>(&tables[5], catalog::source_5::run);
    check::<2, 3>(&tables[6], catalog::source_6::run);
    check::<3, 2>(&tables[7], catalog::source_7::run);
    check::<5, 2>(&tables[8], catalog::source_8::run);
    check::<8, 7>(&tables[9], catalog::source_9::run);
    check::<8, 3>(&tables[10], catalog::source_10::run);
    check::<8, 3>(&tables[11], catalog::source_11::run);
    check::<8, 5>(&tables[12], catalog::source_12::run);
    check::<2, 2>(&tables[13], catalog::source_13::run);
    check::<2, 2>(&tables[14], catalog::source_14::run);
    check::<2, 1>(&tables[15], catalog::source_15::run);
    check::<2, 5>(&tables[16], catalog::source_16::run);
    check::<4, 2>(&tables[17], catalog::source_17::run);
    check::<4, 2>(&tables[18], catalog::source_18::run);
    check::<4, 2>(&tables[19], catalog::source_19::run);
    check::<2, 2>(&tables[20], catalog::source_20::run);
    check::<8, 13>(&tables[21], catalog::source_21::run);
    check::<4, 2>(&tables[22], catalog::source_22::run);
    check::<4, 2>(&tables[23], catalog::source_23::run);
    check::<4, 2>(&tables[24], catalog::source_24::run);
    check::<4, 1>(&tables[25], catalog::source_25::run);
    check::<6, 3>(&tables[26], catalog::source_26::run);
    check::<5, 3>(&tables[27], catalog::source_27::run);
    check::<3, 2>(&tables[28], catalog::source_28::run);
    check::<4, 2>(&tables[29], catalog::source_29::run);
    check::<3, 2>(&tables[30], catalog::source_30::run);
    check::<3, 3>(&tables[31], catalog::source_31::run);
    check::<8, 2>(&tables[32], catalog::source_32::run);
    check::<3, 1>(&tables[33], catalog::source_33::run);
    check::<2, 2>(&tables[34], catalog::source_34::run);
    check::<3, 1>(&tables[35], catalog::source_35::run);
    check::<3, 2>(&tables[36], catalog::source_36::run);
    check::<5, 1>(&tables[37], catalog::source_37::run);
    check::<3, 2>(&tables[38], catalog::source_38::run);
    check::<3, 1>(&tables[39], catalog::source_39::run);
    check::<8, 3>(&tables[40], catalog::source_40::run);
    check::<2, 2>(&tables[41], catalog::source_41::run);
    check::<3, 2>(&tables[42], catalog::source_42::run);
    check::<4, 2>(&tables[43], catalog::source_43::run);
    check::<2, 2>(&tables[44], catalog::source_44::run);
    check::<4, 10>(&tables[45], catalog::source_45::run);
    check::<3, 3>(&tables[46], catalog::source_46::run);
    check::<3, 7>(&tables[47], catalog::source_47::run);
    check::<2, 4>(&tables[48], catalog::source_48::run);
    check::<2, 4>(&tables[49], catalog::source_49::run);
    check::<3, 3>(&tables[50], catalog::source_50::run);
    check::<3, 2>(&tables[51], catalog::source_51::run);
    check::<5, 2>(&tables[52], catalog::source_52::run);
    check::<8, 2>(&tables[53], catalog::source_53::run);
    check::<2, 2>(&tables[54], catalog::source_54::run);
    check::<3, 3>(&tables[55], catalog::source_55::run);
    check::<3, 7>(&tables[56], catalog::source_56::run);
    check::<2, 3>(&tables[57], catalog::source_57::run);
    check::<2, 2>(&tables[58], catalog::source_58::run);
    check::<3, 3>(&tables[59], catalog::source_59::run);
    check::<3, 3>(&tables[60], catalog::source_60::run);
    check::<3, 4>(&tables[61], catalog::source_61::run);
    check::<8, 3>(&tables[62], catalog::source_62::run);
    check::<3, 5>(&tables[63], catalog::source_63::run);
    check::<2, 2>(&tables[64], catalog::source_64::run);
}
