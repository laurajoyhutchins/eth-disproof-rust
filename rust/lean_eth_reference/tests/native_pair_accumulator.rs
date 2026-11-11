//! Independent machine-state tests for *preparing* one signed pair update.
//! The actual `pairUpdate` is deliberately NOT supplied by a test oracle.
use lean_eth_reference::Error;
use lean_eth_reference::bit_program::{Config, Program, RunLimits};
use lean_eth_reference::native_pair_accumulator::{
    CACHE_PAIRS, PAIR_SCRATCH, bootstrap_environment_command, clear_pair_command,
    prepare_pair_program,
};

fn put(d: &mut Config<40, 896>, port: usize, word: &[bool]) {
    d.stacks[port] = word.iter().copied().collect();
}
fn got(d: &Config<40, 896>, port: usize) -> Vec<bool> {
    d.stacks[port].iter().copied().collect()
}
fn run(p: &Program<40, 896>, d: &mut Config<40, 896>) -> u64 {
    p.run(
        d,
        RunLimits {
            max_steps: 1_000_000,
            max_stack_bits: 400_000,
        },
    )
    .unwrap()
    .instructions
}
fn source_word(port: usize, length: usize) -> Vec<bool> {
    (0..length).map(|i| (i + port) % 3 != 1).collect()
}

#[test]
fn scratch_index_set_is_exactly_the_lean_source_set() {
    let source: Vec<usize> = (0..56)
        .chain(100..128)
        .chain([159, 841, 848, 849])
        .collect();
    assert_eq!(PAIR_SCRATCH, source.as_slice());
    assert_eq!(PAIR_SCRATCH.len(), 88);
    let unique: std::collections::HashSet<_> = PAIR_SCRATCH.iter().copied().collect();
    assert_eq!(unique.len(), 88);
    assert_eq!(
        CACHE_PAIRS,
        [
            (194, 5),
            (202, 12),
            (203, 17),
            (201, 22),
            (204, 39),
            (212, 45),
            (243, 46),
        ]
    );
    for &preserved in &[
        194, 202, 203, 201, 204, 212, 243, 211, 834, 835, 850, 851, 837,
    ] {
        assert!(
            !unique.contains(&preserved),
            "source master or guard {preserved} overwritten"
        );
    }
}

#[test]
fn clear_pair_is_a_lifted_physical_clear_and_preserves_every_other_stack() {
    let program = clear_pair_command().unwrap().compiled(851, 850).unwrap();
    let mut d = program.initial([]);
    let mut expected = vec![Vec::new(); 896];
    for (port, slot) in expected.iter_mut().enumerate() {
        let word = source_word(port, port % 5);
        put(&mut d, port, &word);
        *slot = word;
    }
    let original = d.regs;
    let original_bits = d.stack_bits().unwrap();
    let steps = run(&program, &mut d);
    let source_steps: u64 = PAIR_SCRATCH
        .iter()
        .map(|&i| (2 * expected[i].len() + 3) as u64)
        .sum();
    // The lifted compiled clearMany contributes its halt, the outer
    // compiled call contributes another final halt.
    assert_eq!(steps, source_steps + 2);
    assert!(d.pc.is_none());
    assert!(d.stack_bits().unwrap() <= original_bits);
    for (port, word) in expected.iter().enumerate() {
        assert_eq!(
            got(&d, port),
            if PAIR_SCRATCH.contains(&port) {
                vec![]
            } else {
                word.clone()
            },
            "port {port}"
        );
    }
    assert_eq!(&d.regs[2..], &original[2..]);
}

#[test]
fn preparation_recovers_all_real_caches_and_preserves_both_pair_words() {
    let p = prepare_pair_program().unwrap();
    for width in [0, 1, 2, 7, 21] {
        let mut d = p.initial([]);
        let mut masters = Vec::new();
        for (src, dst) in CACHE_PAIRS {
            let word = source_word(src, width + dst % 5);
            put(&mut d, src, &word);
            put(&mut d, dst, &[true, false, false, true]);
            masters.push((src, dst, word));
        }
        let scale = source_word(211, width + 3);
        put(&mut d, 211, &scale);
        let extras = [
            (834, vec![false, true]),
            (835, vec![true, true, false]),
            (850, vec![true, false, true]),
            (851, vec![false, false, true, true]),
            (837, vec![true, false]),
            (649, vec![true, true, true]),
        ];
        for (port, word) in &extras {
            put(&mut d, *port, word);
        }
        // The source contract explicitly allows stale scratch on entry.
        for port in PAIR_SCRATCH {
            if !CACHE_PAIRS.iter().any(|(_, dst)| *dst == port) {
                put(&mut d, port, &[true, false, true]);
            }
        }
        // The source uses registers 0/1 via Fin.castAdd; 24/25 must survive.
        d.regs[24] = true;
        d.regs[25] = true;
        let instruction_count = run(&p, &mut d);
        assert!(instruction_count > 0);
        assert!(d.pc.is_none());
        for (src, dst, word) in masters {
            assert_eq!(got(&d, src), word, "cache master {src}");
            assert_eq!(got(&d, dst), word, "copied workspace {dst}");
        }
        assert_eq!(got(&d, 211), scale);
        assert_eq!(
            got(&d, 34),
            scale,
            "scale word copied into arithmetic port 34"
        );
        for (port, word) in &extras {
            assert_eq!(got(&d, *port), *word, "persistent port {port}");
        }
        for port in PAIR_SCRATCH {
            if CACHE_PAIRS.iter().any(|(_, dst)| *dst == port) || port == 34 {
                continue;
            }
            assert!(got(&d, port).is_empty(), "scratch {port} survived");
        }
        assert!(d.regs[24] && d.regs[25]);
    }
}

#[test]
fn same_preparation_can_run_after_mutating_masters_without_retaining_stale_words() {
    let p = prepare_pair_program().unwrap();
    let mut d = p.initial([]);
    put(&mut d, 850, &[true, false]);
    put(&mut d, 851, &[false, true]);
    for iteration in 0..5 {
        for (src, _) in CACHE_PAIRS {
            put(&mut d, src, &source_word(src, 2 + iteration));
        }
        put(&mut d, 211, &source_word(211, 3 + iteration));
        d.pc = Some(p.entry());
        run(&p, &mut d);
        for (src, dst) in CACHE_PAIRS {
            assert_eq!(
                got(&d, src),
                got(&d, dst),
                "iteration {iteration} port {dst}"
            );
        }
        assert_eq!(got(&d, 211), got(&d, 34));
        assert_eq!(got(&d, 850), [true, false]);
        assert_eq!(got(&d, 851), [false, true]);
    }
}

#[test]
fn independent_separate_stages_match_composition_and_refuse_step_exhaustion() {
    let assembled = prepare_pair_program().unwrap();
    let clear = clear_pair_command().unwrap().compiled(851, 850).unwrap();
    let bootstrap = bootstrap_environment_command()
        .unwrap()
        .compiled(851, 850)
        .unwrap();
    let mut d = assembled.initial([]);
    for (src, _) in CACHE_PAIRS {
        put(&mut d, src, &source_word(src, 12));
    }
    put(&mut d, 211, &source_word(211, 9));
    for stack in PAIR_SCRATCH {
        put(&mut d, stack, &[true, false]);
    }
    put(&mut d, 850, &[false, true]);
    let mut control = Config {
        pc: Some(assembled.entry()),
        regs: d.regs,
        stacks: d.stacks.clone(),
    };
    run(&assembled, &mut control);
    d.pc = Some(clear.entry());
    run(&clear, &mut d);
    d.pc = Some(bootstrap.entry());
    run(&bootstrap, &mut d);
    assert_eq!(got(&d, 5), got(&control, 5));
    assert_eq!(got(&d, 12), got(&control, 12));
    assert_eq!(got(&d, 39), got(&control, 39));
    assert_eq!(got(&control, 34), got(&control, 211));

    let mut bounded = assembled.initial([]);
    put(&mut bounded, 194, &[true, false, true]);
    assert!(matches!(
        assembled.run(
            &mut bounded,
            RunLimits {
                max_steps: 5,
                max_stack_bits: 400_000
            }
        ),
        Err(Error::Capacity(_)),
    ));
    assert!(
        bounded.pc.is_some(),
        "budget exhaustion must never masquerade as halt"
    );
}

#[test]
fn source_measured_step_formula_accounts_for_clear_bootstrap_and_overwrite() {
    let p = prepare_pair_program().unwrap();
    for width in [0, 1, 3, 11] {
        let mut d = p.initial([]);
        for port in PAIR_SCRATCH {
            put(&mut d, port, &source_word(port, width + port % 4));
        }
        for (src, _) in CACHE_PAIRS {
            put(&mut d, src, &source_word(src, width + src % 3));
        }
        put(&mut d, 211, &source_word(211, width + 2));
        let source_clear: usize = PAIR_SCRATCH
            .iter()
            .map(|&port| 2 * d.stacks[port].len() + 3)
            .sum::<usize>()
            + 1;
        let source_cache: usize = CACHE_PAIRS
            .iter()
            .map(|&(src, _)| 7 * d.stacks[src].len() + 5)
            .sum::<usize>()
            + 1;
        // clearPair empties 34 before overwrite 211 -> 34.
        let source_overwrite = 7 * d.stacks[211].len() + 8;
        let compiled_halt = 1;
        assert_eq!(
            run(&p, &mut d),
            (source_clear + source_cache + source_overwrite + compiled_halt) as u64,
            "word length {width}"
        );
    }
}
