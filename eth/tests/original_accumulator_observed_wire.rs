//! Diagnostic-only parity for the original numerical accumulator's 309 source
//! opcodes. The input is an *observation* from pinned original Lean #eval,
//! NOT a Lean kernel certificate. This test does not authorize native AOT
//! production admission or assert mathematical counting correctness.
//!
//! Original OAI: openai/math@4eaee87548250b2682affda7d05d947c05554bae
//! Accumulate source git blob: 3e1664be261748c6e12a2d1cafb033dc26131bf9
//! Original Lean #eval: GH Actions #44827182079, artifact #14675006664.
//! All-label proof attempts at #44827182079 / #44828568939 refused >12GiB.
use lean_eth_reference::bit_program::{
    Config, DeferredProgram, Instr, Program, RunLimits, SourceGraphBinding,
};
use sha2::{Digest, Sha256};
use std::collections::VecDeque;

const GRAPH: &[u8] = include_bytes!("../fixtures/original-accumulate-observed-unverified.json");
const GRAPH_SHA256: &str = "0af370ad3ca3f8a5a9c0a144e8ffc82c07bc9b24acd206fa3ed863d8a58d2ea3";
const SOURCE_BLOB: &str = "3e1664be261748c6e12a2d1cafb033dc26131bf9";
const DECLARATION: &str =
    "OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsReadoutProgram.accumulateProgram";
const SOURCE_ID: &str = "query_module_moments_accumulate";

fn binding<'a>(sha: &'a str) -> SourceGraphBinding<'a> {
    SourceGraphBinding {
        id: SOURCE_ID,
        declaration: DECLARATION,
        source_blob: SOURCE_BLOB,
        graph_sha256: sha,
    }
}

// Independent, small *wire serializer* for an existing physical instruction.
// No duplicate program execution or alternative arithmetic semantics.
fn wire(instr: &Instr) -> String {
    match instr {
        Instr::Halt => "halt".into(),
        Instr::Goto { next } => format!("goto:{next}"),
        Instr::Set { dst, value, next } => {
            format!("set:{dst}:{}:{next}", usize::from(*value))
        }
        Instr::Copy { dst, src, next } => format!("copy:{dst}:{src}:{next}"),
        Instr::Not { dst, src, next } => format!("not:{dst}:{src}:{next}"),
        Instr::And {
            dst,
            left,
            right,
            next,
        } => {
            format!("and:{dst}:{left}:{right}:{next}")
        }
        Instr::Or {
            dst,
            left,
            right,
            next,
        } => {
            format!("or:{dst}:{left}:{right}:{next}")
        }
        Instr::Xor {
            dst,
            left,
            right,
            next,
        } => {
            format!("xor:{dst}:{left}:{right}:{next}")
        }
        Instr::Branch { test, yes, no } => format!("branch:{test}:{yes}:{no}"),
        Instr::Push { stack, src, next } => format!("push:{stack}:{src}:{next}"),
        Instr::Peek {
            stack,
            value,
            present,
            next,
        } => {
            format!("peek:{stack}:{value}:{present}:{next}")
        }
        Instr::Pop {
            stack,
            value,
            present,
            next,
        } => {
            format!("pop:{stack}:{value}:{present}:{next}")
        }
    }
}

#[test]
fn observed_lean_accumulator_round_trips_all_309_physical_labels_in_rust() {
    // A graph SHA binds the exact byte observation; it does NOT prove that
    // these bytes equal the original Lean source at every address.
    assert_eq!(format!("{:x}", Sha256::digest(GRAPH)), GRAPH_SHA256);
    let graph: serde_json::Value = serde_json::from_slice(GRAPH).unwrap();
    let rows = graph["program"]["code"].as_array().unwrap();
    assert_eq!(rows.len(), 309);
    let machine =
        DeferredProgram::<8, 27>::from_original_source_json(GRAPH, binding(GRAPH_SHA256)).unwrap();
    assert_eq!(machine.labels(), 309);
    assert_eq!(machine.entry(), 1);
    assert_eq!(machine.input_stack(), 15);
    assert_eq!(machine.output_stack(), 17);

    for (pc, expected) in rows.iter().enumerate() {
        let actual = machine.instruction_at(pc).unwrap();
        assert_eq!(
            wire(&actual),
            expected.as_str().unwrap(),
            "physical original-source observation mismatch at pc {pc}"
        );
    }
    assert_eq!(wire(&machine.instruction_at(0).unwrap()), "halt");
    assert_eq!(wire(&machine.instruction_at(1).unwrap()), "pop:15:0:1:2");
    assert_eq!(wire(&machine.instruction_at(308).unwrap()), "goto:0");
    assert!(machine.instruction_at(309).is_err());
}

#[test]
fn uncertified_observation_cannot_be_rebound_to_another_graph() {
    let bad_sha = "f".repeat(64);
    assert!(
        DeferredProgram::<8, 27>::from_original_source_json(GRAPH, binding(&bad_sha),).is_err()
    );

    let mut changed = GRAPH.to_vec();
    let index = changed
        .iter()
        .position(|&byte| byte == b'h')
        .expect("source graph contains a halt opcode");
    changed[index] = b'x';
    assert!(
        DeferredProgram::<8, 27>::from_original_source_json(&changed, binding(GRAPH_SHA256),)
            .is_err()
    );
}

// Genuine original Encoding.frame (one escape bit per payload bit, then false)
// and Squarefree.Program.rawEntries for ONE source dictionary record.
// This is input construction only, never a second instruction interpreter.
fn source_frame(bits: &[bool]) -> Vec<bool> {
    let mut out = Vec::with_capacity(2 * bits.len() + 1);
    for &bit in bits {
        out.push(true);
        out.push(bit);
    }
    out.push(false);
    out
}

fn source_legal_accumulator_input(hit: bool) -> Config<8, 27> {
    let mut initial = Config {
        pc: Some(1),
        regs: [false; 8],
        stacks: std::array::from_fn(|_| VecDeque::new()),
    };
    // Original SubexpLiftRing.baseWidth 2 1 = 2.
    // Original canonicalModulus 2 1 = little-endian modulus 2: 01.
    initial.stacks[5].extend([false, true]);
    initial.stacks[12].extend([true, true]);
    initial.stacks[24].push_back(true);
    // Original literalWordRun 2 1 [true] = little-endian one: 10.
    initial.stacks[17].extend([true, false]);
    // Original Squarefree.Program.rawEntries [([true], [true, false])].
    // This must be 11011100 under the source's Encoding.frame.
    let mut dictionary = source_frame(&[true]);
    dictionary.extend(source_frame(&[true, false]));
    assert_eq!(
        dictionary,
        [true, true, false, true, true, true, false, false]
    );
    initial.stacks[15].extend(dictionary);
    // Original inputTape reverses the query before placing it on stack 16.
    initial.stacks[16].push_back(hit);
    initial
}

fn assert_bits(actual: &VecDeque<bool>, expected: &[bool], label: &str) {
    assert!(
        actual.iter().copied().eq(expected.iter().copied()),
        "original observed accumulator final stack {label}: expected {expected:?}, got {actual:?}"
    );
}

#[test]
fn observed_original_accumulator_executes_real_modular_hit_and_absent_key_miss() {
    // The exact original instruction table is a source-observed fixture,
    // NOT an all-label Lean kernel-certified graph. This is an empirical
    // execution test of the existing canonical Rust BitProgram interpreter.
    let source =
        DeferredProgram::<8, 27>::from_original_source_json(GRAPH, binding(GRAPH_SHA256)).unwrap();
    let code = (0..309)
        .map(|pc| source.instruction_at(pc).unwrap())
        .collect::<Vec<_>>();
    let flat = Program::<8, 27>::new(15, 17, 1, code).unwrap();
    for hit in [true, false] {
        let mut cfg = source_legal_accumulator_input(hit);
        let stats = flat
            .run(
                &mut cfg,
                RunLimits {
                    max_steps: 100_000,
                    max_stack_bits: 8192,
                },
            )
            .expect("source-observed accumulator refused source-legal p=2,d=1 input");
        assert_eq!(cfg.pc, None, "original observed accumulator did not halt");
        assert!(
            stats.instructions > 1,
            "no actual arithmetic/dictionary execution"
        );
        // Expected one-word sum modulo 2: hit 1+1=0, absent key 1+0=1.
        assert_bits(
            &cfg.stacks[17],
            if hit { &[false, false] } else { &[true, false] },
            "17",
        );
        assert_bits(&cfg.stacks[5], &[false, true], "5");
        assert_bits(&cfg.stacks[12], &[true, true], "12");
        assert_bits(&cfg.stacks[24], &[true], "24");
        assert_bits(
            &cfg.stacks[15],
            &[true, true, false, true, true, true, false, false],
            "15",
        );
        assert_bits(&cfg.stacks[16], &[hit], "16");
        for i in 0..27 {
            if ![5, 12, 15, 16, 17, 24].contains(&i) {
                assert!(
                    cfg.stacks[i].is_empty(),
                    "source scratch stack {i} not cleared"
                );
            }
        }
        println!(
            "ORIGINAL_OBSERVED_ACCUMULATOR_EXECUTION case={} steps={} peak_bits={} \
             observation_only=true",
            if hit { "hit" } else { "miss" },
            stats.instructions,
            stats.peak_stack_bits
        );
    }
}
