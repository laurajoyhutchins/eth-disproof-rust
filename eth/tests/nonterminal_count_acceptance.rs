//! Acceptance boundary for a genuinely nonterminal CNF.
//!
//! This is NOT evidence that general counting is implemented. The independent
//! oracle establishes #SAT = 5; the original-source physical frontend and
//! classifier must agree that the input is nonterminal. Until the actual
//! QueryStream -> high query -> leaf -> DFS -> outer path runs to completion,
//! a native count remains unavailable and MUST NOT be fabricated.
//!
//! Upstream: openai/math@4eaee87548250b2682affda7d05d947c05554bae
//! Relevant declarations: Native.frontendCommand,
//! NativeTerminal.readyCommand, NativeLeafProgram.command,
//! QueryStreamProgram.command, DFSCountProgram.command, Native.outerCommand.

use lean_eth_reference::bit_program::RunLimits;
use lean_eth_reference::native_terminal_count::count_terminal;
use lean_eth_reference::{Error, native_frontend, native_terminal_classifier, parse_dimacs};

// F = (x1 OR x2) AND (x1 OR x3).
const CNF: &str = "p cnf 3 2\n1 2 0\n1 3 0\n";

fn limits() -> RunLimits {
    RunLimits {
        max_steps: 20_000_000,
        max_stack_bits: 300_000,
    }
}

/// Independent Boolean truth-table oracle. This does not consult the crate's
/// CNF evaluator, semantic #SAT solver, normalized formula, or native output.
fn independent_models() -> Vec<usize> {
    (0usize..8)
        .filter(|&assignment| {
            let x1 = (assignment & 1) != 0;
            let x2 = (assignment & 2) != 0;
            let x3 = (assignment & 4) != 0;
            (x1 || x2) && (x1 || x3)
        })
        .collect()
}

#[test]
fn nonterminal_oracle_is_exactly_five() {
    assert_eq!(independent_models(), [1, 3, 5, 6, 7]);
}

#[test]
fn physical_machine_reaches_nonterminal_boundary_without_fabricated_count() {
    let cnf = parse_dimacs(CNF).expect("fixed nonterminal DIMACS");
    let encoded = cnf.encode_lean();
    let frontend = native_frontend::program().expect("source-defined frontend");
    let mut machine = frontend.initial(encoded.bytes().map(|b| b == b'1'));
    let frontend_stats = frontend
        .run(&mut machine, limits())
        .expect("frontend halts");
    assert!(machine.pc.is_none());
    assert!(frontend_stats.instructions > 0);

    // Resume on the SAME physical state. Only the program counter is reset.
    let classify = native_terminal_classifier::ready_program().expect("source classifier");
    machine.pc = Some(classify.entry());
    let classify_stats = classify
        .run(&mut machine, limits())
        .expect("classifier halts");
    assert!(machine.pc.is_none());
    assert!(classify_stats.instructions > 0);

    assert!(
        !machine.regs[0],
        "no empty clause in the normalized formula"
    );
    assert!(machine.regs[7], "the normalized formula has real clauses");
    assert!(
        machine.stacks[263].is_empty(),
        "a nonterminal count has NOT been produced"
    );
    assert_eq!(
        machine.stacks[256].iter().copied().collect::<Vec<_>>(),
        encoded.bytes().map(|b| b == b'1').collect::<Vec<_>>(),
        "the original input remains intact"
    );

    // A successful count is forbidden until the missing source-defined
    // QueryStream/HighQuery/NativeLeaf/DFS/outer composition is executable.
    assert!(matches!(
        count_terminal(&cnf, limits()),
        Err(Error::NotImplemented(
            "NativeLeafProgram.nonterminal #SAT counting"
        ))
    ));
}
