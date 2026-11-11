//! A deliberately bounded end-to-end #SAT slice through actual source-defined
//! Rust BitProgram commands. This executes Native.frontendCommand, then
//! NativeTerminal.readyCommand, then Native.answerCommand on the SAME physical
//! 80-register / 1220-stack state. No host SAT/count oracle runs on this path.
//!
//! For a nonterminal formula the still-missing NativeLeafProgram is required:
//! refuse rather than interpreting an empty count stack as zero. This is not
//! an implementation of the full ETH construction or its TM2 cost bound.

use crate::bit_program::{Cmd, Config, Program, RunLimits, RunStats};
use crate::native_high::{clear_program, copy_program};
use crate::{Cnf, Error};
use crate::{native_answer, native_frontend, native_terminal_classifier};

pub const SOURCE_STAGES: [&str; 4] = [
    "Native.frontendCommand",
    "NativeTerminal.readyCommand",
    "TerminalCount.count_to_answer_input (source-primitive adapter)",
    "Native.answerCommand",
];

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TerminalCount {
    /// Exact source count stack 263, least-significant bit at the head.
    pub count_lsb: Vec<bool>,
    /// Exact physical answer bit from stack 1216.
    pub positive: bool,
    /// BitProgram instruction counts and live stack-bit peaks, per stage.
    /// These are NOT primitive two-tape TM steps or tape-space bounds.
    pub stages: [RunStats; 4],
    pub total_instructions: u64,
    pub peak_stack_bits: usize,
    pub normalized_body: Vec<bool>,
}

/// The original Native.outerCommand normally establishes the answerCommand
/// precondition: an exact binary count at ABI.countStack = 256. Our bounded
/// terminal-only path does not run the absent outer/DFS counting program.
/// Source-defined StackRoutines.clearProgram and copyProgram physically
/// transfer the terminal count from leaf output 263 to answer input 256.
/// This is an explicitly marked *adapter*, NOT a source-equivalent outer program.
fn count_to_answer_input_program() -> Result<Program<80, 1220>, Error> {
    Cmd::seq(
        Cmd::Call(clear_program(256, 72, 73)?),
        Cmd::Call(copy_program(263, 256, 1219, 72, 73)?),
    )
    .compiled(263, 256)
}

fn execute_stage(
    program: &Program<80, 1220>,
    state: &mut Config<80, 1220>,
    remaining: &mut u64,
    max_stack_bits: usize,
) -> Result<RunStats, Error> {
    // A source-compiled program halts with pc=None. Re-enter the next source
    // command while retaining ALL registers and physical stacks unchanged.
    state.pc = Some(program.entry());
    let stats = program.run(
        state,
        RunLimits {
            max_steps: *remaining,
            max_stack_bits,
        },
    )?;
    if state.pc.is_some() {
        return Err(Error::Invalid("native source stage did not halt".into()));
    }
    *remaining = remaining
        .checked_sub(stats.instructions)
        .ok_or(Error::Overflow)?;
    Ok(stats)
}

pub fn count_terminal(cnf: &Cnf, limits: RunLimits) -> Result<TerminalCount, Error> {
    let input = cnf.encode_lean();
    let frontend = native_frontend::program()?;
    let bits = input.bytes().map(|bit| bit == b'1');
    let mut state = frontend.initial(bits);
    let mut remaining = limits.max_steps;
    let a = execute_stage(&frontend, &mut state, &mut remaining, limits.max_stack_bits)?;
    let ready = native_terminal_classifier::ready_program()?;
    let b = execute_stage(&ready, &mut state, &mut remaining, limits.max_stack_bits)?;

    // These flags come from the *source machine's own* physical classifier.
    // [0] means empty clause, [7] means nonempty normalized clause list.
    if !state.regs[0] && state.regs[7] {
        if !state.stacks[263].is_empty() {
            return Err(Error::Invalid(
                "nonterminal acquired a fabricated count".into(),
            ));
        }
        return Err(Error::NotImplemented(
            "NativeLeafProgram.nonterminal #SAT counting",
        ));
    }
    if state.stacks[263].is_empty() {
        return Err(Error::Invalid(
            "terminal source machine produced no count word".into(),
        ));
    }
    if state.stacks[256]
        .iter()
        .copied()
        .ne(input.bytes().map(|b| b == b'1'))
    {
        return Err(Error::Invalid(
            "source frontend modified its preserved input".into(),
        ));
    }
    if !state.stacks[1219].is_empty() {
        return Err(Error::Invalid(
            "count transfer scratch stack is not empty".into(),
        ));
    }
    let transfer = count_to_answer_input_program()?;
    let c = execute_stage(&transfer, &mut state, &mut remaining, limits.max_stack_bits)?;
    if state.stacks[256] != state.stacks[263] {
        return Err(Error::Invalid(
            "count transfer lost or reordered a source bit".into(),
        ));
    }

    let answer = native_answer::answer_program()?;
    let d = execute_stage(&answer, &mut state, &mut remaining, limits.max_stack_bits)?;

    if state.stacks[1216].len() != 1 {
        return Err(Error::Invalid(
            "source answer was not one physical bit".into(),
        ));
    }
    let count_lsb: Vec<bool> = state.stacks[263].iter().copied().collect();
    let positive = state.stacks[1216][0];
    if positive != count_lsb.iter().any(|b| *b) {
        return Err(Error::Invalid(format!(
            "source answer/count disagreement: flags empty_clause={} nonempty_body={} count_lsb={:?} answer={} ambient_len={} body_len={}",
            state.regs[0],
            state.regs[7],
            count_lsb,
            positive,
            state.stacks[258].len(),
            state.stacks[265].len(),
        )));
    }
    if state.stacks[256] != state.stacks[263] {
        return Err(Error::Invalid(
            "answer command modified its source count".into(),
        ));
    }
    for port in [268, 269, 1217, 1218, 1219] {
        if !state.stacks[port].is_empty() {
            return Err(Error::Invalid(format!(
                "source work stack {port} not cleared"
            )));
        }
    }
    let total_instructions = a
        .instructions
        .checked_add(b.instructions)
        .and_then(|v| v.checked_add(c.instructions))
        .and_then(|v| v.checked_add(d.instructions))
        .ok_or(Error::Overflow)?;
    Ok(TerminalCount {
        count_lsb,
        positive,
        stages: [a, b, c, d],
        total_instructions,
        peak_stack_bits: a
            .peak_stack_bits
            .max(b.peak_stack_bits)
            .max(c.peak_stack_bits)
            .max(d.peak_stack_bits),
        normalized_body: state.stacks[265].iter().copied().collect(),
    })
}

/// Presentation-only conversion of an arbitrary-width bit word to decimal.
/// Host arithmetic here does NOT compute #SAT: the source machine already
/// produced the exact binary count. No u64/u128 truncation or saturation.
pub fn count_word_decimal(word_lsb: &[bool]) -> String {
    let mut decimal_le = vec![0_u8];
    for bit in word_lsb.iter().rev() {
        let mut carry = if *bit { 1_u16 } else { 0_u16 };
        for digit in &mut decimal_le {
            let v = u16::from(*digit) * 2 + carry;
            *digit = (v % 10) as u8;
            carry = v / 10;
        }
        while carry > 0 {
            decimal_le.push((carry % 10) as u8);
            carry /= 10;
        }
    }
    decimal_le
        .iter()
        .rev()
        .map(|digit| char::from(b'0' + *digit))
        .collect()
}
