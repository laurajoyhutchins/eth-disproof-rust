//! Physical suspended-frame protocol for the attained-signature tuple DFS.
//! Source: openai/math@4eaee87548250b2682affda7d05d947c05554bae
//! SignatureTupleProgram.lean and SignatureTupleNative.lean.
//! All operations are source-defined finite bit instructions. The complete
//! predicate, head loader, and tuple visitor are still unimplemented.

use crate::Error;
use crate::bit_program::{Atom, Cmd, Instr, Program};
use crate::native_high::{clear_program, copy_program};
use crate::native_query_prefix::frame_program;
pub use crate::native_signature_tuple::{CONTROLLER_REGISTERS, TUPLE_STACKS};

pub const CURRENT_HEAD_PORTS: [usize; 8] = [838, 839, 840, 841, 843, 844, 846, 847];

fn atom(x: Atom) -> Cmd<40, 896> {
    Cmd::Atom(x)
}
fn set(dst: usize, value: bool) -> Cmd<40, 896> {
    atom(Atom::Set { dst, value })
}
fn clear(src: usize) -> Result<Cmd<40, 896>, Error> {
    Ok(Cmd::Call(clear_program(src, 0, 1)?))
}

/// Exact eight-label pushFrameProgram: consumes source, pushes
/// Encoding.frame(word.reverse) before the prior destination suffix.
pub fn push_frame_program() -> Result<Program<2, 2>, Error> {
    Program::new(
        0,
        1,
        0,
        vec![
            Instr::Set { dst: 0, value: false, next: 1 },
            Instr::Push { stack: 1, src: 0, next: 2 },
            Instr::Pop { stack: 0, value: 0, present: 1, next: 3 },
            Instr::Branch { test: 1, yes: 4, no: 7 },
            Instr::Push { stack: 1, src: 0, next: 5 },
            Instr::Set { dst: 0, value: true, next: 6 },
            Instr::Push { stack: 1, src: 0, next: 2 },
            Instr::Halt,
        ],
    )
}

/// Source pushWordCommand; the lift enforces disjoint in-range stack ports.
pub fn push_word_command(src: usize, dst: usize) -> Result<Cmd<40, 896>, Error> {
    Ok(Cmd::Call(push_frame_program()?.lift::<40, 896>(
        [0, 1],
        [src, dst],
    )?))
}

/// Source popWordCommand, using the existing seven-label frame parser.
pub fn pop_word_command(src: usize, dst: usize) -> Result<Cmd<40, 896>, Error> {
    Ok(Cmd::Call(frame_program()?.lift::<40, 896>(
        [0, 1],
        [src, dst],
    )?))
}

pub fn suspend_command() -> Result<Cmd<40, 896>, Error> {
    push_word_command(TUPLE_STACKS[4], TUPLE_STACKS[0])
}
pub fn resume_command() -> Result<Cmd<40, 896>, Error> {
    pop_word_command(TUPLE_STACKS[0], TUPLE_STACKS[4])
}

/// Save candidate first, then remaining. Restore in the reverse order.
pub fn save_cursor_command() -> Result<Cmd<40, 896>, Error> {
    Ok(Cmd::seq(
        push_word_command(TUPLE_STACKS[2], TUPLE_STACKS[0])?,
        push_word_command(TUPLE_STACKS[7], TUPLE_STACKS[0])?,
    ))
}
pub fn restore_cursor_command() -> Result<Cmd<40, 896>, Error> {
    Ok(Cmd::seq(
        pop_word_command(TUPLE_STACKS[0], TUPLE_STACKS[7])?,
        pop_word_command(TUPLE_STACKS[0], TUPLE_STACKS[2])?,
    ))
}

/// Preserve the current candidate, while recording one framed representative.
pub fn record_representative_command() -> Result<Cmd<40, 896>, Error> {
    Ok(Cmd::seq(
        Cmd::Call(copy_program(
            TUPLE_STACKS[2],
            TUPLE_STACKS[4],
            TUPLE_STACKS[5],
            0,
            1,
        )?),
        push_word_command(TUPLE_STACKS[4], TUPLE_STACKS[1])?,
    ))
}
pub fn drop_representative_command() -> Result<Cmd<40, 896>, Error> {
    Ok(Cmd::seq(
        pop_word_command(TUPLE_STACKS[1], TUPLE_STACKS[4])?,
        clear(TUPLE_STACKS[4])?,
    ))
}

/// Source five-atom descendLevelCommand.
pub fn descend_level_command() -> Cmd<40, 896> {
    Cmd::seq(
        atom(Atom::Pop {
            stack: TUPLE_STACKS[6],
            value: 0,
            present: 1,
        }),
        Cmd::seq(
            set(0, true),
            Cmd::seq(
                atom(Atom::Push {
                    stack: TUPLE_STACKS[9],
                    src: 0,
                }),
                Cmd::seq(
                    atom(Atom::Peek {
                        stack: TUPLE_STACKS[6],
                        value: 0,
                        present: 1,
                    }),
                    atom(Atom::Not {
                        dst: CONTROLLER_REGISTERS[1],
                        src: 1,
                    }),
                ),
            ),
        ),
    )
}

/// Source four-atom ascendLevelCommand.
pub fn ascend_level_command() -> Cmd<40, 896> {
    Cmd::seq(
        atom(Atom::Pop {
            stack: TUPLE_STACKS[9],
            value: 0,
            present: 1,
        }),
        Cmd::seq(
            set(0, true),
            Cmd::seq(
                atom(Atom::Push {
                    stack: TUPLE_STACKS[6],
                    src: 0,
                }),
                set(CONTROLLER_REGISTERS[1], false),
            ),
        ),
    )
}

/// An empty payload frame is still present if its delimiter exists.
pub fn test_parent_command() -> Cmd<40, 896> {
    atom(Atom::Peek {
        stack: TUPLE_STACKS[0],
        value: 0,
        present: CONTROLLER_REGISTERS[0],
    })
}

/// Clear stale one-bit predicate latch and push one false bit.
pub fn initialize_fresh_command() -> Result<Cmd<40, 896>, Error> {
    Ok(Cmd::seq(
        clear(362)?,
        Cmd::seq(
            set(0, false),
            atom(Atom::Push { stack: 362, src: 0 }),
        ),
    ))
}

/// Clear precisely the eight transient current-head stacks.
pub fn leave_head_command() -> Result<Cmd<40, 896>, Error> {
    let mut command = Cmd::Skip;
    for &p in CURRENT_HEAD_PORTS.iter().rev() {
        command = Cmd::seq(clear(p)?, command);
    }
    Ok(command)
}
