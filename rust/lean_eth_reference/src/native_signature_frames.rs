//! Physical suspended-frame protocol of the attained-signature tuple DFS.
//!
//! Source: `openai/math@4eaee87548250b2682affda7d05d947c05554bae`,
//! `SqrtLogSpace/SignatureTupleProgram.lean` (pushFrameProgram,
//! suspend/resume, pushWord/popWord, cursor save/restore, representative
//! install/drop, and level transitions), plus
//! `SqrtLogSpace/SignatureTupleNative.lean` (fresh-latch initializer).
//!
//! These are the actual finite instructions. No Rust-host serialization,
//! DFS recursion, list of emitted tuples, or semantic callback is executed.
//! The remaining signature predicate, head loader, and visitor are NOT ported
//! by this module.

use crate::Error;
use crate::bit_program::{Atom, Cmd, Instr, Program};
use crate::native_high::{clear_program, copy_program};
use crate::native_query_prefix::frame_program;

/// The pinned source tuple frame layout, `tupleStacks i = 836 + i`.
pub const TUPLE_STACKS: [usize; 12] = [836, 837, 838, 839, 840, 841, 842, 843, 844, 845, 846, 847];
/// Source `SignatureTupleProgram.controllerPorts` (active, leaf, available, fresh).
pub const CONTROLLER_REGISTERS: [usize; 4] = [36, 37, 38, 39];
/// `currentHeadPorts`: only transient head state, not persistent cursor/frames.
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

/// The original 8-label `SignatureTupleProgram.pushFrameProgram`.
/// Consumes the source word and prepends `Encoding.frame word.reverse` to dst.
/// Empty words are represented by an actual `[false]` delimiter.
pub fn push_frame_program() -> Result<Program<2, 2>, Error> {
    Program::new(
        0,
        1,
        0,
        vec![
            Instr::Set {
                dst: 0,
                value: false,
                next: 1,
            },
            Instr::Push {
                stack: 1,
                src: 0,
                next: 2,
            },
            Instr::Pop {
                stack: 0,
                value: 0,
                present: 1,
                next: 3,
            },
            Instr::Branch {
                test: 1,
                yes: 4,
                no: 7,
            },
            Instr::Push {
                stack: 1,
                src: 0,
                next: 5,
            },
            Instr::Set {
                dst: 0,
                value: true,
                next: 6,
            },
            Instr::Push {
                stack: 1,
                src: 0,
                next: 2,
            },
            Instr::Halt,
        ],
    )
}

/// Generic source `pushWordCommand src dst`, requiring distinct ports.
pub fn push_word_command(src: usize, dst: usize) -> Result<Cmd<40, 896>, Error> {
    Ok(Cmd::Call(
        push_frame_program()?.lift::<40, 896>([0, 1], [src, dst])?,
    ))
}

/// Generic source `popWordCommand src dst`, using the audited 7-label parser.
pub fn pop_word_command(src: usize, dst: usize) -> Result<Cmd<40, 896>, Error> {
    Ok(Cmd::Call(
        frame_program()?.lift::<40, 896>([0, 1], [src, dst])?,
    ))
}

/// Suspend source 840 -> 836; resume source 836 -> 840.
pub fn suspend_command() -> Result<Cmd<40, 896>, Error> {
    push_word_command(TUPLE_STACKS[4], TUPLE_STACKS[0])
}
pub fn resume_command() -> Result<Cmd<40, 896>, Error> {
    pop_word_command(TUPLE_STACKS[0], TUPLE_STACKS[4])
}

/// Source `saveCursorCommand`. The remaining word is pushed *after* the
/// candidate word, so restoration pops remaining first.
pub fn save_cursor_command() -> Result<Cmd<40, 896>, Error> {
    Ok(Cmd::seq(
        push_word_command(TUPLE_STACKS[2], TUPLE_STACKS[0])?,
        push_word_command(TUPLE_STACKS[7], TUPLE_STACKS[0])?,
    ))
}

/// Source `restoreCursorCommand`. Requires empty candidate/remaining stacks.
pub fn restore_cursor_command() -> Result<Cmd<40, 896>, Error> {
    Ok(Cmd::seq(
        pop_word_command(TUPLE_STACKS[0], TUPLE_STACKS[7])?,
        pop_word_command(TUPLE_STACKS[0], TUPLE_STACKS[2])?,
    ))
}

/// Source `recordRepresentativeCommand`, with physical source copy then frame.
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

/// Source `dropRepresentativeCommand` discards exactly one stored frame.
pub fn drop_representative_command() -> Result<Cmd<40, 896>, Error> {
    Ok(Cmd::seq(
        pop_word_command(TUPLE_STACKS[1], TUPLE_STACKS[4])?,
        clear(TUPLE_STACKS[4])?,
    ))
}

/// Source `descendLevelCommand`: unary decrement of heads remaining and
/// increment of physical head address, then update the leaf flag.
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

/// Source `ascendLevelCommand`: reverse one level, leaving leaf false.
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

/// Root-frame presence, not the value of its first bit.
pub fn test_parent_command() -> Cmd<40, 896> {
    atom(Atom::Peek {
        stack: TUPLE_STACKS[0],
        value: 0,
        present: CONTROLLER_REGISTERS[0],
    })
}

/// `SignatureTupleNative.initializeFreshCommand`: physically clear stale
/// latch bits and write exactly one false bit for the predecessor scan.
pub fn initialize_fresh_command() -> Result<Cmd<40, 896>, Error> {
    Ok(Cmd::seq(
        clear(362)?,
        Cmd::seq(set(0, false), atom(Atom::Push { stack: 362, src: 0 })),
    ))
}

/// Source `leaveHeadCommand` clears exactly eight transient head tapes.
pub fn leave_head_command() -> Result<Cmd<40, 896>, Error> {
    let mut command = Cmd::Skip;
    for &p in CURRENT_HEAD_PORTS.iter().rev() {
        command = Cmd::seq(clear(p)?, command);
    }
    Ok(command)
}
