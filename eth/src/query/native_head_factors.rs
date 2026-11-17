//! Source-pinned executable factor head selection and complete `prepareHead`.
//!
//! Lean: `openai/math@4eaee87548250b2682affda7d05d947c05554bae`
//! `SqrtLog/LeafHeadFactorsProgram{Test,Visit,Loop,Run}.lean` and
//! `SqrtLog/LeafHeadSetupProgram{Selection,Prepare}.lean`.
//!
//! Unlike ambient head selection, the factor scan visits the N factor rows
//! beginning at the *physical runtime offset A*. Its records encode the
//! original factor-relative index `j` as `encodeNat j`, not the absolute
//! index `A+j`. `factorProgram` and `prepareHead` are finite BitProgram
//! instruction tables; A, N, width, and bit index are unary stack data.

use crate::Error;
use crate::bit_program::{Atom, Cmd, Program};
use crate::native_bootstrap::stage;
use crate::native_head_selection::{
    color_select_program, escape_program, heads_command, type_bit_program,
};
use crate::native_head_support::support_command;
use crate::native_high::{clear_program, copy_program};

fn copy(src: usize, dst: usize) -> Result<Cmd<16, 64>, Error> {
    Ok(Cmd::Call(copy_program(src, dst, 42, 0, 1)?))
}
fn set(reg: usize, value: bool) -> Cmd<16, 64> {
    Cmd::Atom(Atom::Set { dst: reg, value })
}
fn push(stack: usize, reg: usize) -> Cmd<16, 64> {
    Cmd::Atom(Atom::Push { stack, src: reg })
}
fn pop(stack: usize, value: usize, present: usize) -> Cmd<16, 64> {
    Cmd::Atom(Atom::Pop {
        stack,
        value,
        present,
    })
}

/// Exact `LeafHeadFactorsProgram.test`: form the `A+j` unary address by
/// preserving copies 31→40, 39→40, read the packed word at that address,
/// clear the address, then read its bit at unary position z into register 4.
/// The low-mask is not inspected by this factor predicate.
pub fn factor_test_command() -> Result<Cmd<16, 64>, Error> {
    let selected = color_select_program()?.lift::<16, 64>(
        [11, 12, 13, 14, 15],
        [33, 40, 38, 16, 17, 36, 18, 19, 20, 21],
    )?;
    let bit = type_bit_program()?.lift::<16, 64>([0, 1, 4], [12, 36])?;
    Ok(Cmd::seq(
        copy(31, 40)?,
        Cmd::seq(
            copy(39, 40)?,
            Cmd::seq(
                Cmd::Call(selected),
                Cmd::seq(
                    Cmd::Call(clear_program(40, 0, 1)?),
                    Cmd::seq(copy(32, 12)?, Cmd::Call(bit)),
                ),
            ),
        ),
    ))
}

pub fn factor_test_program() -> Result<Program<16, 64>, Error> {
    factor_test_command()?.compiled(39, 36)
}

/// Emits `true :: frame(encodeNat j)` then a `false` count bit using the
/// *actual* reverse-stream escape routine and a paid unary index copy.
/// Unlike `HeadIdentifierProgram.emit`, `encodeNat j` contains the trailing
/// false bit. The source prepends that bit on stack 34 before escaping.
pub fn factor_emit_command() -> Result<Cmd<16, 64>, Error> {
    let escape = escape_program()?.lift::<16, 64>([0, 1], [34, 0])?;
    Ok(Cmd::seq(
        copy(39, 34)?,
        Cmd::seq(
            set(0, false),
            Cmd::seq(
                push(34, 0),
                Cmd::seq(
                    set(0, false),
                    Cmd::seq(
                        push(0, 0),
                        Cmd::seq(
                            Cmd::Call(escape),
                            Cmd::seq(
                                set(0, true),
                                Cmd::seq(push(0, 0), Cmd::seq(set(0, false), push(1, 0))),
                            ),
                        ),
                    ),
                ),
            ),
        ),
    ))
}

/// Physical factor visit: test the source bit and emit an encoded relative
/// factor index only if register 4 is true. No semantic fast path is used.
pub fn factor_visit_command() -> Result<Cmd<16, 64>, Error> {
    Ok(Cmd::seq(
        factor_test_command()?,
        Cmd::ite(4, factor_emit_command()?, Cmd::Skip),
    ))
}

pub fn factor_visit_program() -> Result<Program<16, 64>, Error> {
    factor_visit_command()?.compiled(39, 0)
}

/// `LeafHeadFactorsProgram.command`: the source descending unary for-loop,
/// including final absent pop, terminator, and all-16-register reset.
pub fn factor_full_command() -> Result<Cmd<16, 64>, Error> {
    let pop_index = pop(39, 14, 15);
    let iteration = Cmd::seq(
        pop_index.clone(),
        Cmd::while_(15, Cmd::seq(factor_visit_command()?, pop_index)),
    );
    let reset = (0..16)
        .rev()
        .fold(Cmd::Skip, |tail, r| Cmd::seq(set(r, false), tail));
    Ok(Cmd::seq(
        copy(30, 39)?,
        Cmd::seq(
            set(0, false),
            Cmd::seq(push(0, 0), Cmd::seq(iteration, reset)),
        ),
    ))
}

pub fn factor_full_program() -> Result<Program<16, 64>, Error> {
    factor_full_command()?.compiled(30, 0)
}

/// Source `LeafHeadSetupProgram.factors`, stage input mappings and output:
/// 129→30 (N), 128→31 (A), 649→32 (z), 133→33 (rows), 132→38 (W);
/// 0→671 (framed factor-relative IDs). The full 64-stack bank is cleaned.
pub fn factors_command() -> Result<Cmd<16, 768>, Error> {
    stage(
        factor_full_program()?,
        std::array::from_fn(|i| i),
        &[(129, 30), (128, 31), (649, 32), (133, 33), (132, 38)],
        &[(0, 671)],
    )
}

pub fn factors_program() -> Result<Program<16, 768>, Error> {
    factors_command()?.compiled(129, 671)
}

/// Full source `LeafHeadSetupProgram.prepareHead`:
/// `seq heads (seq support factors)` in the 16×768 machine.
/// This does **not** implement the subsequent matrix or bucket readout.
pub fn prepare_head_command() -> Result<Cmd<16, 768>, Error> {
    Ok(Cmd::seq(
        heads_command()?,
        Cmd::seq(support_command()?, factors_command()?),
    ))
}

pub fn prepare_head_program() -> Result<Program<16, 768>, Error> {
    prepare_head_command()?.compiled(128, 671)
}
