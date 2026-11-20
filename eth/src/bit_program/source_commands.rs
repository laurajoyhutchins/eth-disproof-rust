//! Source-shaped command composition shared by query and counting.
//!
//! These are builders of structured finite-machine syntax, not host-level
//! operations. A right-associated `Seq` ending in `Skip` is deliberately
//! distinct from one ending in a real terminal command. Source order,
//! duplicate operations and the `Skip` leaf must remain observable.

use std::ops::Range;

use crate::Error;

use super::stack_routines::clear_program;
use super::{Atom, Cmd};

/// The exact `Seq(first, Seq(second, ... Skip))` syntax used by the
/// signature and matrix-preprocessing source ports. Collecting first allows
/// the supplied iterator to be forward-only, as in the previous callers.
pub(crate) fn seq<const R: usize, const S: usize>(
    commands: impl IntoIterator<Item = Cmd<R, S>>,
) -> Cmd<R, S> {
    commands
        .into_iter()
        .collect::<Vec<_>>()
        .into_iter()
        .rev()
        .fold(Cmd::Skip, |tail, first| Cmd::seq(first, tail))
}

/// Clear the given source stacks in order, including duplicates, before
/// executing `tail`, using the source's read registers 0 and 1.
/// Unlike `clear_many`, this does not append `Skip`
/// after the final command. The source cost of each clear is retained.
pub(crate) fn clear_many_then<const R: usize, const S: usize>(
    ports: &[usize],
    mut tail: Cmd<R, S>,
) -> Result<Cmd<R, S>, Error> {
    for &port in ports.iter().rev() {
        tail = Cmd::seq(Cmd::Call(clear_program(port, 0, 1)?), tail);
    }
    Ok(tail)
}

/// Right-associated source clears ending in the explicit `Skip` command.
/// Even an empty port list yields `Skip`, not a host-level no-op.
pub(crate) fn clear_many<const R: usize, const S: usize>(
    ports: &[usize],
) -> Result<Cmd<R, S>, Error> {
    clear_many_then(ports, Cmd::Skip)
}

/// Original source work-register resets in ascending register order.
/// The reverse fold is deliberate; it preserves `Seq(Set, ..., Skip)`.
pub(crate) fn reset_false<const R: usize, const S: usize>(registers: Range<usize>) -> Cmd<R, S> {
    registers.rev().fold(Cmd::Skip, |tail, dst| {
        Cmd::seq(Cmd::Atom(Atom::Set { dst, value: false }), tail)
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    fn old_clear_many<const R: usize, const S: usize>(
        ports: &[usize],
        tail: Cmd<R, S>,
    ) -> Result<Cmd<R, S>, Error> {
        let mut command = tail;
        for &port in ports.iter().rev() {
            command = Cmd::seq(Cmd::Call(clear_program(port, 0, 1)?), command);
        }
        Ok(command)
    }

    #[test]
    fn right_association_preserves_the_explicit_skip_leaf() {
        let first: Cmd<4, 8> = Cmd::Atom(Atom::Set {
            dst: 2,
            value: true,
        });
        let second = Cmd::Atom(Atom::Push { stack: 3, src: 2 });
        let expected = Cmd::seq(first.clone(), Cmd::seq(second.clone(), Cmd::Skip));
        assert_eq!(seq([first.clone(), second.clone()]), expected);
        assert_eq!(seq(std::iter::empty::<Cmd<4, 8>>()), Cmd::Skip);
        assert_eq!(seq([first.clone()]), Cmd::seq(first.clone(), Cmd::Skip));
        assert_ne!(
            expected,
            Cmd::seq(Cmd::seq(first.clone(), second.clone()), Cmd::Skip)
        );
        assert_eq!(
            seq([first, second]).compiled(0, 3).unwrap(),
            expected.compiled(0, 3).unwrap()
        );
    }

    #[test]
    fn canonical_clears_match_both_previous_source_suffix_conventions() {
        for ports in [vec![], vec![3], vec![1, 3, 1], vec![7, 0, 7, 2]] {
            let old = old_clear_many::<4, 8>(&ports, Cmd::Skip).unwrap();
            let new = clear_many::<4, 8>(&ports).unwrap();
            assert_eq!(new, old);
            assert_eq!(new.compiled(0, 0).unwrap(), old.compiled(0, 0).unwrap());

            let terminal = Cmd::Atom(Atom::Set {
                dst: 2,
                value: true,
            });
            let old = old_clear_many::<4, 8>(&ports, terminal.clone()).unwrap();
            let new = clear_many_then(&ports, terminal).unwrap();
            assert_eq!(new, old);
            assert_eq!(new.compiled(0, 0).unwrap(), old.compiled(0, 0).unwrap());
        }
    }

    #[test]
    fn reset_range_matches_the_independent_reverse_fold() {
        for count in [0, 1, 3, 9] {
            let old: Cmd<16, 8> = (0..count).rev().fold(Cmd::Skip, |tail, dst| {
                Cmd::seq(Cmd::Atom(Atom::Set { dst, value: false }), tail)
            });
            let new = reset_false(0..count);
            assert_eq!(new, old);
            assert_eq!(new.compiled(0, 0).unwrap(), old.compiled(0, 0).unwrap());
        }
    }

    #[test]
    fn invalid_clear_port_refuses_in_the_same_reverse_order() {
        let old = old_clear_many::<4, 8>(&[99, 8], Cmd::Skip).unwrap_err();
        let new = clear_many::<4, 8>(&[99, 8]).unwrap_err();
        assert_eq!(format!("{old:?}"), format!("{new:?}"));
    }
}
