//! Original `RecordPrograms.iterate` structured finite-machine control flow.
//!
//! This preserves the source's sequence, conditional and loop nodes, not a
//! host-side record traversal. The initial pop precedes the loop; when the
//! callback sets `found`, the advance operation clears `tag` without
//! consuming an additional input record.

use crate::Error;

use super::frame_programs::frame_program;
use super::{Atom, Cmd};

/// Register and stack indices of the source record iterator.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct RecordPorts {
    pub tag: usize,
    pub present: usize,
    pub found: usize,
    pub source: usize,
}

/// Assemble the same command tree for each source-native scanner.
/// The caller supplies the physical frame-reader and record callback.
pub(crate) fn iterate<const R: usize, const S: usize>(
    ports: RecordPorts,
    reader: Cmd<R, S>,
    callback: Cmd<R, S>,
) -> Cmd<R, S> {
    let pop = || {
        Cmd::Atom(Atom::Pop {
            stack: ports.source,
            value: ports.tag,
            present: ports.present,
        })
    };
    let advance = Cmd::ite(
        ports.found,
        Cmd::Atom(Atom::Set {
            dst: ports.tag,
            value: false,
        }),
        pop(),
    );
    let body = Cmd::seq(reader, Cmd::seq(callback, advance));
    Cmd::seq(
        Cmd::Atom(Atom::Set {
            dst: ports.found,
            value: false,
        }),
        Cmd::seq(pop(), Cmd::while_(ports.tag, body)),
    )
}

/// Build the original framed RecordPrograms iterator, retaining the explicit
/// physical two-register/two-stack ParserProgram.frameProgram call.
/// The reader uses [tag, present] and [source, payload]; an invalid
/// (aliased or out-of-range) lift refuses rather than silently remapping.
/// The callback remains source-specific and is never interpreted on the host.
/// As in the pinned Lean `RecordPrograms.Ports`, `found` must also be
/// distinct from `tag` and `present`; a parser lift cannot test that.
pub(crate) fn iterate_framed<const R: usize, const S: usize>(
    ports: RecordPorts,
    payload: usize,
    callback: Cmd<R, S>,
) -> Result<Cmd<R, S>, Error> {
    // Lean RecordPrograms.Ports requires three distinct reader registers.
    // Program::lift alone validates tag/present, not found.
    if ports.found >= R || ports.found == ports.tag || ports.found == ports.present {
        return Err(Error::Invalid(
            "framed iterator requires a distinct in-range found register".into(),
        ));
    }
    let reader = Cmd::Call(
        frame_program()?.lift::<R, S>([ports.tag, ports.present], [ports.source, payload])?,
    );
    Ok(iterate(ports, reader, callback))
}

#[cfg(test)]
mod tests {
    use std::collections::VecDeque;

    use super::*;
    use crate::bit_program::RunLimits;

    const PORTS: RecordPorts = RecordPorts {
        tag: 0,
        present: 1,
        found: 2,
        source: 0,
    };

    #[test]
    fn invalid_framed_reader_maps_refuse_instead_of_aliasing() {
        let invalid = [
            (
                RecordPorts {
                    present: 0,
                    ..PORTS
                },
                1,
            ),
            (PORTS, 0),
            (RecordPorts { tag: 3, ..PORTS }, 1),
            (PORTS, 3),
            (RecordPorts { found: 0, ..PORTS }, 1),
            (RecordPorts { found: 1, ..PORTS }, 1),
            (RecordPorts { found: 3, ..PORTS }, 1),
        ];
        for (ports, payload) in invalid {
            assert!(matches!(
                iterate_framed::<3, 3>(ports, payload, Cmd::Skip),
                Err(Error::Invalid(_))
            ));
        }
    }

    #[test]
    fn early_found_does_not_consume_the_next_record_tag() {
        // Two encoded records, [true] then [false], with final list terminator.
        // The first callback sets found; the second record remains unread.
        let input = [true, true, true, false, true, true, false, false, false];
        let command = iterate_framed::<3, 3>(
            PORTS,
            1,
            Cmd::Atom(Atom::Set {
                dst: 2,
                value: true,
            }),
        )
        .unwrap();
        let program = command.compiled(0, 0).unwrap();
        let mut state = program.initial(input);
        program.run(&mut state, RunLimits::default()).unwrap();
        assert_eq!(
            state.stacks[0],
            VecDeque::from([true, true, false, false, false])
        );
        assert_eq!(state.stacks[1], VecDeque::from([true]));
        assert!(state.regs[2]);
        assert!(!state.regs[0]);
        assert!(state.pc.is_none());
    }

    #[test]
    fn false_callback_consumes_all_records_and_preserves_payload_order() {
        let input = [true, true, true, false, true, true, false, false, false];
        let command = iterate_framed::<3, 3>(
            PORTS,
            1,
            Cmd::Atom(Atom::Set {
                dst: 2,
                value: false,
            }),
        )
        .unwrap();
        let program = command.compiled(0, 0).unwrap();
        let mut state = program.initial(input);
        program.run(&mut state, RunLimits::default()).unwrap();
        assert!(state.stacks[0].is_empty());
        assert_eq!(state.stacks[1], VecDeque::from([false, true]));
        assert!(!state.regs[2]);
        assert!(state.pc.is_none());
    }
}
