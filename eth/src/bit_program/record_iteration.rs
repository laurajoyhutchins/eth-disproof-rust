//! Original `RecordPrograms.iterate` structured finite-machine control flow.
//!
//! This preserves the source's sequence, conditional and loop nodes, not a
//! host-side record traversal. The initial pop precedes the loop; when the
//! callback sets `found`, the advance operation clears `tag` without
//! consuming an additional input record.

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
