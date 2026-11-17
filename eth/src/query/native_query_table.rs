//! Import a *compiled*, immutable native query instruction table produced by
//! the exact pinned Lean `QueryStreamProgram.program`.
//!
//! This deliberately avoids translating the enormous transitive source DAG
//! into ad-hoc Rust arithmetic.  Every imported instruction is executed by
//! the same independently tested `bit_program::Program<40, 896>` evaluator.
//! No stub, semantic SAT oracle, dynamic callback or success-on-refusal path.
//!
//! Table production requires a **real imported Lean source environment**.
//! A Rust parse pass proves only that the bytes form a valid finite machine;
//! it is not evidence that they came from Lean. See the sidecar exporter.

use std::io::BufRead;

use crate::Error;
use crate::bit_program::{Instr, Program};

pub const SOURCE_COMMIT: &str = "4eaee87548250b2682affda7d05d947c05554bae";
pub const QUERY_SOURCE_BLOB: &str = "c2fb29983bb33229d5cf60729cd3d1e37b9b00ca";

#[derive(Clone, Copy, Debug)]
pub struct ImportLimits {
    pub max_labels: usize,
    pub max_bytes: usize,
}

impl Default for ImportLimits {
    fn default() -> Self {
        Self {
            max_labels: 2_000_000,
            max_bytes: 256_000_000,
        }
    }
}

fn invalid(reason: &str) -> Error {
    Error::Invalid(format!("native query table: {reason}"))
}

fn number(value: &str) -> Result<usize, Error> {
    if value.is_empty()
        || !value.bytes().all(|b| b.is_ascii_digit())
        || (value.len() > 1 && value.starts_with('0'))
    {
        return Err(invalid("noncanonical decimal integer"));
    }
    value.parse().map_err(|_| invalid("decimal overflow"))
}

fn bit(value: &str) -> Result<bool, Error> {
    match value {
        "0" => Ok(false),
        "1" => Ok(true),
        _ => Err(invalid("Boolean field must be 0 or 1")),
    }
}

fn instr(value: &str) -> Result<Instr, Error> {
    let words: Vec<&str> = value.split(':').collect();
    let get = |index: usize| -> Result<usize, Error> {
        number(
            words
                .get(index)
                .copied()
                .ok_or_else(|| invalid("missing opcode argument"))?,
        )
    };
    let opcode = words.first().copied().unwrap_or_default();
    let arity = match opcode {
        "halt" => 1,
        "goto" => 2,
        "set" | "copy" | "not" | "push" => 4,
        "and" | "or" | "xor" | "peek" | "pop" => 5,
        "branch" => 4,
        _ => return Err(invalid("unknown source instruction")),
    };
    if words.len() != arity {
        return Err(invalid("wrong number of opcode arguments"));
    }
    Ok(match opcode {
        "halt" => Instr::Halt,
        "goto" => Instr::Goto { next: get(1)? },
        "set" => Instr::Set {
            dst: get(1)?,
            value: bit(words[2])?,
            next: get(3)?,
        },
        "copy" => Instr::Copy {
            dst: get(1)?,
            src: get(2)?,
            next: get(3)?,
        },
        "not" => Instr::Not {
            dst: get(1)?,
            src: get(2)?,
            next: get(3)?,
        },
        "and" => Instr::And {
            dst: get(1)?,
            left: get(2)?,
            right: get(3)?,
            next: get(4)?,
        },
        "or" => Instr::Or {
            dst: get(1)?,
            left: get(2)?,
            right: get(3)?,
            next: get(4)?,
        },
        "xor" => Instr::Xor {
            dst: get(1)?,
            left: get(2)?,
            right: get(3)?,
            next: get(4)?,
        },
        "branch" => Instr::Branch {
            test: get(1)?,
            yes: get(2)?,
            no: get(3)?,
        },
        "push" => Instr::Push {
            stack: get(1)?,
            src: get(2)?,
            next: get(3)?,
        },
        "peek" => Instr::Peek {
            stack: get(1)?,
            value: get(2)?,
            present: get(3)?,
            next: get(4)?,
        },
        "pop" => Instr::Pop {
            stack: get(1)?,
            value: get(2)?,
            present: get(3)?,
            next: get(4)?,
        },
        _ => unreachable!("checked opcode above"),
    })
}

/// Import the Lean capture protocol with a strict query/source pin, ordered
/// complete label range and terminal record.  Do not feed arbitrary exported
/// diagnostic callbacks here: only the source-defined program is admissible.
///
/// The caller must separately check the exported artifact SHA-256 and original
/// Lean import evidence; a label table is not proof of source provenance.
pub fn import_query_table(
    input: impl BufRead,
    limits: ImportLimits,
) -> Result<Program<40, 896>, Error> {
    if limits.max_labels == 0 || limits.max_bytes == 0 {
        return Err(Error::Capacity(
            "zero native query table import budget".into(),
        ));
    }
    // Bound individual `read_line` allocations before parsing, including
    // a maliciously huge single record or content after the terminator.
    let mut input = input.take(limits.max_bytes.saturating_add(1) as u64);
    let mut total_bytes = 0usize;
    let mut line = String::new();
    let mut read = |name: &str| -> Result<String, Error> {
        line.clear();
        let n = input
            .read_line(&mut line)
            .map_err(|e| invalid(&format!("{name}: {e}")))?;
        total_bytes = total_bytes
            .checked_add(n)
            .ok_or_else(|| Error::Capacity("native query table byte overflow".into()))?;
        if total_bytes > limits.max_bytes {
            return Err(Error::Capacity(
                "native query table exceeds byte budget".into(),
            ));
        }
        if n == 0 || !line.ends_with('\n') || line.ends_with("\r\n") {
            return Err(invalid("missing or noncanonical complete line"));
        }
        line.pop();
        Ok(line.clone())
    };

    let provenance = read("PIN")?;
    if provenance != format!("PIN|query|{SOURCE_COMMIT}|{QUERY_SOURCE_BLOB}") {
        return Err(invalid("source/commit identity mismatch"));
    }
    let header = read("PROGRAM")?;
    let header: Vec<_> = header.split('|').collect();
    if header.len() != 8 || header[0] != "PROGRAM" || header[1] != "query" {
        return Err(invalid("malformed query program header"));
    }
    if number(header[2])? != 40 || number(header[3])? != 896 {
        return Err(invalid("machine dimensions must be 40 x 896"));
    }
    let labels = number(header[4])?;
    if labels == 0 || labels > limits.max_labels {
        return Err(Error::Capacity("native query table label budget".into()));
    }
    let entry = number(header[5])?;
    let source = number(header[6])?;
    let target = number(header[7])?;
    if source != 330 || target != 323 {
        return Err(invalid("unexpected query input/output ports"));
    }

    let mut code = Vec::with_capacity(labels);
    for i in 0..labels {
        let text = read("CODE")?;
        let parts: Vec<_> = text.split('|').collect();
        if parts.len() != 4 || parts[0] != "CODE" || parts[1] != "query" {
            return Err(invalid("malformed instruction record"));
        }
        if number(parts[2])? != i {
            return Err(invalid(
                "out-of-order, duplicate, or missing instruction label",
            ));
        }
        code.push(instr(parts[3])?);
    }
    if read("END")? != format!("END|query|{labels}") {
        return Err(invalid("missing or incorrect table terminator"));
    }
    // Even a trailing blank line is an unaccounted record.
    line.clear();
    if input
        .read_line(&mut line)
        .map_err(|e| invalid(&format!("trailing data: {e}")))?
        != 0
    {
        return Err(invalid("trailing content after terminator"));
    }
    Program::new(source, target, entry, code)
}
