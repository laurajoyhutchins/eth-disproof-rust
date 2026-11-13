//! Strict native decoder for the exact JSON emitted by pinned Lean StructuredCalls.
//!
//! No Python-generated Rust AST is executed. The caller must supply the trusted
//! identity and SHA-256 from a *successful* Lean kernel-certificate receipt.
//! Checking an arbitrary self-reported hash is NOT proof that Lean certified it.
//! Accepted JSON becomes the same on-demand DeferredProgram used by Rust.
//!
//! The byte limit, Serde recursion limit and source dimensional caps are
//! intentional fail-closed restrictions, not semantic replacements.
use std::collections::HashMap;
use std::sync::Arc;

use serde::Deserialize;
use sha2::{Digest, Sha256};

use super::deferred::{PhysicalSource, check_injective_map, relocate_ports};
use super::{Atom, Block, DeferredProgram, Instr, Program};
use crate::Error;

const SOURCE_COMMIT: &str = "4eaee87548250b2682affda7d05d947c05554bae";
const MAX_BYTES: usize = 4 * 1024 * 1024;
const MAX_NODES: usize = 8192;
// The composed graph is resolved on demand; this is a numeric address bound,
// not a table allocation. Serialized bytes/nodes and finite leaf labels remain
// independently capped, so expanding the symbolic address range does not
// authorize materializing a billion-entry physical table.
const MAX_LABELS: usize = 1_000_000_000;
const MAX_CALL_LABELS: usize = 4096;

/// Expected source identity and digest, obtained from a separate,
/// successfully checked original-Lean certificate and its receipt.
/// This is an assertion by the caller, not a self-authenticating signature.
#[derive(Clone, Copy, Debug)]
pub struct SourceGraphBinding<'a> {
    pub id: &'a str,
    pub declaration: &'a str,
    pub source_blob: &'a str,
    pub graph_sha256: &'a str,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct SerializedGraph {
    kind: String,
    source_commit: String,
    source_blob: String,
    declaration: String,
    id: String,
    abi: Abi,
    // Exactly one root representation is admitted by the protocol kind.
    // A linked root is an ordinary physical Program, not an extra Call site.
    command: Option<Command>,
    program: Option<ProgramTree>,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct Abi {
    r: usize,
    s: usize,
    labels: usize,
    input: usize,
    output: usize,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct Callee {
    r: usize,
    s: usize,
    labels: usize,
    entry: usize,
    input: usize,
    output: usize,
    code: Vec<String>,
}

/// Nested linked programs have source-specific finite dimensions. Unlike a
/// flattened table, each node is decoded and executed on demand in Rust.
#[derive(Deserialize)]
#[serde(untagged)]
enum ProgramTree {
    Table(Callee),
    Linked(LinkedProgram),
}

#[derive(Deserialize)]
#[serde(tag = "kind", deny_unknown_fields)]
enum LinkedProgram {
    #[serde(rename = "composed")]
    Composed {
        r: usize,
        s: usize,
        input: usize,
        output: usize,
        command: Box<Command>,
    },
    #[serde(rename = "lift")]
    Lift {
        r: usize,
        s: usize,
        registers: Vec<usize>,
        stacks: Vec<usize>,
        source: Box<ProgramTree>,
    },
    #[serde(rename = "link")]
    Link {
        left: Box<ProgramTree>,
        right: Box<ProgramTree>,
    },
    #[serde(rename = "link_into")]
    LinkInto {
        r: usize,
        s: usize,
        left: Box<ProgramTree>,
        right: Box<ProgramTree>,
        left_registers: Vec<usize>,
        left_stacks: Vec<usize>,
        right_registers: Vec<usize>,
        right_stacks: Vec<usize>,
    },
}

#[derive(Deserialize)]
#[serde(tag = "kind", deny_unknown_fields)]
enum Command {
    #[serde(rename = "skip")]
    Skip,
    #[serde(rename = "atom")]
    Atom { opcode: String },
    #[serde(rename = "call")]
    Call { program: ProgramTree },
    #[serde(rename = "seq")]
    Seq {
        first: Box<Command>,
        second: Box<Command>,
    },
    #[serde(rename = "if")]
    If {
        test: usize,
        yes: Box<Command>,
        no: Box<Command>,
    },
    #[serde(rename = "while")]
    While { test: usize, body: Box<Command> },
    /// Exact fixed sequential repetition of one source command. This node
    /// never changes the source's physical step/label semantics.
    #[serde(rename = "repeat")]
    Repeat { count: usize, body: Box<Command> },
}

fn invalid(message: &str) -> Error {
    Error::Invalid(format!("original source graph: {message}"))
}

fn finite(raw: &str, bound: usize) -> Result<usize, Error> {
    if raw.is_empty()
        || (raw.len() > 1 && raw.starts_with('0'))
        || !raw.bytes().all(|byte| byte.is_ascii_digit())
    {
        return Err(invalid("noncanonical finite index"));
    }
    let n: usize = raw.parse().map_err(|_| invalid("finite index overflow"))?;
    if n >= bound {
        return Err(invalid("finite index out of bounds"));
    }
    Ok(n)
}

fn parse_operands(
    opcode: &str,
    atom: bool,
    r: usize,
    s: usize,
    labels: usize,
) -> Result<(&str, Vec<usize>), Error> {
    if opcode.len() >= 80 || !opcode.is_ascii() {
        return Err(invalid("noncanonical opcode"));
    }
    let mut fields = opcode.split(':');
    let name = fields.next().ok_or_else(|| invalid("empty opcode"))?;
    let signature = match name {
        "halt" if !atom => "",
        "goto" if !atom => "l",
        "set" => {
            if atom {
                "rb"
            } else {
                "rbl"
            }
        }
        "copy" | "not" => {
            if atom {
                "rr"
            } else {
                "rrl"
            }
        }
        "and" | "or" | "xor" => {
            if atom {
                "rrr"
            } else {
                "rrrl"
            }
        }
        "branch" if !atom => "rll",
        "push" => {
            if atom {
                "sr"
            } else {
                "srl"
            }
        }
        "peek" | "pop" => {
            if atom {
                "srr"
            } else {
                "srrl"
            }
        }
        _ => return Err(invalid("unknown source opcode")),
    };
    let texts = fields.collect::<Vec<_>>();
    if texts.len() != signature.len() {
        return Err(invalid("source opcode arity mismatch"));
    }
    let mut args = Vec::with_capacity(signature.len());
    for (raw, ty) in texts.into_iter().zip(signature.bytes()) {
        let bound = match ty {
            b'r' => r,
            b's' => s,
            b'l' => labels,
            b'b' => 2,
            _ => unreachable!("all operand signatures are constants"),
        };
        args.push(finite(raw, bound)?);
    }
    Ok((name, args))
}

fn parse_source_atom(opcode: &str, r: usize, s: usize) -> Result<Atom, Error> {
    let (op, vals) = parse_operands(opcode, true, r, s, 1)?;
    Ok(match (op, vals.as_slice()) {
        ("set", [dst, value]) => Atom::Set {
            dst: *dst,
            value: *value == 1,
        },
        ("copy", [dst, src]) => Atom::Copy {
            dst: *dst,
            src: *src,
        },
        ("not", [dst, src]) => Atom::Not {
            dst: *dst,
            src: *src,
        },
        ("and", [dst, left, right]) => Atom::And {
            dst: *dst,
            left: *left,
            right: *right,
        },
        ("or", [dst, left, right]) => Atom::Or {
            dst: *dst,
            left: *left,
            right: *right,
        },
        ("xor", [dst, left, right]) => Atom::Xor {
            dst: *dst,
            left: *left,
            right: *right,
        },
        ("push", [stack, src]) => Atom::Push {
            stack: *stack,
            src: *src,
        },
        ("peek", [stack, value, present]) => Atom::Peek {
            stack: *stack,
            value: *value,
            present: *present,
        },
        ("pop", [stack, value, present]) => Atom::Pop {
            stack: *stack,
            value: *value,
            present: *present,
        },
        _ => return Err(invalid("invalid atom operand pattern")),
    })
}

fn parse_atom<const R: usize, const S: usize>(opcode: &str) -> Result<Atom, Error> {
    parse_source_atom(opcode, R, S)
}

fn parse_physical_instr(opcode: &str, r: usize, s: usize, labels: usize) -> Result<Instr, Error> {
    let (op, v) = parse_operands(opcode, false, r, s, labels)?;
    Ok(match (op, v.as_slice()) {
        ("halt", []) => Instr::Halt,
        ("goto", [next]) => Instr::Goto { next: *next },
        ("set", [dst, value, next]) => Instr::Set {
            dst: *dst,
            value: *value == 1,
            next: *next,
        },
        ("copy", [dst, src, next]) => Instr::Copy {
            dst: *dst,
            src: *src,
            next: *next,
        },
        ("not", [dst, src, next]) => Instr::Not {
            dst: *dst,
            src: *src,
            next: *next,
        },
        ("and", [dst, left, right, next]) => Instr::And {
            dst: *dst,
            left: *left,
            right: *right,
            next: *next,
        },
        ("or", [dst, left, right, next]) => Instr::Or {
            dst: *dst,
            left: *left,
            right: *right,
            next: *next,
        },
        ("xor", [dst, left, right, next]) => Instr::Xor {
            dst: *dst,
            left: *left,
            right: *right,
            next: *next,
        },
        ("branch", [test, yes, no]) => Instr::Branch {
            test: *test,
            yes: *yes,
            no: *no,
        },
        ("push", [stack, src, next]) => Instr::Push {
            stack: *stack,
            src: *src,
            next: *next,
        },
        ("peek", [stack, value, present, next]) => Instr::Peek {
            stack: *stack,
            value: *value,
            present: *present,
            next: *next,
        },
        ("pop", [stack, value, present, next]) => Instr::Pop {
            stack: *stack,
            value: *value,
            present: *present,
            next: *next,
        },
        _ => return Err(invalid("invalid instruction operand pattern")),
    })
}

/// A dimension-erased *physical* program, distinct from a host-level SAT
/// operation. All nodes retain exact label spaces and instructions.
#[derive(Debug)]
struct NativeSource {
    r: usize,
    s: usize,
    labels: usize,
    entry: usize,
    input: usize,
    output: usize,
    body: NativeBody,
}

#[derive(Debug)]
enum NativeBody {
    Table(Vec<Instr>),
    Composed(Arc<NativeBlock>),
    Lift {
        source: Arc<NativeSource>,
        registers: Vec<usize>,
        stacks: Vec<usize>,
    },
    Link {
        left: Arc<NativeSource>,
        right: Arc<NativeSource>,
    },
}

impl PhysicalSource for NativeSource {
    fn instruction_at(&self, pc: usize) -> Result<Instr, Error> {
        if pc >= self.labels {
            return Err(invalid("linked callee physical address out of range"));
        }
        match &self.body {
            NativeBody::Table(code) => Ok(code[pc].clone()),
            NativeBody::Composed(_) if pc == 0 => Ok(Instr::Halt),
            NativeBody::Composed(block) => block.instruction_at(1, 0, pc),
            NativeBody::Lift {
                source,
                registers,
                stacks,
            } => relocate_ports(source.instruction_at(pc)?, registers, stacks),
            NativeBody::Link { left, right } if pc < left.labels => {
                let original = left.instruction_at(pc)?;
                if matches!(original, Instr::Halt) {
                    Ok(Instr::Goto {
                        next: left
                            .labels
                            .checked_add(right.entry)
                            .ok_or(Error::Overflow)?,
                    })
                } else {
                    Ok(original)
                }
            }
            NativeBody::Link { left, right } => {
                let original = right.instruction_at(pc - left.labels)?;
                if matches!(original, Instr::Halt) {
                    Ok(Instr::Halt)
                } else {
                    original.relocate(left.labels, 0)
                }
            }
        }
    }
}

/// Dynamic finite dimensions are checked once at decode. The exact same
/// Block site semantics are used for nested source-defined compiled callees:
/// label zero is halt; calls relocate halt to their continuation.
#[derive(Debug)]
struct NativeBlock {
    size: usize,
    kind: NativeBlockKind,
}

#[derive(Debug)]
enum NativeBlockKind {
    Skip,
    Atom(Atom),
    Call(Arc<NativeSource>),
    Seq(Arc<NativeBlock>, Arc<NativeBlock>),
    If {
        test: usize,
        yes: Arc<NativeBlock>,
        no: Arc<NativeBlock>,
    },
    While {
        test: usize,
        body: Arc<NativeBlock>,
    },
    Repeat {
        count: usize,
        body: Arc<NativeBlock>,
    },
}

impl NativeBlock {
    fn entry_at(&self, base: usize, exit: usize) -> Result<usize, Error> {
        match &self.kind {
            NativeBlockKind::Skip => Ok(exit),
            NativeBlockKind::Atom(_)
            | NativeBlockKind::If { .. }
            | NativeBlockKind::While { .. } => Ok(base),
            NativeBlockKind::Call(program) => {
                base.checked_add(program.entry).ok_or(Error::Overflow)
            }
            NativeBlockKind::Seq(first, second) => {
                let mid = base.checked_add(first.size).ok_or(Error::Overflow)?;
                first.entry_at(base, second.entry_at(mid, exit)?)
            }
            NativeBlockKind::Repeat { count, body } => {
                if *count == 0 || body.size == 0 {
                    return Ok(exit);
                }
                let next = if *count > 1 {
                    body.entry_at(base.checked_add(body.size).ok_or(Error::Overflow)?, exit)?
                } else {
                    exit
                };
                body.entry_at(base, next)
            }
        }
    }

    fn instruction_at(&self, base: usize, exit: usize, pc: usize) -> Result<Instr, Error> {
        let end = base.checked_add(self.size).ok_or(Error::Overflow)?;
        if pc < base || pc >= end {
            return Err(invalid(
                "nested structured source site outside physical block",
            ));
        }
        match &self.kind {
            NativeBlockKind::Skip => Err(invalid("empty nested source block has no instruction")),
            NativeBlockKind::Atom(atom) => Ok(atom.instr(exit)),
            NativeBlockKind::Call(program) => {
                program.instruction_at(pc - base)?.relocate(base, exit)
            }
            NativeBlockKind::Seq(first, second) => {
                let mid = base.checked_add(first.size).ok_or(Error::Overflow)?;
                if pc < mid {
                    first.instruction_at(base, second.entry_at(mid, exit)?, pc)
                } else {
                    second.instruction_at(mid, exit, pc)
                }
            }
            NativeBlockKind::If { test, yes, no } => {
                let first = base.checked_add(1).ok_or(Error::Overflow)?;
                let second = first.checked_add(yes.size).ok_or(Error::Overflow)?;
                if pc == base {
                    Ok(Instr::Branch {
                        test: *test,
                        yes: yes.entry_at(first, exit)?,
                        no: no.entry_at(second, exit)?,
                    })
                } else if pc < second {
                    yes.instruction_at(first, exit, pc)
                } else {
                    no.instruction_at(second, exit, pc)
                }
            }
            NativeBlockKind::While { test, body } => {
                let first = base.checked_add(1).ok_or(Error::Overflow)?;
                if pc == base {
                    Ok(Instr::Branch {
                        test: *test,
                        yes: body.entry_at(first, base)?,
                        no: exit,
                    })
                } else {
                    body.instruction_at(first, base, pc)
                }
            }
            NativeBlockKind::Repeat { count, body } => {
                // Zero-sized repetitions contain no source sites, so they
                // never reach an instruction lookup or divide by zero.
                if *count == 0 || body.size == 0 {
                    return Err(invalid("empty nested repeat has no physical sites"));
                }
                let iteration = (pc - base) / body.size;
                if iteration >= *count {
                    return Err(invalid("nested repeat site outside iteration count"));
                }
                let start = base
                    .checked_add(iteration.checked_mul(body.size).ok_or(Error::Overflow)?)
                    .ok_or(Error::Overflow)?;
                let next = if iteration + 1 < *count {
                    body.entry_at(start.checked_add(body.size).ok_or(Error::Overflow)?, exit)?
                } else {
                    exit
                };
                body.instruction_at(start, next, pc)
            }
        }
    }
}

fn lower_native_block(
    command: Command,
    r: usize,
    s: usize,
    remaining: &mut usize,
    depth: usize,
) -> Result<Arc<NativeBlock>, Error> {
    if *remaining == 0 || depth > 128 {
        return Err(Error::Capacity("nested composed source node budget".into()));
    }
    *remaining -= 1;
    let (size, kind) = match command {
        Command::Skip => (0, NativeBlockKind::Skip),
        Command::Atom { opcode } => (1, NativeBlockKind::Atom(parse_source_atom(&opcode, r, s)?)),
        Command::Call { program } => {
            let source = lower_linked_program(program, remaining, depth + 1)?;
            if (source.r, source.s) != (r, s) {
                return Err(invalid("nested source call has wrong physical dimensions"));
            }
            (source.labels, NativeBlockKind::Call(Arc::new(source)))
        }
        Command::Seq { first, second } => {
            let first = lower_native_block(*first, r, s, remaining, depth + 1)?;
            let second = lower_native_block(*second, r, s, remaining, depth + 1)?;
            let size = first.size.checked_add(second.size).ok_or(Error::Overflow)?;
            (size, NativeBlockKind::Seq(first, second))
        }
        Command::If { test, yes, no } => {
            if test >= r {
                return Err(invalid("nested source branch register out of range"));
            }
            let yes = lower_native_block(*yes, r, s, remaining, depth + 1)?;
            let no = lower_native_block(*no, r, s, remaining, depth + 1)?;
            let size = yes
                .size
                .checked_add(no.size)
                .and_then(|v| v.checked_add(1))
                .ok_or(Error::Overflow)?;
            (size, NativeBlockKind::If { test, yes, no })
        }
        Command::While { test, body } => {
            if test >= r {
                return Err(invalid("nested source while register out of range"));
            }
            let body = lower_native_block(*body, r, s, remaining, depth + 1)?;
            let size = body.size.checked_add(1).ok_or(Error::Overflow)?;
            (size, NativeBlockKind::While { test, body })
        }
        Command::Repeat { count, body } => {
            let body = lower_native_block(*body, r, s, remaining, depth + 1)?;
            let size = body.size.checked_mul(count).ok_or(Error::Overflow)?;
            (size, NativeBlockKind::Repeat { count, body })
        }
    };
    if size >= MAX_LABELS {
        return Err(Error::Capacity(
            "nested composed source exceeds physical site budget".into(),
        ));
    }
    Ok(Arc::new(NativeBlock { size, kind }))
}

fn source_dimensions(r: usize, s: usize) -> Result<(), Error> {
    if r == 0 || r > 256 || s == 0 || s > 4096 {
        return Err(invalid(
            "linked source port dimensions outside supported Fin",
        ));
    }
    Ok(())
}

fn lift_source(
    source: NativeSource,
    r: usize,
    s: usize,
    registers: Vec<usize>,
    stacks: Vec<usize>,
) -> Result<NativeSource, Error> {
    source_dimensions(r, s)?;
    if registers.len() != source.r || stacks.len() != source.s {
        return Err(invalid("linked source embedding domain has wrong size"));
    }
    check_injective_map(&registers, r, "register")?;
    check_injective_map(&stacks, s, "stack")?;
    let input = stacks[source.input];
    let output = stacks[source.output];
    Ok(NativeSource {
        r,
        s,
        labels: source.labels,
        entry: source.entry,
        input,
        output,
        body: NativeBody::Lift {
            source: Arc::new(source),
            registers,
            stacks,
        },
    })
}

fn link_sources(left: NativeSource, right: NativeSource) -> Result<NativeSource, Error> {
    if (left.r, left.s) != (right.r, right.s) {
        return Err(invalid(
            "linked program children have different target dimensions",
        ));
    }
    let labels = left
        .labels
        .checked_add(right.labels)
        .ok_or(Error::Overflow)?;
    if labels > MAX_LABELS {
        return Err(Error::Capacity(
            "linked source exceeds physical label budget".into(),
        ));
    }
    Ok(NativeSource {
        r: left.r,
        s: left.s,
        labels,
        entry: left.entry,
        input: left.input,
        output: right.output,
        body: NativeBody::Link {
            left: Arc::new(left),
            right: Arc::new(right),
        },
    })
}

fn lower_linked_program(
    tree: ProgramTree,
    remaining: &mut usize,
    depth: usize,
) -> Result<NativeSource, Error> {
    if *remaining == 0 || depth > 128 {
        return Err(Error::Capacity(
            "linked source recursion or node budget".into(),
        ));
    }
    *remaining -= 1;
    match tree {
        ProgramTree::Table(p) => {
            source_dimensions(p.r, p.s)?;
            if p.labels == 0
                || p.labels > MAX_CALL_LABELS
                || p.entry >= p.labels
                || p.input >= p.s
                || p.output >= p.s
                || p.code.len() != p.labels
            {
                return Err(invalid("invalid finite linked source table ABI"));
            }
            let code = p
                .code
                .iter()
                .map(|op| parse_physical_instr(op, p.r, p.s, p.labels))
                .collect::<Result<Vec<_>, _>>()?;
            Ok(NativeSource {
                r: p.r,
                s: p.s,
                labels: p.labels,
                entry: p.entry,
                input: p.input,
                output: p.output,
                body: NativeBody::Table(code),
            })
        }
        ProgramTree::Linked(LinkedProgram::Composed {
            r,
            s,
            input,
            output,
            command,
        }) => {
            source_dimensions(r, s)?;
            if input >= s || output >= s {
                return Err(invalid(
                    "nested composed source ports outside source dimensions",
                ));
            }
            let block = lower_native_block(*command, r, s, remaining, depth + 1)?;
            let labels = block.size.checked_add(1).ok_or(Error::Overflow)?;
            if labels > MAX_LABELS {
                return Err(Error::Capacity(
                    "nested composed source labels out of range".into(),
                ));
            }
            let entry = block.entry_at(1, 0)?;
            if entry >= labels {
                return Err(invalid(
                    "nested composed source entry outside physical labels",
                ));
            }
            Ok(NativeSource {
                r,
                s,
                labels,
                entry,
                input,
                output,
                body: NativeBody::Composed(block),
            })
        }
        ProgramTree::Linked(LinkedProgram::Lift {
            r,
            s,
            registers,
            stacks,
            source,
        }) => {
            let child = lower_linked_program(*source, remaining, depth + 1)?;
            lift_source(child, r, s, registers, stacks)
        }
        ProgramTree::Linked(LinkedProgram::Link { left, right }) => {
            let left = lower_linked_program(*left, remaining, depth + 1)?;
            let right = lower_linked_program(*right, remaining, depth + 1)?;
            link_sources(left, right)
        }
        ProgramTree::Linked(LinkedProgram::LinkInto {
            r,
            s,
            left,
            right,
            left_registers,
            left_stacks,
            right_registers,
            right_stacks,
        }) => {
            let left = lower_linked_program(*left, remaining, depth + 1)?;
            let right = lower_linked_program(*right, remaining, depth + 1)?;
            let left = lift_source(left, r, s, left_registers, left_stacks)?;
            let right = lift_source(right, r, s, right_registers, right_stacks)?;
            link_sources(left, right)
        }
    }
}

type CalleeKey = (usize, usize, usize, usize, Vec<String>);

fn lower<const R: usize, const S: usize>(
    command: Command,
    remaining: &mut usize,
    callees: &mut HashMap<CalleeKey, Arc<DeferredProgram<R, S>>>,
) -> Result<Arc<Block<R, S>>, Error> {
    if *remaining == 0 {
        return Err(Error::Capacity("source graph node budget".into()));
    }
    *remaining -= 1;
    match command {
        Command::Skip => Ok(Block::skip()),
        Command::Atom { opcode } => Block::atom(parse_atom::<R, S>(&opcode)?),
        Command::Call {
            program: ProgramTree::Table(p),
        } => {
            if p.r != R
                || p.s != S
                || p.labels == 0
                || p.labels > MAX_CALL_LABELS
                || p.code.len() != p.labels
                || p.entry >= p.labels
                || p.input >= S
                || p.output >= S
            {
                return Err(invalid("invalid source callee dimensions"));
            }
            let key = (p.labels, p.input, p.output, p.entry, p.code.clone());
            if let Some(existing) = callees.get(&key) {
                return Ok(Block::call(Arc::clone(existing)));
            }
            let table = p
                .code
                .iter()
                .map(|op| parse_physical_instr(op, R, S, p.labels))
                .collect::<Result<Vec<_>, _>>()?;
            let program =
                DeferredProgram::table(Program::<R, S>::new(p.input, p.output, p.entry, table)?);
            callees.insert(key, Arc::clone(&program));
            Ok(Block::call(program))
        }
        Command::Call { program } => {
            let source = lower_linked_program(program, remaining, 0)?;
            if (source.r, source.s) != (R, S) {
                return Err(invalid(
                    "linked callee differs from enclosing source port dimensions",
                ));
            }
            let program = DeferredProgram::<R, S>::source_program(
                source.input,
                source.output,
                source.entry,
                source.labels,
                Arc::new(source),
            )?;
            Ok(Block::call(program))
        }
        Command::Seq { first, second } => Block::seq(
            lower::<R, S>(*first, remaining, callees)?,
            lower::<R, S>(*second, remaining, callees)?,
        ),
        Command::If { test, yes, no } => Block::ite(
            test,
            lower::<R, S>(*yes, remaining, callees)?,
            lower::<R, S>(*no, remaining, callees)?,
        ),
        Command::While { test, body } => {
            Block::while_(test, lower::<R, S>(*body, remaining, callees)?)
        }
        Command::Repeat { count, body } => {
            Block::repeat(count, lower::<R, S>(*body, remaining, callees)?)
        }
    }
}

impl<const R: usize, const S: usize> DeferredProgram<R, S> {
    /// Interpret the exact serialized bytes bound by an external Lean-certificate receipt.
    ///
    /// The Rust parser is independent of the Python graph-to-Rust generator.
    /// A matching hash is a *binding*, not a proof by itself; users must obtain
    /// the expectation from a checked Lean certificate, never from untrusted JSON.
    pub fn from_original_source_json(
        bytes: &[u8],
        expected: SourceGraphBinding<'_>,
    ) -> Result<Arc<Self>, Error> {
        if bytes.is_empty()
            || bytes.len() > MAX_BYTES
            || bytes.last() != Some(&b'\n')
            || bytes.iter().filter(|&&b| b == b'\n').count() != 1
            || bytes.contains(&b'\r')
            || !bytes.is_ascii()
        {
            return Err(invalid("source graph must be one bounded ASCII JSON line"));
        }
        if expected.graph_sha256.len() != 64
            || !expected
                .graph_sha256
                .bytes()
                .all(|b| b.is_ascii_hexdigit() && !b.is_ascii_uppercase())
        {
            return Err(invalid("certificate digest must be lowercase hex SHA-256"));
        }
        let computed = format!("{:x}", Sha256::digest(bytes));
        if computed != expected.graph_sha256 {
            return Err(invalid(
                "graph SHA-256 differs from Lean certificate binding",
            ));
        }
        let source: SerializedGraph = serde_json::from_slice(bytes)
            .map_err(|e| Error::Invalid(format!("source graph JSON schema: {e}")))?;
        if !matches!(
            source.kind.as_str(),
            "original-structured-source-v1" | "original-linked-source-v1"
        ) || source.source_commit != SOURCE_COMMIT
            || source.id != expected.id
            || source.declaration != expected.declaration
            || source.source_blob != expected.source_blob
            || source.source_blob.len() != 40
            || !source
                .source_blob
                .bytes()
                .all(|b| b.is_ascii_hexdigit() && !b.is_ascii_uppercase())
        {
            return Err(invalid(
                "source declaration/blob does not match trusted binding",
            ));
        }
        let abi = source.abi;
        if R == 0
            || R > 256
            || S == 0
            || S > 4096
            || abi.r != R
            || abi.s != S
            || abi.labels == 0
            || abi.labels > MAX_LABELS
            || abi.input >= S
            || abi.output >= S
        {
            return Err(invalid("source machine dimensions outside supported ABI"));
        }
        let mut budget = MAX_NODES;
        let program = match (source.kind.as_str(), source.command, source.program) {
            ("original-structured-source-v1", Some(command), None) => {
                let mut callees = HashMap::new();
                let block = lower::<R, S>(command, &mut budget, &mut callees)?;
                DeferredProgram::composed(abi.input, abi.output, block)?
            }
            ("original-linked-source-v1", None, Some(tree)) => {
                let linked = lower_linked_program(tree, &mut budget, 0)?;
                if (
                    linked.r,
                    linked.s,
                    linked.labels,
                    linked.input,
                    linked.output,
                ) != (R, S, abi.labels, abi.input, abi.output)
                {
                    return Err(invalid("linked root differs from elaborated source ABI"));
                }
                DeferredProgram::<R, S>::source_program(
                    linked.input,
                    linked.output,
                    linked.entry,
                    linked.labels,
                    Arc::new(linked),
                )?
            }
            _ => return Err(invalid("source graph has ambiguous or absent root")),
        };
        if program.labels() != abi.labels {
            return Err(invalid(
                "source graph site count differs from original Lean ABI",
            ));
        }
        Ok(program)
    }
}

#[cfg(test)]
mod native_interning_tests {
    use super::*;

    fn callee(output: usize) -> Command {
        Command::Call {
            program: ProgramTree::Table(Callee {
                r: 2,
                s: 2,
                labels: 2,
                entry: 1,
                input: 0,
                output,
                code: vec!["halt".into(), "goto:0".into()],
            }),
        }
    }

    #[test]
    fn identical_callee_table_is_shared_and_distinct_abi_is_not() {
        let repeated = Command::Seq {
            first: Box::new(callee(1)),
            second: Box::new(Command::Seq {
                first: Box::new(callee(1)),
                second: Box::new(callee(0)),
            }),
        };
        let mut remaining = MAX_NODES;
        let mut cache = HashMap::new();
        let block = lower::<2, 2>(repeated, &mut remaining, &mut cache).unwrap();
        assert_eq!(cache.len(), 2);
        assert_eq!(block.size(), 6);
        assert_eq!(remaining, MAX_NODES - 5);
    }
}
