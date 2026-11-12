//! Strict native decoder for the exact JSON emitted by pinned Lean StructuredCalls.
//!
//! No Python-generated Rust AST is executed. The caller must supply the trusted
//! identity and SHA-256 from a *successful* Lean kernel-certificate receipt.
//! Checking an arbitrary self-reported hash is NOT proof that Lean certified it.
//! Accepted JSON becomes the same on-demand DeferredProgram used by Rust.
//!
//! The byte limit, Serde recursion limit and source dimensional caps are
//! intentional fail-closed restrictions, not semantic replacements.
use std::sync::Arc;

use serde::Deserialize;
use sha2::{Digest, Sha256};

use super::{Atom, Block, DeferredProgram, Instr, Program};
use crate::Error;

const SOURCE_COMMIT: &str = "4eaee87548250b2682affda7d05d947c05554bae";
const MAX_BYTES: usize = 4 * 1024 * 1024;
const MAX_NODES: usize = 8192;
const MAX_LABELS: usize = 50_000;
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
    command: Command,
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

#[derive(Deserialize)]
#[serde(tag = "kind", deny_unknown_fields)]
enum Command {
    #[serde(rename = "skip")]
    Skip,
    #[serde(rename = "atom")]
    Atom { opcode: String },
    #[serde(rename = "call")]
    Call { program: Callee },
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

fn parse_operands<'a>(
    opcode: &'a str,
    atom: bool,
    r: usize,
    s: usize,
    labels: usize,
) -> Result<(&'a str, Vec<usize>), Error> {
    if opcode.len() >= 80 || !opcode.is_ascii() {
        return Err(invalid("noncanonical opcode"));
    }
    let mut fields = opcode.split(':');
    let name = fields.next().ok_or_else(|| invalid("empty opcode"))?;
    let signature = match name {
        "halt" if !atom => "",
        "goto" if !atom => "l",
        "set" => if atom { "rb" } else { "rbl" },
        "copy" | "not" => if atom { "rr" } else { "rrl" },
        "and" | "or" | "xor" => if atom { "rrr" } else { "rrrl" },
        "branch" if !atom => "rll",
        "push" => if atom { "sr" } else { "srl" },
        "peek" | "pop" => if atom { "srr" } else { "srrl" },
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

fn parse_atom<const R: usize, const S: usize>(opcode: &str) -> Result<Atom, Error> {
    let (op, vals) = parse_operands(opcode, true, R, S, 1)?;
    Ok(match (op, vals.as_slice()) {
        ("set", [dst, value]) => Atom::Set { dst: *dst, value: *value == 1 },
        ("copy", [dst, src]) => Atom::Copy { dst: *dst, src: *src },
        ("not", [dst, src]) => Atom::Not { dst: *dst, src: *src },
        ("and", [dst, left, right]) => Atom::And { dst: *dst, left: *left, right: *right },
        ("or", [dst, left, right]) => Atom::Or { dst: *dst, left: *left, right: *right },
        ("xor", [dst, left, right]) => Atom::Xor { dst: *dst, left: *left, right: *right },
        ("push", [stack, src]) => Atom::Push { stack: *stack, src: *src },
        ("peek", [stack, value, present]) => Atom::Peek {
            stack: *stack, value: *value, present: *present,
        },
        ("pop", [stack, value, present]) => Atom::Pop {
            stack: *stack, value: *value, present: *present,
        },
        _ => return Err(invalid("invalid atom operand pattern")),
    })
}

fn parse_instr<const R: usize, const S: usize>(
    opcode: &str,
    labels: usize,
) -> Result<Instr, Error> {
    let (op, v) = parse_operands(opcode, false, R, S, labels)?;
    Ok(match (op, v.as_slice()) {
        ("halt", []) => Instr::Halt,
        ("goto", [next]) => Instr::Goto { next: *next },
        ("set", [dst, value, next]) => Instr::Set {
            dst: *dst, value: *value == 1, next: *next,
        },
        ("copy", [dst, src, next]) => Instr::Copy { dst: *dst, src: *src, next: *next },
        ("not", [dst, src, next]) => Instr::Not { dst: *dst, src: *src, next: *next },
        ("and", [dst, left, right, next]) => Instr::And {
            dst: *dst, left: *left, right: *right, next: *next,
        },
        ("or", [dst, left, right, next]) => Instr::Or {
            dst: *dst, left: *left, right: *right, next: *next,
        },
        ("xor", [dst, left, right, next]) => Instr::Xor {
            dst: *dst, left: *left, right: *right, next: *next,
        },
        ("branch", [test, yes, no]) => Instr::Branch { test: *test, yes: *yes, no: *no },
        ("push", [stack, src, next]) => Instr::Push {
            stack: *stack, src: *src, next: *next,
        },
        ("peek", [stack, value, present, next]) => Instr::Peek {
            stack: *stack, value: *value, present: *present, next: *next,
        },
        ("pop", [stack, value, present, next]) => Instr::Pop {
            stack: *stack, value: *value, present: *present, next: *next,
        },
        _ => return Err(invalid("invalid instruction operand pattern")),
    })
}

fn lower<const R: usize, const S: usize>(
    command: Command,
    remaining: &mut usize,
) -> Result<Arc<Block<R, S>>, Error> {
    if *remaining == 0 {
        return Err(Error::Capacity("source graph node budget".into()));
    }
    *remaining -= 1;
    match command {
        Command::Skip => Ok(Block::skip()),
        Command::Atom { opcode } => Block::atom(parse_atom::<R, S>(&opcode)?),
        Command::Call { program: p } => {
            if p.r != R || p.s != S || p.labels == 0 || p.labels > MAX_CALL_LABELS
                || p.code.len() != p.labels || p.entry >= p.labels
            {
                return Err(invalid("invalid source callee dimensions"));
            }
            let table = p.code.iter()
                .map(|op| parse_instr::<R, S>(op, p.labels))
                .collect::<Result<Vec<_>, _>>()?;
            Ok(Block::call(DeferredProgram::table(
                Program::<R, S>::new(p.input, p.output, p.entry, table)?
            )))
        }
        Command::Seq { first, second } =>
            Block::seq(lower::<R, S>(*first, remaining)?, lower::<R, S>(*second, remaining)?),
        Command::If { test, yes, no } =>
            Block::ite(test, lower::<R, S>(*yes, remaining)?, lower::<R, S>(*no, remaining)?),
        Command::While { test, body } =>
            Block::while_(test, lower::<R, S>(*body, remaining)?),
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
        if bytes.is_empty() || bytes.len() > MAX_BYTES || bytes.last() != Some(&b'\n')
            || bytes.iter().filter(|&&b| b == b'\n').count() != 1
            || bytes.contains(&b'\r') || !bytes.is_ascii()
        {
            return Err(invalid("source graph must be one bounded ASCII JSON line"));
        }
        if expected.graph_sha256.len() != 64 ||
            !expected.graph_sha256.bytes().all(|b| b.is_ascii_hexdigit() && !b.is_ascii_uppercase())
        {
            return Err(invalid("certificate digest must be lowercase hex SHA-256"));
        }
        let computed = format!("{:x}", Sha256::digest(bytes));
        if computed != expected.graph_sha256 {
            return Err(invalid("graph SHA-256 differs from Lean certificate binding"));
        }
        let source: SerializedGraph = serde_json::from_slice(bytes)
            .map_err(|e| Error::Invalid(format!("source graph JSON schema: {e}")))?;
        if source.kind != "original-structured-source-v1"
            || source.source_commit != SOURCE_COMMIT
            || source.id != expected.id
            || source.declaration != expected.declaration
            || source.source_blob != expected.source_blob
            || source.source_blob.len() != 40
            || !source.source_blob.bytes().all(|b| b.is_ascii_hexdigit() && !b.is_ascii_uppercase())
        {
            return Err(invalid("source declaration/blob does not match trusted binding"));
        }
        let abi = source.abi;
        if R == 0 || R > 256 || S == 0 || S > 4096
            || abi.r != R || abi.s != S || abi.labels == 0 || abi.labels > MAX_LABELS
            || abi.input >= S || abi.output >= S
        {
            return Err(invalid("source machine dimensions outside supported ABI"));
        }
        let mut budget = MAX_NODES;
        let block = lower::<R, S>(source.command, &mut budget)?;
        let program = DeferredProgram::composed(abi.input, abi.output, block)?;
        if program.labels() != abi.labels {
            return Err(invalid("source graph site count differs from original Lean ABI"));
        }
        Ok(program)
    }
}
