//! Ahead-of-time Rust source emission from the same receipt-bound physical graph.
//!
//! A generated binary resolves source labels by specialized Rust functions.
//! It never embeds/reparses the JSON IR and never materializes symbolic repeats.
//! The shared BitProgram runner remains authoritative for state transitions.
use super::*;
use std::fmt::Write;

const MAX_RUST_SOURCE_BYTES: usize = 16 * 1024 * 1024;

#[derive(Default)]
struct Emitter {
    next: usize,
    functions: Vec<String>,
}

impl Emitter {
    fn name(&mut self, prefix: &str) -> String {
        let id = self.next;
        self.next += 1;
        format!("{prefix}_{id}")
    }

    /// The emitted source node returns one relocated physical instruction.
    /// A lift remaps data ports; a link relocates right-side label addresses.
    fn source(&mut self, source: &NativeSource) -> String {
        let name = self.name("source");
        let body = match &source.body {
            NativeBody::Table(code) => {
                let mut body = String::from("match pc {\n");
                for (pc, instruction) in code.iter().enumerate() {
                    writeln!(&mut body, "    {pc} => Ok(Instr::{instruction:?}),").unwrap();
                }
                body.push_str("    _ => Err(Error::Invalid(\"source table label\".into())),\n}");
                body
            }
            NativeBody::Composed(block) => {
                let (_, instruction) = self.block(block);
                format!("if pc == 0 {{ Ok(Instr::Halt) }} else {{ {instruction}(1, 0, pc) }}")
            }
            NativeBody::Lift {
                source,
                registers,
                stacks,
            } => {
                let child = self.source(source);
                format!("relocate_ports({child}(pc)?, &{registers:?}, &{stacks:?})")
            }
            NativeBody::Link { left, right } => {
                let l = self.source(left);
                let r = self.source(right);
                let left_labels = left.labels;
                let right_entry = right.entry;
                format!(
                    "if pc < {left_labels} {{\n\
                         let instruction = {l}(pc)?;\n\
                         if matches!(instruction, Instr::Halt) {{\n\
                             Ok(Instr::Goto {{ next: {left_labels} + {right_entry} }})\n\
                         }} else {{ Ok(instruction) }}\n\
                     }} else {{\n\
                         let instruction = {r}(pc - {left_labels})?;\n\
                         if matches!(instruction, Instr::Halt) {{ Ok(Instr::Halt) }}\n\
                         else {{ instruction.relocate({left_labels}, 0) }}\n\
                     }}"
                )
            }
        };
        self.functions.push(format!(
            "fn {name}(pc: usize) -> Result<Instr, Error> {{\n\
                 if pc >= {} {{ return Err(Error::Invalid(\"source label out of range\".into())); }}\n\
                 {body}\n\
             }}\n",
            source.labels
        ));
        name
    }

    /// Emit both entry and instruction functions for one structured block.
    /// Calls/branch targets depend on their physical placement, so base and
    /// continuation remain explicit parameters rather than host call frames.
    fn block(&mut self, node: &NativeBlock) -> (String, String) {
        let entry = self.name("entry");
        let instruction = self.name("block");
        let (entry_body, instruction_body) = match &node.kind {
            NativeBlockKind::Skip => (
                "Ok(exit)".to_string(),
                "Err(Error::Invalid(\"empty source block\".into()))".to_string(),
            ),
            NativeBlockKind::Atom(atom) => (
                "Ok(base)".to_string(),
                format!("Ok({})", atom_instruction(atom)),
            ),
            NativeBlockKind::Call(source) => {
                let child = self.source(source);
                (
                    format!("base.checked_add({}).ok_or(Error::Overflow)", source.entry),
                    format!("{child}(pc - base)?.relocate(base, exit)"),
                )
            }
            NativeBlockKind::Seq(first, second) => {
                let (a_entry, a_instruction) = self.block(first);
                let (b_entry, b_instruction) = self.block(second);
                let offset = first.size;
                (
                    format!(
                        "let mid = base.checked_add({offset}).ok_or(Error::Overflow)?;\n\
                         {a_entry}(base, {b_entry}(mid, exit)?)"
                    ),
                    format!(
                        "let mid = base.checked_add({offset}).ok_or(Error::Overflow)?;\n\
                         if pc < mid {{ {a_instruction}(base, {b_entry}(mid, exit)?, pc) }}\n\
                         else {{ {b_instruction}(mid, exit, pc) }}"
                    ),
                )
            }
            NativeBlockKind::If { test, yes, no } => {
                let (yes_entry, yes_instruction) = self.block(yes);
                let (no_entry, no_instruction) = self.block(no);
                let second_offset = yes.size;
                (
                    "Ok(base)".to_string(),
                    format!(
                        "let first = base.checked_add(1).ok_or(Error::Overflow)?;\n\
                         let second = first.checked_add({second_offset}).ok_or(Error::Overflow)?;\n\
                         if pc == base {{\n\
                             Ok(Instr::Branch {{ test: {test}, yes: {yes_entry}(first, exit)?, no: {no_entry}(second, exit)? }})\n\
                         }} else if pc < second {{ {yes_instruction}(first, exit, pc) }}\n\
                         else {{ {no_instruction}(second, exit, pc) }}"
                    ),
                )
            }
            NativeBlockKind::While { test, body } => {
                let (child_entry, child_instruction) = self.block(body);
                (
                    "Ok(base)".to_string(),
                    format!(
                        "let first = base.checked_add(1).ok_or(Error::Overflow)?;\n\
                         if pc == base {{\n\
                             Ok(Instr::Branch {{ test: {test}, yes: {child_entry}(first, base)?, no: exit }})\n\
                         }} else {{ {child_instruction}(first, base, pc) }}"
                    ),
                )
            }
            NativeBlockKind::Repeat { count, body } if *count == 0 || body.size == 0 => (
                "Ok(exit)".to_string(),
                "Err(Error::Invalid(\"empty repeat has no physical sites\".into()))".to_string(),
            ),
            NativeBlockKind::Repeat { count, body } => {
                let (child_entry, child_instruction) = self.block(body);
                let size = body.size;
                (
                    format!(
                        "let following = if {count} > 1 {{\n\
                             {child_entry}(base.checked_add({size}).ok_or(Error::Overflow)?, exit)?\n\
                         }} else {{ exit }};\n\
                         {child_entry}(base, following)"
                    ),
                    format!(
                        "let iteration = (pc - base) / {size};\n\
                         if iteration >= {count} {{ return Err(Error::Invalid(\"repeat iteration out of range\".into())); }}\n\
                         let offset = iteration.checked_mul({size}).ok_or(Error::Overflow)?;\n\
                         let start = base.checked_add(offset).ok_or(Error::Overflow)?;\n\
                         let following = if iteration + 1 < {count} {{\n\
                             {child_entry}(start.checked_add({size}).ok_or(Error::Overflow)?, exit)?\n\
                         }} else {{ exit }};\n\
                         {child_instruction}(start, following, pc)"
                    ),
                )
            }
        };
        self.functions.push(format!(
            "fn {entry}(base: usize, exit: usize) -> Result<usize, Error> {{\n\
                 {entry_body}\n\
             }}\n\
             fn {instruction}(base: usize, exit: usize, pc: usize) -> Result<Instr, Error> {{\n\
                 let end = base.checked_add({}).ok_or(Error::Overflow)?;\n\
                 if pc < base || pc >= end {{ return Err(Error::Invalid(\"block site out of range\".into())); }}\n\
                 {instruction_body}\n\
             }}\n",
            node.size
        ));
        (entry, instruction)
    }
}

fn atom_instruction(atom: &Atom) -> String {
    match *atom {
        Atom::Set { dst, value } => {
            format!("Instr::Set {{ dst: {dst}, value: {value}, next: exit }}")
        }
        Atom::Copy { dst, src } => format!("Instr::Copy {{ dst: {dst}, src: {src}, next: exit }}"),
        Atom::Not { dst, src } => format!("Instr::Not {{ dst: {dst}, src: {src}, next: exit }}"),
        Atom::And { dst, left, right } => {
            format!("Instr::And {{ dst: {dst}, left: {left}, right: {right}, next: exit }}")
        }
        Atom::Or { dst, left, right } => {
            format!("Instr::Or {{ dst: {dst}, left: {left}, right: {right}, next: exit }}")
        }
        Atom::Xor { dst, left, right } => {
            format!("Instr::Xor {{ dst: {dst}, left: {left}, right: {right}, next: exit }}")
        }
        Atom::Push { stack, src } => {
            format!("Instr::Push {{ stack: {stack}, src: {src}, next: exit }}")
        }
        Atom::Peek {
            stack,
            value,
            present,
        } => format!(
            "Instr::Peek {{ stack: {stack}, value: {value}, present: {present}, next: exit }}"
        ),
        Atom::Pop {
            stack,
            value,
            present,
        } => format!(
            "Instr::Pop {{ stack: {stack}, value: {value}, present: {present}, next: exit }}"
        ),
    }
}

/// Emit a compilable Rust binary, with physical labels resolved by specialized
/// functions and execution delegated to the shared machine runner.
///
/// Binding must be supplied from a separately verified original-Lean receipt.
/// Passing a hash computed from arbitrary input is *not* source attestation.
pub fn emit_original_source_rust(
    bytes: &[u8],
    expected: SourceGraphBinding<'_>,
) -> Result<String, Error> {
    let graph = parse_bound_graph(bytes, expected)?;
    let abi = graph.abi;
    source_dimensions(abi.r, abi.s)?;
    if abi.labels == 0 || abi.labels > MAX_LABELS || abi.input >= abi.s || abi.output >= abi.s {
        return Err(invalid("AOT root ABI outside physical machine bounds"));
    }
    let mut budget = MAX_NODES;
    let root = match (graph.kind.as_str(), graph.command, graph.program) {
        ("original-structured-source-v1", Some(command), None) => {
            let block = lower_native_block(command, abi.r, abi.s, &mut budget, 0)?;
            let labels = block.size.checked_add(1).ok_or(Error::Overflow)?;
            if labels > MAX_LABELS {
                return Err(Error::Capacity("AOT composed label budget".into()));
            }
            let entry = block.entry_at(1, 0)?;
            NativeSource {
                r: abi.r,
                s: abi.s,
                labels,
                entry,
                input: abi.input,
                output: abi.output,
                body: NativeBody::Composed(block),
            }
        }
        ("original-linked-source-v1", None, Some(tree)) => {
            lower_linked_program(tree, &mut budget, 0)?
        }
        _ => return Err(invalid("AOT source graph has ambiguous or absent root")),
    };
    if (root.r, root.s, root.labels, root.input, root.output)
        != (abi.r, abi.s, abi.labels, abi.input, abi.output)
        || root.entry >= root.labels
    {
        return Err(invalid("AOT root differs from elaborated Lean ABI"));
    }

    let mut emitter = Emitter::default();
    let root_function = emitter.source(&root);
    let mut output = format!(
        "// Generated from receipt-bound OpenAI Lean source; do not edit.\n\
         // Physical BitProgram steps and labels, not a TM2 microstep refinement.\n\
         use lean_eth_reference::bit_program::{{Config, Instr, RunLimits, relocate_ports, run_with_instruction_at}};\n\
         use lean_eth_reference::Error;\n\n\
         pub const SOURCE_COMMIT: &str = {source_commit:?};\n\
         pub const SOURCE_BLOB: &str = {source_blob:?};\n\
         pub const SOURCE_ID: &str = {source_id:?};\n\
         pub const SOURCE_DECLARATION: &str = {declaration:?};\n\
         pub const SOURCE_GRAPH_SHA256: &str = {digest:?};\n\
         pub const REGISTERS: usize = {r};\n\
         pub const STACKS: usize = {s};\n\
         pub const LABELS: usize = {labels};\n\
         pub const ENTRY: usize = {entry};\n\
         pub const INPUT_STACK: usize = {input};\n\
         pub const OUTPUT_STACK: usize = {output_stack};\n\n",
        source_commit = SOURCE_COMMIT,
        source_blob = expected.source_blob,
        source_id = expected.id,
        declaration = expected.declaration,
        digest = expected.graph_sha256,
        r = root.r,
        s = root.s,
        labels = root.labels,
        entry = root.entry,
        input = root.input,
        output_stack = root.output,
    );
    for function in emitter.functions {
        output.push_str(&function);
        if output.len() > MAX_RUST_SOURCE_BYTES {
            return Err(Error::Capacity(
                "AOT generated Rust exceeds source budget".into(),
            ));
        }
    }
    writeln!(
        &mut output,
        "pub fn instruction_at(pc: usize) -> Result<Instr, Error> {{ {root_function}(pc) }}"
    )
    .unwrap();
    output.push_str(
        r#"
fn run() -> Result<(), Box<dyn std::error::Error>> {
    let mut args = std::env::args().skip(1);
    let mode = args.next().ok_or("usage: generated [lookup PC | run BITS MAX_STEPS MAX_STACK_BITS]")?;
    match mode.as_str() {
        "lookup" => {
            let pc: usize = args.next().ok_or("missing pc")?.parse()?;
            if args.next().is_some() { return Err("extra argument".into()); }
            println!("{:?}", instruction_at(pc)?);
        }
        "run" => {
            let bits = args.next().ok_or("missing input bitstring")?;
            let max_steps: u64 = args.next().ok_or("missing max steps")?.parse()?;
            let max_stack_bits: usize = args.next().ok_or("missing max stack bits")?.parse()?;
            if args.next().is_some() { return Err("extra argument".into()); }
            let mut config = Config::<REGISTERS, STACKS> {
                pc: Some(ENTRY),
                regs: [false; REGISTERS],
                stacks: std::array::from_fn(|_| std::collections::VecDeque::new()),
            };
            for bit in bits.bytes() {
                config.stacks[INPUT_STACK].push_back(match bit {
                    b'0' => false,
                    b'1' => true,
                    _ => return Err("input must be a 0/1 bitstring".into()),
                });
            }
            let stats = run_with_instruction_at(
                &mut config,
                RunLimits { max_steps, max_stack_bits },
                instruction_at,
            )?;
            println!(
                "steps={};peak={};pc={:?};regs={:?};stacks={:?}",
                stats.instructions, stats.peak_stack_bits,
                config.pc, config.regs, config.stacks
            );
        }
        _ => return Err("expected lookup or run".into()),
    }
    Ok(())
}

fn main() {
    if let Err(error) = run() {
        eprintln!("{error}");
        std::process::exit(2);
    }
}
"#,
    );
    if output.len() > MAX_RUST_SOURCE_BYTES {
        return Err(Error::Capacity(
            "AOT generated Rust exceeds source budget".into(),
        ));
    }
    Ok(output)
}
