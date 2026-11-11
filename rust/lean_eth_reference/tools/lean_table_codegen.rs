//! Deterministic, bounded lowering of a pinned Lean BitProgram table to Rust.
//!
//! No host SAT solver, runtime table interpreter, or optimization. The result
//! executes one original source instruction per dispatch iteration.
//! This is an experiment, not an attested Lean export or a TM2 refinement.
use std::fmt::Write;

const SOURCE_COMMIT: &str = "4eaee87548250b2682affda7d05d947c05554bae";
const QUERY_SOURCE_BLOB: &str = "c2fb29983bb33229d5cf60729cd3d1e37b9b00ca";
const CHUNK_SIZE: usize = 256;
const MAX_TABLE_BYTES: usize = 32_000_000;

// This shared module is also compiled by build.rs, which uses only Fixture.
#[allow(dead_code)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum TableKind<'a> {
    /// Accept only the provenance fields and ABI of the original query program.
    Query,
    /// Synthetic test data: never attribute this table to the original Lean source.
    Fixture,
    /// Literal fixed-control programs in the pinned original Lean source.
    OriginalBinaryAdd,
    OriginalQueryParity,
    OriginalTypeBit,
    /// A manifest-attested source declaration, not self-attested input bytes.
    Catalog {
        name: &'a str,
        blob: &'a str,
        /// Registers, stacks, labels, entry, input port and output port.
        abi: (usize, usize, usize, usize, usize, usize),
    },
}

fn decimal(s: &str) -> Result<usize, String> {
    if s.is_empty() || !s.bytes().all(|b| b.is_ascii_digit()) || (s.len() > 1 && s.starts_with('0'))
    {
        return Err(format!("noncanonical decimal: {s:?}"));
    }
    s.parse::<usize>().map_err(|_| "decimal overflow".into())
}

fn parse_instr(s: &str, r: usize, stacks: usize, labels: usize) -> Result<String, String> {
    let parts: Vec<_> = s.split(':').collect();
    let opcode = parts[0];
    // r=register, s=stack, l=label, b=Boolean. This covers all 12
    // constructors of the pinned BitProgram.Instr.
    let kinds = match opcode {
        "halt" => "",
        "goto" => "l",
        "set" => "rbl",
        "copy" | "not" => "rrl",
        "and" | "or" | "xor" => "rrrl",
        "branch" => "rll",
        "push" => "srl",
        "peek" | "pop" => "srrl",
        _ => return Err(format!("unknown opcode: {opcode}")),
    };
    if parts.len() != kinds.len() + 1 {
        return Err(format!("incorrect {opcode} arity"));
    }
    let mut values = Vec::with_capacity(kinds.len());
    for (field, kind) in parts[1..].iter().zip(kinds.chars()) {
        let n = decimal(field)?;
        let upper = match kind {
            'r' => r,
            's' => stacks,
            'l' => labels,
            'b' => 2,
            _ => unreachable!(),
        };
        if n >= upper {
            return Err(format!("{opcode}: {kind} index {n} outside {upper}"));
        }
        values.push(n);
    }

    // The instruction bodies intentionally mirror Program::step exactly.
    // In Peek and Pop the second register write wins when both ports alias.
    let line = match (opcode, values.as_slice()) {
        ("halt", []) => "config.pc = None;".to_string(),
        ("goto", [next]) => format!("config.pc = Some({next});"),
        ("set", [dst, bit, next]) => format!(
            "config.regs[{dst}] = {}; config.pc = Some({next});",
            if *bit == 1 { "true" } else { "false" }
        ),
        ("copy", [dst, src, next]) => {
            format!("config.regs[{dst}] = config.regs[{src}]; config.pc = Some({next});")
        }
        ("not", [dst, src, next]) => {
            format!("config.regs[{dst}] = !config.regs[{src}]; config.pc = Some({next});")
        }
        ("and", [dst, a, b, next]) => format!(
            "config.regs[{dst}] = config.regs[{a}] && config.regs[{b}]; config.pc = Some({next});"
        ),
        ("or", [dst, a, b, next]) => format!(
            "config.regs[{dst}] = config.regs[{a}] || config.regs[{b}]; config.pc = Some({next});"
        ),
        ("xor", [dst, a, b, next]) => format!(
            "config.regs[{dst}] = config.regs[{a}] ^ config.regs[{b}]; config.pc = Some({next});"
        ),
        ("branch", [test, yes, no]) => {
            format!("config.pc = Some(if config.regs[{test}] {{ {yes} }} else {{ {no} }});")
        }
        ("push", [stack, src, next]) => format!(
            "if live_bits >= limits.max_stack_bits {{ return Err(Error::Capacity(\"BitProgram stack-bit limit\".into())); }}\n                live_bits = live_bits.checked_add(1).ok_or(Error::Overflow)?;\n                config.stacks[{stack}].push_front(config.regs[{src}]); config.pc = Some({next});"
        ),
        ("peek", [stack, value, present, next]) => format!(
            "let top = config.stacks[{stack}].front().copied();\n                config.regs[{value}] = top.unwrap_or(false);\n                config.regs[{present}] = top.is_some(); config.pc = Some({next});"
        ),
        ("pop", [stack, value, present, next]) => format!(
            "let top = config.stacks[{stack}].pop_front();\n                if top.is_some() {{ live_bits -= 1; }}\n                config.regs[{value}] = top.unwrap_or(false);\n                config.regs[{present}] = top.is_some(); config.pc = Some({next});"
        ),
        _ => unreachable!("validated opcode and arity"),
    };
    Ok(line)
}

/// Produce the same Rust bytes for the same canonical table bytes.
/// The table is not proof of its own Lean provenance. A separate attested
/// exporter/receipt and original-source differential tests are required.
pub fn generate(table: &str, kind: TableKind, max_labels: usize) -> Result<String, String> {
    if !table.is_ascii() || table.contains('\r') || !table.ends_with('\n') {
        return Err("table must be canonical ASCII/LF with final newline".into());
    }
    if max_labels == 0 || table.len() > MAX_TABLE_BYTES {
        return Err("code generation capacity exceeded".into());
    }
    let rows: Vec<_> = table[..table.len() - 1].split('\n').collect();
    if rows.len() < 4 || rows.iter().any(|r| r.is_empty()) {
        return Err("missing or empty table record".into());
    }
    let name = match kind {
        TableKind::Query => "query",
        TableKind::Fixture => "fixture",
        TableKind::OriginalBinaryAdd => "binary-add",
        TableKind::OriginalQueryParity => "query-parity",
        TableKind::OriginalTypeBit => "type-bit",
        TableKind::Catalog { name, .. } => name,
    };
    let expected_pin = match kind {
        TableKind::Query => format!("PIN|query|{SOURCE_COMMIT}|{QUERY_SOURCE_BLOB}"),
        TableKind::Fixture => "PIN|fixture|synthetic".to_string(),
        TableKind::OriginalBinaryAdd => {
            format!("PIN|binary-add|{SOURCE_COMMIT}|ab8a858c2466aa3879087f825802aa76c7aa768f")
        }
        TableKind::OriginalQueryParity => {
            format!("PIN|query-parity|{SOURCE_COMMIT}|7a2535f7c479463a5f5ed8a30a33192aad1b063e")
        }
        TableKind::OriginalTypeBit => {
            format!("PIN|type-bit|{SOURCE_COMMIT}|4e020c828e458b4420179da94c3451bea653a7b9")
        }
        TableKind::Catalog { name, blob, .. } => {
            format!("PIN|{name}|{SOURCE_COMMIT}|{blob}")
        }
    };
    if rows[0] != expected_pin {
        return Err("table provenance/pin mismatch".into());
    }
    let header: Vec<_> = rows[1].split('|').collect();
    if header.len() != 8 || header[0] != "PROGRAM" || header[1] != name {
        return Err("invalid program header".into());
    }
    let r = decimal(header[2])?;
    let s = decimal(header[3])?;
    let labels = decimal(header[4])?;
    let entry = decimal(header[5])?;
    let input = decimal(header[6])?;
    let output = decimal(header[7])?;
    if r == 0
        || s == 0
        || labels == 0
        || labels > max_labels
        || entry >= labels
        || input >= s
        || output >= s
    {
        return Err("invalid dimensions, ports, entry or label budget".into());
    }
    let expected_abi = match kind {
        TableKind::Query => Some((40, 896, 330, 323, None)),
        TableKind::OriginalBinaryAdd => Some((8, 3, 0, 2, Some(13))),
        TableKind::OriginalQueryParity => Some((3, 1, 0, 0, Some(4))),
        TableKind::OriginalTypeBit => Some((3, 2, 1, 1, Some(7))),
        TableKind::Fixture => None,
        TableKind::Catalog { abi, .. } => Some((abi.0, abi.1, abi.4, abi.5, Some(abi.2))),
    };
    if let Some((er, es, ei, eo, el)) = expected_abi
        && ((r, s, input, output) != (er, es, ei, eo)
            || el.is_some_and(|expected_labels| expected_labels != labels))
    {
        return Err("pinned source machine ABI mismatch".into());
    }
    if let TableKind::Catalog { abi, .. } = kind
        && entry != abi.3
    {
        return Err("source declaration entry mismatch".into());
    }
    if rows.len().checked_sub(3) != Some(labels)
        || rows[labels + 2] != format!("END|{name}|{labels}")
    {
        return Err("missing, excess, or incorrect table records".into());
    }

    let mut body = String::new();
    let chunked = labels > CHUNK_SIZE * 2;
    let mut effects = if chunked {
        Vec::with_capacity(labels)
    } else {
        Vec::new()
    };
    for i in 0..labels {
        let record: Vec<_> = rows[i + 2].split('|').collect();
        if record.len() != 4 || record[0] != "CODE" || record[1] != name || decimal(record[2])? != i
        {
            return Err(format!("missing, unordered or duplicate CODE label {i}"));
        }
        let effect = parse_instr(record[3], r, s, labels)?;
        if chunked {
            effects.push(effect);
        } else {
            writeln!(body, "            {i} => {{").unwrap();
            for line in effect.lines() {
                writeln!(body, "                {line}").unwrap();
            }
            body.push_str("            }\n");
        }
    }

    let mut output_rs = String::new();
    output_rs.push_str("// @generated by tools/lean_table_codegen.rs; DO NOT EDIT.\n");
    output_rs.push_str("// The input table and provenance receipt are external evidence.\n");
    writeln!(output_rs, "pub const ENTRY: usize = {entry};").unwrap();
    writeln!(output_rs, "pub const INPUT_STACK: usize = {input};").unwrap();
    writeln!(output_rs, "pub const OUTPUT_STACK: usize = {output};").unwrap();
    writeln!(output_rs, "pub const LABELS: usize = {labels};").unwrap();
    if chunked {
        // Each helper keeps at most CHUNK_SIZE instruction arms. We compile
        // direct source instructions, never an interpreter or a dynamically
        // dispatched instruction array. The dispatch PC remains global.
        for (chunk_index, chunk) in effects.chunks(CHUNK_SIZE).enumerate() {
            output_rs.push_str("#[allow(unused_variables)]\n");
            writeln!(output_rs, "fn chunk_{chunk_index}(pc: usize, config: &mut lean_eth_reference::bit_program::Config<{r}, {s}>, limits: lean_eth_reference::bit_program::RunLimits, live_bits: &mut usize) -> Result<(), lean_eth_reference::Error> {{").unwrap();
            output_rs.push_str("    use lean_eth_reference::Error;\n    match pc {\n");
            for (offset, effect) in chunk.iter().enumerate() {
                let pc = chunk_index * CHUNK_SIZE + offset;
                writeln!(output_rs, "        {pc} => {{").unwrap();
                for line in effect.lines() {
                    writeln!(
                        output_rs,
                        "            {}",
                        line.replace("live_bits", "(*live_bits)")
                    )
                    .unwrap();
                }
                output_rs.push_str("        }\n");
            }
            writeln!(output_rs, "        _ => return Err(Error::Invalid(format!(\"configuration pc {{pc}} outside Fin {labels}\"))),").unwrap();
            output_rs.push_str("    }\n    Ok(())\n}\n");
        }
    }
    output_rs.push_str("#[allow(clippy::assign_op_pattern)]\n#[allow(unused_mut)]\n");
    writeln!(output_rs, "pub fn run(config: &mut lean_eth_reference::bit_program::Config<{r}, {s}>, limits: lean_eth_reference::bit_program::RunLimits) -> Result<lean_eth_reference::bit_program::RunStats, lean_eth_reference::Error> {{").unwrap();
    output_rs.push_str(
        "    use lean_eth_reference::Error;\n\
         \x20   use lean_eth_reference::bit_program::RunStats;\n\
         \x20   let mut stats = RunStats { peak_stack_bits: config.stack_bits()?, ..RunStats::default() };\n\
         \x20   if stats.peak_stack_bits > limits.max_stack_bits {\n\
         \x20       return Err(Error::Capacity(\"initial bit-stack capacity\".into()));\n\
         \x20   }\n\
         \x20   let mut live_bits = stats.peak_stack_bits;\n\
         \x20   while let Some(pc) = config.pc {\n\
         \x20       if stats.instructions >= limits.max_steps {\n\
         \x20           return Err(Error::Capacity(\"BitProgram instruction limit\".into()));\n\
         \x20       }\n\
         \x20       "
    );
    if chunked {
        output_rs.push_str("match pc / 256 {\n");
        for index in 0..effects.len().div_ceil(CHUNK_SIZE) {
            writeln!(
                output_rs,
                "            {index} => chunk_{index}(pc, config, limits, &mut live_bits)?,"
            )
            .unwrap();
        }
    } else {
        output_rs.push_str("match pc {\n");
        output_rs.push_str(&body);
    }
    writeln!(output_rs, "            _ => return Err(Error::Invalid(format!(\"configuration pc {{pc}} outside Fin {labels}\"))),").unwrap();
    output_rs.push_str(
        "        }\n\
         \x20       stats.instructions += 1;\n\
         \x20       stats.peak_stack_bits = stats.peak_stack_bits.max(live_bits);\n\
         \x20   }\n\
         \x20   Ok(stats)\n\
         }\n",
    );
    Ok(output_rs)
}

#[cfg(test)]
mod tests {
    use super::*;

    const TINY: &str = include_str!("fixtures/tiny.table");

    #[test]
    fn deterministic_and_fail_closed() {
        let a = generate(TINY, TableKind::Fixture, 100).unwrap();
        let b = generate(TINY, TableKind::Fixture, 100).unwrap();
        assert_eq!(a.as_bytes(), b.as_bytes());
        assert!(a.contains("config.stacks[0].push_front"));
        assert!(generate(TINY, TableKind::Query, 100).is_err());
        assert!(generate(TINY, TableKind::Fixture, 2).is_err());
        assert!(
            generate(
                &TINY.replace("CODE|fixture|3", "CODE|fixture|2"),
                TableKind::Fixture,
                100
            )
            .is_err()
        );
        assert!(
            generate(
                &TINY.replace("push:0:0:3", "push:4:0:3"),
                TableKind::Fixture,
                100
            )
            .is_err()
        );
        assert!(
            generate(
                &TINY.replace("branch:3:1:14", "branch:3:1:99"),
                TableKind::Fixture,
                100
            )
            .is_err()
        );
        assert!(generate(&format!("{TINY}\n"), TableKind::Fixture, 100).is_err());
        let originals = [
            (
                include_str!("fixtures/original/binary-add.table"),
                TableKind::OriginalBinaryAdd,
            ),
            (
                include_str!("fixtures/original/query-parity.table"),
                TableKind::OriginalQueryParity,
            ),
            (
                include_str!("fixtures/original/type-bit.table"),
                TableKind::OriginalTypeBit,
            ),
        ];
        for (original, kind) in originals {
            let result = generate(original, kind, 100).unwrap();
            assert_eq!(result, generate(original, kind, 100).unwrap());
            assert!(generate(original, TableKind::Fixture, 100).is_err());
            assert!(generate(TINY, kind, 100).is_err());
        }
    }
}
