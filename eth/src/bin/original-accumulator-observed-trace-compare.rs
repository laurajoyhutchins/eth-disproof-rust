//! Experimental *full-frame* differential against genuine original-Lean
//! hit/miss execution traces. This is NOT a kernel certificate or universal
//! Rust-to-Lean refinement, and it cannot bless an observed-only source graph.
//!
//! Supply the exact stdout from the pinned original-Lean trace workflow.
//! The original source constructs all input stacks via Dictionary.inputTape;
//! this tool uses ONLY the existing canonical Rust BitProgram instruction
//! decoder and step semantics. A divergence reports its first physical step.
//!
//! See technical notebook: studies/source-readout-visit-costs.
use lean_eth_reference::bit_program::{
    Config, DeferredProgram, Program, SourceGraphBinding,
};
use sha2::{Digest, Sha256};
use std::collections::{BTreeMap, VecDeque};
use std::error::Error;
use std::fs;
use std::path::Path;

const SOURCE_GRAPH: &[u8] =
    include_bytes!("../../fixtures/original-accumulate-observed-unverified.json");
const GRAPH_SHA256: &str = "0af370ad3ca3f8a5a9c0a144e8ffc82c07bc9b24acd206fa3ed863d8a58d2ea3";
const SOURCE_BLOB: &str = "3e1664be261748c6e12a2d1cafb033dc26131bf9";
const SOURCE_DECL: &str =
    "OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsReadoutProgram.accumulateProgram";
const MAX_TRACE_BYTES: u64 = 4 * 1024 * 1024;
const MAX_STEPS_PER_CASE: usize = 2500;
type Frame = Config<8, 27>;

fn invalid(why: impl Into<String>) -> Box<dyn Error> {
    why.into().into()
}

fn bits(text: &str) -> Result<VecDeque<bool>, Box<dyn Error>> {
    text.bytes()
        .map(|c| match c {
            b'0' => Ok(false),
            b'1' => Ok(true),
            _ => Err(invalid("invalid Boolean stack bit in original trace")),
        })
        .collect()
}

fn parse_frame(pc: &str, regs: &str, stacks: &str) -> Result<Frame, Box<dyn Error>> {
    let pc = if pc == "X" {
        None
    } else {
        let label = pc.parse::<usize>()?;
        if label >= 309 || label.to_string() != pc {
            return Err(invalid("noncanonical or out-of-range original source PC"));
        }
        Some(label)
    };
    if regs.len() != 8 {
        return Err(invalid("original source trace requires eight register bits"));
    }
    let registers = bits(regs)?;
    let regs: [bool; 8] = registers
        .into_iter()
        .collect::<Vec<_>>()
        .try_into()
        .map_err(|_| invalid("invalid original register width"))?;
    let columns: Vec<_> = stacks.split(',').map(bits).collect::<Result<_, _>>()?;
    let stacks: [VecDeque<bool>; 27] = columns
        .try_into()
        .map_err(|_| invalid("original source trace requires exactly 27 stack fields"))?;
    Ok(Frame { pc, regs, stacks })
}

fn flat_observation() -> Result<Program<8, 27>, Box<dyn Error>> {
    if format!("{:x}", Sha256::digest(SOURCE_GRAPH)) != GRAPH_SHA256 {
        return Err(invalid("observed-only original source fixture hash changed"));
    }
    let source = DeferredProgram::<8, 27>::from_original_source_json(
        SOURCE_GRAPH,
        SourceGraphBinding {
            id: "query_module_moments_accumulate",
            declaration: SOURCE_DECL,
            source_blob: SOURCE_BLOB,
            graph_sha256: GRAPH_SHA256,
        },
    )?;
    if source.labels() != 309
        || source.entry() != 1
        || source.input_stack() != 15
        || source.output_stack() != 17
    {
        return Err(invalid("original source ABI mismatch"));
    }
    let code = (0..source.labels())
        .map(|pc| source.instruction_at(pc))
        .collect::<Result<Vec<_>, _>>()?;
    Ok(Program::<8, 27>::new(15, 17, 1, code)?)
}

fn param<'a>(
    params: &'a BTreeMap<String, String>,
    key: &str,
) -> Result<&'a str, Box<dyn Error>> {
    params
        .get(key)
        .map(String::as_str)
        .ok_or_else(|| invalid(format!("missing source parameter {key}")))
}

fn assert_source_input(
    case: &str,
    state: &Frame,
    params: &BTreeMap<String, String>,
) -> Result<(), Box<dyn Error>> {
    if state.pc != Some(1) || state.regs != [false; 8] {
        return Err(invalid(format!("{case}: invalid source initial PC/registers")));
    }
    let expected_query = match case {
        "hit" => param(params, "hit_query")?,
        "miss" => param(params, "miss_query")?,
        _ => return Err(invalid("unknown original source case")),
    };
    if param(params, "prime")? != "2"
        || param(params, "exponent")? != "1"
        || param(params, "entries")? != "1"
        || expected_query.len() != 1
        || param(params, "hit_query")? == param(params, "miss_query")?
    {
        return Err(invalid("unrecognized source hit/miss domain"));
    }
    let width = param(params, "width")?.parse::<usize>()?;
    if width == 0 || width > 1024 {
        return Err(invalid("source coefficient width outside bounded fixture domain"));
    }
    let source_coefficient = bits(param(params, "coefficient")?)?;
    if source_coefficient.len() != width {
        return Err(invalid("coefficient width disagrees with source encoding"));
    }
    let source_modulus = bits(param(params, "modulus")?)?;
    if state.stacks[5] != source_modulus
        || state.stacks[12] != VecDeque::from(vec![true; width])
        || state.stacks[24] != VecDeque::from(vec![true])
        || state.stacks[17] != source_coefficient
    {
        return Err(invalid("source initial modulus/width/count/coefficient mismatch"));
    }
    let reverse_query = bits(&expected_query.chars().rev().collect::<String>())?;
    if state.stacks[16] != reverse_query || state.stacks[15].is_empty() {
        return Err(invalid("source inputTape dictionary/query mismatch"));
    }
    for stack in 0..27 {
        if ![5, 12, 15, 16, 17, 24].contains(&stack) && !state.stacks[stack].is_empty() {
            return Err(invalid(format!(
                "{case}: source initial scratch stack {stack} is not empty"
            )));
        }
    }
    Ok(())
}

fn compare_trace(text: &str) -> Result<(usize, usize), Box<dyn Error>> {
    let machine = flat_observation()?;
    let mut lines = text.lines();
    if lines.next() != Some("ORIGINAL_ACCUMULATE_TRACE_V1") {
        return Err(invalid("original Lean trace version header missing"));
    }
    let mut params = BTreeMap::<String, String>::new();
    let mut finished = [None, None];
    let mut current: Option<Frame> = None;
    let mut active_case: Option<&str> = None;
    let mut step: usize = 0;
    let mut started = false;
    for line in lines {
        let parts: Vec<_> = line.split('|').collect();
        match parts.as_slice() {
            ["PARAM", key, value] if !started => {
                if params.insert((*key).to_owned(), (*value).to_owned()).is_some() {
                    return Err(invalid("duplicate source parameter"));
                }
            }
            ["TRACE", case, index, pc, regs, stacks] => {
                started = true;
                let required = if finished[0].is_none() { "hit" } else { "miss" };
                if *case != required || (*case == "hit" && finished[1].is_some()) {
                    return Err(invalid("source case order or coverage mismatch"));
                }
                let index = index.parse::<usize>()?;
                if index > MAX_STEPS_PER_CASE || index.to_string() != *index {
                    return Err(invalid("original source trace step out of range"));
                }
                let expected = parse_frame(pc, regs, stacks)?;
                if active_case != Some(case) {
                    if index != 0 || current.is_some() || active_case.is_some() {
                        return Err(invalid("source case restarted or nonzero first index"));
                    }
                    assert_source_input(case, &expected, &params)?;
                    current = Some(expected);
                    active_case = Some(case);
                    step = 0;
                    continue;
                }
                if index != step + 1 {
                    return Err(invalid(format!("{case}: source trace step discontinuity")));
                }
                let state = current.as_mut().ok_or_else(|| invalid("missing current frame"))?;
                if !machine.step(state)? {
                    return Err(invalid(format!(
                        "{case}: Rust halted before source step {index}"
                    )));
                }
                if *state != expected {
                    return Err(invalid(format!(
                        "{case}: FULL-FRAME divergence at source step {index}, \
                         Rust PC {:?}, Lean PC {:?}; Rust regs {:?}, Lean regs {:?}; \
                         first mismatching stack {:?}",
                        state.pc,
                        expected.pc,
                        state.regs,
                        expected.regs,
                        (0..27).find(|&i| state.stacks[i] != expected.stacks[i])
                    )));
                }
                step = index;
            }
            ["END", case, count, "HALTED"] => {
                let required = if finished[0].is_none() { "hit" } else { "miss" };
                if *case != required || active_case != Some(case) {
                    return Err(invalid("unexpected source end record"));
                }
                let count = count.parse::<usize>()?;
                let state = current.take().ok_or_else(|| invalid("missing final frame"))?;
                if count != step || count == 0 || state.pc.is_some() {
                    return Err(invalid(format!("{case}: incomplete/nonterminal physical trace")));
                }
                if finished[0].is_none() {
                    finished[0] = Some(count);
                } else {
                    finished[1] = Some(count);
                }
                active_case = None;
            }
            _ => return Err(invalid(format!("invalid source trace record: {}", &line[..line.len().min(90)]))),
        }
    }
    match (finished[0], finished[1]) {
        (Some(hit), Some(miss)) => Ok((hit, miss)),
        _ => Err(invalid("missing terminating hit or miss source trace")),
    }
}

fn main() -> Result<(), Box<dyn Error>> {
    let mut args = std::env::args_os().skip(1);
    let path = args.next().ok_or("usage: original-accumulator-observed-trace-compare TRACE.stdout.log")?;
    if args.next().is_some() {
        return Err(invalid("unexpected extra CLI arguments"));
    }
    let path = Path::new(&path);
    if !path.is_file() || path.symlink_metadata()?.file_type().is_symlink() {
        return Err(invalid("trace must be a regular, nonsymlink file"));
    }
    if path.metadata()?.len() == 0 || path.metadata()?.len() > MAX_TRACE_BYTES {
        return Err(invalid("original source trace exceeds bounded evidence size"));
    }
    let trace = fs::read_to_string(path)?;
    let (hit, miss) = compare_trace(&trace)?;
    println!(
        "ORIGINAL_ACCUMULATE_HIT_MISS_STEP_PARITY \
         hit_steps={hit} miss_steps={miss} \
         graph_sha256={GRAPH_SHA256} \
         observation_only=true kernel_certificate=false"
    );
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::{flat_observation, parse_frame};

    #[test]
    fn original_observed_table_is_decodable_with_expected_abi() {
        let program = flat_observation().unwrap();
        assert_eq!(program.code().len(), 309);
        assert_eq!(program.entry(), 1);
        assert_eq!(program.input_stack(), 15);
        assert_eq!(program.output_stack(), 17);
    }

    #[test]
    fn invalid_pc_and_stack_shape_fail_before_any_transition() {
        assert!(parse_frame("309", "00000000", &vec![""; 27].join(",")).is_err());
        assert!(parse_frame("1", "00000000", &vec![""; 26].join(",")).is_err());
        assert!(parse_frame("1", "0000000q", &vec![""; 27].join(",")).is_err());
    }
}
