//! Human-facing commands, separate from the finite-machine and oracle semantics.
//! Existing stand-alone binary names remain compatibility entry points.
use std::fmt::Write as _;
use std::fs;
use std::io::{self, Read};
use std::path::{Path, PathBuf};

use clap::{Args, Parser, Subcommand};

use crate::bit_program::RunLimits;
use crate::native_frontend;
use crate::native_terminal_count::{SOURCE_STAGES, count_terminal, count_word_decimal};
use crate::{EnumeratingLeaf, Limits, count_cnf, parse_dimacs};

#[derive(Debug, Parser)]
#[command(
    name = "eth",
    version,
    about = "Execute source-pinned Lean ETH machine fragments and bounded reference oracles",
    long_about = "Research CLI for selected executable machinery from OpenAI's Lean ETH development.\n\
                  The frontend does not count satisfying assignments. Terminal counting only\n\
                  supports a restricted family. The semantic oracle is exponential. None of\n\
                  these commands independently establishes the ETH disproof or TM2 bounds.",
    subcommand_required = true,
    arg_required_else_help = true
)]
pub struct EthCli {
    #[command(subcommand)]
    command: EthCommand,
}

#[derive(Debug, Subcommand)]
enum EthCommand {
    /// Run the source-defined physical frontend; does not count solutions.
    Frontend(FrontendArgs),
    /// Count only source-supported terminal formulas; refuse all others.
    TerminalCount(TerminalCountArgs),
    /// Count small CNFs with an explicitly exponential semantic oracle.
    Oracle(OracleArgs),
}

#[derive(Debug, Args)]
pub struct FrontendArgs {
    /// DIMACS CNF file, or '-' for standard input.
    #[arg(value_name = "INPUT", default_value = "-")]
    pub input: PathBuf,
    /// Maximum source BitProgram instructions.
    #[arg(
        long,
        value_name = "N",
        default_value_t = 1_000_000,
        value_parser = positive_u64
    )]
    pub max_steps: u64,
    /// Maximum live stack bits.
    #[arg(
        long,
        value_name = "N",
        default_value_t = 1_000_000,
        value_parser = positive_usize
    )]
    pub max_stack_bits: usize,
}

#[derive(Debug, Args)]
pub struct TerminalCountArgs {
    /// DIMACS CNF file, or '-' for standard input.
    #[arg(value_name = "INPUT", default_value = "-")]
    pub input: PathBuf,
    /// Maximum source BitProgram instructions per stage.
    #[arg(
        long,
        value_name = "N",
        default_value_t = 20_000_000,
        value_parser = positive_u64
    )]
    pub max_steps: u64,
    /// Maximum live stack bits.
    #[arg(
        long,
        value_name = "N",
        default_value_t = 300_000,
        value_parser = positive_usize
    )]
    pub max_stack_bits: usize,
}

#[derive(Debug, Args)]
pub struct OracleArgs {
    /// DIMACS CNF file, or '-' for standard input.
    #[arg(value_name = "INPUT", default_value = "-")]
    pub input: PathBuf,
    /// Maximum variables admitted by the exponential leaf (cannot exceed 20).
    #[arg(
        long,
        value_name = "N",
        default_value_t = 20,
        value_parser = bounded_variables
    )]
    pub max_variables: usize,
}

fn positive_u64(raw: &str) -> Result<u64, String> {
    let n: u64 = raw.parse().map_err(|_| "expected a positive integer")?;
    if n == 0 {
        return Err("must be greater than zero".into());
    }
    Ok(n)
}

fn positive_usize(raw: &str) -> Result<usize, String> {
    let n: usize = raw.parse().map_err(|_| "expected a positive integer")?;
    if n == 0 {
        return Err("must be greater than zero".into());
    }
    Ok(n)
}

fn bounded_variables(raw: &str) -> Result<usize, String> {
    let n: usize = raw.parse().map_err(|_| "expected an integer from 0 through 20")?;
    if n > 20 {
        return Err("exponential oracle limit cannot exceed 20 variables".into());
    }
    Ok(n)
}

fn read_input(path: &Path) -> Result<String, String> {
    if path.as_os_str() == "-" {
        let mut source = String::new();
        io::stdin()
            .read_to_string(&mut source)
            .map_err(|e| format!("standard input: {e}"))?;
        Ok(source)
    } else {
        fs::read_to_string(path).map_err(|e| format!("{}: {e}", path.display()))
    }
}

fn bits(word: impl IntoIterator<Item = bool>) -> String {
    word.into_iter().map(|b| if b { '1' } else { '0' }).collect()
}

/// The report is returned only after the physical program halts and all
/// existing source ABI postconditions are established.
pub fn frontend(args: &FrontendArgs) -> Result<String, String> {
    let source = read_input(&args.input)?;
    let formula = parse_dimacs(&source).map_err(|e| e.to_string())?;
    let original = formula.encode_lean();
    let program = native_frontend::program().map_err(|e| e.to_string())?;
    let mut state = program.initial(original.bytes().map(|b| b == b'1'));
    let stats = program
        .run(
            &mut state,
            RunLimits {
                max_steps: args.max_steps,
                max_stack_bits: args.max_stack_bits,
            },
        )
        .map_err(|e| e.to_string())?;
    if state.pc.is_some() {
        return Err("front-end did not reach its halt instruction".into());
    }
    let output = |port: usize| bits(state.stacks[port].iter().copied());
    if output(256) != original || !state.stacks[263].is_empty() {
        return Err("source ABI postcondition failed".into());
    }
    for i in 0..1220 {
        if ![256, 258, 265, 267].contains(&i) && !state.stacks[i].is_empty() {
            return Err(format!("source scratch stack {i} was not cleaned"));
        }
    }
    let mut report = String::new();
    writeln!(report, "status=frontend-completed").unwrap();
    writeln!(report, "instructions={}", stats.instructions).unwrap();
    writeln!(report, "peak_stack_bits={}", stats.peak_stack_bits).unwrap();
    writeln!(report, "original_encoding={}", output(256)).unwrap();
    writeln!(report, "ambient_unary={}", output(258)).unwrap();
    writeln!(report, "variables_binary_lsb={}", output(267)).unwrap();
    writeln!(report, "normalized_body={}", output(265)).unwrap();
    Ok(report)
}

/// A count here is never a fallback to the bounded host enumeration oracle.
pub fn terminal_count(args: &TerminalCountArgs) -> Result<String, String> {
    let source = read_input(&args.input)?;
    let cnf = parse_dimacs(&source).map_err(|e| e.to_string())?;
    let result = count_terminal(
        &cnf,
        RunLimits {
            max_steps: args.max_steps,
            max_stack_bits: args.max_stack_bits,
        },
    )
    .map_err(|e| e.to_string())?;
    let mut report = String::new();
    writeln!(report, "status=terminal-count-complete").unwrap();
    writeln!(report, "count={}", count_word_decimal(&result.count_lsb)).unwrap();
    writeln!(
        report,
        "count_bits_lsb={}",
        bits(result.count_lsb.iter().copied())
    )
    .unwrap();
    writeln!(report, "answer={}", if result.positive { 1 } else { 0 }).unwrap();
    for (name, stats) in SOURCE_STAGES.iter().zip(result.stages.iter()) {
        writeln!(
            report,
            "stage={name} instructions={} peak_stack_bits={}",
            stats.instructions, stats.peak_stack_bits
        )
        .unwrap();
    }
    writeln!(report, "source_instructions={}", result.total_instructions).unwrap();
    writeln!(report, "peak_live_stack_bits={}", result.peak_stack_bits).unwrap();
    writeln!(
        report,
        "resource_basis=BitProgram_source_instructions_not_TM2_microsteps"
    )
    .unwrap();
    Ok(report)
}

/// This command is deliberately and explicitly exponential.
pub fn oracle(args: &OracleArgs) -> Result<String, String> {
    let source = read_input(&args.input)?;
    let cnf = parse_dimacs(&source).map_err(|e| e.to_string())?;
    let (count, stats) = count_cnf(
        cnf.normalize(),
        2,
        &mut EnumeratingLeaf {
            max_variables: args.max_variables,
        },
        Limits::default(),
    )
    .map_err(|e| e.to_string())?;
    Ok(format!(
        "count={count} nodes={} leaves={} peak_frontier={}\n",
        stats.nodes, stats.leaves, stats.peak_frontier
    ))
}

pub fn execute(args: EthCli) -> Result<String, String> {
    match args.command {
        EthCommand::Frontend(args) => frontend(&args),
        EthCommand::TerminalCount(args) => terminal_count(&args),
        EthCommand::Oracle(args) => oracle(&args),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use clap::CommandFactory;

    #[test]
    fn command_tree_is_consistent() {
        EthCli::command().debug_assert();
    }

    #[test]
    fn help_and_refusals_are_typed() {
        let help = EthCli::try_parse_from(["eth", "--help"]).unwrap_err();
        assert_eq!(help.kind(), clap::error::ErrorKind::DisplayHelp);
        assert!(EthCli::try_parse_from(["eth", "frontend", "--max-steps", "0"]).is_err());
        assert!(
            EthCli::try_parse_from(["eth", "terminal-count", "--max-stack-bits", "0"])
                .is_err()
        );
        assert!(
            EthCli::try_parse_from(["eth", "oracle", "--max-variables", "21"]).is_err()
        );
        assert!(EthCli::try_parse_from(["eth", "unknown"]).is_err());
        assert!(EthCli::try_parse_from(["eth"]).is_err());
    }
}
