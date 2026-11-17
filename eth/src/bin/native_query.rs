//! Run a fully exported, pinned Lean query program. Never calls a SAT oracle.
//! The source table MUST be separately verified against the genuine Lean run.
use std::collections::HashSet;
use std::fs::File;
use std::io::{BufRead, BufReader};

use lean_eth_reference::Error;
use lean_eth_reference::bit_program::{Config, RunLimits};
use lean_eth_reference::native_query_table::{ImportLimits, import_query_table};

fn load_fixture(
    path: &str,
    p: &lean_eth_reference::bit_program::Program<40, 896>,
) -> Result<Config<40, 896>, Error> {
    let file = File::open(path).map_err(|e| Error::Invalid(format!("fixture: {e}")))?;
    let mut config = p.initial([]);
    let mut seen = HashSet::new();
    for line in BufReader::new(file).lines() {
        let line = line.map_err(|e| Error::Invalid(format!("fixture: {e}")))?;
        let parts: Vec<_> = line.split('|').collect();
        if parts.len() != 3 {
            return Err(Error::Invalid(
                "fixture must use STACK|port|bits or REG|port|0/1".into(),
            ));
        }
        let port: usize = parts[1]
            .parse()
            .map_err(|_| Error::Invalid("fixture port is not a decimal integer".into()))?;
        let kind = match parts[0] {
            "STACK" => "STACK",
            "REG" => "REG",
            _ => return Err(Error::Invalid("unknown fixture record".into())),
        };
        if !seen.insert((kind, port)) {
            return Err(Error::Invalid("fixture repeats a physical port".into()));
        }
        match kind {
            "STACK" if port < 896 => {
                if !parts[2].bytes().all(|b| b == b'0' || b == b'1') {
                    return Err(Error::Invalid("fixture stack contains non-bits".into()));
                }
                config.stacks[port] = parts[2].bytes().map(|b| b == b'1').collect();
            }
            "REG" if port < 40 => {
                config.regs[port] = match parts[2] {
                    "0" => false,
                    "1" => true,
                    _ => return Err(Error::Invalid("fixture register must be 0 or 1".into())),
                };
            }
            _ => return Err(Error::Invalid("fixture port or kind out of range".into())),
        }
    }
    Ok(config)
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let args: Vec<String> = std::env::args().collect();
    if args.len() != 5 {
        return Err("usage: native_query QUERY_TABLE FIXTURE MAX_STEPS MAX_STACK_BITS".into());
    }
    let max_steps: u64 = args[3].parse()?;
    let max_stack_bits: usize = args[4].parse()?;
    if max_steps == 0 || max_stack_bits == 0 {
        return Err("positive execution limits are required".into());
    }
    let table = File::open(&args[1])?;
    let p = import_query_table(BufReader::new(table), ImportLimits::default())?;
    let mut config = load_fixture(&args[2], &p)?;
    let stats = p.run(
        &mut config,
        RunLimits {
            max_steps,
            max_stack_bits,
        },
    )?;
    // A successful result is printed ONLY after an authentic source halt.
    if config.pc.is_some() {
        return Err("native query did not halt".into());
    }
    let bits: String = config.stacks[p.output_stack()]
        .iter()
        .map(|&bit| if bit { '1' } else { '0' })
        .collect();
    println!(
        "HALT|{}|{}|{}",
        stats.instructions, stats.peak_stack_bits, bits
    );
    Ok(())
}
