//! Compatibility entry point for the bounded exponential semantic oracle.
use clap::Parser;
use lean_eth_reference::cli::{OracleArgs, oracle};

#[derive(Parser)]
#[command(about = "Explicitly exponential bounded #SAT semantic oracle")]
struct Cli {
    #[command(flatten)]
    args: OracleArgs,
}

fn main() {
    match oracle(&Cli::parse().args) {
        Ok(report) => print!("{report}"),
        Err(error) => {
            eprintln!("lean-eth-reference: {error}");
            std::process::exit(2);
        }
    }
}
