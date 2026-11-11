//! Single human-facing CLI. Specialized research binaries remain available.
use clap::Parser;
use lean_eth_reference::cli::{EthCli, execute};

fn main() {
    let args = EthCli::parse();
    match execute(args) {
        Ok(report) => print!("{report}"),
        Err(error) => {
            eprintln!("eth: {error}");
            std::process::exit(2);
        }
    }
}
