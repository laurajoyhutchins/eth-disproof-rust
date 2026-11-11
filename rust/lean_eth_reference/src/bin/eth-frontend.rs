//! Compatibility entry point for the source-defined physical frontend.
use clap::Parser;
use lean_eth_reference::cli::{FrontendArgs, frontend};

#[derive(Parser)]
#[command(about = "Run the source-defined physical frontend; does not count #SAT")]
struct Cli {
    #[command(flatten)]
    args: FrontendArgs,
}

fn main() {
    match frontend(&Cli::parse().args) {
        Ok(report) => print!("{report}"),
        Err(error) => {
            eprintln!("eth-frontend: {error}");
            std::process::exit(2);
        }
    }
}
