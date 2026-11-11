//! Compatibility entry point for the restricted source-native terminal counter.
use clap::Parser;
use lean_eth_reference::cli::{TerminalCountArgs, terminal_count};

#[derive(Parser)]
#[command(about = "Count only source-supported terminal CNFs; refuse nonterminal inputs")]
struct Cli {
    #[command(flatten)]
    args: TerminalCountArgs,
}

fn main() {
    match terminal_count(&Cli::parse().args) {
        Ok(report) => print!("{report}"),
        Err(error) => {
            eprintln!("eth-terminal-count: {error}");
            std::process::exit(2);
        }
    }
}
