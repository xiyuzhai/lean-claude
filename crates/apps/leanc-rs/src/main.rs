use anyhow::Result;
use clap::Parser;

#[derive(Parser, Debug)]
#[command(name = "leanc-rs")]
#[command(about = "Lean compiler written in Rust", long_about = None)]
struct Args {
    /// Input file to compile
    input: String,

    /// Output file (optional)
    #[arg(short, long)]
    output: Option<String>,

    /// Enable verbose output
    #[arg(short, long)]
    verbose: bool,
}

fn main() -> Result<()> {
    let args = Args::parse();

    if args.verbose {
        tracing_subscriber::fmt()
            .with_max_level(tracing::Level::DEBUG)
            .init();
    } else {
        tracing_subscriber::fmt()
            .with_max_level(tracing::Level::INFO)
            .init();
    }

    println!("Compiling: {}", args.input);

    // TODO: Implement compilation pipeline

    Ok(())
}
