use pikelet_cli::Options;
use structopt::StructOpt;

fn main() -> anyhow::Result<()> {
    pikelet_cli::run(Options::from_args())
}
