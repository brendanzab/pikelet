use std::error::Error;

pub mod repl;

/// The Pikelet command line interface.
#[derive(structopt::StructOpt)]
#[structopt(name = "mltt")]
pub enum Options {
    /// Type check some files (not yet implemented).
    #[structopt(name = "check")]
    Check,
    /// Runs the language server/IDE support (not yet implemented).
    #[cfg(feature = "ide")]
    #[structopt(name = "ide")]
    Ide,
    /// Runs the REPL/interactive mode.
    #[structopt(name = "repl")]
    Repl(repl::Options),
    /// Runs the GUI mode.
    #[cfg(feature = "gui")]
    #[structopt(name = "gui")]
    Gui,
}

/// Run the CLI with the given options
pub fn run(options: Options) -> Result<(), Box<dyn Error>> {
    match options {
        Options::Check => Err("not yet implemented".into()),
        #[cfg(feature = "ide")]
        Options::Ide => pikelet_ide::run(),
        Options::Repl(options) => repl::run(options),
        #[cfg(feature = "gui")]
        Options::Gui => {
            pikelet_gui::run();
            Ok(())
        }
    }
}
