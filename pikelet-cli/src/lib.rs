use std::error::Error;

pub mod repl;

/// The Pikelet command line interface.
#[derive(structopt::StructOpt)]
#[structopt(name = "mltt")]
pub enum Options {
    /// Type check some files (not yet implemented).
    #[structopt(name = "check")]
    Check,
    /// Runs the structured editor.
    #[cfg(feature = "editor")]
    #[structopt(name = "editor")]
    Editor,
    /// Runs the language server.
    #[cfg(feature = "language-server")]
    #[structopt(name = "language-server")]
    LanguageServer,
    /// Runs the REPL/interactive mode.
    #[structopt(name = "repl")]
    Repl(repl::Options),
}

/// Run the CLI with the given options
pub fn run(options: Options) -> Result<(), Box<dyn Error>> {
    match options {
        Options::Check => Err("not yet implemented".into()),
        #[cfg(feature = "editor")]
        Options::Editor => {
            pikelet_editor::run();
            Ok(())
        }
        #[cfg(feature = "language-server")]
        Options::LanguageServer => pikelet_language_server::run(),
        Options::Repl(options) => repl::run(options),
    }
}
