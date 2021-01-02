//! The surface language.
//!
//! This is a user-friendly concrete syntax for the language.

use crossbeam_channel::Sender;

use crate::lang::{FileId, Located, Location};
use crate::reporting::Message;

mod lexer;

#[allow(clippy::all, unused_parens)]
mod grammar {
    include!(concat!(env!("OUT_DIR"), "/lang/surface/grammar.rs"));
}

/// Entry in a [record type](Term::RecordType).
pub type TypeEntry = (Located<String>, Option<Located<String>>, Term);
/// Entry in a [record term](Term::RecordTerm).
pub type TermEntry = (Located<String>, Option<Located<String>>, Term);
/// A group of function inputs that are elements of the same type.
pub type InputGroup = (Vec<Located<String>>, Term);

pub type Term = Located<TermData>;

/// Terms in the surface language.
#[derive(Debug, Clone)]
pub enum TermData {
    /// Names.
    Name(String),

    /// Annotated terms.
    Ann(Box<Term>, Box<Term>),

    /// Function types.
    ///
    /// Also known as: pi type, dependent product type.
    FunctionType(Vec<InputGroup>, Box<Term>),
    /// Arrow function types.
    ///
    /// Also known as: non-dependent function type.
    FunctionArrowType(Box<Term>, Box<Term>),
    /// Function terms.
    ///
    /// Also known as: lambda abstraction, anonymous function.
    FunctionTerm(Vec<Located<String>>, Box<Term>),
    /// Function eliminations.
    ///
    /// Also known as: function application.
    FunctionElim(Box<Term>, Vec<Term>),

    /// Record types.
    RecordType(Vec<TypeEntry>),
    /// Record terms.
    RecordTerm(Vec<TermEntry>),
    /// Record eliminations.
    ///
    /// Also known as: record projections, field lookup.
    RecordElim(Box<Term>, Located<String>),

    /// Enumeration types.
    ///
    /// Also known as: finite sets, enumeration set.
    EnumType(Vec<String>),
    /// Enumeration terms.
    EnumTerm(String),

    /// Ordered sequences.
    SequenceTerm(Vec<Term>),
    /// Character literals.
    CharTerm(String),
    /// String literals.
    StringTerm(String),
    /// Numeric literals.
    NumberTerm(String),

    /// Error sentinel.
    Error,
}

impl<'input> Term {
    /// Parse a term from an input string.
    #[allow(clippy::should_implement_trait)]
    pub fn from_str(file_id: FileId, input: &str, messages_tx: &Sender<Message>) -> Term {
        let tokens = lexer::tokens(file_id, input);
        grammar::TermParser::new()
            .parse(file_id, tokens)
            .unwrap_or_else(|error| {
                messages_tx
                    .send(Message::from_lalrpop(file_id, error))
                    .unwrap();
                Term::new(
                    Location::file_range(file_id, 0..input.len()),
                    TermData::Error,
                )
            })
    }
}
