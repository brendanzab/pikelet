//! The surface language.
//!
//! This is a user-friendly concrete syntax for the language.

use crate::lang::Ranged;

mod lexer;

#[allow(clippy::all, unused_parens)]
mod grammar {
    include!(concat!(env!("OUT_DIR"), "/lang/surface/grammar.rs"));
}

/// Literals.
#[derive(Debug, Clone)]
pub enum Literal<S> {
    /// Character literals.
    Char(S),
    /// String literals.
    String(S),
    /// Numeric literals.
    Number(S),
}

/// Entry in a [record type](Term::RecordType).
pub type TypeEntry<S> = (Ranged<S>, Option<Ranged<S>>, Term<S>);
/// Entry in a [record term](Term::RecordTerm).
pub type TermEntry<S> = (Ranged<S>, Term<S>);
/// A group of function inputs that are elements of the same type.
pub type InputGroup<S> = (Vec<Ranged<S>>, Term<S>);

pub type Term<S> = Ranged<TermData<S>>;

/// Terms in the surface language.
#[derive(Debug, Clone)]
pub enum TermData<S> {
    /// Names.
    Name(S),

    /// Annotated terms.
    Ann(Box<Term<S>>, Box<Term<S>>),

    /// Lift a term by the given number of universe levels.
    Lift(Box<Term<S>>, u32),

    /// Function types.
    ///
    /// Also known as: pi type, dependent product type.
    FunctionType(Vec<InputGroup<S>>, Box<Term<S>>),
    /// Arrow function types.
    ///
    /// Also known as: non-dependent function type.
    FunctionArrowType(Box<Term<S>>, Box<Term<S>>),
    /// Function terms.
    ///
    /// Also known as: lambda abstraction, anonymous function.
    FunctionTerm(Vec<Ranged<S>>, Box<Term<S>>),
    /// Function eliminations.
    ///
    /// Also known as: function application.
    FunctionElim(Box<Term<S>>, Vec<Term<S>>),

    /// Record types.
    RecordType(Vec<TypeEntry<S>>),
    /// Record terms.
    RecordTerm(Vec<TermEntry<S>>),
    /// Record eliminations.
    ///
    /// Also known as: record projections, field lookup.
    RecordElim(Box<Term<S>>, Ranged<S>),

    /// Ordered sequences.
    Sequence(Vec<Term<S>>),

    /// Literals.
    Literal(Literal<S>),

    /// Error sentinel.
    Error,
}

type ParseError<'input> = lalrpop_util::ParseError<usize, lexer::Token<'input>, lexer::LexerError>;

impl<'input> Term<&'input str> {
    /// Parse a term from an input string.
    #[allow(clippy::should_implement_trait)]
    pub fn from_str(input: &'input str) -> Result<Term<&'input str>, ParseError<'input>> {
        let tokens = lexer::tokens(input);
        grammar::TermParser::new().parse(tokens)
    }
}
