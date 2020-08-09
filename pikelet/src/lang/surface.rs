//! The surface language.
//!
//! This is a user-friendly concrete syntax for the language.

use std::ops::{Range, RangeFrom};

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
pub type TypeEntry<S> = (Range<usize>, S, Option<S>, Term<S>);
/// Entry in a [record term](Term::RecordTerm).
pub type TermEntry<S> = (Range<usize>, S, Term<S>);
/// A group of function parameters that are elements of the same type.
pub type ParameterGroup<S> = (Vec<(Range<usize>, S)>, Term<S>);

/// Terms in the surface language.
#[derive(Debug, Clone)]
pub enum Term<S> {
    /// Names.
    Name(Range<usize>, S),
    /// Annotated terms.
    Ann(Box<Term<S>>, Box<Term<S>>),
    /// Literals.
    Literal(Range<usize>, Literal<S>),
    /// Ordered sequences.
    Sequence(Range<usize>, Vec<Term<S>>),
    /// Record types.
    RecordType(Range<usize>, Vec<TypeEntry<S>>),
    /// Record terms.
    RecordTerm(Range<usize>, Vec<TermEntry<S>>),
    /// Record eliminations.
    ///
    /// Also known as: record projections, field lookup.
    RecordElim(Box<Term<S>>, Range<usize>, S),
    /// Function types.
    ///
    /// Also known as: pi type, dependent product type.
    FunctionType(RangeFrom<usize>, Vec<ParameterGroup<S>>, Box<Term<S>>),
    /// Arrow function types.
    ///
    /// Also known as: non-dependent function type.
    FunctionArrowType(Box<Term<S>>, Box<Term<S>>),
    /// Function terms.
    ///
    /// Also known as: lambda abstraction, anonymous function.
    FunctionTerm(RangeFrom<usize>, Vec<(Range<usize>, S)>, Box<Term<S>>),
    /// Function eliminations.
    ///
    /// Also known as: function application.
    FunctionElim(Box<Term<S>>, Vec<Term<S>>),
    /// Lift a term by the given number of universe levels.
    Lift(Range<usize>, Box<Term<S>>, u32),
    /// Error sentinel.
    Error(Range<usize>),
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

impl<T> Term<T> {
    /// Return the source range of the term.
    pub fn range(&self) -> Range<usize> {
        match self {
            Term::Name(range, _)
            | Term::Literal(range, _)
            | Term::Sequence(range, _)
            | Term::RecordType(range, _)
            | Term::RecordTerm(range, _)
            | Term::Lift(range, _, _)
            | Term::Error(range) => range.clone(),
            Term::Ann(term, r#type) => term.range().start..r#type.range().end,
            Term::RecordElim(term, label_range, _) => term.range().start..label_range.end,
            Term::FunctionType(range, _, body_type) => range.start..body_type.range().end,
            Term::FunctionArrowType(param_type, body_type) => {
                param_type.range().start..body_type.range().end
            }
            Term::FunctionTerm(range, _, body) => range.start..body.range().end,
            Term::FunctionElim(head, arguments) => match arguments.last() {
                Some(argument) => head.range().start..argument.range().end,
                None => head.range(),
            },
        }
    }
}
