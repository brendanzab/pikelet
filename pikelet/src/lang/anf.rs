//! The A-normal form language, with types preserved.
//!
//! This language makes an explicit distinction between _computations_ and
//! _values_, and makes the evaluation indifferent to the order in which
//! computations are executed (somewhat like [applicative functors in
//! Haskell][applicative-functors]). It does this through alterations to the
//! syntactic structure of the [core language][crate::lang::core], while
//! avoiding making many significant changes to the type structure which
//! would make type preservation more challenging.
//!
//! The main inspiration for this language is William Bowman's dissertation,
//! [Compiling with Dependent Types][wjb-dissertation].
//!
//! Note: the 'A' in 'A-Normal Form' does not stand for anything, at least
//! [according to one of the original authors, Matthias Felleisen][just-a].
//! I really wish there was a better name for this language.
//!
//! [applicative-functors]: https://wiki.haskell.org/Applicative_functor
//! [wjb-dissertation]: https://www.williamjbowman.com/resources/wjb-dissertation.pdf
//! [just-a]: https://vimeo.com/387739817

pub use crate::lang::core::{Constant, LocalIndex, UniverseLevel, UniverseOffset};

/// Values are terms that do not reduce.
pub enum Value {
    /// Global variables.
    Global(String),
    /// Local variables.
    Local(LocalIndex),

    /// Annotated values
    Ann(Box<Value>, Box<Configuration>),

    /// The type of types.
    TypeType(UniverseLevel),
    /// Lift a value by the given number of universe levels.
    Lift(Box<Value>, UniverseOffset),

    /// Function types.
    ///
    /// Also known as: pi type, dependent product type.
    FunctionType(Option<String>, Box<Configuration>, Box<Configuration>),
    /// Function terms.
    ///
    /// Also known as: lambda abstraction, anonymous function.
    FunctionTerm(String, Box<Configuration>),

    /// Record types.
    RecordType(Vec<(String, Box<Configuration>)>),
    /// Record terms.
    RecordTerm(Vec<(String, Box<Value>)>),

    /// Constants.
    Constant(Constant),

    /// Error sentinel.
    Error,
}

/// Computations eliminate values.
pub enum Computation {
    /// Values.
    Value(Box<Value>),
    /// Function eliminations.
    ///
    /// Also known as: function application.
    FunctionElim(Box<Value>, Box<Value>),
    /// Record eliminations.
    ///
    /// Also known as: record projection, field lookup.
    RecordElim(Box<Value>, String),
}

/// Programs that are ready to be executed.
pub struct Configuration {
    /// A list of computations to be used when we execute this program.
    pub bindings: Vec<Computation>,
    /// The final output of the program.
    pub output: Computation,
}
