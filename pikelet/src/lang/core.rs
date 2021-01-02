//! The core language.
//!
//! This is not intended to be used directly by users of the programming
//! language.

use std::collections::BTreeMap;
use std::fmt;
use std::sync::Arc;

use crate::lang::Located;

pub mod marshall;
pub mod semantics;
pub mod typing;

/// Constants used in the core language.
// FIXME: Partial eq for floating point numbers
#[derive(Clone, Debug, PartialEq)]
pub enum Constant {
    /// 8-bit unsigned integers.
    U8(u8),
    /// 16-bit unsigned integers.
    U16(u16),
    /// 32-bit unsigned integers.
    U32(u32),
    /// 64-bit unsigned integers.
    U64(u64),
    /// 8-bit signed [two's complement] integers.
    ///
    /// [two's complement]: https://en.wikipedia.org/wiki/Two%27s_complement
    S8(i8),
    /// 16-bit signed [two's complement] integers.
    ///
    /// [two's complement]: https://en.wikipedia.org/wiki/Two%27s_complement
    S16(i16),
    /// 32-bit signed [two's complement] integers.
    ///
    /// [two's complement]: https://en.wikipedia.org/wiki/Two%27s_complement
    S32(i32),
    /// 64-bit signed [two's complement] integers.
    ///
    /// [two's complement]: https://en.wikipedia.org/wiki/Two%27s_complement
    S64(i64),
    /// 32-bit [IEEE-754] floating point numbers.
    ///
    /// [IEEE-754]: https://en.wikipedia.org/wiki/IEEE_754
    F32(f32),
    /// 64-bit [IEEE-754] floating point numbers.
    ///
    /// [IEEE-754]: https://en.wikipedia.org/wiki/IEEE_754
    F64(f64),
    /// [Unicode scalar values](http://www.unicode.org/glossary/#unicode_scalar_value).
    Char(char),
    /// [UTF-8] encoded strings.
    ///
    /// [UTF-8]: http://www.unicode.org/glossary/#UTF_8
    String(String),
}

pub type Term = Located<TermData>;

/// Terms in the core language.
#[derive(Clone, Debug)]
pub enum TermData {
    /// Global variables.
    Global(String),
    /// Local variables.
    Local(LocalIndex),

    /// Annotated terms
    Ann(Arc<Term>, Arc<Term>),

    /// The type of types.
    TypeType,

    /// Function types.
    ///
    /// Also known as: pi type, dependent product type.
    FunctionType(Option<String>, Arc<Term>, Arc<Term>),
    /// Function terms.
    ///
    /// Also known as: lambda abstraction, anonymous function.
    FunctionTerm(String, Arc<Term>),
    /// Function eliminations.
    ///
    /// Also known as: function application.
    FunctionElim(Arc<Term>, Arc<Term>),

    /// Record types.
    RecordType(Arc<[(String, Arc<Term>)]>),
    /// Record terms.
    RecordTerm(Arc<[(String, Arc<Term>)]>),
    /// Record eliminations.
    ///
    /// Also known as: record projection, field lookup.
    RecordElim(Arc<Term>, String),

    /// Enumeration types.
    ///
    /// Also known as: finite sets, enumeration set.
    EnumType(Arc<[String]>),
    /// Enumeration terms.
    EnumTerm(String),
    /// Enumeration eliminations.
    ///
    /// Also known as: case split.
    EnumElim(Arc<[(String, Arc<Term>)]>),

    /// Array terms.
    ArrayTerm(Vec<Arc<Term>>),
    /// List terms.
    ListTerm(Vec<Arc<Term>>),

    /// Constants.
    Constant(Constant),

    /// Error sentinel.
    Error,
}

impl From<Constant> for TermData {
    fn from(constant: Constant) -> TermData {
        TermData::Constant(constant)
    }
}

/// An environment of global definitions.
pub struct Globals {
    entries: BTreeMap<String, (Arc<Term>, Option<Arc<Term>>)>,
}

impl Globals {
    pub fn new(entries: BTreeMap<String, (Arc<Term>, Option<Arc<Term>>)>) -> Globals {
        Globals { entries }
    }

    pub fn get(&self, name: &str) -> Option<&(Arc<Term>, Option<Arc<Term>>)> {
        self.entries.get(name)
    }

    pub fn entries(&self) -> impl Iterator<Item = (&String, &(Arc<Term>, Option<Arc<Term>>))> {
        self.entries.iter()
    }
}

impl Default for Globals {
    fn default() -> Globals {
        let mut entries = BTreeMap::new();

        let global = |name: &str| Arc::new(Term::generated(TermData::Global(name.to_owned())));
        let type_type = || Arc::new(Term::generated(TermData::TypeType));
        let function_type = |input_type, output_type| {
            Arc::new(Term::generated(TermData::FunctionType(
                None,
                input_type,
                output_type,
            )))
        };

        entries.insert("Type".to_owned(), (type_type(), Some(type_type())));
        entries.insert("U8".to_owned(), (global("Type"), None));
        entries.insert("U16".to_owned(), (global("Type"), None));
        entries.insert("U32".to_owned(), (global("Type"), None));
        entries.insert("U64".to_owned(), (global("Type"), None));
        entries.insert("S8".to_owned(), (global("Type"), None));
        entries.insert("S16".to_owned(), (global("Type"), None));
        entries.insert("S32".to_owned(), (global("Type"), None));
        entries.insert("S64".to_owned(), (global("Type"), None));
        entries.insert("F32".to_owned(), (global("Type"), None));
        entries.insert("F64".to_owned(), (global("Type"), None));
        entries.insert("Char".to_owned(), (global("Type"), None));
        entries.insert("String".to_owned(), (global("Type"), None));
        entries.insert(
            "Bool".to_owned(),
            (
                global("Type"),
                Some(Arc::new(Term::generated(TermData::EnumType(
                    vec!["false".to_owned(), "true".to_owned()].into(),
                )))),
            ),
        );
        entries.insert(
            "true".to_owned(),
            (
                global("Bool"),
                Some(Arc::new(Term::generated(TermData::EnumTerm(
                    "true".to_owned(),
                )))),
            ),
        );
        entries.insert(
            "false".to_owned(),
            (
                global("Bool"),
                Some(Arc::new(Term::generated(TermData::EnumTerm(
                    "false".to_owned(),
                )))),
            ),
        );
        entries.insert(
            "Array".to_owned(),
            (
                function_type(global("U32"), function_type(type_type(), type_type())),
                None,
            ),
        );
        entries.insert(
            "List".to_owned(),
            (function_type(type_type(), type_type()), None),
        );

        Globals::new(entries)
    }
}

/// A [de Bruijn index][de-bruijn-index] in the [local environment].
///
/// De Bruijn indices describe an occurrence of a variable in terms of the
/// number of binders between the occurrence and its associated binder.
/// For example:
///
/// | Representation    | Example (S combinator)  |
/// | ----------------- | ----------------------- |
/// | Named             | `λx. λy. λz. x z (y z)` |
/// | De Bruijn indices | `λ_. λ_. λ_. 2 0 (1 0)` |
///
/// This is a helpful representation because it allows us to easily compare
/// terms for equivalence based on their binding structure without maintaining a
/// list of name substitutions. For example we want `λx. x` to be the same as
/// `λy. y`. With de Bruijn indices these would both be described as `λ 0`.
///
/// [local environment]: `Locals`
/// [de-bruijn-index]: https://en.wikipedia.org/wiki/De_Bruijn_index
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct LocalIndex(pub u32);

/// A de Bruijn level in the [local environment].
///
/// This describes an occurrence of a variable by counting the binders inwards
/// from the top of the term until the occurrence is reached. For example:
///
/// | Representation    | Example (S combinator)  |
/// | ----------------- | ----------------------- |
/// | Named             | `λx. λy. λz. x z (y z)` |
/// | De Bruijn levels  | `λ_. λ_. λ_. 0 2 (1 2)` |
///
/// Levels are used in [values][semantics::Value] because they are not context-
/// dependent (this is in contrast to [indices][LocalIndex]). Because of this,
/// we're able to sidestep the need for expensive variable shifting in the
/// semantics. More information can be found in Soham Chowdhury's blog post,
/// “[Real-world type theory I: untyped normalisation by evaluation for λ-calculus][untyped-nbe-for-lc]”.
///
/// [local environment]: `Locals`
/// [untyped-nbe-for-lc]: https://colimit.net/posts/normalisation-by-evaluation/
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct LocalLevel(u32);

/// The size, or 'binding depth', of the [local environment].
///
/// This is used for [index-to-level] and [level-to-index] conversions.
///
/// [local environment]: `Locals`
/// [index-to-level]: `LocalSize::index_to_level`
/// [level-to-index]: `LocalSize::level_to_index`
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct LocalSize(u32);

impl LocalSize {
    pub fn increment(self) -> LocalSize {
        LocalSize(self.0 + 1)
    }

    /// Return the level of the next variable to be added to the environment.
    pub fn next_level(self) -> LocalLevel {
        LocalLevel(self.0)
    }

    /// Convert a local index to a local level in the current environment.
    ///
    /// `None` is returned if the local environment is not large enough to
    /// contain the local variable.
    pub fn index_to_level(self, local_index: LocalIndex) -> Option<LocalLevel> {
        let local_level = self.0.checked_sub(local_index.0)?.checked_sub(1)?;
        Some(LocalLevel(local_level))
    }

    /// Convert a local level to a local index in the current environment.
    ///
    /// `None` is returned if the local environment is not large enough to
    /// contain the local variable.
    pub fn level_to_index(self, local_level: LocalLevel) -> Option<LocalIndex> {
        let local_index = self.0.checked_sub(local_level.0)?.checked_sub(1)?;
        Some(LocalIndex(local_index))
    }
}

/// A local environment.
#[derive(Clone)]
pub struct Locals<Entry> {
    /// The local entries that are currently defined in the environment.
    entries: im::Vector<Entry>,
}

impl<Entry: Clone> Locals<Entry> {
    /// Create a new local environment.
    pub fn new() -> Locals<Entry> {
        Locals {
            entries: im::Vector::new(),
        }
    }

    /// Get the size of the environment.
    pub fn size(&self) -> LocalSize {
        LocalSize(self.entries.len() as u32) // FIXME: Check for overflow?
    }

    /// Lookup an entry in the environment.
    pub fn get(&self, local_index: LocalIndex) -> Option<&Entry> {
        let entry_index = (self.entries.len())
            .checked_sub(local_index.0 as usize)?
            .checked_sub(1)?;
        self.entries.get(entry_index)
    }

    /// Push an entry onto the environment.
    pub fn push(&mut self, entry: Entry) {
        self.entries.push_back(entry);
    }

    /// Pop an entry off the environment.
    pub fn pop(&mut self) -> Option<Entry> {
        self.entries.pop_back()
    }

    /// Pop a number of entries off the environment.
    pub fn pop_many(&mut self, count: usize) {
        self.entries
            .truncate(self.entries.len().saturating_sub(count));
    }

    /// Clear the entries from the environment.
    pub fn clear(&mut self) {
        self.entries.clear();
    }

    /// Returns a reverse iterator over the entries in the environment and the
    /// indices where those entries were bound.
    pub fn iter_rev(&self) -> impl Iterator<Item = (LocalIndex, &Entry)> {
        (self.entries.iter().rev()).scan(0, |current_index, entry| {
            let local_index = LocalIndex(std::mem::replace(current_index, *current_index + 1));
            Some((local_index, entry))
        })
    }
}

impl<Entry: Clone + fmt::Debug> fmt::Debug for Locals<Entry> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Locals")
            .field("entries", &self.entries)
            .finish()
    }
}
