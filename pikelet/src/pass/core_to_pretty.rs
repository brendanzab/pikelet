//! Pretty prints the core language to a textual form.

use pretty::{DocAllocator, DocBuilder};

use crate::lang::core::{Constant, Term};

/// The precedence of a term.
#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Prec {
    Term = 0,
    Expr,
    Arrow,
    App,
    Atomic,
}

pub fn from_term<'a, D>(alloc: &'a D, term: &'a Term) -> DocBuilder<'a, D>
where
    D: DocAllocator<'a>,
    D::Doc: Clone,
{
    from_term_prec(alloc, term, Prec::Term)
}

pub fn from_term_prec<'a, D>(alloc: &'a D, term: &'a Term, prec: Prec) -> DocBuilder<'a, D>
where
    D: DocAllocator<'a>,
    D::Doc: Clone,
{
    match term {
        Term::Global(name) => (alloc.nil())
            .append(alloc.text("global"))
            .append(alloc.space())
            .append(alloc.text(name)),
        Term::Local(index) => (alloc.nil())
            .append(alloc.text("local"))
            .append(alloc.space())
            .append(alloc.as_string(index.0)),

        Term::Ann(term, r#type) => paren(
            alloc,
            prec > Prec::Term,
            (alloc.nil())
                .append(from_term_prec(alloc, term, Prec::Expr))
                .append(alloc.space())
                .append(":")
                .append(
                    (alloc.space())
                        .append(from_term_prec(alloc, r#type, Prec::Term))
                        .group()
                        .nest(4),
                ),
        ),

        Term::Universe(level) => (alloc.nil())
            .append("Type")
            .append("^")
            .append(alloc.as_string(level.0)),
        Term::Lift(term, shift) => (alloc.nil())
            .append(from_term_prec(alloc, term, Prec::Atomic))
            .append("^")
            .append(alloc.as_string(shift.0)),

        Term::FunctionType(_, input_type, output_type) => paren(
            alloc,
            prec > Prec::Arrow,
            (alloc.nil())
                .append(from_term_prec(alloc, input_type, Prec::App))
                .append(alloc.space())
                .append("->")
                .append(alloc.space())
                .append(from_term_prec(alloc, output_type, Prec::Arrow)),
        ),
        Term::FunctionTerm(_, output_term) => paren(
            alloc,
            prec > Prec::Expr,
            (alloc.nil())
                .append("fun")
                .append(alloc.space())
                .append("_")
                .append(alloc.space())
                .append("=>")
                .group()
                .append(alloc.space())
                .append(from_term_prec(alloc, output_term, Prec::Expr).nest(4)),
        ),
        Term::FunctionElim(head_term, input_term) => paren(
            alloc,
            prec > Prec::App,
            from_term_prec(alloc, head_term, Prec::App).append(
                (alloc.space())
                    .append(from_term_prec(alloc, input_term, Prec::Arrow))
                    .group()
                    .nest(4),
            ),
        ),

        Term::RecordType(type_entries) => (alloc.nil())
            .append("Record")
            .append(alloc.space())
            .append("{")
            .group()
            .append(alloc.concat(type_entries.iter().map(|(label, r#type)| {
                (alloc.nil())
                    .append(alloc.hardline())
                    .append(alloc.text(label))
                    .append(alloc.space())
                    .append(":")
                    .group()
                    .append(
                        (alloc.space())
                            .append(from_term_prec(alloc, r#type, Prec::Term))
                            .append(",")
                            .group()
                            .nest(4),
                    )
                    .nest(4)
                    .group()
            })))
            .append("}"),
        Term::RecordTerm(term_entries) => (alloc.nil())
            .append("record")
            .append(alloc.space())
            .append("{")
            .group()
            .append(alloc.concat(term_entries.iter().map(|(label, term)| {
                (alloc.nil())
                    .append(alloc.hardline())
                    .append(alloc.text(label))
                    .append(alloc.space())
                    .append("=")
                    .group()
                    .append(
                        (alloc.space())
                            .append(from_term_prec(alloc, term, Prec::Term))
                            .append(",")
                            .group()
                            .nest(4),
                    )
                    .nest(4)
                    .group()
            })))
            .append("}"),
        Term::RecordElim(head_term, label) => (alloc.nil())
            .append(from_term_prec(alloc, head_term, Prec::Atomic))
            .append(".")
            .append(alloc.text(label)),

        Term::Sequence(term_entries) => (alloc.nil())
            .append("[")
            .group()
            .append(
                alloc.intersperse(
                    term_entries
                        .iter()
                        .map(|term| from_term_prec(alloc, term, Prec::Term).group().nest(4)),
                    alloc.text(",").append(alloc.space()),
                ),
            )
            .append("]"),

        Term::Constant(constant) => from_constant(alloc, constant),

        Term::Error => alloc.text("!"),
    }
}

pub fn from_constant<'a, D>(alloc: &'a D, constant: &'a Constant) -> DocBuilder<'a, D>
where
    D: DocAllocator<'a>,
    D::Doc: Clone,
{
    match constant {
        Constant::U8(value) => alloc.text(format!("{}", value)),
        Constant::U16(value) => alloc.text(format!("{}", value)),
        Constant::U32(value) => alloc.text(format!("{}", value)),
        Constant::U64(value) => alloc.text(format!("{}", value)),
        Constant::S8(value) => alloc.text(format!("{}", value)),
        Constant::S16(value) => alloc.text(format!("{}", value)),
        Constant::S32(value) => alloc.text(format!("{}", value)),
        Constant::S64(value) => alloc.text(format!("{}", value)),
        Constant::F32(value) => alloc.text(format!("{}", value)),
        Constant::F64(value) => alloc.text(format!("{}", value)),
        Constant::Char(value) => alloc.text(format!("{:?}", value)),
        Constant::String(value) => alloc.text(format!("{:?}", value)),
    }
}

fn paren<'a, D>(alloc: &'a D, b: bool, doc: DocBuilder<'a, D>) -> DocBuilder<'a, D>
where
    D: DocAllocator<'a>,
    D::Doc: Clone,
{
    if b {
        alloc.text("(").append(doc).append(")")
    } else {
        doc
    }
}
