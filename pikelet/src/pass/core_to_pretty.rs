//! Pretty prints the [core language] to a [pretty] document.
//!
//! [core language]: crate::lang::core

use pretty::{DocAllocator, DocBuilder};

use crate::lang::core::{Constant, Term, TermData};

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
    match &term.data {
        TermData::Global(name) => (alloc.nil())
            .append(alloc.text("global"))
            .append(alloc.space())
            .append(alloc.text(name)),
        TermData::Local(local_index) => (alloc.nil())
            .append(alloc.text("local"))
            .append(alloc.space())
            .append(alloc.as_string(local_index.0)),

        TermData::Ann(term, r#type) => paren(
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

        TermData::TypeType => alloc.text("Type"),

        TermData::FunctionType(_, input_type, output_type) => paren(
            alloc,
            prec > Prec::Arrow,
            (alloc.nil())
                .append(from_term_prec(alloc, input_type, Prec::App))
                .append(alloc.space())
                .append("->")
                .append(alloc.space())
                .append(from_term_prec(alloc, output_type, Prec::Arrow)),
        ),
        TermData::FunctionTerm(_, output_term) => paren(
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
        TermData::FunctionElim(head_term, input_term) => paren(
            alloc,
            prec > Prec::App,
            from_term_prec(alloc, head_term, Prec::App).append(
                (alloc.space())
                    .append(from_term_prec(alloc, input_term, Prec::Arrow))
                    .group()
                    .nest(4),
            ),
        ),

        TermData::RecordType(type_entries) => (alloc.nil())
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
        TermData::RecordTerm(term_entries) => (alloc.nil())
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
        TermData::RecordElim(head_term, label) => (alloc.nil())
            .append(from_term_prec(alloc, head_term, Prec::Atomic))
            .append(".")
            .append(alloc.text(label)),

        TermData::EnumType(labels) => (alloc.nil())
            .append("Enum")
            .append(alloc.space())
            .append("{")
            .group()
            .append(alloc.concat(labels.iter().map(|label| {
                (alloc.nil())
                    .append(alloc.hardline())
                    .append(alloc.text(label))
                    .append(",")
                    .group()
                    .nest(4)
                    .group()
            })))
            .append("}"),
        TermData::EnumTerm(label) => (alloc.nil())
            .append("enum")
            .append(alloc.space())
            .append(alloc.text(label)),
        TermData::EnumElim(clauses) => todo!(),

        TermData::ArrayTerm(term_entries) | TermData::ListTerm(term_entries) => (alloc.nil())
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

        TermData::Constant(constant) => from_constant(alloc, constant),

        TermData::Error => alloc.text("!"),
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
