//! Pretty prints the surface language to a textual form.

use pretty::{DocAllocator, DocBuilder};

use crate::lang::surface::{Literal, Term};

/// The precedence of a term.
#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Prec {
    Term = 0,
    Expr,
    Arrow,
    App,
    Atomic,
}

pub fn from_term<'a, D, S>(alloc: &'a D, term: &'a Term<S>) -> DocBuilder<'a, D>
where
    S: 'a + AsRef<str>,
    D: DocAllocator<'a>,
    D::Doc: Clone,
{
    from_term_prec(alloc, term, Prec::Term)
}

pub fn from_term_prec<'a, D, S>(alloc: &'a D, term: &'a Term<S>, prec: Prec) -> DocBuilder<'a, D>
where
    S: 'a + AsRef<str>,
    D: DocAllocator<'a>,
    D::Doc: Clone,
{
    match term {
        Term::Name(_, name) => alloc.text(name.as_ref()),

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

        Term::Lift(_, term, shift) => (alloc.nil())
            .append(from_term_prec(alloc, term, Prec::Atomic))
            .append("^")
            .append(shift.to_string()),

        Term::FunctionType(_, input_type_groups, output_type) => paren(
            alloc,
            prec > Prec::Arrow,
            (alloc.nil())
                .append("Fun")
                .append(alloc.space())
                .append(alloc.intersperse(
                    input_type_groups.iter().map(|(input_names, input_type)| {
                        (alloc.nil())
                            .append("(")
                            .append(
                                alloc.intersperse(
                                    input_names
                                        .iter()
                                        .map(|(_, input_name)| input_name.as_ref()),
                                    alloc.space(),
                                ),
                            )
                            .append(alloc.space())
                            .append(":")
                            .append(alloc.space())
                            .append(from_term_prec(alloc, input_type, Prec::Term))
                            .append(")")
                    }),
                    alloc.space(),
                ))
                .append(alloc.space())
                .append("->")
                .group()
                .append(
                    (alloc.nil()).append(alloc.space()).append(
                        from_term_prec(alloc, output_type, Prec::Arrow)
                            .group()
                            .nest(4),
                    ),
                ),
        ),
        Term::FunctionArrowType(input_type, output_type) => paren(
            alloc,
            prec > Prec::Arrow,
            (alloc.nil())
                .append(from_term_prec(alloc, input_type, Prec::App))
                .append(alloc.space())
                .append("->")
                .append(alloc.space())
                .append(from_term_prec(alloc, output_type, Prec::Arrow)),
        ),
        Term::FunctionTerm(_, input_names, output_term) => paren(
            alloc,
            prec > Prec::Expr,
            (alloc.nil())
                .append("fun")
                .append(alloc.space())
                .append(
                    alloc.intersperse(
                        input_names
                            .iter()
                            .map(|(_, input_name)| input_name.as_ref()),
                        alloc.space(),
                    ),
                )
                .append(alloc.space())
                .append("=>")
                .group()
                .append(
                    (alloc.nil()).append(alloc.space()).append(
                        from_term_prec(alloc, output_term, Prec::Expr)
                            .group()
                            .nest(4),
                    ),
                ),
        ),
        Term::FunctionElim(head_term, input_terms) => paren(
            alloc,
            prec > Prec::App,
            from_term_prec(alloc, head_term, Prec::App).append(
                (alloc.nil())
                    .append(alloc.concat(input_terms.iter().map(|input_term| {
                        alloc
                            .space()
                            .append(from_term_prec(alloc, input_term, Prec::Arrow))
                    })))
                    .group()
                    .nest(4),
            ),
        ),

        Term::RecordType(_, type_entries) => (alloc.nil())
            .append("Record")
            .append(alloc.space())
            .append("{")
            .group()
            .append(
                alloc.concat(type_entries.iter().map(|(_, label, name, entry_type)| {
                    (alloc.nil())
                        .append(alloc.hardline())
                        .append(match name {
                            None => alloc.text(label.as_ref()).append(alloc.space()),
                            Some(name) => alloc
                                .text(label.as_ref())
                                .append(alloc.space())
                                .append("as")
                                .append(alloc.space())
                                .append(name.as_ref())
                                .append(alloc.space()),
                        })
                        .append(":")
                        .group()
                        .append(
                            (alloc.space())
                                .append(from_term_prec(alloc, entry_type, Prec::Term))
                                .append(",")
                                .group()
                                .nest(4),
                        )
                        .nest(4)
                        .group()
                })),
            )
            .append("}"),
        Term::RecordTerm(_, term_entries) => (alloc.nil())
            .append("record")
            .append(alloc.space())
            .append("{")
            .group()
            .append(
                alloc.concat(term_entries.iter().map(|(_, label, entry_term)| {
                    (alloc.nil())
                        .append(alloc.hardline())
                        .append(alloc.text(label.as_ref()))
                        .append(alloc.space())
                        .append("=")
                        .group()
                        .append(
                            (alloc.space())
                                .append(from_term_prec(alloc, entry_term, Prec::Term))
                                .append(",")
                                .group()
                                .nest(4),
                        )
                        .nest(4)
                        .group()
                })),
            )
            .append("}"),
        Term::RecordElim(head_term, _, label) => (alloc.nil())
            .append(from_term_prec(alloc, head_term, Prec::Atomic))
            .append(".")
            .append(label.as_ref()),

        Term::Sequence(_, term_entries) => (alloc.nil())
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

        Term::Literal(_, literal) => from_literal(alloc, literal),

        Term::Error(_) => alloc.text("!"),
    }
}

pub fn from_literal<'a, D, S>(alloc: &'a D, literal: &'a Literal<S>) -> DocBuilder<'a, D>
where
    S: 'a + AsRef<str>,
    D: DocAllocator<'a>,
    D::Doc: Clone,
{
    match literal {
        Literal::Char(text) | Literal::String(text) | Literal::Number(text) => {
            alloc.text(text.as_ref())
        }
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
