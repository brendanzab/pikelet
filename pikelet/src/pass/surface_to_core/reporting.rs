use codespan_reporting::diagnostic::{Diagnostic, Label};
use pretty::DocAllocator;
use std::ops::Range;

use crate::lang::surface::Term;

#[derive(Clone, Debug)]
pub enum InvalidLiteral {
    Char,
    String,
    Number,
}

#[derive(Clone, Debug)]
pub enum AmbiguousTerm {
    NumberLiteral,
    Sequence,
    FunctionTerm,
    RecordTerm,
}

#[derive(Clone, Debug)]
pub enum ExpectedType {
    Universe,
    Type(Term<String>),
}

#[derive(Clone, Debug)]
pub enum Message {
    MaximumUniverseLevelReached {
        range: Range<usize>,
    },
    UnboundName {
        range: Range<usize>,
        name: String,
    },
    InvalidRecordType {
        duplicate_labels: Vec<(String, Range<usize>, Range<usize>)>,
    },
    InvalidRecordTerm {
        range: Range<usize>,
        duplicate_labels: Vec<(String, Range<usize>, Range<usize>)>,
        missing_labels: Vec<String>,
        unexpected_labels: Vec<(String, Range<usize>)>,
    },
    LabelNotFound {
        head_range: Range<usize>,
        label_range: Range<usize>,
        expected_label: String,
        head_type: Term<String>,
    },
    TooManyInputsInFunctionTerm {
        unexpected_inputs: Vec<Range<usize>>,
    },
    TooManyInputsInFunctionElim {
        head_range: Range<usize>,
        head_type: Term<String>,
        unexpected_input_terms: Vec<Range<usize>>,
    },
    InvalidLiteral {
        range: Range<usize>,
        literal: InvalidLiteral,
    },
    NoLiteralConversion {
        range: Range<usize>,
        expected_type: Term<String>,
    },
    MismatchedSequenceLength {
        range: Range<usize>,
        found_len: usize,
        expected_len: Term<String>,
    },
    NoSequenceConversion {
        range: Range<usize>,
        expected_type: Term<String>,
    },
    AmbiguousTerm {
        range: Range<usize>,
        term: AmbiguousTerm,
    },
    MismatchedTypes {
        range: Range<usize>,
        found_type: Term<String>,
        expected_type: ExpectedType,
    },
}

impl Message {
    pub fn to_diagnostic<'a, D>(&'a self, pretty_alloc: &'a D) -> Diagnostic<()>
    where
        D: DocAllocator<'a>,
        D::Doc: Clone,
    {
        use itertools::Itertools;

        use crate::pass::surface_to_pretty;

        let to_doc = |term| surface_to_pretty::from_term(pretty_alloc, term).1;

        match self {
            Message::MaximumUniverseLevelReached { range } => Diagnostic::error()
                .with_message("maximum universe level reached")
                .with_labels(vec![
                    Label::primary((), range.clone()).with_message("overflowing universe level")
                ]),

            Message::UnboundName { range, name } => Diagnostic::error()
                .with_message(format!("cannot find `{}` in this scope", name))
                // TODO: name suggestions?
                .with_labels(vec![
                    Label::primary((), range.clone()).with_message("not found in this scope")
                ]),

            Message::InvalidRecordType { duplicate_labels } => Diagnostic::error()
                .with_message("invalid record type")
                .with_labels({
                    let mut labels = Vec::with_capacity(duplicate_labels.len() * 2);

                    for (label, label_range1, label_range2) in duplicate_labels {
                        labels.push(
                            Label::secondary((), label_range1.clone())
                                .with_message(format!("first use of `{}`", label)),
                        );
                        labels.push(
                            Label::primary((), label_range2.clone())
                                .with_message("entry label used more than once"),
                        );
                    }

                    labels
                }),

            Message::InvalidRecordTerm {
                range,
                duplicate_labels,
                missing_labels,
                unexpected_labels,
            } => Diagnostic::error()
                .with_message("invalid record term")
                .with_labels({
                    let mut labels = Vec::with_capacity(
                        duplicate_labels.len() * 2
                            + unexpected_labels.len()
                            + if missing_labels.is_empty() { 0 } else { 1 },
                    );

                    for (label, label_range1, label_range2) in duplicate_labels {
                        labels.push(
                            Label::primary((), label_range1.clone())
                                .with_message(format!("first use of `{}`", label)),
                        );
                        labels.push(
                            Label::primary((), label_range2.clone())
                                .with_message("entry label used more than once"),
                        );
                    }

                    for (_, label_range) in unexpected_labels {
                        labels.push(
                            Label::primary((), label_range.clone())
                                .with_message("unexpected entry label"),
                        );
                    }

                    if !missing_labels.is_empty() {
                        labels.push(Label::primary((), range.clone()).with_message(format!(
                                "missing the labels {} in this record term",
                                missing_labels
                                    .iter()
                                    // TODO: reduce string allocations
                                    .map(|label| format!("`{}`", label))
                                    .format(", "),
                            )));
                    }

                    labels
                }),

            Message::LabelNotFound {
                head_range,
                label_range,
                expected_label,
                head_type,
            } => Diagnostic::error()
                .with_message(format!(
                    "no entry with label `{}` in type `{}`",
                    expected_label,
                    to_doc(&head_type).pretty(std::usize::MAX),
                ))
                .with_labels(vec![
                    Label::primary((), label_range.clone()).with_message("unknown entry label"),
                    Label::secondary((), head_range.clone()).with_message(format!(
                        "the type here is `{}`",
                        to_doc(&head_type).pretty(std::usize::MAX),
                    )),
                ]),

            Message::TooManyInputsInFunctionTerm { unexpected_inputs } => Diagnostic::error()
                .with_message("too many inputs given for function term")
                .with_labels(
                    unexpected_inputs
                        .iter()
                        .map(|input_range| {
                            Label::primary((), input_range.clone()).with_message("unexpected input")
                        })
                        .collect(),
                ),

            Message::TooManyInputsInFunctionElim {
                head_range,
                head_type,
                unexpected_input_terms,
            } => Diagnostic::error()
                .with_message("term was applied to too many inputs")
                .with_labels(
                    std::iter::once(Label::primary((), head_range.clone()).with_message(format!(
                        // TODO: multi-line?
                        "expected a function, found `{}`",
                        to_doc(&head_type).pretty(std::usize::MAX),
                    )))
                    .chain(unexpected_input_terms.iter().map(|input_range| {
                        Label::primary((), input_range.clone())
                            .with_message("unexpected input".to_owned())
                    }))
                    .collect(),
                ),

            Message::InvalidLiteral { range, literal } => Diagnostic::error()
                .with_message(format!(
                    // TODO: supply expected type information
                    "invalid {} literal",
                    match literal {
                        InvalidLiteral::Char => "character",
                        InvalidLiteral::String => "string",
                        InvalidLiteral::Number => "numeric",
                    },
                ))
                .with_labels(vec![
                    Label::primary((), range.clone()).with_message("failed to parse literal")
                ]),

            Message::NoLiteralConversion {
                range,
                expected_type,
            } => Diagnostic::error()
                .with_message("no known literal conversion")
                .with_labels(vec![Label::primary((), range.clone()).with_message(
                    format!(
                        // TODO: multi-line?
                        "expected `{}`, found a literal",
                        to_doc(&expected_type).pretty(std::usize::MAX),
                    ),
                )]),

            Message::MismatchedSequenceLength {
                range,
                found_len,
                expected_len,
            } => Diagnostic::error()
                .with_message("mismatched sequence length")
                .with_labels(vec![Label::primary((), range.clone()).with_message(
                    format!(
                        // TODO: multi-line?
                        "expected `{}` entries, found `{}` entries",
                        to_doc(&expected_len).pretty(std::usize::MAX),
                        found_len,
                    ),
                )]),

            Message::NoSequenceConversion {
                range,
                expected_type,
            } => Diagnostic::error()
                .with_message("no known sequence conversion")
                .with_labels(vec![Label::primary((), range.clone()).with_message(
                    format!(
                        // TODO: multi-line?
                        "expected `{}`, found a sequence",
                        to_doc(&expected_type).pretty(std::usize::MAX),
                    ),
                )]),

            Message::AmbiguousTerm { range, term } => Diagnostic::error()
                .with_message(format!(
                    "ambiguous {}",
                    match term {
                        AmbiguousTerm::NumberLiteral => "numeric literal",
                        AmbiguousTerm::Sequence => "sequence",
                        AmbiguousTerm::FunctionTerm => "function term",
                        AmbiguousTerm::RecordTerm => "record term",
                    },
                ))
                .with_labels(vec![
                    Label::primary((), range.clone()).with_message("type annotations needed")
                ]),

            Message::MismatchedTypes {
                range,
                found_type,
                expected_type,
            } => Diagnostic::error()
                .with_message("mismatched types")
                .with_labels(vec![Label::primary((), range.clone()).with_message(
                    match expected_type {
                        ExpectedType::Universe => format!(
                            // TODO: multi-line?
                            "expected a type, found `{}`",
                            to_doc(&found_type).pretty(std::usize::MAX),
                        ),
                        ExpectedType::Type(expected_type) => format!(
                            // TODO: multi-line?
                            "expected `{}`, found `{}`",
                            to_doc(&expected_type).pretty(std::usize::MAX),
                            to_doc(&found_type).pretty(std::usize::MAX),
                        ),
                    },
                )]),
        }
    }
}
