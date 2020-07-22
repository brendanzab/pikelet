//! Elaborates the surface language into the core language.

use std::ops::Range;
use std::str::FromStr;
use std::sync::Arc;

use crate::lang::core;
use crate::lang::core::semantics::{self, Elim, Head, RecordTypeClosure, Unfold, Value};
use crate::lang::surface::{Literal, Term};
use crate::pass::core_to_surface;

pub mod reporting;

pub use self::reporting::*;

/// The state of the elaborator.
pub struct State<'me> {
    /// Global definition environment.
    globals: &'me core::Globals,
    /// The current universe offset.
    universe_offset: core::UniverseOffset,
    /// Substitutions from the user-defined names to the level in which they were bound.
    names_to_levels: Vec<(Option<String>, core::LocalLevel)>,
    /// Distillation state (used for pretty printing).
    core_to_surface: core_to_surface::State<'me>,
    /// Local type environment (used for getting the types of local variables).
    types: core::Locals<Arc<Value>>,
    /// Local value environment (used for evaluation).
    values: core::Locals<Arc<Value>>,
    /// The diagnostic messages accumulated during elaboration.
    messages: Vec<Message>,
}

impl<'me> State<'me> {
    /// Construct a new elaborator state.
    pub fn new(globals: &'me core::Globals) -> State<'me> {
        State {
            globals,
            universe_offset: core::UniverseOffset(0),
            names_to_levels: Vec::new(),
            core_to_surface: core_to_surface::State::new(globals),
            types: core::Locals::new(),
            values: core::Locals::new(),
            messages: Vec::new(),
        }
    }

    /// Get the next level to be used for a local entry.
    fn next_level(&self) -> core::LocalLevel {
        self.values.size().next_level()
    }

    /// Get a local entry.
    fn get_local(&self, name: &str) -> Option<(core::LocalIndex, &Arc<Value>)> {
        let (_, level) = self.names_to_levels.iter().rev().find(|(n, _)| match n {
            Some(n) => n == name,
            None => false,
        })?;
        let index = self.values.size().index(*level);
        let ty = self.types.get(index)?;
        Some((index, ty))
    }

    /// Push a local entry.
    fn push_local(&mut self, name: Option<&str>, value: Arc<Value>, r#type: Arc<Value>) {
        self.names_to_levels
            .push((name.map(str::to_owned), self.next_level()));
        self.core_to_surface.push_name(name);
        self.types.push(r#type);
        self.values.push(value);
    }

    /// Push a local parameter.
    fn push_local_param(&mut self, name: Option<&str>, r#type: Arc<Value>) -> Arc<Value> {
        let value = Arc::new(Value::local(self.next_level()));
        self.push_local(name, value.clone(), r#type);
        value
    }

    /// Pop a local entry.
    fn pop_local(&mut self) {
        self.core_to_surface.pop_name();
        self.names_to_levels.pop();
        self.types.pop();
        self.values.pop();
    }

    /// Pop the given number of local entries.
    fn pop_many_locals(&mut self, count: usize) {
        self.core_to_surface.pop_many_names(count);
        self.names_to_levels
            .truncate(self.names_to_levels.len().saturating_sub(count));
        self.types.pop_many(count);
        self.values.pop_many(count);
    }

    /// Report a diagnostic message.
    fn report(&mut self, error: Message) {
        self.messages.push(error);
    }

    /// Drain the currently accumulated diagnostic messages.
    pub fn drain_messages(&mut self) -> std::vec::Drain<Message> {
        self.messages.drain(..)
    }

    /// Reset the elaborator state while retaining existing allocations.
    pub fn clear(&mut self) {
        self.universe_offset = core::UniverseOffset(0);
        self.names_to_levels.clear();
        self.types.clear();
        self.values.clear();
        self.messages.clear();
    }

    /// Evaluate a term using the current state of the elaborator.
    pub fn eval_term(&mut self, term: &core::Term) -> Arc<Value> {
        semantics::eval_term(self.globals, self.universe_offset, &mut self.values, term)
    }

    /// Return the type of the record elimination.
    pub fn record_elim_type(
        &mut self,
        head_value: &Value,
        label: &str,
        closure: &RecordTypeClosure,
    ) -> Option<Arc<Value>> {
        semantics::record_elim_type(self.globals, head_value, label, closure)
    }

    /// Normalize a term using the current state of the elaborator.
    pub fn normalize_term(&mut self, term: &core::Term) -> core::Term {
        semantics::normalize_term(self.globals, self.universe_offset, &mut self.values, term)
    }

    /// Read back a value into a normal form using the current state of the elaborator.
    pub fn read_back_value(&mut self, value: &Value) -> core::Term {
        semantics::read_back_value(self.globals, self.values.size(), Unfold::None, value)
    }

    /// Check if `value0` is a subtype of `value1`.
    pub fn is_subtype(&self, value0: &Value, value1: &Value) -> bool {
        semantics::is_subtype(self.globals, self.values.size(), value0, value1)
    }

    /// Distill a `core::Term` into a `surface::Term`.
    pub fn core_to_surface_term(&mut self, core_term: &core::Term) -> Term<String> {
        core_to_surface::from_term(&mut self.core_to_surface, &core_term)
    }
}

/// Check that a term is a type return, and return the elaborated term and the
/// universe level it inhabits.
pub fn is_type<S: AsRef<str>>(
    state: &mut State<'_>,
    term: &Term<S>,
) -> (core::Term, Option<core::UniverseLevel>) {
    let (core_term, r#type) = synth_type(state, term);
    match r#type.force(state.globals) {
        Value::Universe(level) => (core_term, Some(*level)),
        Value::Error => (core::Term::Error, None),
        found_type => {
            let found_type = state.read_back_value(&found_type);
            let found_type = state.core_to_surface_term(&found_type);
            state.report(Message::MismatchedTypes {
                range: term.range(),
                found_type,
                expected_type: ExpectedType::Universe,
            });
            (core::Term::Error, None)
        }
    }
}

/// Check that a term is an element of a type, and return the elaborated term.
pub fn check_type<S: AsRef<str>>(
    state: &mut State<'_>,
    term: &Term<S>,
    expected_type: &Arc<Value>,
) -> core::Term {
    match (term, expected_type.force(state.globals)) {
        (_, Value::Error) => core::Term::Error,
        (Term::Literal(_, literal), Value::Stuck(Head::Global(name, _), spine)) => {
            use crate::lang::core::Constant::*;

            match (literal, name.as_ref(), spine.as_slice()) {
                (Literal::Number(data), "U8", []) => parse_number(state, term.range(), data, U8),
                (Literal::Number(data), "U16", []) => parse_number(state, term.range(), data, U16),
                (Literal::Number(data), "U32", []) => parse_number(state, term.range(), data, U32),
                (Literal::Number(data), "U64", []) => parse_number(state, term.range(), data, U64),
                (Literal::Number(data), "S8", []) => parse_number(state, term.range(), data, S8),
                (Literal::Number(data), "S16", []) => parse_number(state, term.range(), data, S16),
                (Literal::Number(data), "S32", []) => parse_number(state, term.range(), data, S32),
                (Literal::Number(data), "S64", []) => parse_number(state, term.range(), data, S64),
                (Literal::Number(data), "F32", []) => parse_number(state, term.range(), data, F32),
                (Literal::Number(data), "F64", []) => parse_number(state, term.range(), data, F64),
                (Literal::Char(data), "Char", []) => parse_char(state, term.range(), data),
                (Literal::String(data), "String", []) => parse_string(state, term.range(), data),
                (_, _, _) => {
                    let expected_type = state.read_back_value(expected_type);
                    let expected_type = state.core_to_surface_term(&expected_type);
                    state.report(Message::NoLiteralConversion {
                        range: term.range(),
                        expected_type,
                    });
                    core::Term::Error
                }
            }
        }
        (Term::Literal(_, _), _) => {
            let expected_type = state.read_back_value(expected_type);
            let expected_type = state.core_to_surface_term(&expected_type);
            state.report(Message::NoLiteralConversion {
                range: term.range(),
                expected_type,
            });
            core::Term::Error
        }
        (Term::Sequence(_, entry_terms), Value::Stuck(Head::Global(name, _), spine)) => {
            match (name.as_ref(), spine.as_slice()) {
                ("Array", [Elim::Function(len), Elim::Function(core_entry_type)]) => {
                    let core_entry_terms = entry_terms
                        .iter()
                        .map(|entry_term| {
                            Arc::new(check_type(
                                state,
                                entry_term,
                                core_entry_type.force(state.globals),
                            ))
                        })
                        .collect();

                    let len = len.force(state.globals);
                    match len.as_ref() {
                        Value::Constant(core::Constant::U32(len))
                            if *len as usize == entry_terms.len() =>
                        {
                            core::Term::Sequence(core_entry_terms)
                        }
                        Value::Error => core::Term::Error,
                        _ => {
                            let expected_len = state.read_back_value(&len);
                            let expected_len = state.core_to_surface_term(&expected_len);
                            state.report(Message::MismatchedSequenceLength {
                                range: term.range(),
                                found_len: entry_terms.len(),
                                expected_len,
                            });

                            core::Term::Error
                        }
                    }
                }
                ("List", [Elim::Function(core_entry_type)]) => {
                    let core_entry_terms = entry_terms
                        .iter()
                        .map(|entry_term| {
                            Arc::new(check_type(
                                state,
                                entry_term,
                                core_entry_type.force(state.globals),
                            ))
                        })
                        .collect();

                    core::Term::Sequence(core_entry_terms)
                }
                _ => {
                    let expected_type = state.read_back_value(expected_type);
                    let expected_type = state.core_to_surface_term(&expected_type);
                    state.report(Message::NoSequenceConversion {
                        range: term.range(),
                        expected_type,
                    });
                    core::Term::Error
                }
            }
        }
        (Term::Sequence(_, _), _) => {
            let expected_type = state.read_back_value(expected_type);
            let expected_type = state.core_to_surface_term(&expected_type);
            state.report(Message::NoSequenceConversion {
                range: term.range(),
                expected_type,
            });
            core::Term::Error
        }
        (Term::RecordTerm(_, term_entries), Value::RecordType(closure)) => {
            use std::collections::btree_map::Entry;
            use std::collections::BTreeMap;

            let mut duplicate_labels = Vec::new();
            let mut missing_labels = Vec::new();

            let mut core_term_entries = BTreeMap::new();
            let mut pending_term_entries = BTreeMap::new();
            for (label_range, label, entry_term) in term_entries {
                let range = label_range.clone();
                match pending_term_entries.entry(label.as_ref().to_owned()) {
                    Entry::Vacant(entry) => drop(entry.insert((range, entry_term))),
                    Entry::Occupied(entry) => {
                        duplicate_labels.push((entry.key().clone(), entry.get().0.clone(), range));
                    }
                }
            }

            closure.entries(
                state.globals,
                |label, entry_type| match pending_term_entries.remove(label) {
                    Some((_, entry_term)) => {
                        let core_entry_term = check_type(state, entry_term, &entry_type);
                        let core_entry_value = state.eval_term(&core_entry_term);
                        core_term_entries.insert(label.to_owned(), Arc::new(core_entry_term));
                        core_entry_value
                    }
                    None => {
                        missing_labels.push(label.to_owned());
                        Arc::new(Value::Error)
                    }
                },
            );

            if !duplicate_labels.is_empty()
                || !missing_labels.is_empty()
                || !pending_term_entries.is_empty()
            {
                let unexpected_labels = (pending_term_entries.into_iter())
                    .map(|(label, (label_range, _))| (label, label_range))
                    .collect();
                state.report(Message::InvalidRecordTerm {
                    range: term.range(),
                    duplicate_labels,
                    missing_labels,
                    unexpected_labels,
                });
            }

            core::Term::RecordTerm(core_term_entries)
        }
        (Term::FunctionTerm(_, param_names, body), _) => {
            let mut seen_param_count = 0;
            let mut expected_type = expected_type.clone();
            let mut pending_param_names = param_names.iter();

            while let Some((param_range, param_name)) = pending_param_names.next() {
                match expected_type.force(state.globals) {
                    Value::FunctionType(_, param_type, body_closure) => {
                        let param =
                            state.push_local_param(Some(param_name.as_ref()), param_type.clone());
                        seen_param_count += 1;
                        expected_type = body_closure.elim(state.globals, param);
                    }
                    Value::Error => {
                        state.pop_many_locals(seen_param_count);
                        return core::Term::Error;
                    }
                    _ => {
                        state.report(Message::TooManyParameters {
                            unexpected_parameters: std::iter::once(param_range.clone())
                                .chain(pending_param_names.map(|(range, _)| range.clone()))
                                .collect(),
                        });
                        check_type(state, body, &expected_type);
                        state.pop_many_locals(seen_param_count);
                        return core::Term::Error;
                    }
                }
            }

            let core_body = check_type(state, body, &expected_type);
            state.pop_many_locals(seen_param_count);
            (param_names.iter().rev()).fold(core_body, |core_body, (_, param_name)| {
                core::Term::FunctionTerm(param_name.as_ref().to_owned(), Arc::new(core_body))
            })
        }
        (term, _) => match synth_type(state, term) {
            (term, found_type) if state.is_subtype(&found_type, expected_type) => term,
            (_, found_type) => {
                let found_type = state.read_back_value(&found_type);
                let found_type = state.core_to_surface_term(&found_type);
                let expected_type = state.read_back_value(expected_type);
                let expected_type = state.core_to_surface_term(&expected_type);
                state.report(Message::MismatchedTypes {
                    range: term.range(),
                    found_type,
                    expected_type: ExpectedType::Type(expected_type),
                });
                core::Term::Error
            }
        },
    }
}

/// Synthesize the type of a surface term, and return the elaborated term.
pub fn synth_type<S: AsRef<str>>(
    state: &mut State<'_>,
    term: &Term<S>,
) -> (core::Term, Arc<Value>) {
    use std::collections::BTreeMap;

    match term {
        Term::Name(_, name) => {
            if let Some((index, r#type)) = state.get_local(name.as_ref()) {
                return (core::Term::Local(index), r#type.clone());
            }

            if let Some((r#type, _)) = state.globals.get(name.as_ref()) {
                let global = core::Term::Global(name.as_ref().to_owned());
                return (global.lift(state.universe_offset), state.eval_term(r#type));
            }

            state.report(Message::UnboundName {
                range: term.range(),
                name: name.as_ref().to_owned(),
            });
            (core::Term::Error, Arc::new(Value::Error))
        }
        Term::Ann(term, r#type) => {
            let (core_type, _) = is_type(state, r#type);
            let core_type_value = state.eval_term(&core_type);
            let core_term = check_type(state, term, &core_type_value);
            (
                core::Term::Ann(Arc::new(core_term), Arc::new(core_type)),
                core_type_value,
            )
        }
        Term::Literal(_, literal) => match literal {
            Literal::Number(_) => {
                state.report(Message::AmbiguousTerm {
                    range: term.range(),
                    term: AmbiguousTerm::NumberLiteral,
                });
                (core::Term::Error, Arc::new(Value::Error))
            }
            Literal::Char(data) => (
                parse_char(state, term.range(), data),
                Arc::new(Value::global("Char", 0)),
            ),
            Literal::String(data) => (
                parse_string(state, term.range(), data),
                Arc::new(Value::global("String", 0)),
            ),
        },
        Term::Sequence(_, _) => {
            state.report(Message::AmbiguousTerm {
                range: term.range(),
                term: AmbiguousTerm::Sequence,
            });
            (core::Term::Error, Arc::new(Value::Error))
        }
        Term::RecordTerm(_, term_entries) => {
            if term_entries.is_empty() {
                (
                    core::Term::RecordTerm(BTreeMap::new()),
                    Arc::from(Value::RecordType(RecordTypeClosure::new(
                        state.universe_offset,
                        state.values.clone(),
                        Arc::new([]),
                    ))),
                )
            } else {
                state.report(Message::AmbiguousTerm {
                    range: term.range(),
                    term: AmbiguousTerm::RecordTerm,
                });
                (core::Term::Error, Arc::new(Value::Error))
            }
        }
        Term::RecordType(_, type_entries) => {
            use std::collections::btree_map::Entry;

            let mut max_level = core::UniverseLevel(0);
            let mut duplicate_labels = Vec::new();
            let mut seen_labels = BTreeMap::new();
            let mut core_type_entries = Vec::new();

            for (label_range, label, name, entry_type) in type_entries {
                let name = name.as_ref().unwrap_or(label);
                match seen_labels.entry(label.as_ref()) {
                    Entry::Vacant(entry) => {
                        let (core_type, level) = is_type(state, entry_type);
                        max_level = match level {
                            Some(level) => std::cmp::max(max_level, level),
                            None => {
                                state.pop_many_locals(seen_labels.len());
                                return (core::Term::Error, Arc::new(Value::Error));
                            }
                        };
                        let core_type = Arc::new(core_type);
                        let core_type_value = state.eval_term(&core_type);
                        core_type_entries.push((label.as_ref().to_owned(), core_type));
                        state.push_local_param(Some(name.as_ref()), core_type_value);
                        entry.insert(label_range.clone());
                    }
                    Entry::Occupied(entry) => {
                        duplicate_labels.push((
                            (*entry.key()).to_owned(),
                            entry.get().clone(),
                            label_range.clone(),
                        ));
                        is_type(state, entry_type);
                    }
                }
            }

            if !duplicate_labels.is_empty() {
                state.report(Message::InvalidRecordType { duplicate_labels });
            }

            state.pop_many_locals(seen_labels.len());
            (
                core::Term::RecordType(core_type_entries.into()),
                Arc::new(Value::Universe(max_level)),
            )
        }
        Term::RecordElim(head, label_range, label) => {
            let (core_head, head_type) = synth_type(state, head);

            match head_type.force(state.globals) {
                Value::RecordType(closure) => {
                    let head_value = state.eval_term(&core_head);
                    let label = label.as_ref();

                    if let Some(entry_type) = state.record_elim_type(&head_value, label, closure) {
                        let core_head = Arc::new(core_head);
                        let core_term = core::Term::RecordElim(core_head, label.to_owned());
                        return (core_term, entry_type);
                    }
                }
                Value::Error => return (core::Term::Error, Arc::new(Value::Error)),
                _ => {}
            }

            let head_type = state.read_back_value(&head_type);
            let head_type = state.core_to_surface_term(&head_type);
            state.report(Message::LabelNotFound {
                head_range: head.range(),
                label_range: label_range.clone(),
                expected_label: label.as_ref().to_owned(),
                head_type,
            });
            (core::Term::Error, Arc::new(Value::Error))
        }
        Term::FunctionType(_, param_type_groups, body_type) => {
            let mut max_level = Some(core::UniverseLevel(0));
            let update_level = |max_level, next_level| match (max_level, next_level) {
                (Some(max_level), Some(pl)) => Some(std::cmp::max(max_level, pl)),
                (None, _) | (_, None) => None,
            };
            let mut core_params = Vec::new();

            for (param_names, param_type) in param_type_groups {
                for (_, param_name) in param_names {
                    let (core_param_type, param_level) = is_type(state, param_type);
                    max_level = update_level(max_level, param_level);

                    let core_param_type_value = state.eval_term(&core_param_type);
                    state.push_local_param(Some(param_name.as_ref()), core_param_type_value);
                    core_params.push((Some(param_name.as_ref().to_owned()), core_param_type));
                }
            }

            let (core_body_type, body_level) = is_type(state, body_type);
            max_level = update_level(max_level, body_level);

            state.pop_many_locals(core_params.len());

            match max_level {
                None => (core::Term::Error, Arc::new(Value::Error)),
                Some(max_level) => (
                    core_params.into_iter().rev().fold(
                        core_body_type,
                        |body_type, (param_name, param_type)| {
                            core::Term::FunctionType(
                                param_name,
                                Arc::new(param_type),
                                Arc::new(body_type),
                            )
                        },
                    ),
                    Arc::new(Value::Universe(max_level)),
                ),
            }
        }
        Term::FunctionArrowType(param_type, body_type) => {
            let (core_param_type, param_level) = is_type(state, param_type);
            let core_param_type_value = match param_level {
                None => Arc::new(Value::Error),
                Some(_) => state.eval_term(&core_param_type),
            };

            state.push_local_param(None, core_param_type_value);
            let (core_body_type, body_level) = is_type(state, body_type);
            state.pop_local();

            match (param_level, body_level) {
                (Some(param_level), Some(body_level)) => (
                    core::Term::FunctionType(
                        None,
                        Arc::new(core_param_type),
                        Arc::new(core_body_type),
                    ),
                    Arc::new(Value::Universe(std::cmp::max(param_level, body_level))),
                ),
                (_, _) => (core::Term::Error, Arc::new(Value::Error)),
            }
        }
        Term::FunctionTerm(_, _, _) => {
            state.report(Message::AmbiguousTerm {
                range: term.range(),
                term: AmbiguousTerm::FunctionTerm,
            });
            (core::Term::Error, Arc::new(Value::Error))
        }
        Term::FunctionElim(head, arguments) => {
            let mut head_range = head.range();
            let (mut core_head, mut head_type) = synth_type(state, head);
            let mut arguments = arguments.iter();

            while let Some(argument) = arguments.next() {
                match head_type.force(state.globals) {
                    Value::FunctionType(_, param_type, body_closure) => {
                        head_range.end = argument.range().end;
                        let core_argument = check_type(state, argument, &param_type);
                        let core_argument_value = state.eval_term(&core_argument);
                        core_head =
                            core::Term::FunctionElim(Arc::new(core_head), Arc::new(core_argument));
                        head_type = body_closure.elim(state.globals, core_argument_value);
                    }
                    Value::Error => return (core::Term::Error, Arc::new(Value::Error)),
                    _ => {
                        let head_type = state.read_back_value(&head_type);
                        let head_type = state.core_to_surface_term(&head_type);
                        let unexpected_arguments = arguments.map(|arg| arg.range()).collect();
                        state.report(Message::TooManyArguments {
                            head_range,
                            head_type,
                            unexpected_arguments,
                        });
                        return (core::Term::Error, Arc::new(Value::Error));
                    }
                }
            }

            (core_head, head_type)
        }
        Term::Lift(_, inner_term, offset) => {
            match state.universe_offset + core::UniverseOffset(*offset) {
                Some(new_offset) => {
                    let previous_offset = std::mem::replace(&mut state.universe_offset, new_offset);
                    let (core_term, r#type) = synth_type(state, inner_term);
                    state.universe_offset = previous_offset;
                    (core_term, r#type)
                }
                None => {
                    state.report(Message::MaximumUniverseLevelReached {
                        range: term.range(),
                    });
                    (core::Term::Error, Arc::new(Value::Error))
                }
            }
        }
        Term::Error(_) => (core::Term::Error, Arc::new(Value::Error)),
    }
}

fn parse_number<S: AsRef<str>, T: FromStr>(
    state: &mut State<'_>,
    range: Range<usize>,
    data: &S,
    f: impl Fn(T) -> core::Constant,
) -> core::Term {
    // TODO: improve parser (eg. numeric separators, positive sign)
    match data.as_ref().parse() {
        Ok(value) => core::Term::Constant(f(value)),
        Err(_) => {
            state.report(Message::InvalidLiteral {
                range,
                literal: InvalidLiteral::Number,
            });
            core::Term::Error
        }
    }
}

fn parse_char<S: AsRef<str>>(state: &mut State<'_>, range: Range<usize>, data: &S) -> core::Term {
    // TODO: Improve parser (escapes)
    match data.as_ref().chars().nth(1) {
        Some(value) => core::Term::Constant(core::Constant::Char(value)),
        None => {
            state.report(Message::InvalidLiteral {
                range,
                literal: InvalidLiteral::Char,
            });
            core::Term::Error
        }
    }
}

fn parse_string<S: AsRef<str>>(state: &mut State<'_>, range: Range<usize>, data: &S) -> core::Term {
    // TODO: Improve parser (escapes)
    match data.as_ref().get(1..data.as_ref().len() - 1) {
        Some(value) => core::Term::Constant(core::Constant::String(value.to_owned())),
        None => {
            state.report(Message::InvalidLiteral {
                range,
                literal: InvalidLiteral::String,
            });
            core::Term::Error
        }
    }
}
