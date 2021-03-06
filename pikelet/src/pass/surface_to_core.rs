//! Elaborates the [surface language] into the [core language].
//!
//! This translation pass is the main place where user-facing type errors will be returned.
//!
//! [surface language]: crate::lang::surface
//! [core language]: crate::lang::core

use contracts::debug_ensures;
use crossbeam_channel::Sender;
use num_traits::{Float, PrimInt, Signed, Unsigned};
use std::sync::Arc;

use crate::lang::core::semantics::{self, Elim, RecordClosure, Unfold, Value};
use crate::lang::surface::{Term, TermData};
use crate::lang::{core, Location};
use crate::literal;
use crate::pass::core_to_surface;
use crate::reporting::{AmbiguousTerm, ExpectedType, Message, SurfaceToCoreMessage};

/// The state of the elaborator.
pub struct State<'me> {
    /// Global definition environment.
    globals: &'me core::Globals,
    /// The current universe offset.
    universe_offset: core::UniverseOffset,
    /// Substitutions from the user-defined names to the level in which they were bound.
    local_levels: Vec<(Option<String>, core::LocalLevel)>,
    /// Local type environment (used for getting the types of local variables).
    local_declarations: core::Locals<Arc<Value>>,
    /// Local value environment (used for evaluation).
    local_definitions: core::Locals<Arc<Value>>,
    /// Distillation state (used for pretty printing).
    core_to_surface: core_to_surface::State<'me>,
    /// The diagnostic messages accumulated during elaboration.
    message_tx: Sender<Message>,
}

impl<'me> State<'me> {
    /// Construct a new elaborator state.
    pub fn new(globals: &'me core::Globals, message_tx: Sender<Message>) -> State<'me> {
        State {
            globals,
            universe_offset: core::UniverseOffset(0),
            local_levels: Vec::new(),
            local_declarations: core::Locals::new(),
            local_definitions: core::Locals::new(),
            core_to_surface: core_to_surface::State::new(globals),
            message_tx,
        }
    }

    /// Get the next level to be used for a local entry.
    fn next_level(&self) -> core::LocalLevel {
        self.local_definitions.size().next_level()
    }

    /// Get a local entry.
    fn get_local(&self, name: &str) -> Option<(core::LocalIndex, &Arc<Value>)> {
        let (_, level) = self.local_levels.iter().rev().find(|(n, _)| match n {
            Some(n) => n == name,
            None => false,
        })?;
        let index = level.to_index(self.local_definitions.size()).unwrap(); // TODO: Handle overflow
        let r#type = self.local_declarations.get(index)?;
        Some((index, r#type))
    }

    /// Push a local entry.
    fn push_local(&mut self, name: Option<&str>, value: Arc<Value>, r#type: Arc<Value>) {
        self.local_levels
            .push((name.map(str::to_owned), self.next_level()));
        self.local_declarations.push(r#type);
        self.local_definitions.push(value);
        self.core_to_surface.push_name(name);
    }

    /// Push a local parameter.
    fn push_local_param(&mut self, name: Option<&str>, r#type: Arc<Value>) -> Arc<Value> {
        let value = Arc::new(Value::local(self.next_level(), []));
        self.push_local(name, value.clone(), r#type);
        value
    }

    /// Pop a local entry.
    fn pop_local(&mut self) {
        self.local_levels.pop();
        self.local_declarations.pop();
        self.local_definitions.pop();
        self.core_to_surface.pop_name();
    }

    /// Pop the given number of local entries.
    fn pop_many_locals(&mut self, count: usize) {
        self.local_levels
            .truncate(self.local_levels.len().saturating_sub(count));
        self.local_declarations.pop_many(count);
        self.local_definitions.pop_many(count);
        self.core_to_surface.pop_many_names(count);
    }

    /// Report a diagnostic message.
    fn report(&self, error: SurfaceToCoreMessage) {
        self.message_tx.send(error.into()).unwrap();
    }

    /// Evaluate a [`core::Term`] into a [`Value`].
    ///
    /// [`Value`]: crate::lang::core::semantics::Value
    /// [`core::Term`]: crate::lang::core::Term
    pub fn eval_term(&mut self, term: &core::Term) -> Arc<Value> {
        semantics::eval_term(
            self.globals,
            self.universe_offset,
            &mut self.local_definitions,
            term,
        )
    }

    /// Return the type of the record elimination.
    pub fn record_elim_type(
        &self,
        head_value: Arc<Value>,
        label: &str,
        closure: &RecordClosure,
    ) -> Option<Arc<Value>> {
        semantics::record_elim_type(self.globals, head_value, label, closure)
    }

    /// Fully normalize a [`core::Term`] using [normalization by evaluation].
    ///
    /// [`core::Term`]: crate::lang::core::Term
    /// [normalization by evaluation]: https://en.wikipedia.org/wiki/Normalisation_by_evaluation
    pub fn normalize_term(&mut self, term: &core::Term) -> core::Term {
        semantics::normalize_term(
            self.globals,
            self.universe_offset,
            &mut self.local_definitions,
            term,
        )
    }

    /// Read back a [`Value`] to a [`core::Term`] using the current
    /// state of the elaborator.
    ///
    /// Unstuck eliminations are not unfolded, making this useful for printing
    /// terms and types in user-facing diagnostics.
    ///
    /// [`Value`]: crate::lang::core::semantics::Value
    /// [`core::Term`]: crate::lang::core::Term
    pub fn read_back_value(&self, value: &Value) -> core::Term {
        semantics::read_back_value(
            self.globals,
            self.local_definitions.size(),
            Unfold::Never,
            value,
        )
    }

    /// Check that one [`Value`] is a subtype of another [`Value`].
    ///
    /// Returns `false` if either value is not a type.
    ///
    /// [`Value`]: crate::lang::core::semantics::Value
    pub fn is_subtype(&self, value0: &Value, value1: &Value) -> bool {
        semantics::is_subtype(self.globals, self.local_definitions.size(), value0, value1)
    }

    /// Distill a [`core::Term`] into a [`surface::Term`].
    ///
    /// [`core::Term`]: crate::lang::core::Term
    /// [`surface::Term`]: crate::lang::surface::Term
    pub fn core_to_surface_term(&mut self, core_term: &core::Term) -> Term {
        self.core_to_surface.from_term(&core_term)
    }

    /// Read back a [`Value`] into a [`surface::Term`] using the
    /// current state of the elaborator.
    ///
    /// Unstuck eliminations are not unfolded, making this useful for printing
    /// terms and types in user-facing diagnostics.
    ///
    /// [`Value`]: crate::lang::core::semantics::Value
    /// [`surface::Term`]: crate::lang::surface::Term
    pub fn read_back_to_surface_term(&mut self, value: &Value) -> Term {
        let core_term = self.read_back_value(value);
        self.core_to_surface_term(&core_term)
    }

    /// Check that a term is a type, and return the elaborated term and the
    /// universe level it inhabits.
    #[debug_ensures(self.universe_offset == old(self.universe_offset))]
    #[debug_ensures(self.local_levels.len() == old(self.local_levels.len()))]
    #[debug_ensures(self.local_declarations.size() == old(self.local_declarations.size()))]
    #[debug_ensures(self.local_definitions.size() == old(self.local_definitions.size()))]
    pub fn is_type(&mut self, term: &Term) -> (core::Term, Option<core::UniverseLevel>) {
        let (core_term, r#type) = self.synth_type(term);
        match r#type.force(self.globals) {
            Value::TypeType(level) => (core_term, Some(*level)),
            Value::Error => (core::Term::new(term.location, core::TermData::Error), None),
            found_type => {
                let found_type = self.read_back_to_surface_term(&found_type);
                self.report(SurfaceToCoreMessage::MismatchedTypes {
                    location: term.location,
                    found_type,
                    expected_type: ExpectedType::Universe,
                });
                (core::Term::new(term.location, core::TermData::Error), None)
            }
        }
    }

    /// Check that a term is an element of a type, and return the elaborated term.
    #[debug_ensures(self.universe_offset == old(self.universe_offset))]
    #[debug_ensures(self.local_levels.len() == old(self.local_levels.len()))]
    #[debug_ensures(self.local_declarations.size() == old(self.local_declarations.size()))]
    #[debug_ensures(self.local_definitions.size() == old(self.local_definitions.size()))]
    pub fn check_type(&mut self, term: &Term, expected_type: &Arc<Value>) -> core::Term {
        match (&term.data, expected_type.force(self.globals)) {
            (_, Value::Error) => core::Term::new(term.location, core::TermData::Error),

            (TermData::FunctionTerm(input_names, output_term), _) => {
                let mut seen_input_count = 0;
                let mut expected_type = expected_type.clone();
                let mut pending_input_names = input_names.iter();

                while let Some(input_name) = pending_input_names.next() {
                    match expected_type.force(self.globals) {
                        Value::FunctionType(_, input_type, output_closure) => {
                            let input_value =
                                self.push_local_param(Some(&input_name.data), input_type.clone());
                            seen_input_count += 1;
                            expected_type = output_closure.apply(self.globals, input_value);
                        }
                        Value::Error => {
                            self.pop_many_locals(seen_input_count);
                            return core::Term::new(term.location, core::TermData::Error);
                        }
                        _ => {
                            self.report(SurfaceToCoreMessage::TooManyInputsInFunctionTerm {
                                unexpected_inputs: std::iter::once(input_name.location)
                                    .chain(
                                        pending_input_names.map(|input_name| input_name.location),
                                    )
                                    .collect(),
                            });
                            self.check_type(output_term, &expected_type);
                            self.pop_many_locals(seen_input_count);
                            return core::Term::new(term.location, core::TermData::Error);
                        }
                    }
                }

                let core_output_term = self.check_type(output_term, &expected_type);
                self.pop_many_locals(seen_input_count);
                (input_names.iter().rev()).fold(core_output_term, |core_output_term, input_name| {
                    core::Term::new(
                        Location::merge(input_name.location, core_output_term.location),
                        core::TermData::FunctionTerm(
                            input_name.data.clone(),
                            Arc::new(core_output_term),
                        ),
                    )
                })
            }

            (TermData::RecordTerm(term_entries), Value::RecordType(closure)) => {
                let mut pending_term_entries = term_entries.iter();
                let mut missing_labels = Vec::new();
                let mut unexpected_labels = Vec::new();

                let mut core_term_entries = Vec::with_capacity(term_entries.len());

                closure.for_each_entry(self.globals, |label, entry_type| loop {
                    match pending_term_entries.next() {
                        Some((next_label, next_name, entry_term)) if next_label.data == label => {
                            let next_name = next_name.as_ref().unwrap_or(next_label);
                            let core_entry_term = self.check_type(entry_term, &entry_type);
                            let core_entry_value = self.eval_term(&core_entry_term);

                            self.push_local(
                                Some(&next_name.data),
                                core_entry_value.clone(),
                                entry_type,
                            );
                            core_term_entries.push((label.to_owned(), Arc::new(core_entry_term)));

                            return core_entry_value;
                        }
                        Some((next_label, _, _)) => unexpected_labels.push(next_label.location),
                        None => {
                            missing_labels.push(label.to_owned());
                            return Arc::new(Value::Error);
                        }
                    }
                });

                self.pop_many_locals(core_term_entries.len());
                unexpected_labels.extend(pending_term_entries.map(|(label, _, _)| label.location));

                if !missing_labels.is_empty() || !unexpected_labels.is_empty() {
                    self.report(SurfaceToCoreMessage::InvalidRecordTerm {
                        location: term.location,
                        missing_labels,
                        unexpected_labels,
                    });
                }

                core::Term::new(
                    term.location,
                    core::TermData::RecordTerm(core_term_entries.into()),
                )
            }

            (TermData::SequenceTerm(entry_terms), forced_type) => match forced_type.try_global() {
                Some(("Array", _, [Elim::Function(len), Elim::Function(core_entry_type)])) => {
                    let core_entry_type = core_entry_type.force(self.globals);
                    let core_entry_terms = entry_terms
                        .iter()
                        .map(|entry_term| Arc::new(self.check_type(entry_term, core_entry_type)))
                        .collect();

                    let len = len.force(self.globals);
                    match len.as_ref() {
                        Value::Constant(core::Constant::U32(len))
                            if *len as usize == entry_terms.len() =>
                        {
                            core::Term::new(
                                term.location,
                                core::TermData::ArrayTerm(core_entry_terms),
                            )
                        }
                        Value::Error => core::Term::new(term.location, core::TermData::Error),
                        _ => {
                            let expected_len = self.read_back_to_surface_term(&len);
                            self.report(SurfaceToCoreMessage::MismatchedSequenceLength {
                                location: term.location,
                                found_len: entry_terms.len(),
                                expected_len,
                            });
                            core::Term::new(term.location, core::TermData::Error)
                        }
                    }
                }
                Some(("List", _, [Elim::Function(core_entry_type)])) => {
                    let core_entry_type = core_entry_type.force(self.globals);
                    let core_entry_terms = entry_terms
                        .iter()
                        .map(|entry_term| Arc::new(self.check_type(entry_term, core_entry_type)))
                        .collect();

                    core::Term::new(term.location, core::TermData::ListTerm(core_entry_terms))
                }
                Some(_) | None => {
                    let expected_type = self.read_back_to_surface_term(expected_type);
                    self.report(SurfaceToCoreMessage::NoSequenceConversion {
                        location: term.location,
                        expected_type,
                    });
                    core::Term::new(term.location, core::TermData::Error)
                }
            },
            (TermData::NumberTerm(data), forced_type) => {
                use crate::lang::core::Constant::*;

                match forced_type.try_global() {
                    Some(("U8", _, [])) => self.parse_unsigned(term.location, data, U8),
                    Some(("U16", _, [])) => self.parse_unsigned(term.location, data, U16),
                    Some(("U32", _, [])) => self.parse_unsigned(term.location, data, U32),
                    Some(("U64", _, [])) => self.parse_unsigned(term.location, data, U64),
                    Some(("S8", _, [])) => self.parse_signed(term.location, data, S8),
                    Some(("S16", _, [])) => self.parse_signed(term.location, data, S16),
                    Some(("S32", _, [])) => self.parse_signed(term.location, data, S32),
                    Some(("S64", _, [])) => self.parse_signed(term.location, data, S64),
                    Some(("F32", _, [])) => self.parse_float(term.location, data, F32),
                    Some(("F64", _, [])) => self.parse_float(term.location, data, F64),
                    Some(_) | None => {
                        let expected_type = self.read_back_to_surface_term(expected_type);
                        self.report(SurfaceToCoreMessage::NoLiteralConversion {
                            location: term.location,
                            expected_type,
                        });
                        core::Term::new(term.location, core::TermData::Error)
                    }
                }
            }
            (TermData::CharTerm(data), forced_type) => match forced_type.try_global() {
                Some(("Char", _, [])) => self.parse_char(term.location, data),
                Some(_) | None => {
                    let expected_type = self.read_back_to_surface_term(expected_type);
                    self.report(SurfaceToCoreMessage::NoLiteralConversion {
                        location: term.location,
                        expected_type,
                    });
                    core::Term::new(term.location, core::TermData::Error)
                }
            },
            (TermData::StringTerm(data), forced_type) => match forced_type.try_global() {
                Some(("String", _, [])) => self.parse_string(term.location, data),
                Some(_) | None => {
                    let expected_type = self.read_back_to_surface_term(expected_type);
                    self.report(SurfaceToCoreMessage::NoLiteralConversion {
                        location: term.location,
                        expected_type,
                    });
                    core::Term::new(term.location, core::TermData::Error)
                }
            },

            (_, _) => match self.synth_type(term) {
                (term, found_type) if self.is_subtype(&found_type, expected_type) => term,
                (_, found_type) => {
                    let found_type = self.read_back_to_surface_term(&found_type);
                    let expected_type = self.read_back_to_surface_term(expected_type);
                    self.report(SurfaceToCoreMessage::MismatchedTypes {
                        location: term.location,
                        found_type,
                        expected_type: ExpectedType::Type(expected_type),
                    });
                    core::Term::new(term.location, core::TermData::Error)
                }
            },
        }
    }

    /// Synthesize the type of a surface term, and return the elaborated term.
    #[debug_ensures(self.universe_offset == old(self.universe_offset))]
    #[debug_ensures(self.local_levels.len() == old(self.local_levels.len()))]
    #[debug_ensures(self.local_declarations.size() == old(self.local_declarations.size()))]
    #[debug_ensures(self.local_definitions.size() == old(self.local_definitions.size()))]
    pub fn synth_type(&mut self, term: &Term) -> (core::Term, Arc<Value>) {
        use std::collections::BTreeMap;

        let error_term = || core::Term::new(term.location, core::TermData::Error);

        match &term.data {
            TermData::Name(name) => {
                if let Some((index, r#type)) = self.get_local(name.as_ref()) {
                    let core_term = core::Term::new(term.location, core::TermData::Local(index));
                    return (core_term, r#type.clone());
                }

                if let Some((r#type, _)) = self.globals.get(name.as_ref()) {
                    let name = name.clone();
                    let global = core::Term::new(term.location, core::TermData::Global(name));
                    let core_term = match self.universe_offset {
                        core::UniverseOffset(0) => global,
                        offset => {
                            core::Term::generated(core::TermData::Lift(Arc::new(global), offset))
                        }
                    };
                    return (core_term, self.eval_term(r#type));
                }

                self.report(SurfaceToCoreMessage::UnboundName {
                    location: term.location,
                    name: name.clone(),
                });
                (error_term(), Arc::new(Value::Error))
            }

            TermData::Ann(term, r#type) => {
                let (core_type, _) = self.is_type(r#type);
                let core_type_value = self.eval_term(&core_type);
                let core_term = self.check_type(term, &core_type_value);
                (
                    core::Term::new(
                        term.location,
                        core::TermData::Ann(Arc::new(core_term), Arc::new(core_type)),
                    ),
                    core_type_value,
                )
            }

            TermData::Lift(inner_term, offset) => {
                match self.universe_offset + core::UniverseOffset(*offset) {
                    Some(new_offset) => {
                        let old_offset = std::mem::replace(&mut self.universe_offset, new_offset);
                        let (core_term, r#type) = self.synth_type(inner_term);
                        self.universe_offset = old_offset;
                        (core_term, r#type)
                    }
                    None => {
                        self.report(SurfaceToCoreMessage::MaximumUniverseLevelReached {
                            location: term.location,
                        });
                        (error_term(), Arc::new(Value::Error))
                    }
                }
            }

            TermData::FunctionType(input_type_groups, output_type) => {
                let mut max_level = Some(core::UniverseLevel(0));
                let update_level = |max_level, next_level| match (max_level, next_level) {
                    (Some(max_level), Some(pl)) => Some(std::cmp::max(max_level, pl)),
                    (None, _) | (_, None) => None,
                };
                let mut core_inputs = Vec::new();

                for (input_names, input_type) in input_type_groups {
                    for input_name in input_names {
                        let (core_input_type, input_level) = self.is_type(input_type);
                        max_level = update_level(max_level, input_level);

                        let core_input_type_value = self.eval_term(&core_input_type);
                        self.push_local_param(Some(&input_name.data), core_input_type_value);
                        core_inputs.push((input_name.clone(), core_input_type));
                    }
                }

                let (core_output_type, output_level) = self.is_type(output_type);
                max_level = update_level(max_level, output_level);

                self.pop_many_locals(core_inputs.len());

                match max_level {
                    None => (error_term(), Arc::new(Value::Error)),
                    Some(max_level) => {
                        let mut core_type = core_output_type;
                        for (input_name, input_type) in core_inputs.into_iter().rev() {
                            core_type = core::Term::new(
                                Location::merge(input_name.location, output_type.location),
                                core::TermData::FunctionType(
                                    Some(input_name.data),
                                    Arc::new(input_type),
                                    Arc::new(core_type),
                                ),
                            );
                        }

                        (core_type, Arc::new(Value::TypeType(max_level)))
                    }
                }
            }
            TermData::FunctionArrowType(input_type, output_type) => {
                let (core_input_type, input_level) = self.is_type(input_type);
                let core_input_type_value = match input_level {
                    None => Arc::new(Value::Error),
                    Some(_) => self.eval_term(&core_input_type),
                };

                self.push_local_param(None, core_input_type_value);
                let (core_output_type, output_level) = self.is_type(output_type);
                self.pop_local();

                match (input_level, output_level) {
                    (Some(input_level), Some(output_level)) => (
                        core::Term::new(
                            term.location,
                            core::TermData::FunctionType(
                                None,
                                Arc::new(core_input_type),
                                Arc::new(core_output_type),
                            ),
                        ),
                        Arc::new(Value::TypeType(std::cmp::max(input_level, output_level))),
                    ),
                    (_, _) => (error_term(), Arc::new(Value::Error)),
                }
            }
            TermData::FunctionTerm(_, _) => {
                self.report(SurfaceToCoreMessage::AmbiguousTerm {
                    location: term.location,
                    term: AmbiguousTerm::FunctionTerm,
                });
                (error_term(), Arc::new(Value::Error))
            }
            TermData::FunctionElim(head_term, input_terms) => {
                let mut head_location = head_term.location;
                let (mut core_head_term, mut head_type) = self.synth_type(head_term);
                let mut input_terms = input_terms.iter();

                while let Some(input) = input_terms.next() {
                    match head_type.force(self.globals) {
                        Value::FunctionType(_, input_type, output_closure) => {
                            head_location = input.location;
                            let core_input = self.check_type(input, &input_type);
                            let core_input_value = self.eval_term(&core_input);
                            core_head_term = core::Term::new(
                                Location::merge(head_location, input.location),
                                core::TermData::FunctionElim(
                                    Arc::new(core_head_term),
                                    Arc::new(core_input),
                                ),
                            );
                            head_type = output_closure.apply(self.globals, core_input_value);
                        }
                        Value::Error => return (error_term(), Arc::new(Value::Error)),
                        _ => {
                            let head_type = self.read_back_to_surface_term(&head_type);
                            let unexpected_input_terms =
                                input_terms.map(|arg| arg.location).collect();
                            self.report(SurfaceToCoreMessage::TooManyInputsInFunctionElim {
                                head_location,
                                head_type,
                                unexpected_input_terms,
                            });
                            return (error_term(), Arc::new(Value::Error));
                        }
                    }
                }

                (core_head_term, head_type)
            }

            TermData::RecordTerm(term_entries) => {
                if term_entries.is_empty() {
                    (
                        core::Term::new(term.location, core::TermData::RecordTerm(Arc::new([]))),
                        Arc::from(Value::RecordType(RecordClosure::new(
                            self.universe_offset,
                            self.local_definitions.clone(),
                            Arc::new([]),
                        ))),
                    )
                } else {
                    self.report(SurfaceToCoreMessage::AmbiguousTerm {
                        location: term.location,
                        term: AmbiguousTerm::RecordTerm,
                    });
                    (error_term(), Arc::new(Value::Error))
                }
            }
            TermData::RecordType(type_entries) => {
                use std::collections::btree_map::Entry;

                let mut max_level = core::UniverseLevel(0);
                let mut duplicate_labels = Vec::new();
                let mut seen_labels = BTreeMap::new();
                let mut core_type_entries = Vec::new();

                for (label, name, entry_type) in type_entries {
                    let name = name.as_ref().unwrap_or(label);
                    match seen_labels.entry(label.data.as_str()) {
                        Entry::Vacant(entry) => {
                            let (core_type, level) = self.is_type(entry_type);
                            max_level = match level {
                                Some(level) => std::cmp::max(max_level, level),
                                None => {
                                    self.pop_many_locals(seen_labels.len());
                                    return (error_term(), Arc::new(Value::Error));
                                }
                            };
                            let core_type = Arc::new(core_type);
                            let core_type_value = self.eval_term(&core_type);
                            core_type_entries.push((label.data.clone(), core_type));
                            self.push_local_param(Some(&name.data), core_type_value);
                            entry.insert(label.location);
                        }
                        Entry::Occupied(entry) => {
                            let seen_range = *entry.get();
                            let current_range = label.location;
                            duplicate_labels.push((label.data.clone(), seen_range, current_range));
                            self.is_type(entry_type);
                        }
                    }
                }

                if !duplicate_labels.is_empty() {
                    self.report(SurfaceToCoreMessage::InvalidRecordType { duplicate_labels });
                }

                self.pop_many_locals(seen_labels.len());
                (
                    core::Term::new(
                        term.location,
                        core::TermData::RecordType(core_type_entries.into()),
                    ),
                    Arc::new(Value::TypeType(max_level)),
                )
            }
            TermData::RecordElim(head_term, label) => {
                let (core_head_term, head_type) = self.synth_type(head_term);

                match head_type.force(self.globals) {
                    Value::RecordType(closure) => {
                        let head_value = self.eval_term(&core_head_term);

                        if let Some(entry_type) =
                            self.record_elim_type(head_value, &label.data, closure)
                        {
                            let core_head_term = Arc::new(core_head_term);
                            let core_term = core::Term::new(
                                term.location,
                                core::TermData::RecordElim(core_head_term, label.data.clone()),
                            );
                            return (core_term, entry_type);
                        }
                    }
                    Value::Error => return (error_term(), Arc::new(Value::Error)),
                    _ => {}
                }

                let head_type = self.read_back_to_surface_term(&head_type);
                self.report(SurfaceToCoreMessage::LabelNotFound {
                    head_location: head_term.location,
                    label_location: label.location,
                    expected_label: label.data.clone(),
                    head_type,
                });
                (error_term(), Arc::new(Value::Error))
            }

            TermData::SequenceTerm(_) => {
                self.report(SurfaceToCoreMessage::AmbiguousTerm {
                    location: term.location,
                    term: AmbiguousTerm::Sequence,
                });
                (error_term(), Arc::new(Value::Error))
            }

            TermData::NumberTerm(_) => {
                self.report(SurfaceToCoreMessage::AmbiguousTerm {
                    location: term.location,
                    term: AmbiguousTerm::NumberLiteral,
                });
                (error_term(), Arc::new(Value::Error))
            }
            TermData::CharTerm(data) => (
                self.parse_char(term.location, data),
                Arc::new(Value::global("Char", 0, [])),
            ),
            TermData::StringTerm(data) => (
                self.parse_string(term.location, data),
                Arc::new(Value::global("String", 0, [])),
            ),

            TermData::Error => (error_term(), Arc::new(Value::Error)),
        }
    }

    fn parse_float<T: Float + From<u8>>(
        &mut self,
        location: Location,
        data: &str,
        make_constant: fn(T) -> core::Constant,
    ) -> core::Term {
        let term_data = literal::State::new(location, data, &self.message_tx)
            .number_to_float()
            .map(make_constant)
            .map_or(core::TermData::Error, core::TermData::from);

        core::Term::new(location, term_data)
    }

    fn parse_unsigned<T: PrimInt + Unsigned>(
        &mut self,
        location: Location,
        source: &str,
        make_constant: fn(T) -> core::Constant,
    ) -> core::Term {
        let term_data = literal::State::new(location, source, &self.message_tx)
            .number_to_unsigned_int()
            .map(make_constant)
            .map_or(core::TermData::Error, core::TermData::from);

        core::Term::new(location, term_data)
    }

    fn parse_signed<T: PrimInt + Signed>(
        &mut self,
        location: Location,
        source: &str,
        make_constant: fn(T) -> core::Constant,
    ) -> core::Term {
        let term_data = literal::State::new(location, source, &self.message_tx)
            .number_to_signed_int()
            .map(make_constant)
            .map_or(core::TermData::Error, core::TermData::from);

        core::Term::new(location, term_data)
    }

    fn parse_char(&mut self, location: Location, source: &str) -> core::Term {
        let term_data = literal::State::new(location, source, &self.message_tx)
            .quoted_to_unicode_char()
            .map(core::Constant::Char)
            .map_or(core::TermData::Error, core::TermData::from);

        core::Term::new(location, term_data)
    }

    fn parse_string(&mut self, location: Location, source: &str) -> core::Term {
        let term_data = literal::State::new(location, source, &self.message_tx)
            .quoted_to_utf8_string()
            .map(core::Constant::String)
            .map_or(core::TermData::Error, core::TermData::from);

        core::Term::new(location, term_data)
    }
}
