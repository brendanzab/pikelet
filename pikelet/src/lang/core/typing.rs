//! Bidirectional type checker for the [core language].
//!
//! This is a simpler implementation of type checking than the one found in
//! [pass::surface_to_core], because it only needs to check the (much simpler)
//! core language, and doesn't need to perform any additional elaboration.
//! We can use it as a way to validate that elaborated terms are well-formed
//! for debugging and development purposes.
//!
//! [core language]: crate::lang::core
//! [`pass::surface_to_core`]: crate::pass::surface_to_core

use contracts::debug_ensures;
use crossbeam_channel::Sender;
use std::sync::Arc;

use crate::lang::core::semantics::{self, Elim, RecordClosure, Unfold, Value};
use crate::lang::core::{Constant, Globals, LocalSize, Locals, Term, TermData};
use crate::reporting::{AmbiguousTerm, CoreTypingMessage, ExpectedType, Message};

/// The state of the type checker.
pub struct State<'me> {
    /// Global definition environment.
    globals: &'me Globals,
    /// Local type environment (used for getting the types of local variables).
    local_declarations: Locals<Arc<Value>>,
    /// Local value environment (used for evaluation).
    local_definitions: Locals<Arc<Value>>,
    /// The diagnostic messages accumulated during type checking.
    message_tx: Sender<Message>,
}

impl<'me> State<'me> {
    /// Construct a new type checker state.
    pub fn new(globals: &'me Globals, message_tx: Sender<Message>) -> State<'me> {
        State {
            globals,
            local_declarations: Locals::new(),
            local_definitions: Locals::new(),
            message_tx,
        }
    }

    /// Get the size of the local environment.
    fn size(&self) -> LocalSize {
        self.local_definitions.size()
    }

    /// Push a local entry.
    fn push_local(&mut self, value: Arc<Value>, r#type: Arc<Value>) {
        self.local_declarations.push(r#type);
        self.local_definitions.push(value);
    }

    /// Push a local parameter.
    fn push_local_param(&mut self, r#type: Arc<Value>) -> Arc<Value> {
        let value = Arc::new(Value::local(self.size().next_level(), []));
        self.push_local(value.clone(), r#type);
        value
    }

    /// Pop a local entry.
    fn pop_local(&mut self) {
        self.local_declarations.pop();
        self.local_definitions.pop();
    }

    /// Pop the given number of local entries.
    fn pop_many_locals(&mut self, count: usize) {
        self.local_declarations.pop_many(count);
        self.local_definitions.pop_many(count);
    }

    /// Report a diagnostic message.
    fn report(&self, message: CoreTypingMessage) {
        self.message_tx.send(message.into()).unwrap();
    }

    /// Evaluate a [`Term`] into a [`Value`].
    ///
    /// [`Value`]: crate::lang::core::semantics::Value
    /// [`Term`]: crate::lang::core::Term
    pub fn eval(&mut self, term: &Term) -> Arc<Value> {
        semantics::eval(self.globals, &mut self.local_definitions, term)
    }

    /// Return the type of the record elimination.
    pub fn record_elim_type(
        &self,
        head_value: Arc<Value>,
        name: &str,
        closure: &RecordClosure,
    ) -> Option<Arc<Value>> {
        semantics::record_elim_type(self.globals, head_value, name, closure)
    }

    /// Read back a value into a normal form using the current state of the elaborator.
    pub fn read_back(&self, value: &Value) -> Term {
        semantics::read_back(
            self.globals,
            self.local_definitions.size(),
            Unfold::Never,
            value,
        )
    }

    /// Check that one [`Value`] is computationally equal to another [`Value`].
    ///
    /// Returns `false` if either value is not a type.
    ///
    /// [`Value`]: crate::lang::core::semantics::Value
    pub fn is_equal(&self, value0: &Value, value1: &Value) -> bool {
        semantics::is_equal(self.globals, self.local_definitions.size(), value0, value1)
    }

    /// Check that a term is a type.
    #[debug_ensures(self.local_declarations.size() == old(self.local_declarations.size()))]
    #[debug_ensures(self.local_definitions.size() == old(self.local_definitions.size()))]
    pub fn is_type(&mut self, term: &Term) -> bool {
        let r#type = self.synth_type(term);
        match r#type.force(self.globals) {
            Value::TypeType => true,
            Value::Error => false,
            _ => {
                self.report(CoreTypingMessage::MismatchedTypes {
                    found_type: self.read_back(&r#type),
                    expected_type: ExpectedType::Universe,
                });
                false
            }
        }
    }

    /// Check that a term is an element of a type.
    #[debug_ensures(self.local_declarations.size() == old(self.local_declarations.size()))]
    #[debug_ensures(self.local_definitions.size() == old(self.local_definitions.size()))]
    pub fn check_type(&mut self, term: &Term, expected_type: &Arc<Value>) {
        match (&term.data, expected_type.force(self.globals)) {
            (_, Value::Error) => {}

            (
                TermData::FunctionTerm(_, output_term),
                Value::FunctionType(_, input_type, output_closure),
            ) => {
                let input_term = self.push_local_param(input_type.clone());
                let output_type = output_closure.apply(self.globals, input_term);
                self.check_type(output_term, &output_type);
                self.pop_local();
            }
            (TermData::FunctionTerm(_, _), _) => {
                self.report(CoreTypingMessage::TooManyInputsInFunctionTerm);
            }

            (TermData::RecordTerm(term_entries), Value::RecordType(closure)) => {
                let mut pending_term_entries = term_entries.iter();
                let mut missing_labels = Vec::new();
                let mut unexpected_labels = Vec::new();
                let mut term_entry_count = 0;

                closure.for_each_entry(self.globals, |label, entry_type| loop {
                    match pending_term_entries.next() {
                        Some((next_label, entry_term)) if next_label == label => {
                            self.check_type(&entry_term, &entry_type);
                            let entry_value = self.eval(&entry_term);

                            self.push_local(entry_value.clone(), entry_type);
                            term_entry_count += 1;

                            break entry_value;
                        }
                        Some((next_label, _)) => unexpected_labels.push(next_label.to_owned()),
                        None => {
                            missing_labels.push(label.to_owned());
                            break Arc::new(Value::Error);
                        }
                    }
                });

                self.pop_many_locals(term_entry_count);
                unexpected_labels.extend(pending_term_entries.map(|(label, _)| label.clone()));

                if !missing_labels.is_empty() || !unexpected_labels.is_empty() {
                    self.report(CoreTypingMessage::InvalidRecordTerm {
                        missing_labels,
                        unexpected_labels,
                    });
                }
            }

            (TermData::EnumTerm(label), Value::EnumType(labels)) => {
                match labels.binary_search(label) {
                    Ok(_) => todo!(),
                    Err(_) => todo!(),
                }
            }
            (TermData::EnumElim(clauses), expected_type) => todo!(),

            (TermData::ArrayTerm(entry_terms), forced_type) => match forced_type.try_global() {
                Some(("Array", [Elim::Function(len), Elim::Function(entry_type)])) => {
                    let forced_entry_type = entry_type.force(self.globals);
                    for entry_term in entry_terms {
                        self.check_type(entry_term, forced_entry_type);
                    }

                    match len.force(self.globals).as_ref() {
                        Value::Constant(Constant::U32(len))
                            if *len as usize == entry_terms.len() => {}
                        _ => {
                            self.report(CoreTypingMessage::MismatchedTypes {
                                expected_type: ExpectedType::Type(self.read_back(expected_type)),
                                found_type: self.read_back(&Value::global(
                                    "Array",
                                    [
                                        Elim::Function(len.clone()),
                                        Elim::Function(entry_type.clone()),
                                    ],
                                )),
                            });
                        }
                    }
                }
                Some(_) | None => {
                    let expected_type = self.read_back(expected_type);
                    self.report(CoreTypingMessage::UnexpectedArrayTerm { expected_type })
                }
            },
            (TermData::ListTerm(entry_terms), forced_type) => match forced_type.try_global() {
                Some(("List", [Elim::Function(entry_type)])) => {
                    let forced_entry_type = entry_type.force(self.globals);
                    for entry_term in entry_terms {
                        self.check_type(entry_term, forced_entry_type);
                    }
                }
                Some(_) | None => {
                    let expected_type = self.read_back(expected_type);
                    self.report(CoreTypingMessage::UnexpectedListTerm { expected_type })
                }
            },

            (_, _) => match self.synth_type(term) {
                found_type if self.is_equal(&found_type, expected_type) => {}
                found_type => self.report(CoreTypingMessage::MismatchedTypes {
                    found_type: self.read_back(&found_type),
                    expected_type: ExpectedType::Type(self.read_back(expected_type)),
                }),
            },
        }
    }

    /// Synthesize the type of a term.
    #[debug_ensures(self.local_declarations.size() == old(self.local_declarations.size()))]
    #[debug_ensures(self.local_definitions.size() == old(self.local_definitions.size()))]
    pub fn synth_type(&mut self, term: &Term) -> Arc<Value> {
        match &term.data {
            TermData::Global(name) => match self.globals.get(name) {
                Some((r#type, _)) => self.eval(r#type),
                None => {
                    self.report(CoreTypingMessage::UnboundGlobal {
                        name: name.to_owned(),
                    });
                    Arc::new(Value::Error)
                }
            },
            TermData::Local(local_index) => match self.local_declarations.get(*local_index) {
                Some(r#type) => r#type.clone(),
                None => {
                    self.report(CoreTypingMessage::UnboundLocal);
                    Arc::new(Value::Error)
                }
            },

            TermData::Ann(term, r#type) => {
                if !self.is_type(r#type) {
                    return Arc::new(Value::Error);
                }
                let r#type = self.eval(r#type);
                self.check_type(term, &r#type);
                r#type
            }

            TermData::TypeType => Arc::new(Value::TypeType),

            TermData::FunctionType(_, input_type, output_type) => {
                if !self.is_type(input_type) {
                    return Arc::new(Value::Error);
                }
                let input_type = self.eval(input_type);

                self.push_local_param(input_type);
                if !self.is_type(output_type) {
                    self.pop_local();
                    return Arc::new(Value::Error);
                }
                self.pop_local();
                Arc::new(Value::TypeType)
            }
            TermData::FunctionTerm(_, _) => {
                self.report(CoreTypingMessage::AmbiguousTerm {
                    term: AmbiguousTerm::FunctionTerm,
                });
                Arc::new(Value::Error)
            }
            TermData::FunctionElim(head_term, input_term) => {
                let head_type = self.synth_type(head_term);
                match head_type.force(self.globals) {
                    Value::FunctionType(_, input_type, output_closure) => {
                        self.check_type(input_term, &input_type);
                        let input_value = self.eval(input_term);
                        output_closure.apply(self.globals, input_value)
                    }
                    Value::Error => Arc::new(Value::Error),
                    _ => {
                        let head_type = self.read_back(&head_type);
                        self.report(CoreTypingMessage::TooManyInputsInFunctionElim { head_type });
                        Arc::new(Value::Error)
                    }
                }
            }

            TermData::RecordTerm(term_entries) => {
                if term_entries.is_empty() {
                    Arc::from(Value::RecordType(RecordClosure::new(
                        self.local_definitions.clone(),
                        Arc::new([]),
                    )))
                } else {
                    self.report(CoreTypingMessage::AmbiguousTerm {
                        term: AmbiguousTerm::RecordTerm,
                    });
                    Arc::new(Value::Error)
                }
            }
            TermData::RecordType(type_entries) => {
                use std::collections::BTreeSet;

                let mut duplicate_labels = Vec::new();
                let mut seen_labels = BTreeSet::new();

                for (name, r#type) in type_entries.iter() {
                    if !seen_labels.insert(name) {
                        duplicate_labels.push(name.clone());
                    }
                    if !self.is_type(r#type) {
                        self.pop_many_locals(seen_labels.len());
                        return Arc::new(Value::Error);
                    }
                    let r#type = self.eval(r#type);
                    self.push_local_param(r#type);
                }

                self.pop_many_locals(seen_labels.len());

                if !duplicate_labels.is_empty() {
                    self.report(CoreTypingMessage::InvalidRecordType { duplicate_labels });
                }

                Arc::new(Value::TypeType)
            }
            TermData::RecordElim(head_term, label) => {
                let head_type = self.synth_type(head_term);

                match head_type.force(self.globals) {
                    Value::RecordType(closure) => {
                        let head_value = self.eval(head_term);

                        if let Some(entry_type) = self.record_elim_type(head_value, label, closure)
                        {
                            return entry_type;
                        }
                    }
                    Value::Error => return Arc::new(Value::Error),
                    _ => {}
                }

                let head_type = self.read_back(&head_type);
                self.report(CoreTypingMessage::LabelNotFound {
                    expected_label: label.clone(),
                    head_type,
                });
                Arc::new(Value::Error)
            }

            TermData::ArrayTerm(_) => {
                self.report(CoreTypingMessage::AmbiguousTerm {
                    term: AmbiguousTerm::Sequence,
                });
                Arc::new(Value::Error)
            }
            TermData::ListTerm(_) => {
                self.report(CoreTypingMessage::AmbiguousTerm {
                    term: AmbiguousTerm::Sequence,
                });
                Arc::new(Value::Error)
            }

            TermData::EnumType(labels) => todo!(),
            TermData::EnumTerm(label) => todo!(),
            TermData::EnumElim(clauses) => todo!(),

            TermData::Constant(constant) => Arc::new(match constant {
                Constant::U8(_) => Value::global("U8", []),
                Constant::U16(_) => Value::global("U16", []),
                Constant::U32(_) => Value::global("U32", []),
                Constant::U64(_) => Value::global("U64", []),
                Constant::S8(_) => Value::global("S8", []),
                Constant::S16(_) => Value::global("S16", []),
                Constant::S32(_) => Value::global("S32", []),
                Constant::S64(_) => Value::global("S64", []),
                Constant::F32(_) => Value::global("F32", []),
                Constant::F64(_) => Value::global("F64", []),
                Constant::Char(_) => Value::global("Char", []),
                Constant::String(_) => Value::global("String", []),
            }),

            TermData::Error => Arc::new(Value::Error),
        }
    }
}
