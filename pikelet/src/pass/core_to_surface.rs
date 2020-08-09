//! Distill the core language into the surface language.

#![allow(clippy::reversed_empty_ranges)]

use std::collections::HashMap;

use crate::lang::core::{Constant, Globals, Locals, Term, UniverseLevel, UniverseOffset};
use crate::lang::surface;

pub struct State<'me> {
    globals: &'me Globals,
    usages: HashMap<String, Usage>,
    names: Locals<String>,
}

struct Usage {
    base_name: Option<String>,
    count: usize,
}

const DEFAULT_NAME: &str = "t";

impl<'me> State<'me> {
    pub fn new(globals: &'me Globals) -> State<'me> {
        let usages = globals
            .entries()
            .map(|(name, _)| {
                (
                    name.to_owned(),
                    Usage {
                        base_name: None,
                        count: 1,
                    },
                )
            })
            .collect();

        State {
            globals,
            usages,
            names: Locals::new(),
        }
    }

    // TODO: Find optimal names by using free variables
    // TODO: Reduce string allocations
    pub fn push_name(&mut self, name_hint: Option<&str>) -> String {
        let base_name = name_hint.unwrap_or(DEFAULT_NAME);
        let (fresh_name, base_name) = match self.usages.get_mut(base_name) {
            // The name has not been used yet
            None => (base_name.to_owned(), None),
            // The name is in use - find a free one to use!
            Some(usage) => {
                let mut suffix = usage.count;
                // Update the usage count to make finding the next name faster.
                usage.count += 1;
                // Attempt names with incrementing numeric suffixes until we
                // find one that has yet to be used.
                loop {
                    // TODO: Reduce string allocations
                    match format!("{}-{}", base_name, suffix) {
                        // Candidate name has been used - try another!
                        name if self.usages.contains_key(&name) => suffix += 1,
                        // The candidate has not been used - we're free to use it
                        name => break (name, Some(base_name.to_owned())),
                    }
                }
            }
        };

        let usage = Usage {
            base_name,
            count: 1,
        };
        // TODO: Reduce cloning of names
        self.usages.insert(fresh_name.clone(), usage);
        self.names.push(fresh_name.clone());
        fresh_name
    }

    pub fn pop_name(&mut self) {
        if let Some(mut name) = self.names.pop() {
            while let Some(base_name) = self.remove_usage(name) {
                name = base_name;
            }
        }
    }

    fn remove_usage(&mut self, name: String) -> Option<String> {
        use std::collections::hash_map::Entry;

        match self.usages.entry(name) {
            Entry::Occupied(entry) if entry.get().count >= 1 => entry.remove().base_name,
            Entry::Occupied(mut entry) => {
                entry.get_mut().count -= 1;
                None
            }
            Entry::Vacant(_) => None,
        }
    }

    pub fn pop_many_names(&mut self, count: usize) {
        (0..count).for_each(|_| self.pop_name());
    }
}

pub fn from_term(state: &mut State<'_>, term: &Term) -> surface::Term<String> {
    match term {
        Term::Universe(level) => {
            let universe0 = match state.globals.get("Type") {
                Some(_) => surface::Term::Name(0..0, "Type".to_owned()),
                None => surface::Term::Error(0..0), // TODO: Log error?
            };
            match level {
                UniverseLevel(0) => universe0,
                UniverseLevel(level) => surface::Term::Lift(0..0, Box::new(universe0), *level),
            }
        }
        Term::Global(name) => match state.globals.get(name) {
            Some(_) => surface::Term::Name(0..0, name.to_owned()),
            None => surface::Term::Error(0..0), // TODO: Log error?
        },
        Term::Local(index) => match state.names.get(*index) {
            Some(name) => surface::Term::Name(0..0, name.clone()),
            None => surface::Term::Error(0..0), // TODO: Log error?
        },
        Term::Constant(constant) => delaborate_constant(constant),
        Term::Sequence(entry_terms) => {
            let core_entry_terms = entry_terms
                .iter()
                .map(|entry_term| from_term(state, entry_term))
                .collect();

            surface::Term::Sequence(0..0, core_entry_terms)
        }
        Term::Ann(term, r#type) => surface::Term::Ann(
            Box::new(from_term(state, term)),
            Box::new(from_term(state, r#type)),
        ),
        Term::RecordType(type_entries) => {
            let core_type_entries = type_entries
                .iter()
                .map(|(label, r#type)| {
                    let r#type = from_term(state, r#type);
                    match state.push_name(Some(label)) {
                        name if name == *label => (0..0, label.clone(), None, r#type),
                        name => (0..0, label.clone(), Some(name), r#type),
                    }
                })
                .collect();

            surface::Term::RecordType(0..0, core_type_entries)
        }
        Term::RecordTerm(term_entries) => {
            let core_term_entries = term_entries
                .iter()
                .map(|(entry_name, entry_term)| {
                    (0..0, entry_name.clone(), from_term(state, entry_term))
                })
                .collect();
            state.pop_many_names(term_entries.len());

            surface::Term::RecordTerm(0..0, core_term_entries)
        }
        Term::RecordElim(head_term, label) => {
            surface::Term::RecordElim(Box::new(from_term(state, head_term)), 0..0, label.clone())
        }
        Term::FunctionType(input_name_hint, input_type, output_type) => {
            // FIXME: properly group inputs!
            let input_type = from_term(state, input_type);
            let fresh_input_name = state.push_name(input_name_hint.as_ref().map(String::as_ref));
            let input_type_groups = vec![(vec![(0..0, fresh_input_name)], input_type)];

            surface::Term::FunctionType(
                0..,
                input_type_groups,
                Box::new(from_term(state, output_type)),
            )
        }
        Term::FunctionTerm(input_name_hint, output_term) => {
            let mut current_output_term = output_term;

            let fresh_input_name = state.push_name(Some(input_name_hint));
            let mut input_names = vec![(0..0, fresh_input_name)];

            while let Term::FunctionTerm(input_name_hint, output_term) =
                current_output_term.as_ref()
            {
                let fresh_input_name = state.push_name(Some(input_name_hint));
                input_names.push((0..0, fresh_input_name));
                current_output_term = output_term;
            }

            let output_term = from_term(state, current_output_term);
            state.pop_many_names(input_names.len());

            surface::Term::FunctionTerm(0.., input_names, Box::new(output_term))
        }
        Term::FunctionElim(head_term, input_term) => {
            let mut current_head_term = head_term;

            let mut input_terms = vec![from_term(state, input_term)];
            while let Term::FunctionElim(head_term, input_term) = current_head_term.as_ref() {
                input_terms.push(from_term(state, input_term));
                current_head_term = head_term;
            }
            input_terms.reverse();

            let head_term = from_term(state, current_head_term);
            surface::Term::FunctionElim(Box::new(head_term), input_terms)
        }
        Term::Lift(term, UniverseOffset(offset)) => {
            surface::Term::Lift(0..0, Box::new(from_term(state, term)), *offset)
        }
        Term::Error => surface::Term::Error(0..0),
    }
}

pub fn delaborate_constant(constant: &Constant) -> surface::Term<String> {
    use crate::lang::surface::Literal::{Char, Number, String};

    match constant {
        Constant::U8(value) => surface::Term::Literal(0..0, Number(value.to_string())),
        Constant::U16(value) => surface::Term::Literal(0..0, Number(value.to_string())),
        Constant::U32(value) => surface::Term::Literal(0..0, Number(value.to_string())),
        Constant::U64(value) => surface::Term::Literal(0..0, Number(value.to_string())),
        Constant::S8(value) => surface::Term::Literal(0..0, Number(value.to_string())),
        Constant::S16(value) => surface::Term::Literal(0..0, Number(value.to_string())),
        Constant::S32(value) => surface::Term::Literal(0..0, Number(value.to_string())),
        Constant::S64(value) => surface::Term::Literal(0..0, Number(value.to_string())),
        Constant::F32(value) => surface::Term::Literal(0..0, Number(value.to_string())),
        Constant::F64(value) => surface::Term::Literal(0..0, Number(value.to_string())),
        Constant::Char(value) => surface::Term::Literal(0..0, Char(format!("{:?}", value))),
        Constant::String(value) => surface::Term::Literal(0..0, String(format!("{:?}", value))),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn push_default_name() {
        let globals = Globals::default();
        let mut state = State::new(&globals);

        assert_eq!(state.push_name(None), "t");
        assert_eq!(state.push_name(Some("t")), "t-1");
        assert_eq!(state.push_name(None), "t-2");
    }

    #[test]
    fn push_and_pop_default_name() {
        let globals = Globals::default();
        let mut state = State::new(&globals);

        assert_eq!(state.push_name(None), "t");
        state.pop_name();
        assert_eq!(state.push_name(None), "t");
        assert_eq!(state.push_name(None), "t-1");
        state.pop_name();
        state.pop_name();
        assert_eq!(state.push_name(None), "t");
        assert_eq!(state.push_name(None), "t-1");
        assert_eq!(state.push_name(None), "t-2");
        state.pop_name();
        state.pop_name();
        state.pop_name();
        assert_eq!(state.push_name(None), "t");
        assert_eq!(state.push_name(None), "t-1");
        assert_eq!(state.push_name(None), "t-2");
    }

    #[test]
    fn push_name() {
        let globals = Globals::default();
        let mut state = State::new(&globals);

        assert_eq!(state.push_name(Some("test")), "test");
        assert_eq!(state.push_name(Some("test")), "test-1");
        assert_eq!(state.push_name(Some("test")), "test-2");
    }

    #[test]
    fn push_and_pop_name() {
        let globals = Globals::default();
        let mut state = State::new(&globals);

        assert_eq!(state.push_name(Some("test")), "test");
        state.pop_name();
        assert_eq!(state.push_name(Some("test")), "test");
        assert_eq!(state.push_name(Some("test")), "test-1");
        state.pop_name();
        state.pop_name();
        assert_eq!(state.push_name(Some("test")), "test");
        assert_eq!(state.push_name(Some("test")), "test-1");
        assert_eq!(state.push_name(Some("test")), "test-2");
        state.pop_name();
        state.pop_name();
        state.pop_name();
        assert_eq!(state.push_name(Some("test")), "test");
        assert_eq!(state.push_name(Some("test")), "test-1");
        assert_eq!(state.push_name(Some("test")), "test-2");
    }

    #[test]
    fn push_fresh_name() {
        let globals = Globals::default();
        let mut state = State::new(&globals);

        assert_eq!(state.push_name(Some("test")), "test");
        assert_eq!(state.push_name(Some("test")), "test-1");
        assert_eq!(state.push_name(Some("test-1")), "test-1-1");
        assert_eq!(state.push_name(Some("test-1")), "test-1-2");
        assert_eq!(state.push_name(Some("test-1-2")), "test-1-2-1");
    }

    #[test]
    fn push_global_name() {
        let globals = Globals::default();
        let mut state = State::new(&globals);

        assert_eq!(state.push_name(Some("Type")), "Type-1");
        assert_eq!(state.push_name(Some("Type")), "Type-2");
    }
}
