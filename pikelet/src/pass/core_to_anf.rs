//! Type-preserving translation from the [core language][crate::lang::core] to
//! [A-normal form][crate::lang::core].
//!
//! The main inspiration for this translation is Section 4 of William Bowman's
//! dissertation, [Compiling with Dependent Types][wjb-dissertation].
//!
//! [wjb-dissertation]: https://www.williamjbowman.com/resources/wjb-dissertation.pdf

use crate::lang::{anf, core};

pub fn from_term(term: &core::Term, continuation: anf::Continuation) -> anf::Configuration {
    match term {
        core::Term::Global(name) => continuation.compose(anf::Computation::Value(Box::new(
            anf::Value::Global(name.clone()),
        ))),
        core::Term::Local(index) => {
            continuation.compose(anf::Computation::Value(Box::new(anf::Value::Local(*index))))
        }

        core::Term::Ann(term, r#type) => todo!(),

        core::Term::TypeType(level) => continuation.compose(anf::Computation::Value(Box::new(
            anf::Value::TypeType(*level),
        ))),
        core::Term::Lift(term, offset) => todo!(),

        core::Term::FunctionType(input_name_hint, input_type, output_type) => {
            continuation.compose(anf::Computation::Value(Box::new(anf::Value::FunctionType(
                input_name_hint.clone(),
                Box::new(from_term(input_type, anf::Continuation::Nil)),
                Box::new(from_term(output_type, anf::Continuation::Nil)),
            ))))
        }
        core::Term::FunctionTerm(input_name_hint, output_term) => {
            continuation.compose(anf::Computation::Value(Box::new(anf::Value::FunctionTerm(
                input_name_hint.clone(),
                Box::new(from_term(output_term, anf::Continuation::Nil)),
            ))))
        }
        core::Term::FunctionElim(head_term, input_term) => todo!(),

        core::Term::RecordType(type_entries) => todo!(),
        core::Term::RecordTerm(term_entries) => todo!(),
        core::Term::RecordElim(head_term, label) => from_term(
            head_term,
            // TODO: do we need to shift indices?
            anf::Continuation::BindHole(continuation.compose(anf::Computation::RecordElim(
                Box::new(anf::Value::Local(todo!())),
                label.clone(),
            ))),
        ),

        core::Term::Sequence(entry_terms) => todo!(),

        core::Term::Constant(constant) => continuation.compose(anf::Computation::Value(Box::new(
            anf::Value::Constant(constant.clone()),
        ))),

        core::Term::Error => {
            continuation.compose(anf::Computation::Value(Box::new(anf::Value::Error)))
        }
    }
}
