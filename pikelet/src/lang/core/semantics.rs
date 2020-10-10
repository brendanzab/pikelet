//! The operational semantics of the language, implemented using [normalisation-by-evaluation].
//!
//! [normalisation-by-evaluation]: https://en.wikipedia.org/wiki/Normalisation_by_evaluation

use contracts::debug_ensures;
use once_cell::sync::OnceCell;
use std::cell::RefCell;
use std::sync::Arc;

use crate::lang::core::{
    Constant, Globals, LocalLevel, LocalSize, Locals, Term, TermData, UniverseLevel, UniverseOffset,
};

/// Values in the core language.
#[derive(Clone, Debug)]
pub enum Value {
    /// A value that is stuck on some head that cannot be reduced further.
    ///
    /// This is sometimes called a 'neutral value' or an 'accumulator'.
    Stuck(Head, Vec<Elim>),
    /// A value that was previously stuck on some head, but is now unstuck due
    /// to its definition now being known.
    ///
    /// This is sometimes called a 'glued value'.
    ///
    /// We keep the head and eliminations around from the stuck value in order
    /// to reduce the size-blowup that can result from deeply-normalizing terms.
    /// This can help with:
    ///
    /// - reducing the size of elaborated terms when read-back is needed
    /// - making displayed terms easier to understand in error messages
    ///
    /// See the following for more information:
    ///
    /// - [AndrasKovacs/smalltt](https://github.com/AndrasKovacs/smalltt/)
    /// - [ollef/sixty](https://github.com/ollef/sixty/)
    /// - [Non-deterministic normalization-by-evaluation](https://gist.github.com/AndrasKovacs/a0e0938113b193d6b9c1c0620d853784)
    /// - [Example of the blowup that can occur when reading back values](https://twitter.com/brendanzab/status/1283278258818002944)
    Unstuck(Head, Vec<Elim>, Arc<LazyValue>),

    /// The type of types.
    TypeType(UniverseLevel),

    /// Function types.
    ///
    /// Also known as: pi type, dependent product type.
    FunctionType(Option<String>, Arc<Value>, Closure),
    /// Function terms.
    ///
    /// Also known as: lambda abstraction, anonymous function.
    FunctionTerm(String, Closure),

    /// Record types.
    RecordType(RecordClosure),
    /// Record terms.
    RecordTerm(RecordClosure),

    /// Ordered sequences.
    Sequence(Vec<Arc<Value>>),

    /// Constants.
    Constant(Constant),

    /// Error sentinel.
    Error,
}

impl Value {
    /// Create a type of types at the given level.
    pub fn type_type(level: impl Into<UniverseLevel>) -> Value {
        Value::TypeType(level.into())
    }

    /// Create a global variable.
    pub fn global(name: impl Into<String>, offset: impl Into<UniverseOffset>) -> Value {
        Value::Stuck(Head::Global(name.into(), offset.into()), Vec::new())
    }

    /// Create a local variable.
    pub fn local(level: impl Into<LocalLevel>) -> Value {
        Value::Stuck(Head::Local(level.into()), Vec::new())
    }

    /// Force any unstuck values.
    pub fn force(&self, globals: &Globals) -> &Value {
        match self {
            Value::Unstuck(_, _, value) => Value::force(LazyValue::force(value, globals), globals),
            value => value,
        }
    }
}

impl From<Constant> for Value {
    fn from(constant: Constant) -> Value {
        Value::Constant(constant)
    }
}

/// The head of an elimination.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Head {
    /// Global variables.
    Global(String, UniverseOffset),
    /// Local variables.
    Local(LocalLevel),
}

/// An eliminator, to be used in the spine of an elimination.
#[derive(Clone, Debug)]
pub enum Elim {
    /// Function eliminators.
    ///
    /// Also known as: function application.
    Function(Arc<LazyValue>),
    /// Record eliminators.
    ///
    /// Also known as: record projections, field lookup.
    Record(String),
}

/// Closure, capturing the current universe offset and the current locals in scope.
#[derive(Clone, Debug)]
pub struct Closure {
    universe_offset: UniverseOffset,
    values: Locals<Arc<Value>>,
    term: Arc<Term>,
}

impl Closure {
    pub fn new(
        universe_offset: UniverseOffset,
        values: Locals<Arc<Value>>,
        term: Arc<Term>,
    ) -> Closure {
        Closure {
            universe_offset,
            values,
            term,
        }
    }

    /// Eliminate a closure.
    pub fn elim(&self, globals: &Globals, input: Arc<Value>) -> Arc<Value> {
        let mut values = self.values.clone();
        values.push(input);
        eval_term(globals, self.universe_offset, &mut values, &self.term)
    }
}

/// Record closure, capturing the current universe offset and the current locals in scope.
#[derive(Clone, Debug)]
pub struct RecordClosure {
    universe_offset: UniverseOffset,
    values: Locals<Arc<Value>>,
    entries: Arc<[(String, Arc<Term>)]>,
}

impl RecordClosure {
    pub fn new(
        universe_offset: UniverseOffset,
        values: Locals<Arc<Value>>,
        entries: Arc<[(String, Arc<Term>)]>,
    ) -> RecordClosure {
        RecordClosure {
            universe_offset,
            values,
            entries,
        }
    }

    /// Apply a callback to each of the entries in the record closure.
    pub fn for_each_entry<'closure>(
        &'closure self,
        globals: &Globals,
        mut on_entry: impl FnMut(&'closure str, Arc<Value>) -> Arc<Value>,
    ) {
        let universe_offset = self.universe_offset;
        let mut values = self.values.clone();

        for (label, entry_value) in self.entries.iter() {
            let entry_value = eval_term(globals, universe_offset, &mut values, entry_value);
            values.push(on_entry(label, entry_value));
        }
    }

    /// Find an entry in the record closure.
    pub fn find_entry<'closure, T>(
        &'closure self,
        globals: &Globals,
        mut on_entry: impl FnMut(&'closure str, Arc<Value>) -> Result<T, Arc<Value>>,
    ) -> Option<T> {
        let universe_offset = self.universe_offset;
        let mut values = self.values.clone();

        for (label, entry_value) in self.entries.iter() {
            let entry_value = eval_term(globals, universe_offset, &mut values, entry_value);
            match on_entry(label, entry_value) {
                Ok(t) => return Some(t),
                Err(entry_value) => values.push(entry_value),
            }
        }

        None
    }
}

/// Initialization operation for lazy values.
///
/// We need to use a [defunctionalized] representation because Rust does not allow
/// closures of type `dyn (Clone + FnOnce() -> Arc<Value>)`.
///
/// [defunctionalized]: https://en.wikipedia.org/wiki/Defunctionalization
#[derive(Clone, Debug)]
enum LazyInit {
    EvalTerm(UniverseOffset, Locals<Arc<Value>>, Arc<Term>),
    ApplyElim(Arc<LazyValue>, Elim),
}

/// A lazily initialized value.
#[derive(Clone, Debug)]
pub struct LazyValue {
    /// Initialization operation. Will be set to `None` if `cell` is forced.
    init: RefCell<Option<LazyInit>>,
    /// A once-cell to hold the lazily initialized value.
    cell: OnceCell<Arc<Value>>,
}

impl LazyValue {
    /// Eagerly construct the lazy value.
    pub fn new(value: Arc<Value>) -> LazyValue {
        LazyValue {
            init: RefCell::new(None),
            cell: OnceCell::from(value),
        }
    }

    /// Lazily evaluate a term using the given universe offset and local values.
    pub fn eval_term(
        universe_offset: UniverseOffset,
        values: Locals<Arc<Value>>,
        term: Arc<Term>,
    ) -> LazyValue {
        LazyValue {
            init: RefCell::new(Some(LazyInit::EvalTerm(universe_offset, values, term))),
            cell: OnceCell::new(),
        }
    }

    /// Lazily apply an elimination.
    pub fn apply_elim(head: Arc<LazyValue>, elim: Elim) -> LazyValue {
        LazyValue {
            init: RefCell::new(Some(LazyInit::ApplyElim(head, elim))),
            cell: OnceCell::new(),
        }
    }

    /// Force the evaluation of a lazy value.
    pub fn force(&self, globals: &Globals) -> &Arc<Value> {
        self.cell.get_or_init(|| match self.init.replace(None) {
            Some(LazyInit::EvalTerm(universe_offset, mut values, term)) => {
                eval_term(globals, universe_offset, &mut values, &term)
            }
            Some(LazyInit::ApplyElim(head, Elim::Record(label))) => {
                apply_record_elim(globals, head.force(globals).clone(), &label)
            }
            Some(LazyInit::ApplyElim(head, Elim::Function(input))) => {
                apply_function_elim(globals, head.force(globals).clone(), input)
            }
            None => panic!("Lazy instance has previously been poisoned"),
        })
    }
}

/// Fully normalize a [`Term`] using [normalization by evaluation].
///
/// [`Term`]: crate::lang::core::Term
/// [normalization by evaluation]: https://en.wikipedia.org/wiki/Normalisation_by_evaluation
#[debug_ensures(values.size() == old(values.size()))]
pub fn normalize_term(
    globals: &Globals,
    universe_offset: UniverseOffset,
    values: &mut Locals<Arc<Value>>,
    term: &Term,
) -> Term {
    let value = eval_term(globals, universe_offset, values, term);
    read_back_value(globals, values.size(), Unfold::Always, &value)
}

/// Evaluate a [`Term`] into a [`Value`].
///
/// [`Value`]: crate::lang::core::semantics::Value
/// [`Term`]: crate::lang::core::Term
#[debug_ensures(values.size() == old(values.size()))]
pub fn eval_term(
    globals: &Globals,
    universe_offset: UniverseOffset,
    values: &mut Locals<Arc<Value>>,
    term: &Term,
) -> Arc<Value> {
    match &term.data {
        TermData::Global(name) => match globals.get(name) {
            Some((_, Some(term))) => {
                let head = Head::Global(name.into(), universe_offset);
                let value = LazyValue::eval_term(universe_offset, values.clone(), term.clone());
                Arc::new(Value::Unstuck(head, Vec::new(), Arc::new(value)))
            }
            Some((_, None)) | None => {
                let head = Head::Global(name.into(), universe_offset);
                Arc::new(Value::Stuck(head, Vec::new()))
            }
        },
        TermData::Local(index) => match values.get(*index) {
            Some(value) => {
                let head = Head::Local(index.to_level(values.size()).unwrap()); // TODO: Handle overflow
                let value = LazyValue::new(value.clone()); // FIXME: Apply universe_offset?
                Arc::new(Value::Unstuck(head, Vec::new(), Arc::new(value)))
            }
            None => {
                let head = Head::Local(index.to_level(values.size()).unwrap()); // TODO: Handle overflow
                Arc::new(Value::Stuck(head, Vec::new()))
            }
        },

        TermData::Ann(term, _) => eval_term(globals, universe_offset, values, term),

        TermData::TypeType(level) => {
            let universe_level = (*level + universe_offset).unwrap(); // FIXME: Handle overflow
            Arc::new(Value::type_type(universe_level))
        }
        TermData::Lift(term, offset) => {
            let universe_offset = (universe_offset + *offset).unwrap(); // FIXME: Handle overflow
            eval_term(globals, universe_offset, values, term)
        }

        TermData::RecordType(type_entries) => Arc::new(Value::RecordType(RecordClosure::new(
            universe_offset,
            values.clone(),
            type_entries.clone(),
        ))),
        TermData::RecordTerm(term_entries) => Arc::new(Value::RecordTerm(RecordClosure::new(
            universe_offset,
            values.clone(),
            term_entries.clone(),
        ))),
        TermData::RecordElim(head, label) => {
            let head = eval_term(globals, universe_offset, values, head);
            apply_record_elim(globals, head, label)
        }

        TermData::FunctionType(input_name_hint, input_type, output_type) => {
            Arc::new(Value::FunctionType(
                input_name_hint.clone(),
                eval_term(globals, universe_offset, values, input_type),
                Closure::new(universe_offset, values.clone(), output_type.clone()),
            ))
        }
        TermData::FunctionTerm(input_name, output_term) => Arc::new(Value::FunctionTerm(
            input_name.clone(),
            Closure::new(universe_offset, values.clone(), output_term.clone()),
        )),
        TermData::FunctionElim(head, input) => {
            let head = eval_term(globals, universe_offset, values, head);
            let input = LazyValue::eval_term(universe_offset, values.clone(), input.clone());
            apply_function_elim(globals, head, Arc::new(input))
        }

        TermData::Sequence(term_entries) => {
            let value_entries = term_entries
                .iter()
                .map(|entry_term| eval_term(globals, universe_offset, values, entry_term))
                .collect();

            Arc::new(Value::Sequence(value_entries))
        }

        TermData::Constant(constant) => Arc::new(Value::from(constant.clone())),

        TermData::Error => Arc::new(Value::Error),
    }
}

/// Return the type of the record elimination.
pub fn record_elim_type(
    globals: &Globals,
    head_value: Arc<Value>,
    label: &str,
    closure: &RecordClosure,
) -> Option<Arc<Value>> {
    closure.find_entry(globals, |entry_label, entry_type| {
        if entry_label == label {
            Ok(entry_type)
        } else {
            Err(apply_record_elim(globals, head_value.clone(), label))
        }
    })
}

/// Apply a record term elimination.
fn apply_record_elim(globals: &Globals, mut head_value: Arc<Value>, label: &str) -> Arc<Value> {
    match Arc::make_mut(&mut head_value) {
        Value::Stuck(_, spine) => {
            spine.push(Elim::Record(label.to_owned()));
            head_value
        }
        Value::Unstuck(_, spine, value) => {
            spine.push(Elim::Record(label.to_owned()));
            *value = Arc::new(LazyValue::apply_elim(
                value.clone(),
                Elim::Record(label.to_owned()),
            ));
            head_value
        }

        Value::RecordTerm(closure) => closure
            .find_entry(globals, |entry_label, entry_value| {
                if entry_label == label {
                    Ok(entry_value)
                } else {
                    Err(entry_value)
                }
            })
            .unwrap_or_else(|| Arc::new(Value::Error)),

        _ => Arc::new(Value::Error),
    }
}

/// Apply a function term elimination.
fn apply_function_elim(
    globals: &Globals,
    mut head_value: Arc<Value>,
    input: Arc<LazyValue>,
) -> Arc<Value> {
    match Arc::make_mut(&mut head_value) {
        Value::Stuck(_, spine) => {
            spine.push(Elim::Function(input));
            head_value
        }
        Value::Unstuck(_, spine, value) => {
            spine.push(Elim::Function(input.clone()));
            *value = Arc::new(LazyValue::apply_elim(value.clone(), Elim::Function(input)));
            head_value
        }

        Value::FunctionTerm(_, output_closure) => {
            output_closure.elim(globals, input.force(globals).clone())
        }

        _ => Arc::new(Value::Error),
    }
}

/// Describes how definitions should be unfolded to when reading back values.
#[derive(Copy, Clone, Debug)]
pub enum Unfold {
    /// Unfold the least possible amount.
    ///
    /// This avoids generating bloated terms, which can be detrimental for
    /// performance and difficult for humans to read. Examples of where this
    /// might be useful include:
    ///
    /// - elaborating partially annotated surface terms into core terms that
    ///   require explicit type annotations
    /// - displaying terms in diagnostic messages to the user
    Minimal,
    /// Always unfold global and local definitions.
    ///
    /// This is useful for fully normalizing terms.
    Always,
}

/// Attempt to read-back the head of an elimination into the term syntax.
///
/// Returns `None` if the head was not valid for the current size of the local
/// environment. This could occur at the head of a [`Value::Unstuck`] value that
/// has escaped from its original scope.
fn read_back_head(local_size: LocalSize, head: &Head) -> Option<Term> {
    match head {
        Head::Global(name, shift) => {
            let global = Term::from(TermData::Global(name.clone()));
            match shift {
                UniverseOffset(0) => Some(global),
                shift => Some(Term::from(TermData::Lift(Arc::new(global), *shift))),
            }
        }
        Head::Local(level) => {
            let index = level.to_index(local_size)?;
            Some(Term::from(TermData::Local(index)))
        }
    }
}

/// Read-back a spine of eliminators into the term syntax.
fn read_back_stuck_value(
    globals: &Globals,
    local_size: LocalSize,
    unfold: Unfold,
    head: Term,
    spine: &[Elim],
) -> Term {
    spine.iter().fold(head, |head, elim| match elim {
        Elim::Function(input) => {
            let input = read_back_value(globals, local_size, unfold, input.force(globals));
            Term::from(TermData::FunctionElim(Arc::new(head), Arc::new(input)))
        }
        Elim::Record(label) => Term::from(TermData::RecordElim(Arc::new(head), label.clone())),
    })
}

/// Read-back a value into the term syntax.
pub fn read_back_value(
    globals: &Globals,
    local_size: LocalSize,
    unfold: Unfold,
    value: &Value,
) -> Term {
    match value {
        Value::Stuck(head, spine) => {
            let head = read_back_head(local_size, head).unwrap();
            read_back_stuck_value(globals, local_size, unfold, head, spine)
        }
        Value::Unstuck(head, spine, value) => match unfold {
            // NOTE: Not sure if this is actually valid when using levels with
            // unstuck values! We might need to use fresh variables for local
            // variables in values instead, in order to be sure that we don't
            // accidentally compare levels that originate from different scopes.
            Unfold::Minimal => match read_back_head(local_size, head) {
                Some(head) => read_back_stuck_value(globals, local_size, unfold, head, spine),
                // The level is not valid at the current scope, so unfold the value!
                None => read_back_value(globals, local_size, unfold, value.force(globals)),
            },
            Unfold::Always => read_back_value(globals, local_size, unfold, value.force(globals)),
        },

        Value::TypeType(level) => Term::from(TermData::TypeType(*level)),

        Value::FunctionType(input_name_hint, input_type, output_closure) => {
            let local = Arc::new(Value::local(local_size.next_level()));
            let input_type = Arc::new(read_back_value(globals, local_size, unfold, input_type));
            let output_type = output_closure.elim(globals, local);
            let output_type =
                read_back_value(globals, local_size.increment(), unfold, &output_type);

            Term::from(TermData::FunctionType(
                input_name_hint.clone(),
                input_type,
                Arc::new(output_type),
            ))
        }
        Value::FunctionTerm(input_name_hint, output_closure) => {
            let local = Arc::new(Value::local(local_size.next_level()));
            let output_term = output_closure.elim(globals, local);
            let output_term =
                read_back_value(globals, local_size.increment(), unfold, &output_term);

            Term::from(TermData::FunctionTerm(
                input_name_hint.clone(),
                Arc::new(output_term),
            ))
        }

        Value::RecordType(closure) => {
            let mut local_size = local_size;
            let mut type_entries = Vec::with_capacity(closure.entries.len());

            closure.for_each_entry(globals, |label, entry_type| {
                let entry_type = read_back_value(globals, local_size, unfold, &entry_type);
                type_entries.push((label.to_owned(), Arc::new(entry_type)));

                let local_level = local_size.next_level();
                local_size = local_size.increment();

                Arc::new(Value::local(local_level))
            });

            Term::from(TermData::RecordType(type_entries.into()))
        }
        Value::RecordTerm(closure) => {
            let mut local_size = local_size;
            let mut term_entries = Vec::with_capacity(closure.entries.len());

            closure.for_each_entry(globals, |label, entry_term| {
                let entry_term = read_back_value(globals, local_size, unfold, &entry_term);
                term_entries.push((label.to_owned(), Arc::new(entry_term)));

                let local_level = local_size.next_level();
                local_size = local_size.increment();

                Arc::new(Value::local(local_level))
            });

            Term::from(TermData::RecordTerm(term_entries.into()))
        }

        Value::Sequence(value_entries) => {
            let term_entries = value_entries
                .iter()
                .map(|value_entry| {
                    Arc::new(read_back_value(globals, local_size, unfold, value_entry))
                })
                .collect();

            Term::from(TermData::Sequence(term_entries))
        }

        Value::Constant(constant) => Term::from(TermData::from(constant.clone())),

        Value::Error => Term::from(TermData::Error),
    }
}

/// Check that one elimination head is equal to another elimination head.
fn is_equal_head(local_size: LocalSize, head0: &Head, head1: &Head) -> bool {
    match (head0, head1) {
        (Head::Global(name0, _), Head::Global(name1, _)) => name0 == name1,
        (Head::Local(level0), Head::Local(level1)) => {
            match (level0.to_index(local_size), level1.to_index(local_size)) {
                (Some(index0), Some(index1)) => index0 == index1,
                // One or both of levels were invalid for the current local
                // environment, and so they must not be equal.
                (_, _) => false,
            }
        }
        (_, _) => false,
    }
}

/// Check that one stuck value is equal to another stuck value.
fn is_equal_stuck_value(
    globals: &Globals,
    local_size: LocalSize,
    (head0, spine0): (&Head, &[Elim]),
    (head1, spine1): (&Head, &[Elim]),
) -> bool {
    if !is_equal_head(local_size, head0, head1) || spine0.len() != spine1.len() {
        return false;
    }

    for (elim0, elim1) in Iterator::zip(spine0.iter(), spine1.iter()) {
        match (elim0, elim1) {
            (Elim::Function(input0), Elim::Function(input1)) => {
                let input0 = input0.force(globals);
                let input1 = input1.force(globals);

                if !is_equal(globals, local_size, input0, input1) {
                    return false;
                }
            }
            (Elim::Record(label0), Elim::Record(label1)) if label0 == label1 => {}
            (_, _) => return false,
        }
    }

    true
}

/// Check that one value is [computationally equal] to another value.
///
/// [computationally equal]: https://ncatlab.org/nlab/show/equality#computational_equality
fn is_equal(globals: &Globals, local_size: LocalSize, value0: &Value, value1: &Value) -> bool {
    match (value0, value1) {
        (Value::Stuck(head0, spine0), Value::Stuck(head1, spine1)) => {
            is_equal_stuck_value(globals, local_size, (head0, spine0), (head1, spine1))
        }
        (Value::Unstuck(head0, spine0, value0), Value::Unstuck(head1, spine1, value1)) => {
            if is_equal_stuck_value(globals, local_size, (head0, spine0), (head1, spine1)) {
                // No need to force computation if the stuck values are the same!
                return true;
            }

            let value0 = value0.force(globals);
            let value1 = value1.force(globals);
            is_equal(globals, local_size, value0, value1)
        }
        (Value::Unstuck(_, _, value0), value1) => {
            is_equal(globals, local_size, value0.force(globals), value1)
        }
        (value0, Value::Unstuck(_, _, value1)) => {
            is_equal(globals, local_size, value0, value1.force(globals))
        }

        (Value::TypeType(level0), Value::TypeType(level1)) => level0 == level1,

        (
            Value::FunctionType(_, input_type0, output_closure0),
            Value::FunctionType(_, input_type1, output_closure1),
        ) => {
            if !is_equal(globals, local_size, input_type1, input_type0) {
                return false;
            }

            let local = Arc::new(Value::local(local_size.next_level()));
            is_equal(
                globals,
                local_size.increment(),
                &output_closure0.elim(globals, local.clone()),
                &output_closure1.elim(globals, local),
            )
        }
        (Value::FunctionTerm(_, output_closure0), Value::FunctionTerm(_, output_closure1)) => {
            let local = Arc::new(Value::local(local_size.next_level()));
            is_equal(
                globals,
                local_size.increment(),
                &output_closure0.elim(globals, local.clone()),
                &output_closure1.elim(globals, local),
            )
        }

        (Value::RecordType(closure0), Value::RecordType(closure1)) => {
            if closure0.entries.len() != closure1.entries.len() {
                return false;
            }

            let mut local_size = local_size;
            let universe_offset0 = closure0.universe_offset;
            let universe_offset1 = closure1.universe_offset;
            let mut values0 = closure0.values.clone();
            let mut values1 = closure1.values.clone();

            for ((label0, entry_type0), (label1, entry_type1)) in
                Iterator::zip(closure0.entries.iter(), closure1.entries.iter())
            {
                if label0 != label1 {
                    return false;
                }

                let entry_type0 = eval_term(globals, universe_offset0, &mut values0, entry_type0);
                let entry_type1 = eval_term(globals, universe_offset1, &mut values1, entry_type1);

                if !is_equal(globals, local_size, &entry_type0, &entry_type1) {
                    return false;
                }

                let local_level = local_size.next_level();
                values0.push(Arc::new(Value::local(local_level)));
                values1.push(Arc::new(Value::local(local_level)));
                local_size = local_size.increment();
            }

            true
        }
        (Value::RecordTerm(closure0), Value::RecordTerm(closure1)) => {
            if closure0.entries.len() != closure1.entries.len() {
                return false;
            }

            let mut local_size = local_size;
            let universe_offset0 = closure0.universe_offset;
            let universe_offset1 = closure1.universe_offset;
            let mut values0 = closure0.values.clone();
            let mut values1 = closure1.values.clone();

            for ((label0, entry_type0), (label1, entry_type1)) in
                Iterator::zip(closure0.entries.iter(), closure1.entries.iter())
            {
                if label0 != label1 {
                    return false;
                }

                let entry_type0 = eval_term(globals, universe_offset0, &mut values0, entry_type0);
                let entry_type1 = eval_term(globals, universe_offset1, &mut values1, entry_type1);

                if !is_equal(globals, local_size, &entry_type0, &entry_type1) {
                    return false;
                }

                let local_level = local_size.next_level();
                values0.push(Arc::new(Value::local(local_level)));
                values1.push(Arc::new(Value::local(local_level)));
                local_size = local_size.increment();
            }

            true
        }

        (Value::Sequence(value_entries0), Value::Sequence(value_entries1)) => {
            if value_entries0.len() != value_entries1.len() {
                return false;
            }

            Iterator::zip(value_entries0.iter(), value_entries1.iter()).all(
                |(value_entry0, value_entry1)| {
                    is_equal(globals, local_size, value_entry0, value_entry1)
                },
            )
        }

        (Value::Constant(constant0), Value::Constant(constant1)) => constant0 == constant1,

        // Errors are always treated as subtypes, regardless of what they are compared with.
        (Value::Error, _) | (_, Value::Error) => true,
        // Anything else is not equal!
        (_, _) => false,
    }
}

/// Check that one [`Value`] is a subtype of another [`Value`].
///
/// Returns `false` if either value is not a type.
///
/// [`Value`]: crate::lang::core::semantics::Value
pub fn is_subtype(
    globals: &Globals,
    local_size: LocalSize,
    value0: &Value,
    value1: &Value,
) -> bool {
    match (value0, value1) {
        (Value::Stuck(head0, spine0), Value::Stuck(head1, spine1)) => {
            is_equal_stuck_value(globals, local_size, (head0, spine0), (head1, spine1))
        }
        (Value::Unstuck(head0, spine0, value0), Value::Unstuck(head1, spine1, value1)) => {
            if is_equal_stuck_value(globals, local_size, (head0, spine0), (head1, spine1)) {
                // No need to force computation if the spines are the same!
                return true;
            }

            let value0 = value0.force(globals);
            let value1 = value1.force(globals);
            is_subtype(globals, local_size, value0, value1)
        }
        (Value::Unstuck(_, _, value0), value1) => {
            is_subtype(globals, local_size, value0.force(globals), value1)
        }
        (value0, Value::Unstuck(_, _, value1)) => {
            is_subtype(globals, local_size, value0, value1.force(globals))
        }

        (Value::TypeType(level0), Value::TypeType(level1)) => level0 <= level1,

        (
            Value::FunctionType(_, input_type0, output_closure0),
            Value::FunctionType(_, input_type1, output_closure1),
        ) => {
            if !is_subtype(globals, local_size, input_type1, input_type0) {
                return false;
            }

            let local = Arc::new(Value::local(local_size.next_level()));
            let output_term0 = output_closure0.elim(globals, local.clone());
            let output_term1 = output_closure1.elim(globals, local);

            is_subtype(
                globals,
                local_size.increment(),
                &output_term0,
                &output_term1,
            )
        }

        (Value::RecordType(closure0), Value::RecordType(closure1)) => {
            if closure0.entries.len() != closure1.entries.len() {
                return false;
            }

            let mut local_size = local_size;
            let universe_offset0 = closure0.universe_offset;
            let universe_offset1 = closure1.universe_offset;
            let mut values0 = closure0.values.clone();
            let mut values1 = closure1.values.clone();

            for ((label0, entry_type0), (label1, entry_type1)) in
                Iterator::zip(closure0.entries.iter(), closure1.entries.iter())
            {
                if label0 != label1 {
                    return false;
                }

                let entry_type0 = eval_term(globals, universe_offset0, &mut values0, entry_type0);
                let entry_type1 = eval_term(globals, universe_offset1, &mut values1, entry_type1);

                if !is_subtype(globals, local_size, &entry_type0, &entry_type1) {
                    return false;
                }

                let local_level = local_size.next_level();
                values0.push(Arc::new(Value::local(local_level)));
                values1.push(Arc::new(Value::local(local_level)));
                local_size = local_size.increment();
            }

            true
        }

        // Errors are always treated as subtypes, regardless of what they are compared with.
        (Value::Error, _) | (_, Value::Error) => true,
        // Anything else is not equal!
        (_, _) => false,
    }
}
