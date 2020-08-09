//! The operational semantics of the language.

use once_cell::sync::OnceCell;
use std::cell::RefCell;
use std::collections::BTreeMap;
use std::sync::Arc;

use crate::lang::core::{
    Constant, Globals, LocalLevel, LocalSize, Locals, Term, UniverseLevel, UniverseOffset,
};

/// Values in the core language.
#[derive(Clone, Debug)]
pub enum Value {
    /// A suspended elimination.
    ///
    /// This is more commonly known as a 'neutral value' or sometimes as an
    /// 'accumulator'.
    ///
    /// These eliminations cannot be reduced further as a result of being stuck
    /// on some head that also cannot be reduced further (eg. a parameter, an
    /// abstract global, or an unsolved metavariable).
    Stuck(Head, Vec<Elim>),
    /// An elimination that is now 'unstuck'.
    ///
    /// This is sometimes called a 'glued value'.
    ///
    /// We keep the original head and spine around in order to reduce the
    /// size-blowup that can result from deeply-normalizing terms. This can help
    /// with:
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
    Universe(UniverseLevel),
    /// Constants.
    Constant(Constant),
    /// Ordered sequences.
    Sequence(Vec<Arc<Value>>),
    /// Record types.
    RecordType(RecordTypeClosure),
    /// Record terms.
    RecordTerm(BTreeMap<String, Arc<Value>>),
    /// Function types.
    ///
    /// Also known as: pi type, dependent product type.
    FunctionType(Option<String>, Arc<Value>, Closure),
    /// Function terms.
    ///
    /// Also known as: lambda abstraction, anonymous function.
    FunctionTerm(String, Closure),

    /// Error sentinel.
    Error,
}

impl Value {
    /// Create a universe at the given level.
    pub fn universe(level: impl Into<UniverseLevel>) -> Value {
        Value::Universe(level.into())
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
            Value::Unstuck(_, _, value) => value.force(globals).force(globals),
            value => value,
        }
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
    /// Record eliminators.
    ///
    /// Also known as: record projections, field lookup.
    Record(String),
    /// Function eliminators.
    ///
    /// Also known as: function application.
    Function(Arc<LazyValue>),
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

/// Record type closure, capturing the current universe offset and the current locals in scope.
#[derive(Clone, Debug)]
pub struct RecordTypeClosure {
    universe_offset: UniverseOffset,
    values: Locals<Arc<Value>>,
    entries: Arc<[(String, Arc<Term>)]>,
}

impl RecordTypeClosure {
    pub fn new(
        universe_offset: UniverseOffset,
        values: Locals<Arc<Value>>,
        entries: Arc<[(String, Arc<Term>)]>,
    ) -> RecordTypeClosure {
        RecordTypeClosure {
            universe_offset,
            values,
            entries,
        }
    }

    /// Apply a callback to each of the entry types in the record closure.
    pub fn entries<'closure>(
        &'closure self,
        globals: &Globals,
        mut on_entry: impl FnMut(&'closure str, Arc<Value>) -> Arc<Value>,
    ) {
        let universe_offset = self.universe_offset;
        let mut values = self.values.clone();
        for (label, entry_type) in self.entries.iter() {
            let entry_type = eval_term(globals, universe_offset, &mut values, entry_type);
            values.push(on_entry(label, entry_type));
        }
    }
}

/// Initialization operation for lazy values.
///
/// We need to use a defunctionalized representation because Rust does not allow
/// closures of type `dyn (Clone + FnOnce() -> Arc<Value>)`.
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
                apply_record_elim(head.force(globals), &label)
            }
            Some(LazyInit::ApplyElim(head, Elim::Function(input))) => {
                apply_function_elim(globals, head.force(globals), input)
            }
            None => panic!("Lazy instance has previously been poisoned"),
        })
    }
}

/// Fully normalize a term.
pub fn normalize_term(
    globals: &Globals,
    universe_offset: UniverseOffset,
    values: &mut Locals<Arc<Value>>,
    term: &Term,
) -> Term {
    let value = eval_term(globals, universe_offset, values, term);
    read_back_value(globals, values.size(), Unfold::All, &value)
}

/// Evaluate a term into a value in weak-head normal form.
pub fn eval_term(
    globals: &Globals,
    universe_offset: UniverseOffset,
    values: &mut Locals<Arc<Value>>,
    term: &Term,
) -> Arc<Value> {
    match term {
        Term::Universe(level) => Arc::new(Value::universe(
            (*level + universe_offset).unwrap(), // FIXME: Handle overflow
        )),
        Term::Global(name) => {
            let head = Head::Global(name.into(), universe_offset);
            match globals.get(name) {
                Some((_, Some(term))) => {
                    let value = LazyValue::eval_term(universe_offset, values.clone(), term.clone());
                    Arc::new(Value::Unstuck(head, Vec::new(), Arc::new(value)))
                }
                Some((_, None)) | None => Arc::new(Value::Stuck(head, Vec::new())),
            }
        }
        Term::Local(index) => {
            let head = Head::Local(values.size().level(*index));
            match values.get(*index) {
                Some(value) => {
                    let value = LazyValue::new(value.clone());
                    Arc::new(Value::Unstuck(head, Vec::new(), Arc::new(value)))
                }
                None => Arc::new(Value::Stuck(head, Vec::new())),
            }
        }
        Term::Constant(constant) => Arc::new(Value::Constant(constant.clone())),
        Term::Sequence(term_entries) => {
            let value_entries = term_entries
                .iter()
                .map(|entry_term| eval_term(globals, universe_offset, values, entry_term))
                .collect();

            Arc::new(Value::Sequence(value_entries))
        }
        Term::Ann(term, _) => eval_term(globals, universe_offset, values, term),
        Term::RecordType(type_entries) => Arc::new(Value::RecordType(RecordTypeClosure::new(
            universe_offset,
            values.clone(),
            type_entries.clone(),
        ))),
        Term::RecordTerm(term_entries) => {
            let value_entries = term_entries
                .iter()
                .map(|(label, entry_term)| {
                    let entry_term = eval_term(globals, universe_offset, values, entry_term);
                    (label.clone(), entry_term)
                })
                .collect();

            Arc::new(Value::RecordTerm(value_entries))
        }
        Term::RecordElim(head, label) => {
            let head = eval_term(globals, universe_offset, values, head);
            apply_record_elim(&head, label)
        }
        Term::FunctionType(input_name_hint, input_type, output_type) => {
            Arc::new(Value::FunctionType(
                input_name_hint.clone(),
                eval_term(globals, universe_offset, values, input_type),
                Closure::new(universe_offset, values.clone(), output_type.clone()),
            ))
        }
        Term::FunctionTerm(input_name, output_term) => Arc::new(Value::FunctionTerm(
            input_name.clone(),
            Closure::new(universe_offset, values.clone(), output_term.clone()),
        )),
        Term::FunctionElim(head, input) => {
            let head = eval_term(globals, universe_offset, values, head);
            let input = LazyValue::eval_term(universe_offset, values.clone(), input.clone());
            apply_function_elim(globals, &head, Arc::new(input))
        }
        Term::Lift(term, offset) => {
            let universe_offset = (universe_offset + *offset).unwrap(); // FIXME: Handle overflow
            eval_term(globals, universe_offset, values, term)
        }
        Term::Error => Arc::new(Value::Error),
    }
}

/// Return the type of the record elimination.
pub fn record_elim_type(
    globals: &Globals,
    head_value: &Value,
    label: &str,
    closure: &RecordTypeClosure,
) -> Option<Arc<Value>> {
    let universe_offset = closure.universe_offset;
    let mut values = closure.values.clone();
    for (entry_label, entry_type) in closure.entries.iter() {
        if entry_label == label {
            return Some(eval_term(globals, universe_offset, &mut values, entry_type));
        }
        values.push(apply_record_elim(head_value, label));
    }
    None
}

/// Apply a record term elimination.
fn apply_record_elim(head_value: &Value, label: &str) -> Arc<Value> {
    match head_value {
        Value::Stuck(head, spine) => {
            let mut spine = spine.clone(); // FIXME: Avoid clone of spine?
            spine.push(Elim::Record(label.to_owned()));
            Arc::new(Value::Stuck(head.clone(), spine))
        }
        Value::Unstuck(head, spine, value) => {
            let mut spine = spine.clone(); // FIXME: Avoid clone of spine?
            spine.push(Elim::Record(label.to_owned()));
            let value = LazyValue::apply_elim(value.clone(), Elim::Record(label.to_owned()));
            Arc::new(Value::Unstuck(head.clone(), spine, Arc::new(value)))
        }

        Value::RecordTerm(term_entries) => match term_entries.get(label) {
            Some(value) => value.clone(),
            None => Arc::new(Value::Error),
        },

        _ => Arc::new(Value::Error),
    }
}

/// Apply a function term elimination.
fn apply_function_elim(globals: &Globals, head_value: &Value, input: Arc<LazyValue>) -> Arc<Value> {
    match head_value {
        Value::Stuck(head, spine) => {
            let mut spine = spine.clone(); // FIXME: Avoid clone of spine?
            spine.push(Elim::Function(input));
            Arc::new(Value::Stuck(head.clone(), spine))
        }
        Value::Unstuck(head, spine, value) => {
            let mut spine = spine.clone(); // FIXME: Avoid clone of spine?
            spine.push(Elim::Function(input.clone()));
            let value = LazyValue::apply_elim(value.clone(), Elim::Function(input));
            Arc::new(Value::Unstuck(head.clone(), spine, Arc::new(value)))
        }

        Value::FunctionTerm(_, output_closure) => {
            output_closure.elim(globals, input.force(globals).clone())
        }

        _ => Arc::new(Value::Error),
    }
}

/// The type of unfolding to perform when reading back values.
#[derive(Copy, Clone, Debug)]
pub enum Unfold {
    /// Never unfold definitions. This is useful for displaying values to the
    /// user, or when reading them back during elaboration.
    None,
    /// Always unfold global and local definitions.
    All,
}

/// Read-back a spine of eliminators into the term syntax.
fn read_back_spine(
    globals: &Globals,
    local_size: LocalSize,
    unfold: Unfold,
    head: &Head,
    spine: &[Elim],
) -> Term {
    let head = match head {
        Head::Global(name, shift) => Term::Global(name.clone()).lift(*shift),
        Head::Local(level) => Term::Local(local_size.index(*level)),
    };

    spine.iter().fold(head, |head, elim| match elim {
        Elim::Record(label) => Term::RecordElim(Arc::new(head), label.clone()),
        Elim::Function(input) => {
            let input = read_back_value(globals, local_size, unfold, input.force(globals));
            Term::FunctionElim(Arc::new(head), Arc::new(input))
        }
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
        Value::Stuck(head, spine) => read_back_spine(globals, local_size, unfold, head, spine),
        Value::Unstuck(head, spine, value) => match unfold {
            Unfold::None => read_back_spine(globals, local_size, unfold, head, spine),
            Unfold::All => read_back_value(globals, local_size, unfold, value.force(globals)),
        },

        Value::Universe(level) => Term::Universe(*level),
        Value::Constant(constant) => Term::Constant(constant.clone()),
        Value::Sequence(value_entries) => {
            let term_entries = value_entries
                .iter()
                .map(|value_entry| {
                    Arc::new(read_back_value(globals, local_size, unfold, value_entry))
                })
                .collect();

            Term::Sequence(term_entries)
        }
        Value::RecordType(closure) => {
            let mut local_size = local_size;
            let mut type_entries = Vec::with_capacity(closure.entries.len());

            closure.entries(globals, |label, entry_type| {
                let entry_type = read_back_value(globals, local_size, unfold, &entry_type);
                type_entries.push((label.to_owned(), Arc::new(entry_type)));

                let local_level = local_size.next_level();
                local_size = local_size.increment();

                Arc::new(Value::local(local_level))
            });

            Term::RecordType(type_entries.into())
        }
        Value::RecordTerm(value_entries) => {
            let term_entries = value_entries
                .iter()
                .map(|(label, entry_value)| {
                    let entry_term = read_back_value(globals, local_size, unfold, &entry_value);
                    (label.to_owned(), Arc::new(entry_term))
                })
                .collect();

            Term::RecordTerm(term_entries)
        }
        Value::FunctionType(input_name_hint, input_type, output_closure) => {
            let local = Arc::new(Value::local(local_size.next_level()));
            let input_type = Arc::new(read_back_value(globals, local_size, unfold, input_type));
            let output_type = output_closure.elim(globals, local);
            let output_type =
                read_back_value(globals, local_size.increment(), unfold, &output_type);

            Term::FunctionType(input_name_hint.clone(), input_type, Arc::new(output_type))
        }
        Value::FunctionTerm(input_name_hint, output_closure) => {
            let local = Arc::new(Value::local(local_size.next_level()));
            let output_term = output_closure.elim(globals, local);
            let output_term =
                read_back_value(globals, local_size.increment(), unfold, &output_term);

            Term::FunctionTerm(input_name_hint.clone(), Arc::new(output_term))
        }

        Value::Error => Term::Error,
    }
}

/// Check that one elimination is equal to another elimination.
pub fn is_equal_spine(
    globals: &Globals,
    local_size: LocalSize,
    (head0, spine0): (&Head, &[Elim]),
    (head1, spine1): (&Head, &[Elim]),
) -> bool {
    if head0 != head1 || spine0.len() != spine1.len() {
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

/// Check that one value is definitionally equal to another value.
fn is_equal(globals: &Globals, local_size: LocalSize, value0: &Value, value1: &Value) -> bool {
    match (value0, value1) {
        (Value::Stuck(head0, spine0), Value::Stuck(head1, spine1)) => {
            is_equal_spine(globals, local_size, (head0, spine0), (head1, spine1))
        }
        (Value::Unstuck(head0, spine0, value0), Value::Unstuck(head1, spine1, value1)) => {
            if is_equal_spine(globals, local_size, (head0, spine0), (head1, spine1)) {
                // No need to force computation if the spines are the same!
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

        (Value::Universe(level0), Value::Universe(level1)) => level0 == level1,
        (Value::Constant(constant0), Value::Constant(constant1)) => constant0 == constant1,
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
        (Value::RecordTerm(value_entries0), Value::RecordTerm(value_entries1)) => {
            if value_entries0.len() != value_entries1.len() {
                return false;
            }

            Iterator::zip(value_entries0.iter(), value_entries1.iter()).all(
                |((label0, entry_value0), (label1, entry_value1))| {
                    label0 == label1 && is_equal(globals, local_size, entry_value0, entry_value1)
                },
            )
        }
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

        // Errors are always treated as subtypes, regardless of what they are compared with.
        (Value::Error, _) | (_, Value::Error) => true,
        // Anything else is not equal!
        (_, _) => false,
    }
}

/// Check that one type is a subtype of another type.
pub fn is_subtype(
    globals: &Globals,
    local_size: LocalSize,
    value0: &Value,
    value1: &Value,
) -> bool {
    match (value0, value1) {
        (Value::Stuck(head0, spine0), Value::Stuck(head1, spine1)) => {
            is_equal_spine(globals, local_size, (head0, spine0), (head1, spine1))
        }
        (Value::Unstuck(head0, spine0, value0), Value::Unstuck(head1, spine1, value1)) => {
            if is_equal_spine(globals, local_size, (head0, spine0), (head1, spine1)) {
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

        (Value::Universe(level0), Value::Universe(level1)) => level0 <= level1,
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

        // Errors are always treated as subtypes, regardless of what they are compared with.
        (Value::Error, _) | (_, Value::Error) => true,
        // Anything else is not equal!
        (_, _) => false,
    }
}
