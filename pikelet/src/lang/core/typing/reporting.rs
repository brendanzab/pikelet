use std::sync::Arc;

use crate::lang::core::semantics::Value;

#[derive(Clone, Debug)]
pub enum Message {
    MaximumUniverseLevelReached,
    UnboundGlobal {
        name: String,
    },
    UnboundLocal,
    InvalidRecordType {
        duplicate_labels: Vec<String>,
    },
    InvalidRecordTerm {
        missing_labels: Vec<String>,
        unexpected_labels: Vec<String>,
    },
    LabelNotFound {
        expected_label: String,
        head_type: Arc<Value>,
    },
    TooManyParameters,
    TooManyArguments {
        head_type: Arc<Value>,
    },
    MismatchedSequenceLength {
        found_len: usize,
        expected_len: Arc<Value>,
    },
    NoSequenceConversion {
        expected_type: Arc<Value>,
    },
    AmbiguousTerm {
        term: AmbiguousTerm,
    },
    MismatchedTypes {
        found_type: Arc<Value>,
        expected_type: ExpectedType,
    },
}

#[derive(Clone, Debug)]
pub enum AmbiguousTerm {
    Sequence,
    FunctionTerm,
    RecordTerm,
}

#[derive(Clone, Debug)]
pub enum ExpectedType {
    Universe,
    Type(Arc<Value>),
}
