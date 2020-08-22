//! Intermediate languages of the Pikelet compiler.

use std::ops::Range;

pub mod surface;
//       🠃
pub mod core;
//       🠃
pub mod anf;
//       🠃
pub mod cc;
//       🠃
//      ...

/// Data that covers some range of source code.
#[derive(Debug, Clone)]
pub struct Ranged<Data> {
    pub range: Range<usize>,
    pub data: Data,
}

impl<Data> Ranged<Data> {
    pub fn new(range: Range<usize>, data: Data) -> Ranged<Data> {
        Ranged { range, data }
    }

    pub fn range(&self) -> Range<usize> {
        self.range.clone()
    }
}

impl<Data> From<Data> for Ranged<Data> {
    #![allow(clippy::reversed_empty_ranges)]
    fn from(data: Data) -> Ranged<Data> {
        // TODO: Use a better marker for data that does not originate from to a
        // specific source location.
        Ranged::new(0..0, data)
    }
}
