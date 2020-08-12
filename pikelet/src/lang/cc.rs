//! The closure converted language, with types preserved.
//!
//! This language makes an explicit distinction between the _use_ of a
//! computation and the _definition_ of a computation. In doing this we make
//! implicit environment capture explicit through the use of an explicit
//! closure object, which holds the closed code and the local environment.
//!
//! The main inspiration for this language is William Bowman's dissertation,
//! [Compiling with Dependent Types][wjb-dissertation].
//!
//! [wjb-dissertation](https://www.williamjbowman.com/resources/wjb-dissertation.pdf)

// TODO: Define syntax
