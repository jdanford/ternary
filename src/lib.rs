#![deny(clippy::pedantic)]
#![allow(
    clippy::must_use_candidate,
    clippy::missing_errors_doc,
    clippy::missing_panics_doc,
    clippy::return_self_not_must_use
)]

pub mod error;
mod hyte;
mod int;
pub mod tables;
pub mod test_constants;
pub mod text;
pub mod trit;
pub mod tryte;

pub use crate::{
    error::{Error, Result},
    int::{T6, T12, T24, T48, TInt},
    trit::Trit,
    tryte::Tryte,
};
