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
mod tables;
mod test_constants;
pub mod text;
pub mod trit;
pub mod tryte;

pub use crate::{
    error::{Error, Result},
    int::{TInt, T12, T24, T48, T6},
    trit::Trit,
    tryte::Tryte,
};
