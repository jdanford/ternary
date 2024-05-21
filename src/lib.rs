#![deny(clippy::pedantic)]
#![allow(
    clippy::must_use_candidate,
    clippy::missing_errors_doc,
    clippy::missing_panics_doc,
    clippy::return_self_not_must_use
)]

pub mod constants;
mod core;
pub mod error;
mod hyte;
pub mod ops;
pub mod tables;
pub mod test_constants;
pub mod text;
pub mod trit;
pub mod tryte;

pub use crate::{
    core::Ternary,
    error::{Error, Result},
    trit::Trit,
    tryte::Tryte,
};
