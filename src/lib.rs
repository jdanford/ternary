#![cfg_attr(feature = "cargo-clippy", deny(clippy::all, clippy::pedantic))]
#![cfg_attr(
    feature = "cargo-clippy",
    allow(
        clippy::cast_lossless,
        clippy::cast_possible_truncation,
        clippy::cast_possible_wrap,
        clippy::cast_sign_loss,
        clippy::missing_docs_in_private_items,
        clippy::non_ascii_literal
    )
)]

extern crate byteorder;
extern crate lazy_static;
extern crate phf;

mod core;
pub mod constants;
pub mod error;
mod hyte;
pub mod tables;
pub mod test_constants;
pub mod text;
pub mod trit;
pub mod tryte;

pub use crate::core::*;
pub use crate::error::{Error, Result};
pub use crate::trit::Trit;
pub use crate::tryte::Tryte;
