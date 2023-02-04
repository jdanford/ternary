#![cfg_attr(feature = "cargo-clippy", deny(clippy::all, clippy::pedantic))]
#![cfg_attr(
    feature = "cargo-clippy",
    allow(
        clippy::cast_possible_truncation,
        clippy::cast_possible_wrap,
        clippy::cast_sign_loss,
        clippy::missing_docs_in_private_items,
        clippy::missing_errors_doc,
    )
)]

pub mod constants;
mod core;
pub mod error;
pub mod fixed;
mod hyte;
pub mod slice;
pub mod tables;
pub mod test_constants;
pub mod text;
pub mod trit;
pub mod tryte;

pub use crate::core::Ternary;
pub use crate::error::{Error, Result};
pub use crate::trit::Trit;
pub use crate::tryte::Tryte;
