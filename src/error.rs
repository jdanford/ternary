use std::{io, num::TryFromIntError};

use crate::Tryte;

#[derive(Debug)]
pub enum Error {
    IntegerOutOfBoundsI64 {
        min: i64,
        max: i64,
        value: i64,
    },
    IntegerOutOfBounds {
        min: String,
        max: String,
        value: String,
    },
    InvalidBitPattern(u64),
    InvalidCharacter(char),
    InvalidLength {
        actual: usize,
        expected: usize,
    },
    InvalidEncoding(Vec<Tryte>),
    InvalidString(String),
    TryFromInt,
    TryIntoInt,
    Io(io::Error),
}

impl From<TryFromIntError> for Error {
    fn from(_: TryFromIntError) -> Self {
        Error::TryFromInt
    }
}

impl From<io::Error> for Error {
    fn from(error: io::Error) -> Self {
        Error::Io(error)
    }
}

pub type Result<T> = std::result::Result<T, Error>;

pub const fn assert_length_eq(actual: usize, expected: usize) -> Result<()> {
    if actual == expected {
        Ok(())
    } else {
        Err(Error::InvalidLength { actual, expected })
    }
}

pub const fn assert_length_le(actual: usize, expected: usize) -> Result<()> {
    if actual <= expected {
        Ok(())
    } else {
        Err(Error::InvalidLength { actual, expected })
    }
}
