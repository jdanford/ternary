use std::{io, num::TryFromIntError};

#[derive(Debug)]
pub enum Error {
    IntegerOutOfBounds { min: i64, max: i64, value: i64 },
    InvalidBitPattern(u64),
    InvalidCharacter(char),
    InvalidLength { actual: usize, expected: usize },
    InvalidEncoding(String),
    InvalidString(String),
    Io(io::Error),
    TryFromInt,
}

impl From<io::Error> for Error {
    fn from(error: io::Error) -> Self {
        Error::Io(error)
    }
}

impl From<TryFromIntError> for Error {
    fn from(_: TryFromIntError) -> Self {
        Error::TryFromInt
    }
}

pub type Result<T> = std::result::Result<T, Error>;

pub const fn assert_length(actual: usize, expected: usize) -> Result<()> {
    if expected != actual {
        return Err(Error::InvalidLength { actual, expected });
    }

    Ok(())
}
