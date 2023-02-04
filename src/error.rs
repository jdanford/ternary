#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Error {
    FormatError,
    IntegerOutOfBounds(i64, i64, i64),
    InvalidBitPattern(u64),
    InvalidCharacter(char),
    InvalidLength(usize, usize),
    InvalidEncoding(String),
    InvalidString(String),
    IoError,
}

pub type Result<T> = std::result::Result<T, Error>;
