use std::{cmp::Ordering, convert::TryFrom, fmt, ops};

use crate::{
    Tryte,
    error::{Error, Result},
    tables::{TRIT2_TO_AND, TRIT2_TO_CMP, TRIT2_TO_OR, TRIT2_TO_PRODUCT, TRIT3_TO_SUM_AND_CARRY},
};

pub const BITMASK: u8 = 0b11;

pub const BIN_0: u8 = 0b00;
pub const BIN_1: u8 = 0b01;
pub const BIN_INVALID: u8 = 0b10;
pub const BIN_T: u8 = 0b11;

pub const CHAR_0: char = '0';
pub const CHAR_1: char = '1';
pub const CHAR_INVALID: char = '?';
pub const CHAR_T: char = 'T';

#[derive(Debug, Clone, Copy, Default, Eq, PartialEq)]
pub struct Trit(u8);

pub const _0: Trit = Trit(BIN_0);
pub const _1: Trit = Trit(BIN_1);
pub const _INVALID: Trit = Trit(BIN_INVALID);
pub const _T: Trit = Trit(BIN_T);

const TRIT_TO_I8: [i8; 4] = [0, 1, 0, -1];
const U8_TO_TRIT: [Trit; 3] = [_T, _0, _1];
const TRIT_TO_CHAR: [char; 4] = [CHAR_0, CHAR_1, CHAR_INVALID, CHAR_T];

impl Trit {
    pub const BIT_SIZE: usize = 2;

    pub(crate) const fn into_raw(self) -> u8 {
        self.0
    }

    pub(crate) const fn from_raw(bits: u8) -> Self {
        Trit(bits)
    }

    pub const fn try_from_raw(bits: u8) -> Result<Self> {
        match bits {
            BIN_T => Ok(_T),
            BIN_0 => Ok(_0),
            BIN_1 => Ok(_1),
            _ => Err(Error::InvalidBitPattern(bits as u64)),
        }
    }

    pub const fn into_index(self) -> usize {
        self.0 as usize
    }

    const fn into_i8(self) -> i8 {
        TRIT_TO_I8[self.into_index()]
    }

    pub const fn try_from_i8(n: i8) -> Result<Self> {
        if -1 <= n && n <= 1 {
            #[allow(clippy::cast_sign_loss)]
            let index = (n + 1) as usize;
            Ok(U8_TO_TRIT[index])
        } else {
            Err(Error::IntegerOutOfBoundsI64 {
                min: -1,
                max: 1,
                value: n as i64,
            })
        }
    }

    pub const fn into_char(self) -> char {
        TRIT_TO_CHAR[self.into_index()]
    }

    pub const fn try_from_char(c: char) -> Result<Self> {
        match c {
            'T' => Ok(_T),
            '0' => Ok(_0),
            '1' => Ok(_1),
            _ => Err(Error::InvalidCharacter(c)),
        }
    }

    pub const fn into_ordering(self) -> Ordering {
        TRIT_TO_ORDERING[self.into_index()]
    }

    pub const fn from_ordering(ordering: Ordering) -> Self {
        match ordering {
            Ordering::Less => _T,
            Ordering::Equal => _0,
            Ordering::Greater => _1,
        }
    }

    pub const fn from_trit4(trit4: u8) -> Result<Self> {
        let bits = trit4 & BITMASK;
        Trit::try_from_raw(bits)
    }

    const fn negation_bits(self) -> u8 {
        self.0 << 1 & BITMASK
    }

    pub const fn tcmp(self, rhs: Self) -> Self {
        let i = index2(self, rhs);
        TRIT2_TO_CMP[i]
    }

    pub const fn add_with_carry(self, rhs: Self, carry_in: Self) -> (Self, Self) {
        let i = index3(self, rhs, carry_in);
        TRIT3_TO_SUM_AND_CARRY[i]
    }

    pub const fn neg(self) -> Self {
        let bits = self.0 ^ self.negation_bits();
        Trit(bits)
    }

    pub const fn and(self, rhs: Self) -> Self {
        let i = index2(self, rhs);
        TRIT2_TO_AND[i]
    }

    pub const fn or(self, rhs: Self) -> Self {
        let i = index2(self, rhs);
        TRIT2_TO_OR[i]
    }

    pub const fn mul(self, rhs: Self) -> Self {
        let i = index2(self, rhs);
        TRIT2_TO_PRODUCT[i]
    }
}

pub const fn index2(t1: Trit, t0: Trit) -> usize {
    Tryte::from_trits([t0, t1, _0, _0, _0, _0]).into_index()
}

pub const fn index3(t2: Trit, t1: Trit, t0: Trit) -> usize {
    Tryte::from_trits([t0, t1, t2, _0, _0, _0]).into_index()
}

pub const fn index4(t3: Trit, t2: Trit, t1: Trit, t0: Trit) -> usize {
    Tryte::from_trits([t0, t1, t2, t3, _0, _0]).into_index()
}

pub const fn index6(t5: Trit, t4: Trit, t3: Trit, t2: Trit, t1: Trit, t0: Trit) -> usize {
    Tryte::from_trits([t0, t1, t2, t3, t4, t5]).into_index()
}

impl fmt::Display for Trit {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.into_char())
    }
}

impl From<Trit> for i8 {
    fn from(trit: Trit) -> i8 {
        trit.into_i8()
    }
}

impl TryFrom<i8> for Trit {
    type Error = Error;

    fn try_from(n: i8) -> Result<Self> {
        Self::try_from_i8(n)
    }
}

impl From<Trit> for char {
    fn from(trit: Trit) -> char {
        trit.into_char()
    }
}

impl TryFrom<char> for Trit {
    type Error = Error;

    fn try_from(c: char) -> Result<Self> {
        Self::try_from_char(c)
    }
}

const TRIT_TO_ORDERING: [Ordering; 4] = [
    Ordering::Equal,
    Ordering::Greater,
    Ordering::Equal,
    Ordering::Less,
];

impl From<Trit> for Ordering {
    fn from(trit: Trit) -> Ordering {
        trit.into_ordering()
    }
}

impl From<Ordering> for Trit {
    fn from(ordering: Ordering) -> Self {
        Self::from_ordering(ordering)
    }
}

impl Ord for Trit {
    fn cmp(&self, other: &Self) -> Ordering {
        let cmp_trit = self.tcmp(*other);
        cmp_trit.into()
    }
}

impl PartialOrd for Trit {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl ops::Neg for Trit {
    type Output = Self;

    fn neg(self) -> Self::Output {
        self.neg()
    }
}

impl ops::Not for Trit {
    type Output = Self;

    fn not(self) -> Self::Output {
        -self
    }
}

impl ops::BitAnd for Trit {
    type Output = Self;

    fn bitand(self, rhs: Self) -> Self::Output {
        self.and(rhs)
    }
}

impl ops::BitOr for Trit {
    type Output = Self;

    fn bitor(self, rhs: Self) -> Self::Output {
        self.or(rhs)
    }
}

impl ops::Mul for Trit {
    type Output = Self;

    fn mul(self, rhs: Self) -> Self::Output {
        self.mul(rhs)
    }
}

#[cfg(test)]
mod tests {
    use crate::trit::{_0, _1, _T, Trit};

    #[test]
    fn into_i8() {
        assert_eq!(-1, i8::from(_T));
        assert_eq!(0, i8::from(_0));
        assert_eq!(1, i8::from(_1));
    }

    #[test]
    fn try_from_i8() {
        assert_eq!(_T, Trit::try_from(-1).unwrap());
        assert_eq!(_0, Trit::try_from(0).unwrap());
        assert_eq!(_1, Trit::try_from(1).unwrap());

        assert!(Trit::try_from(-2).is_err());
        assert!(Trit::try_from(2).is_err());
    }

    #[test]
    fn into_char() {
        assert_eq!('T', _T.into());
        assert_eq!('0', _0.into());
        assert_eq!('1', _1.into());
    }

    #[test]
    fn try_from_char() {
        assert_eq!(_T, Trit::try_from('T').unwrap());
        assert_eq!(_0, Trit::try_from('0').unwrap());
        assert_eq!(_1, Trit::try_from('1').unwrap());

        assert!(Trit::try_from('t').is_err());
        assert!(Trit::try_from('o').is_err());
        assert!(Trit::try_from('i').is_err());
    }

    #[test]
    fn neg() {
        assert_eq!(_1, -_T);
        assert_eq!(_0, -_0);
        assert_eq!(_T, -_1);
    }

    #[test]
    fn not() {
        assert_eq!(_1, !_T);
        assert_eq!(_0, !_0);
        assert_eq!(_T, !_1);
    }

    #[test]
    fn and() {
        assert_eq!(_T, _T & _T);
        assert_eq!(_T, _T & _0);
        assert_eq!(_T, _T & _1);
        assert_eq!(_T, _0 & _T);
        assert_eq!(_0, _0 & _0);
        assert_eq!(_0, _0 & _1);
        assert_eq!(_T, _1 & _T);
        assert_eq!(_0, _1 & _0);
        assert_eq!(_1, _1 & _1);
    }

    #[test]
    fn or() {
        assert_eq!(_T, _T | _T);
        assert_eq!(_0, _T | _0);
        assert_eq!(_1, _T | _1);
        assert_eq!(_0, _0 | _T);
        assert_eq!(_0, _0 | _0);
        assert_eq!(_1, _0 | _1);
        assert_eq!(_1, _1 | _T);
        assert_eq!(_1, _1 | _0);
        assert_eq!(_1, _1 | _1);
    }

    #[test]
    fn add() {
        assert_eq!((_0, _T), _T.add_with_carry(_T, _T));
        assert_eq!((_1, _T), _T.add_with_carry(_T, _0));
        assert_eq!((_T, _0), _T.add_with_carry(_T, _1));

        assert_eq!((_1, _T), _T.add_with_carry(_0, _T));
        assert_eq!((_T, _0), _T.add_with_carry(_0, _0));
        assert_eq!((_0, _0), _T.add_with_carry(_0, _1));

        assert_eq!((_T, _0), _T.add_with_carry(_1, _T));
        assert_eq!((_0, _0), _T.add_with_carry(_1, _0));
        assert_eq!((_1, _0), _T.add_with_carry(_1, _1));

        assert_eq!((_1, _T), _0.add_with_carry(_T, _T));
        assert_eq!((_T, _0), _0.add_with_carry(_T, _0));
        assert_eq!((_0, _0), _0.add_with_carry(_T, _1));

        assert_eq!((_T, _0), _0.add_with_carry(_0, _T));
        assert_eq!((_0, _0), _0.add_with_carry(_0, _0));
        assert_eq!((_1, _0), _0.add_with_carry(_0, _1));

        assert_eq!((_0, _0), _0.add_with_carry(_1, _T));
        assert_eq!((_1, _0), _0.add_with_carry(_1, _0));
        assert_eq!((_T, _1), _0.add_with_carry(_1, _1));

        assert_eq!((_T, _0), _1.add_with_carry(_T, _T));
        assert_eq!((_0, _0), _1.add_with_carry(_T, _0));
        assert_eq!((_1, _0), _1.add_with_carry(_T, _1));

        assert_eq!((_0, _0), _1.add_with_carry(_0, _T));
        assert_eq!((_1, _0), _1.add_with_carry(_0, _0));
        assert_eq!((_T, _1), _1.add_with_carry(_0, _1));

        assert_eq!((_1, _0), _1.add_with_carry(_1, _T));
        assert_eq!((_T, _1), _1.add_with_carry(_1, _0));
        assert_eq!((_0, _1), _1.add_with_carry(_1, _1));
    }

    #[test]
    fn mul() {
        assert_eq!(_1, _T * _T);
        assert_eq!(_0, _T * _0);
        assert_eq!(_T, _T * _1);
        assert_eq!(_0, _0 * _T);
        assert_eq!(_0, _0 * _0);
        assert_eq!(_0, _0 * _1);
        assert_eq!(_T, _1 * _T);
        assert_eq!(_0, _1 * _0);
        assert_eq!(_1, _1 * _1);
    }

    #[test]
    fn cmp() {
        assert!(_T == _T);
        assert!(_T < _0);
        assert!(_T < _1);
        assert!(_0 > _T);
        assert!(_0 == _0);
        assert!(_0 < _1);
        assert!(_1 > _T);
        assert!(_1 > _0);
        assert!(_1 == _1);
    }
}
