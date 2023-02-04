#![cfg_attr(feature = "cargo-clippy", allow(clippy::from_over_into))]

use std::cmp::Ordering;
use std::convert::TryFrom;
use std::fmt;
use std::ops;

use crate::error::{Error, Result};
use crate::tables::{
    TRIT2_TO_AND, TRIT2_TO_CMP, TRIT2_TO_OR, TRIT2_TO_PRODUCT, TRIT3_TO_SUM_AND_CARRY,
};

pub const BITMASK: u8 = 0b11;

pub const BIN_ZERO: u8 = 0b00;
pub const BIN_POS: u8 = 0b01;
pub const BIN_INVALID: u8 = 0b10;
pub const BIN_NEG: u8 = 0b11;

pub const CHAR_ZERO: char = '0';
pub const CHAR_POS: char = '1';
pub const CHAR_INVALID: char = '?';
pub const CHAR_NEG: char = 'T';

#[derive(Clone, Copy, Default, Eq, PartialEq)]
pub struct Trit(pub(crate) u8);

pub const ZERO: Trit = Trit(BIN_ZERO);
pub const POS: Trit = Trit(BIN_POS);
pub const NEG: Trit = Trit(BIN_NEG);

impl Trit {
    const fn into_i8(self) -> i8 {
        TRIT_TO_I8[self.into_index()]
    }

    pub const fn try_from_i8(n: i8) -> Result<Self> {
        let uint = (n + 1) as usize;
        if uint < 3 {
            let bits = U8_TO_TRIT[uint];
            Ok(Trit(bits))
        } else {
            Err(Error::IntegerOutOfBounds(-1, 1, n as i64))
        }
    }

    #[must_use]
    pub const fn into_char(self) -> char {
        TRIT_TO_CHAR[self.into_index()]
    }

    pub const fn try_from_char(c: char) -> Result<Self> {
        match c {
            'T' => Ok(Trit(BIN_NEG)),
            '0' => Ok(Trit(BIN_ZERO)),
            '1' => Ok(Trit(BIN_POS)),
            _ => Err(Error::InvalidCharacter(c)),
        }
    }

    #[must_use]
    pub const fn into_ordering(self) -> Ordering {
        TRIT_TO_ORDERING[self.into_index()]
    }

    pub const fn try_from_ordering(ordering: Ordering) -> Result<Self> {
        match ordering {
            Ordering::Less => Ok(NEG),
            Ordering::Equal => Ok(ZERO),
            Ordering::Greater => Ok(POS),
        }
    }

    pub const fn from_trit4(trit4: u8) -> Result<Self> {
        let trit_bits = trit4 & BITMASK;
        if trit_bits == BIN_INVALID {
            return Err(Error::InvalidBitPattern(trit_bits as u64));
        }

        Ok(Trit(trit_bits))
    }

    const fn negation_bits(self) -> u8 {
        self.0 << 1 & BITMASK
    }

    #[must_use]
    pub const fn tcmp(self, rhs: Self) -> Self {
        let i = trit2_index(self, rhs);
        let bits = TRIT2_TO_CMP[i];
        Trit(bits)
    }

    #[must_use]
    pub const fn add_with_carry(self, rhs: Self, carry_in: Self) -> (Self, Self) {
        let i = trit3_index(self, rhs, carry_in);
        let (sum, carry) = TRIT3_TO_SUM_AND_CARRY[i];
        (Trit(sum), Trit(carry))
    }

    #[must_use]
    pub const fn into_index(self) -> usize {
        self.0 as usize
    }

    #[must_use]
    pub const fn neg(self) -> Self {
        let bits = self.0 ^ self.negation_bits();
        Trit(bits)
    }

    #[must_use]
    pub const fn and(self, rhs: Self) -> Self {
        let i = trit2_index(self, rhs);
        let bits = TRIT2_TO_AND[i];
        Trit(bits)
    }

    #[must_use]
    pub const fn or(self, rhs: Self) -> Self {
        let i = trit2_index(self, rhs);
        let bits = TRIT2_TO_OR[i];
        Trit(bits)
    }

    #[must_use]
    pub const fn mul(self, rhs: Self) -> Self {
        let i = trit2_index(self, rhs);
        let bits = TRIT2_TO_PRODUCT[i];
        Trit(bits)
    }
}

const fn trit2_index(a: Trit, b: Trit) -> usize {
    a.into_index() << 2 | b.into_index()
}

const fn trit3_index(a: Trit, b: Trit, c: Trit) -> usize {
    a.into_index() << 4 | b.into_index() << 2 | c.into_index()
}

const TRIT_TO_I8: [i8; 4] = [0, 1, 0, -1];

impl Into<i8> for Trit {
    fn into(self) -> i8 {
        self.into_i8()
    }
}

const U8_TO_TRIT: [u8; 3] = [BIN_NEG, BIN_ZERO, BIN_POS];

impl TryFrom<i8> for Trit {
    type Error = Error;

    fn try_from(n: i8) -> Result<Self> {
        Self::try_from_i8(n)
    }
}

const TRIT_TO_CHAR: [char; 4] = [CHAR_ZERO, CHAR_POS, CHAR_INVALID, CHAR_NEG];

impl Into<char> for Trit {
    fn into(self) -> char {
        self.into_char()
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

impl Into<Ordering> for Trit {
    fn into(self) -> Ordering {
        self.into_ordering()
    }
}

impl TryFrom<Ordering> for Trit {
    type Error = Error;

    fn try_from(ordering: Ordering) -> Result<Self> {
        Self::try_from_ordering(ordering)
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

impl fmt::Debug for Trit {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "Trit({:02b})", self.0)
    }
}

#[cfg(test)]
mod tests {
    use crate::trit::{Trit, BIN_NEG, BIN_POS, BIN_ZERO, NEG, POS, ZERO};

    #[test]
    fn trit_into_i8() {
        assert_eq!(-1_i8, Trit(BIN_NEG).into());
        assert_eq!(0_i8, Trit(BIN_ZERO).into());
        assert_eq!(1_i8, Trit(BIN_POS).into());
    }

    #[test]
    fn trit_from_i8() {
        assert_eq!(Ok(Trit(BIN_NEG)), Trit::try_from(-1));
        assert_eq!(Ok(Trit(BIN_ZERO)), Trit::try_from(0));
        assert_eq!(Ok(Trit(BIN_POS)), Trit::try_from(1));

        assert!(Trit::try_from(-2).is_err());
        assert!(Trit::try_from(2).is_err());
    }

    #[test]
    fn trit_into_char() {
        assert_eq!('T', Trit(BIN_NEG).into());
        assert_eq!('0', Trit(BIN_ZERO).into());
        assert_eq!('1', Trit(BIN_POS).into());
    }

    #[test]
    fn trit_from_char() {
        assert_eq!(Ok(Trit(BIN_NEG)), Trit::try_from('T'));
        assert_eq!(Ok(Trit(BIN_ZERO)), Trit::try_from('0'));
        assert_eq!(Ok(Trit(BIN_POS)), Trit::try_from('1'));

        assert!(Trit::try_from('t').is_err());
        assert!(Trit::try_from('o').is_err());
        assert!(Trit::try_from('i').is_err());
    }

    #[test]
    fn trit_negate() {
        assert_eq!(POS, -NEG);
        assert_eq!(ZERO, -ZERO);
        assert_eq!(NEG, -POS);
    }

    #[test]
    fn trit_and() {
        assert_eq!(ZERO, ZERO & ZERO);
        assert_eq!(ZERO, ZERO & POS);
        assert_eq!(NEG, ZERO & NEG);
        assert_eq!(ZERO, POS & ZERO);
        assert_eq!(POS, POS & POS);
        assert_eq!(NEG, POS & NEG);
        assert_eq!(NEG, NEG & ZERO);
        assert_eq!(NEG, NEG & POS);
        assert_eq!(NEG, NEG & NEG);
    }

    #[test]
    fn trit_or() {
        assert_eq!(ZERO, ZERO | ZERO);
        assert_eq!(POS, ZERO | POS);
        assert_eq!(ZERO, ZERO | NEG);
        assert_eq!(POS, POS | ZERO);
        assert_eq!(POS, POS | POS);
        assert_eq!(POS, POS | NEG);
        assert_eq!(ZERO, NEG | ZERO);
        assert_eq!(POS, NEG | POS);
        assert_eq!(NEG, NEG | NEG);
    }

    #[test]
    fn trit_add() {
        assert_eq!((ZERO, ZERO), ZERO.add_with_carry(ZERO, ZERO));
        assert_eq!((POS, ZERO), ZERO.add_with_carry(ZERO, POS));
        assert_eq!((NEG, ZERO), ZERO.add_with_carry(ZERO, NEG));
        assert_eq!((POS, ZERO), ZERO.add_with_carry(POS, ZERO));
        assert_eq!((NEG, POS), ZERO.add_with_carry(POS, POS));
        assert_eq!((ZERO, ZERO), ZERO.add_with_carry(POS, NEG));
        assert_eq!((NEG, ZERO), ZERO.add_with_carry(NEG, ZERO));
        assert_eq!((ZERO, ZERO), ZERO.add_with_carry(NEG, POS));
        assert_eq!((POS, NEG), ZERO.add_with_carry(NEG, NEG));
        assert_eq!((POS, ZERO), POS.add_with_carry(ZERO, ZERO));
        assert_eq!((NEG, POS), POS.add_with_carry(ZERO, POS));
        assert_eq!((ZERO, ZERO), POS.add_with_carry(ZERO, NEG));
        assert_eq!((NEG, POS), POS.add_with_carry(POS, ZERO));
        assert_eq!((ZERO, POS), POS.add_with_carry(POS, POS));
        assert_eq!((POS, ZERO), POS.add_with_carry(POS, NEG));
        assert_eq!((ZERO, ZERO), POS.add_with_carry(NEG, ZERO));
        assert_eq!((POS, ZERO), POS.add_with_carry(NEG, POS));
        assert_eq!((NEG, ZERO), POS.add_with_carry(NEG, NEG));
        assert_eq!((NEG, ZERO), NEG.add_with_carry(ZERO, ZERO));
        assert_eq!((ZERO, ZERO), NEG.add_with_carry(ZERO, POS));
        assert_eq!((POS, NEG), NEG.add_with_carry(ZERO, NEG));
        assert_eq!((ZERO, ZERO), NEG.add_with_carry(POS, ZERO));
        assert_eq!((POS, ZERO), NEG.add_with_carry(POS, POS));
        assert_eq!((NEG, ZERO), NEG.add_with_carry(POS, NEG));
        assert_eq!((POS, NEG), NEG.add_with_carry(NEG, ZERO));
        assert_eq!((NEG, ZERO), NEG.add_with_carry(NEG, POS));
        assert_eq!((ZERO, NEG), NEG.add_with_carry(NEG, NEG));
    }

    #[test]
    fn trit_mul() {
        assert_eq!(ZERO, ZERO * ZERO);
        assert_eq!(ZERO, ZERO * POS);
        assert_eq!(ZERO, ZERO * NEG);
        assert_eq!(ZERO, POS * ZERO);
        assert_eq!(POS, POS * POS);
        assert_eq!(NEG, POS * NEG);
        assert_eq!(ZERO, NEG * ZERO);
        assert_eq!(NEG, NEG * POS);
        assert_eq!(POS, NEG * NEG);
    }

    #[test]
    fn trit_cmp() {
        assert!(ZERO == ZERO);
        assert!(ZERO < POS);
        assert!(ZERO > NEG);
        assert!(POS > ZERO);
        assert!(POS > NEG);
        assert!(POS == POS);
        assert!(NEG < ZERO);
        assert!(NEG < POS);
        assert!(NEG == NEG);
    }
}
