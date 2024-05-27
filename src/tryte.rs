use std::{fmt, io::Cursor, ops};

use byteorder::{LittleEndian, ReadBytesExt, WriteBytesExt};

use crate::{
    error::{assert_length_eq, Error, Result},
    hyte::Hyte,
    tables::TRYTE_TO_I16,
    trit::{self, Trit, _0, _1, _T},
};

pub const BITMASK: u16 = 0b11_11_11_11_11_11;
pub const HYTE_BITMASK: u8 = 0b11_11_11;
const SIGN_BITMASK: u16 = 0b10_10_10_10_10_10;

#[derive(Debug, Clone, Copy, Default, Eq, PartialEq)]
pub struct Tryte(pub(crate) u16);

impl Tryte {
    pub const TRIT_SIZE: usize = 6;
    pub const BIT_SIZE: usize = Self::TRIT_SIZE * Trit::BIT_SIZE;
    pub const BYTE_SIZE: usize = 2;

    pub const ZERO: Tryte = Tryte::from_trit(_0);
    pub const MIN: Tryte = Tryte::from_trits([_T, _T, _T, _T, _T, _T]);
    pub const MAX: Tryte = Tryte::from_trits([_1, _1, _1, _1, _1, _1]);

    pub(crate) const fn from_raw(bits: u16) -> Self {
        Tryte(bits)
    }

    pub(crate) const fn into_raw(self) -> u16 {
        self.0
    }

    pub(crate) const fn try_from_raw(bits: u16) -> Result<Self> {
        if bits >> Self::BIT_SIZE != 0 {
            return Err(Error::InvalidBitPattern(bits as u64));
        }

        let tryte = Tryte(bits);

        let mut i = 0;
        while i < Self::TRIT_SIZE {
            let trit = tryte.trit(i);
            let trit_bits = trit.into_raw();
            if trit_bits == trit::BIN_INVALID {
                return Err(Error::InvalidBitPattern(bits as u64));
            }

            i += 1;
        }

        Ok(tryte)
    }

    pub(crate) const fn into_index(self) -> usize {
        self.0 as usize
    }

    pub const fn from_trit(trit: Trit) -> Self {
        Tryte(trit.into_raw() as u16)
    }

    pub const fn try_into_trit(self) -> Result<Trit> {
        let bits = self.into_raw();
        if bits == trit::BIN_INVALID as u16 || bits > trit::BIN_T as u16 {
            return Err(Error::InvalidBitPattern(bits as u64));
        }

        #[allow(clippy::cast_possible_truncation)]
        Ok(Trit::from_raw(bits as u8))
    }

    pub const fn from_trits(trits: [Trit; Self::TRIT_SIZE]) -> Self {
        let mut i = Self::TRIT_SIZE - 1;
        let mut bits = 0;

        loop {
            let trit = trits[i];
            bits = (bits << Trit::BIT_SIZE) | trit.into_raw() as u16;

            if i == 0 {
                break;
            }

            i -= 1;
        }

        Tryte::from_raw(bits)
    }

    #[allow(clippy::cast_possible_truncation)]
    pub const fn into_trits(self) -> [Trit; Self::TRIT_SIZE] {
        let mut bits = self.into_raw();
        let mut trits = [_0; Self::TRIT_SIZE];
        let mut i = 0;

        while i < Self::TRIT_SIZE {
            trits[i] = Trit::from_raw(bits as u8 & trit::BITMASK);
            bits >>= Trit::BIT_SIZE;
            i += 1;
        }

        trits
    }

    const fn from_hytes(low_hyte: Hyte, high_hyte: Hyte) -> Self {
        let bits = (high_hyte.into_raw() as u16) << Hyte::BIT_SIZE | (low_hyte.into_raw() as u16);
        Tryte(bits)
    }

    pub const fn from_hyte(low_hyte: Hyte) -> Self {
        Self::from_hytes(low_hyte, Hyte::ZERO)
    }

    pub const fn low_hyte(self) -> Hyte {
        Self::hyte_from_raw(self.into_raw())
    }

    #[allow(clippy::cast_possible_truncation)]
    pub const fn high_hyte(self) -> Hyte {
        Self::hyte_from_raw(self.into_raw() >> Hyte::BIT_SIZE as u16)
    }

    pub const fn hyte_from_raw(raw: u16) -> Hyte {
        #[allow(clippy::cast_possible_truncation)]
        let bits = raw as u8 & HYTE_BITMASK;
        Hyte::from_raw(bits)
    }

    pub const fn into_hytes(self) -> (Hyte, Hyte) {
        (self.low_hyte(), self.high_hyte())
    }

    pub fn try_into_hyte(self) -> Result<Hyte> {
        let (lo, hi) = self.into_hytes();
        if hi == Hyte::ZERO {
            Ok(lo)
        } else {
            Err(Error::InvalidBitPattern(u64::from(self.into_raw())))
        }
    }

    pub const fn split_trits_raw(self, n: usize) -> (u16, u16) {
        let mask = (1 << (n * Trit::BIT_SIZE)) - 1;
        let raw = self.into_raw();
        let low = raw & mask;
        let high = raw >> (n * Trit::BIT_SIZE);
        (low, high)
    }

    #[allow(clippy::cast_possible_truncation)]
    pub const fn trit(self, i: usize) -> Trit {
        let shf = (i * Trit::BIT_SIZE) as u16;
        let bits = ((self.into_raw() >> shf) as u8) & trit::BITMASK;
        Trit::from_raw(bits)
    }

    #[allow(clippy::cast_possible_truncation)]
    pub const fn set_trit(self, i: usize, trit: Trit) -> Self {
        let shf = (i * Trit::BIT_SIZE) as u16;
        let zero_bits = !((trit::BITMASK as u16) << shf);
        let tryte_bits = self.into_raw() & zero_bits;
        let trit_bits = (trit.into_raw() as u16) << shf;
        Tryte(tryte_bits | trit_bits)
    }

    pub fn try_from_bytes(bytes: [u8; 2]) -> Result<Self> {
        let bits = Cursor::new(bytes).read_u16::<LittleEndian>().unwrap();
        Tryte::try_from_raw(bits)
    }

    pub fn into_bytes(self) -> [u8; 2] {
        let mut bytes = vec![0; 2];
        let mut cursor = Cursor::new(&mut bytes);
        cursor.write_u16::<LittleEndian>(self.into_raw()).unwrap();
        bytes.try_into().unwrap()
    }

    pub const fn into_i16(self) -> i16 {
        TRYTE_TO_I16[self.into_index()]
    }

    const fn negation_bits(self) -> u16 {
        self.into_raw() << 1 & SIGN_BITMASK
    }

    pub fn add_with_carry(self, rhs: Self, carry: Trit) -> (Self, Trit) {
        let mut tryte = Tryte::ZERO;
        let mut carry = carry;

        for i in 0..Self::TRIT_SIZE {
            let a = self.trit(i);
            let b = rhs.trit(i);
            let (c, new_carry) = a.add_with_carry(b, carry);
            tryte = tryte.set_trit(i, c);
            carry = new_carry;
        }

        (tryte, carry)
    }

    pub fn and(self, rhs: Self) -> Self {
        self.zip_trits(rhs, Trit::and)
    }

    pub fn or(self, rhs: Self) -> Self {
        self.zip_trits(rhs, Trit::or)
    }

    pub fn tcmp(self, rhs: Self) -> Self {
        self.zip_trits(rhs, Trit::tcmp)
    }

    pub fn tmul(self, rhs: Self) -> Self {
        self.zip_trits(rhs, Trit::mul)
    }

    fn zip_trits<F>(self, rhs: Self, f: F) -> Self
    where
        F: Fn(Trit, Trit) -> Trit,
    {
        let mut dest = self;
        for i in 0..Self::TRIT_SIZE {
            let a = self.trit(i);
            let b = rhs.trit(i);
            let c = f(a, b);
            dest = dest.set_trit(i, c);
        }

        dest
    }

    pub fn from_hyte_str(s: &str) -> Result<Self> {
        assert_length_eq(s.len(), 2)?;

        let mut chars = s.chars();
        let high_char = chars
            .next()
            .ok_or_else(|| Error::InvalidString(s.to_owned()))?;
        let low_char = chars
            .next()
            .ok_or_else(|| Error::InvalidString(s.to_owned()))?;
        let high_hyte = Hyte::try_from(high_char)?;
        let low_hyte = Hyte::try_from(low_char)?;
        let tryte = Self::from_hytes(low_hyte, high_hyte);
        Ok(tryte)
    }

    pub fn fmt_hytes<W: fmt::Write>(self, writer: &mut W) -> fmt::Result {
        let (low_hyte, high_hyte) = self.into_hytes();
        let low_char = low_hyte.into_char();
        let high_char = high_hyte.into_char();
        write!(writer, "{high_char}{low_char}")?;
        Ok(())
    }
}

impl From<Trit> for Tryte {
    fn from(trit: Trit) -> Self {
        Tryte::from_trit(trit)
    }
}

impl TryFrom<Tryte> for Trit {
    type Error = Error;

    fn try_from(tryte: Tryte) -> Result<Self> {
        tryte.try_into_trit()
    }
}

impl From<Hyte> for Tryte {
    fn from(hyte: Hyte) -> Self {
        Tryte::from_hyte(hyte)
    }
}

impl TryFrom<Tryte> for Hyte {
    type Error = Error;

    fn try_from(tryte: Tryte) -> Result<Self> {
        let (lo, hi) = tryte.into_hytes();
        if hi == Hyte::ZERO {
            Ok(lo)
        } else {
            Err(Error::InvalidBitPattern(u64::from(tryte.into_raw())))
        }
    }
}

impl ops::Neg for Tryte {
    type Output = Self;

    fn neg(self) -> Self::Output {
        let bits = self.into_raw() ^ self.negation_bits();
        Tryte(bits)
    }
}

impl fmt::Display for Tryte {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let (low_hyte, high_hyte) = self.into_hytes();
        let low_char = char::from(low_hyte);
        let high_char = char::from(high_hyte);
        write!(f, "{high_char}{low_char}")
    }
}

#[cfg(test)]
mod tests {
    use crate::{
        test_constants::{
            TRYTE_0, TRYTE_1, TRYTE_64, TRYTE_MAX, TRYTE_MIN, TRYTE_NEG1, TRYTE_NEG64,
        },
        trit::{_0, _1, _T},
        Trit, Tryte,
    };

    #[test]
    fn trit_from_tryte() {
        assert_eq!(_T, Trit::try_from(TRYTE_NEG1).unwrap());
        assert_eq!(_0, Trit::try_from(TRYTE_0).unwrap());
        assert_eq!(_1, Trit::try_from(TRYTE_1).unwrap());

        assert!(Trit::try_from(TRYTE_NEG64).is_err());
        assert!(Trit::try_from(TRYTE_64).is_err());
    }

    #[test]
    fn tryte_from_trit() {
        assert_eq!(TRYTE_NEG1, _T.into());
        assert_eq!(TRYTE_0, _0.into());
        assert_eq!(TRYTE_1, _1.into());
    }

    #[test]
    fn tryte_try_from_bytes() {
        assert_eq!(
            TRYTE_MIN,
            Tryte::try_from_bytes([0b11_11_11_11, 0b00_00_11_11]).unwrap()
        );
        assert_eq!(
            TRYTE_NEG64,
            Tryte::try_from_bytes([0b01_11_00_11, 0b00_00_00_11]).unwrap()
        );
        assert_eq!(
            TRYTE_NEG1,
            Tryte::try_from_bytes([0b00_00_00_11, 0b00_00_00_00]).unwrap()
        );
        assert_eq!(
            TRYTE_0,
            Tryte::try_from_bytes([0b00_00_00_00, 0b00_00_00_00]).unwrap()
        );
        assert_eq!(
            TRYTE_1,
            Tryte::try_from_bytes([0b00_00_00_01, 0b00_00_00_00]).unwrap()
        );
        assert_eq!(
            TRYTE_64,
            Tryte::try_from_bytes([0b11_01_00_01, 0b00_00_00_01]).unwrap()
        );
        assert_eq!(
            TRYTE_MAX,
            Tryte::try_from_bytes([0b01_01_01_01, 0b00_00_01_01]).unwrap()
        );

        assert!(Tryte::try_from_bytes([0b01_01_10_01, 0b00_00_01_01]).is_err());
    }

    #[test]
    fn tryte_write_bytes() {
        assert_eq!([0b11_11_11_11, 0b00_00_11_11], TRYTE_MIN.into_bytes());
        assert_eq!([0b01_11_00_11, 0b00_00_00_11], TRYTE_NEG64.into_bytes());
        assert_eq!([0b00_00_00_11, 0b00_00_00_00], TRYTE_NEG1.into_bytes());
        assert_eq!([0b00_00_00_00, 0b00_00_00_00], TRYTE_0.into_bytes());
        assert_eq!([0b00_00_00_01, 0b00_00_00_00], TRYTE_1.into_bytes());
        assert_eq!([0b11_01_00_01, 0b00_00_00_01], TRYTE_64.into_bytes());
        assert_eq!([0b01_01_01_01, 0b00_00_01_01], TRYTE_MAX.into_bytes());
    }

    #[test]
    fn tryte_display_hytes() {
        assert_eq!("mm", format!("{TRYTE_MIN}"));
        assert_eq!("bj", format!("{TRYTE_NEG64}"));
        assert_eq!("0a", format!("{TRYTE_NEG1}"));
        assert_eq!("00", format!("{TRYTE_0}"));
        assert_eq!("0A", format!("{TRYTE_1}"));
        assert_eq!("BJ", format!("{TRYTE_64}"));
        assert_eq!("MM", format!("{TRYTE_MAX}"));
    }

    #[test]
    fn tryte_from_hyte_str() {
        assert_eq!(TRYTE_MIN, Tryte::from_hyte_str("mm").unwrap());
        assert_eq!(TRYTE_NEG64, Tryte::from_hyte_str("bj").unwrap());
        assert_eq!(TRYTE_NEG1, Tryte::from_hyte_str("0a").unwrap());
        assert_eq!(TRYTE_0, Tryte::from_hyte_str("00").unwrap());
        assert_eq!(TRYTE_1, Tryte::from_hyte_str("0A").unwrap());
        assert_eq!(TRYTE_64, Tryte::from_hyte_str("BJ").unwrap());
        assert_eq!(TRYTE_MAX, Tryte::from_hyte_str("MM").unwrap());

        assert!(Tryte::from_hyte_str("").is_err());
        assert!(Tryte::from_hyte_str("M").is_err());
        assert!(Tryte::from_hyte_str("MMM").is_err());
        assert!(Tryte::from_hyte_str("NN").is_err());
    }

    #[test]
    fn tryte_negate() {
        assert_eq!(TRYTE_MIN, -TRYTE_MAX);
        assert_eq!(TRYTE_NEG64, -TRYTE_64);
        assert_eq!(TRYTE_NEG1, -TRYTE_1);
        assert_eq!(TRYTE_0, -TRYTE_0);
        assert_eq!(TRYTE_1, -TRYTE_NEG1);
        assert_eq!(TRYTE_64, -TRYTE_NEG64);
        assert_eq!(TRYTE_MAX, -TRYTE_MIN);
    }

    #[test]
    fn tryte_add() {
        assert_eq!((TRYTE_0, _0), TRYTE_1.add_with_carry(TRYTE_NEG1, _0));
        assert_eq!((TRYTE_0, _0), TRYTE_64.add_with_carry(TRYTE_NEG64, _0));
        assert_eq!((TRYTE_0, _0), TRYTE_MAX.add_with_carry(TRYTE_MIN, _0));

        assert_eq!((TRYTE_MIN, _0), TRYTE_MIN.add_with_carry(TRYTE_0, _0));
        assert_eq!((TRYTE_NEG64, _0), TRYTE_NEG64.add_with_carry(TRYTE_0, _0));
        assert_eq!((TRYTE_NEG1, _0), TRYTE_NEG1.add_with_carry(TRYTE_0, _0));
        assert_eq!((TRYTE_0, _0), TRYTE_0.add_with_carry(TRYTE_0, _0));
        assert_eq!((TRYTE_1, _0), TRYTE_1.add_with_carry(TRYTE_0, _0));
        assert_eq!((TRYTE_64, _0), TRYTE_64.add_with_carry(TRYTE_0, _0));
        assert_eq!((TRYTE_MAX, _0), TRYTE_MAX.add_with_carry(TRYTE_0, _0));

        assert_eq!((TRYTE_MIN, _0), TRYTE_0.add_with_carry(TRYTE_MIN, _0));
        assert_eq!((TRYTE_NEG64, _0), TRYTE_0.add_with_carry(TRYTE_NEG64, _0));
        assert_eq!((TRYTE_NEG1, _0), TRYTE_0.add_with_carry(TRYTE_NEG1, _0));
        assert_eq!((TRYTE_0, _0), TRYTE_0.add_with_carry(TRYTE_0, _0));
        assert_eq!((TRYTE_1, _0), TRYTE_0.add_with_carry(TRYTE_1, _0));
        assert_eq!((TRYTE_64, _0), TRYTE_0.add_with_carry(TRYTE_64, _0));
        assert_eq!((TRYTE_MAX, _0), TRYTE_0.add_with_carry(TRYTE_MAX, _0));
    }
}
