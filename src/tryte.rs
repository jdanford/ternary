use std::{fmt, io, ops};

use byteorder::{LittleEndian, ReadBytesExt, WriteBytesExt};

use crate::{
    constants::{HYTE_BIT_LEN, TRIT_BIT_LEN, TRYTE_TRIT_LEN},
    error::{assert_length, Error, Result},
    hyte,
    trit::{self, Trit, _0},
};

pub use crate::constants::TRYTE_TRIT_LEN as TRIT_LEN;

pub const BITMASK: u16 = 0b11_11_11_11_11_11;
const HYTE_BITMASK: u8 = 0b11_11_11;
const SIGN_BITMASK: u16 = 0b10_10_10_10_10_10;

#[derive(Clone, Copy, Default, Eq, PartialEq)]
pub struct Tryte(u16);

pub const ZERO: Tryte = Tryte::from_trit(_0);

impl Tryte {
    pub const fn from_trit(trit: Trit) -> Self {
        Tryte(trit.into_raw() as u16)
    }

    pub const fn try_into_trit(self) -> Result<Trit> {
        let bits = self.0;
        if bits == trit::BIN_INVALID as u16 || bits > trit::BIN_T as u16 {
            return Err(Error::InvalidBitPattern(bits as u64));
        }

        #[allow(clippy::cast_possible_truncation)]
        Trit::try_from_raw(bits as u8)
    }

    pub const fn from_trits(t5: Trit, t4: Trit, t3: Trit, t2: Trit, t1: Trit, t0: Trit) -> Self {
        let mut tryte = ZERO;
        tryte = tryte.set_trit(5, t5);
        tryte = tryte.set_trit(4, t4);
        tryte = tryte.set_trit(3, t3);
        tryte = tryte.set_trit(2, t2);
        tryte = tryte.set_trit(1, t1);
        tryte = tryte.set_trit(0, t0);
        tryte
    }

    pub const fn into_raw(self) -> u16 {
        self.0
    }

    pub const fn try_from_raw(bits: u16) -> Result<Self> {
        let tryte = Tryte(bits);

        let mut i = 0;
        while i < TRYTE_TRIT_LEN {
            let trit = tryte.get_trit(i);
            let trit_bits = trit.into_raw();
            if trit_bits == trit::BIN_INVALID {
                return Err(Error::InvalidBitPattern(trit_bits as u64));
            }

            i += 1;
        }

        Ok(tryte)
    }

    pub const fn from_raw(bits: u16) -> Self {
        Tryte(bits)
    }

    pub const fn split_trits_raw(self, n: usize) -> (u16, u16) {
        let mask = (1 << (n * TRIT_BIT_LEN)) - 1;
        let raw = self.into_raw();
        let low = raw & mask;
        let high = raw >> (n * TRIT_BIT_LEN);
        (low, high)
    }

    pub const fn into_index(self) -> usize {
        self.into_raw() as usize
    }

    #[allow(clippy::cast_possible_truncation)]
    pub const fn get_trit(self, i: usize) -> Trit {
        let shf = (i * TRIT_BIT_LEN) as u16;
        let bits = ((self.0 >> shf) as u8) & trit::BITMASK;
        Trit::from_raw(bits)
    }

    #[allow(clippy::cast_possible_truncation)]
    pub const fn set_trit(self, i: usize, trit: Trit) -> Self {
        let shf = (i * TRIT_BIT_LEN) as u16;
        let zero_bits = !((trit::BITMASK as u16) << shf);
        let tryte_bits = self.0 & zero_bits;
        let trit_bits = (trit.into_raw() as u16) << shf;
        let bits = tryte_bits | trit_bits;
        Tryte(bits)
    }

    pub fn from_bytes<R: ReadBytesExt>(reader: &mut R) -> Result<Self> {
        let bits = reader.read_u16::<LittleEndian>()?;
        Tryte::try_from_raw(bits)
    }

    pub fn write_bytes<W: WriteBytesExt>(self, writer: &mut W) -> Result<()> {
        writer.write_u16::<LittleEndian>(self.into_raw())?;
        Ok(())
    }

    const fn from_hytes(low_hyte: u8, high_hyte: u8) -> Self {
        let bits = (high_hyte as u16) << HYTE_BIT_LEN | (low_hyte as u16);
        Tryte(bits)
    }

    pub const fn low_hyte(self) -> u8 {
        self.low_trit4() & HYTE_BITMASK
    }

    #[allow(clippy::cast_possible_truncation)]
    pub const fn high_hyte(self) -> u8 {
        (self.0 >> HYTE_BIT_LEN) as u8 & HYTE_BITMASK
    }

    pub const fn hytes(self) -> (u8, u8) {
        (self.low_hyte(), self.high_hyte())
    }

    #[allow(clippy::cast_possible_truncation)]
    pub const fn low_trit4(self) -> u8 {
        self.0 as u8
    }

    const fn negation_bits(self) -> u16 {
        self.0 << 1 & SIGN_BITMASK
    }

    pub const fn neg(self) -> Self {
        let bits = self.0 ^ self.negation_bits();
        Tryte(bits)
    }

    pub fn add_with_carry(self, rhs: Self, carry: Trit) -> (Self, Trit) {
        let mut tryte = ZERO;
        let mut carry = carry;

        for i in 0..TRYTE_TRIT_LEN {
            let a = self.get_trit(i);
            let b = rhs.get_trit(i);
            let (c, new_carry) = a.add_with_carry(b, carry);
            tryte = tryte.set_trit(i, c);
            carry = new_carry;
        }

        (tryte, carry)
    }

    pub fn from_hyte_str(s: &str) -> Result<Self> {
        assert_length(s.len(), 2)?;

        let mut chars = s.chars();
        let high_char = chars
            .next()
            .ok_or_else(|| Error::InvalidString(s.to_owned()))?;
        let low_char = chars
            .next()
            .ok_or_else(|| Error::InvalidString(s.to_owned()))?;
        let high_hyte = hyte::try_from_char(high_char)?;
        let low_hyte = hyte::try_from_char(low_char)?;
        let tryte = Self::from_hytes(low_hyte, high_hyte);
        Ok(tryte)
    }

    pub fn write_hytes<W: io::Write>(self, writer: &mut W) -> Result<()> {
        let (low_hyte, high_hyte) = self.hytes();
        let low_char = hyte::into_char(low_hyte);
        let high_char = hyte::into_char(high_hyte);
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

impl ops::Neg for Tryte {
    type Output = Self;

    fn neg(self) -> Self::Output {
        self.neg()
    }
}

impl fmt::Debug for Tryte {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        for i in (0..TRYTE_TRIT_LEN).rev() {
            let trit = self.get_trit(i);
            write!(f, "{trit:?}")?;
        }

        Ok(())
    }
}

impl fmt::Display for Tryte {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let (low_hyte, high_hyte) = self.hytes();
        let low_char = hyte::into_char(low_hyte);
        let high_char = hyte::into_char(high_hyte);
        write!(f, "{high_char}{low_char}")
    }
}

#[cfg(test)]
mod tests {
    use std::io::Cursor;

    use crate::{
        test_constants::{
            TRYTE_0, TRYTE_1, TRYTE_64, TRYTE_MAX, TRYTE_MIN, TRYTE_NEG1, TRYTE_NEG64,
        },
        trit::{_0, _1, _T},
        Result, Trit, Tryte,
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
    fn tryte_from_bytes() {
        assert_eq!(TRYTE_MIN, from_bytes(0b11_11_11_11, 0b00_00_11_11).unwrap());
        assert_eq!(
            TRYTE_NEG64,
            from_bytes(0b01_11_00_11, 0b00_00_00_11).unwrap()
        );
        assert_eq!(
            TRYTE_NEG1,
            from_bytes(0b00_00_00_11, 0b00_00_00_00).unwrap()
        );
        assert_eq!(TRYTE_0, from_bytes(0b00_00_00_00, 0b00_00_00_00).unwrap());
        assert_eq!(TRYTE_1, from_bytes(0b00_00_00_01, 0b00_00_00_00).unwrap());
        assert_eq!(TRYTE_64, from_bytes(0b11_01_00_01, 0b00_00_00_01).unwrap());
        assert_eq!(TRYTE_MAX, from_bytes(0b01_01_01_01, 0b00_00_01_01).unwrap());

        assert!(from_bytes(0b01_01_10_01, 0b00_00_01_01).is_err());
    }

    fn from_bytes(low: u8, high: u8) -> Result<Tryte> {
        let mut cursor = Cursor::new(vec![low, high]);
        Tryte::from_bytes(&mut cursor)
    }

    #[test]
    fn tryte_write_bytes() {
        assert_eq!(vec![0b11_11_11_11, 0b00_00_11_11], get_bytes(TRYTE_MIN));
        assert_eq!(vec![0b01_11_00_11, 0b00_00_00_11], get_bytes(TRYTE_NEG64));
        assert_eq!(vec![0b00_00_00_11, 0b00_00_00_00], get_bytes(TRYTE_NEG1));
        assert_eq!(vec![0b00_00_00_00, 0b00_00_00_00], get_bytes(TRYTE_0));
        assert_eq!(vec![0b00_00_00_01, 0b00_00_00_00], get_bytes(TRYTE_1));
        assert_eq!(vec![0b11_01_00_01, 0b00_00_00_01], get_bytes(TRYTE_64));
        assert_eq!(vec![0b01_01_01_01, 0b00_00_01_01], get_bytes(TRYTE_MAX));
    }

    fn get_bytes(tryte: Tryte) -> Vec<u8> {
        let mut bytes = vec![];
        tryte.write_bytes(&mut bytes).unwrap();
        bytes
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
