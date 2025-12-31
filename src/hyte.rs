use crate::{
    Trit,
    error::{Error, Result},
    trit::{_0, _1, _INVALID, _T, CHAR_INVALID, index3},
};

#[derive(Clone, Copy, Default, Eq, PartialEq)]
pub struct Hyte(u8);

impl Hyte {
    pub const ZERO: Self = Hyte(0);

    pub const TRIT_SIZE: usize = 3;
    pub const BIT_SIZE: usize = Self::TRIT_SIZE * Trit::BIT_SIZE;
    pub const BYTE_SIZE: usize = 1;

    const INVALID: Self = Self::from_trits(_INVALID, _INVALID, _INVALID);

    pub(crate) const fn into_raw(self) -> u8 {
        self.0
    }

    pub(crate) const fn from_raw(bits: u8) -> Self {
        Hyte(bits)
    }

    const fn from_trits(t2: Trit, t1: Trit, t0: Trit) -> Self {
        let bits =
            t2.into_raw() << (2 * Trit::BIT_SIZE) | t1.into_raw() << Trit::BIT_SIZE | t0.into_raw();
        Hyte(bits)
    }

    pub const fn into_char(self) -> char {
        let i = self.0 as usize;
        HYTE_TO_CHAR[i]
    }

    pub const fn try_from_char(c: char) -> Result<Self> {
        let hyte = CHAR_TO_HYTE[c as usize];
        if hyte.0 == Hyte::INVALID.0 {
            Err(Error::InvalidCharacter(c))
        } else {
            Ok(hyte)
        }
    }
}

impl TryFrom<char> for Hyte {
    type Error = Error;

    fn try_from(c: char) -> Result<Self> {
        Hyte::try_from_char(c)
    }
}

impl From<Hyte> for char {
    fn from(hyte: Hyte) -> Self {
        hyte.into_char()
    }
}

const fn hyte(t2: Trit, t1: Trit, t0: Trit) -> Hyte {
    Hyte::from_trits(t2, t1, t0)
}

const CHAR_TO_HYTE: [Hyte; 256] = {
    let mut table = [Hyte::INVALID; 256];

    table['m' as usize] = hyte(_T, _T, _T);
    table['l' as usize] = hyte(_T, _T, _0);
    table['k' as usize] = hyte(_T, _T, _1);
    table['j' as usize] = hyte(_T, _0, _T);
    table['i' as usize] = hyte(_T, _0, _0);
    table['h' as usize] = hyte(_T, _0, _1);
    table['g' as usize] = hyte(_T, _1, _T);
    table['f' as usize] = hyte(_T, _1, _0);
    table['e' as usize] = hyte(_T, _1, _1);
    table['d' as usize] = hyte(_0, _T, _T);
    table['c' as usize] = hyte(_0, _T, _0);
    table['b' as usize] = hyte(_0, _T, _1);
    table['a' as usize] = hyte(_0, _0, _T);
    table['0' as usize] = hyte(_0, _0, _0);
    table['A' as usize] = hyte(_0, _0, _1);
    table['B' as usize] = hyte(_0, _1, _T);
    table['C' as usize] = hyte(_0, _1, _0);
    table['D' as usize] = hyte(_0, _1, _1);
    table['E' as usize] = hyte(_1, _T, _T);
    table['F' as usize] = hyte(_1, _T, _0);
    table['G' as usize] = hyte(_1, _T, _1);
    table['H' as usize] = hyte(_1, _0, _T);
    table['I' as usize] = hyte(_1, _0, _0);
    table['J' as usize] = hyte(_1, _0, _1);
    table['K' as usize] = hyte(_1, _1, _T);
    table['L' as usize] = hyte(_1, _1, _0);
    table['M' as usize] = hyte(_1, _1, _1);

    table
};

const HYTE_TO_CHAR: [char; 64] = {
    let mut table = [CHAR_INVALID; 64];

    table[index3(_T, _T, _T)] = 'm';
    table[index3(_T, _T, _0)] = 'l';
    table[index3(_T, _T, _1)] = 'k';
    table[index3(_T, _0, _T)] = 'j';
    table[index3(_T, _0, _0)] = 'i';
    table[index3(_T, _0, _1)] = 'h';
    table[index3(_T, _1, _T)] = 'g';
    table[index3(_T, _1, _0)] = 'f';
    table[index3(_T, _1, _1)] = 'e';
    table[index3(_0, _T, _T)] = 'd';
    table[index3(_0, _T, _0)] = 'c';
    table[index3(_0, _T, _1)] = 'b';
    table[index3(_0, _0, _T)] = 'a';
    table[index3(_0, _0, _0)] = '0';
    table[index3(_0, _0, _1)] = 'A';
    table[index3(_0, _1, _T)] = 'B';
    table[index3(_0, _1, _0)] = 'C';
    table[index3(_0, _1, _1)] = 'D';
    table[index3(_1, _T, _T)] = 'E';
    table[index3(_1, _T, _0)] = 'F';
    table[index3(_1, _T, _1)] = 'G';
    table[index3(_1, _0, _T)] = 'H';
    table[index3(_1, _0, _0)] = 'I';
    table[index3(_1, _0, _1)] = 'J';
    table[index3(_1, _1, _T)] = 'K';
    table[index3(_1, _1, _0)] = 'L';
    table[index3(_1, _1, _1)] = 'M';

    table
};
