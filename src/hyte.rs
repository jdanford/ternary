use crate::{
    error::{Error, Result},
    trit::{index3, BIN_INVALID, CHAR_INVALID, _0, _1, _T},
    Trit, Tryte,
};

#[allow(clippy::cast_possible_truncation)]
const fn hyte(t2: Trit, t1: Trit, t0: Trit) -> u8 {
    Tryte::from_trits(_0, _0, _0, t2, t1, t0).low_hyte()
}

const CHAR_TO_HYTE: [u8; 256] = {
    let mut table = [BIN_INVALID; 256];

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

pub const fn try_from_char(c: char) -> Result<u8> {
    let hyte = CHAR_TO_HYTE[c as usize];
    if hyte == BIN_INVALID {
        Err(Error::InvalidCharacter(c))
    } else {
        Ok(hyte)
    }
}

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

pub const fn into_char(hyte: u8) -> char {
    let i = hyte as usize;
    HYTE_TO_CHAR[i]
}
