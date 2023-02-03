use super::error::{Error, Result};
use super::trit::{BIN_INVALID, CHAR_INVALID};

const CHAR_TO_HYTE: [u8; 256] = {
    let mut table = [BIN_INVALID; 256];

    table['m' as usize] = 0b11_11_11;
    table['l' as usize] = 0b11_11_00;
    table['k' as usize] = 0b11_11_01;
    table['j' as usize] = 0b11_00_11;
    table['i' as usize] = 0b11_00_00;
    table['h' as usize] = 0b11_00_01;
    table['g' as usize] = 0b11_01_11;
    table['f' as usize] = 0b11_01_00;
    table['e' as usize] = 0b11_01_01;
    table['d' as usize] = 0b00_11_11;
    table['c' as usize] = 0b00_11_00;
    table['b' as usize] = 0b00_11_01;
    table['a' as usize] = 0b00_00_11;
    table['0' as usize] = 0b00_00_00;
    table['A' as usize] = 0b00_00_01;
    table['B' as usize] = 0b00_01_11;
    table['C' as usize] = 0b00_01_00;
    table['D' as usize] = 0b00_01_01;
    table['E' as usize] = 0b01_11_11;
    table['F' as usize] = 0b01_11_00;
    table['G' as usize] = 0b01_11_01;
    table['H' as usize] = 0b01_00_11;
    table['I' as usize] = 0b01_00_00;
    table['J' as usize] = 0b01_00_01;
    table['K' as usize] = 0b01_01_11;
    table['L' as usize] = 0b01_01_00;
    table['M' as usize] = 0b01_01_01;

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

    table[0b11_11_11] = 'm';
    table[0b11_11_00] = 'l';
    table[0b11_11_01] = 'k';
    table[0b11_00_11] = 'j';
    table[0b11_00_00] = 'i';
    table[0b11_00_01] = 'h';
    table[0b11_01_11] = 'g';
    table[0b11_01_00] = 'f';
    table[0b11_01_01] = 'e';
    table[0b00_11_11] = 'd';
    table[0b00_11_00] = 'c';
    table[0b00_11_01] = 'b';
    table[0b00_00_11] = 'a';
    table[0b00_00_00] = '0';
    table[0b00_00_01] = 'A';
    table[0b00_01_11] = 'B';
    table[0b00_01_00] = 'C';
    table[0b00_01_01] = 'D';
    table[0b01_11_11] = 'E';
    table[0b01_11_00] = 'F';
    table[0b01_11_01] = 'G';
    table[0b01_00_11] = 'H';
    table[0b01_00_00] = 'I';
    table[0b01_00_01] = 'J';
    table[0b01_01_11] = 'K';
    table[0b01_01_00] = 'L';
    table[0b01_01_01] = 'M';

    table
};

pub const fn into_char(hyte: u8) -> char {
    let i = hyte as usize;
    HYTE_TO_CHAR[i]
}
