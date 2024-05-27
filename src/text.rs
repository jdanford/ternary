use std::char;

use crate::{
    error::{Error, Result},
    trit::{self, _T},
    tryte::{self, Tryte},
    TInt, Trit,
};

const SINGLE_RANGE: usize = 3usize.pow(5);
const DOUBLE_RANGE: usize = 3usize.pow(9);
const TRIPLE_RANGE: usize = 3usize.pow(14);

#[allow(clippy::cast_possible_wrap)]
const SINGLE_OFFSET: isize = (SINGLE_RANGE as isize - 1) / 2;
#[allow(clippy::cast_possible_wrap)]
const DOUBLE_OFFSET: isize = (DOUBLE_RANGE as isize - 1) / 2;
#[allow(clippy::cast_possible_wrap)]
const TRIPLE_OFFSET: isize = (TRIPLE_RANGE as isize - 1) / 2;

const SINGLE_MIN: usize = 0;
const SINGLE_MAX: usize = SINGLE_MIN + SINGLE_RANGE - 1;

const DOUBLE_MIN: usize = SINGLE_MAX + 1;
const DOUBLE_MAX: usize = DOUBLE_MIN + DOUBLE_RANGE - 1;

const TRIPLE_MIN: usize = DOUBLE_MAX + 1;
const TRIPLE_MAX: usize = TRIPLE_MIN + TRIPLE_RANGE - 1;

#[allow(dead_code)]
const SINGLE_BITMASK: u16 = 0b00_11_11_11_11_11;

const DOUBLE_START_BITMASK: u16 = 0b00_00_11_11_11_11;
const DOUBLE_START_PATTERN: u16 = 0b01_11_00_00_00_00;

const TRIPLE_START_BITMASK: u16 = 0b00_00_11_11_11_11;
const TRIPLE_START_PATTERN: u16 = 0b01_01_00_00_00_00;

const CONTINUATION_BITMASK: u16 = 0b00_11_11_11_11_11;
const CONTINUATION_PATTERN: u16 = 0b11_00_00_00_00_00;

fn tryte_is_continuation(tryte: Tryte) -> bool {
    tryte.trit(5) == _T
}

pub fn encode_str(s: &str) -> Result<Vec<Tryte>> {
    let mut dest = [Tryte::ZERO; 3];
    let mut trytes = Vec::new();
    for c in s.chars() {
        let slice = encode_char(&mut dest[..], c)?;
        trytes.extend_from_slice(slice);
    }

    Ok(trytes)
}

pub fn decode_string(src: &[Tryte]) -> Result<String> {
    let len = src.len();
    let mut s = String::new();
    let mut i = 0;
    while i < len {
        let slice = &src[i..];
        let (c, count) = decode_char(slice)?;
        s.push(c);
        i += count;
    }

    Ok(s)
}

pub fn encode_char(dest: &mut [Tryte], c: char) -> Result<&[Tryte]> {
    let codepoint = c as u32;
    let (len, codepoint_offset) = match codepoint as usize {
        SINGLE_MIN..=SINGLE_MAX => Ok((1, SINGLE_OFFSET)),
        DOUBLE_MIN..=DOUBLE_MAX => Ok((2, DOUBLE_OFFSET)),
        TRIPLE_MIN..=TRIPLE_MAX => Ok((3, TRIPLE_OFFSET)),
        _ => Err(Error::InvalidCharacter(c)),
    }?;

    let shifted_codepoint = shift_codepoint(codepoint, codepoint_offset)?;
    let src = TInt::<3>::try_from_int(shifted_codepoint)?.trytes;

    match len {
        // 0xxxxx -> 0xxxxx
        1 => {
            dest[0] = src[0];
        }

        // yyxxxx 000yyy -> 1Txxxx Tyyyyy
        2 => {
            // yyxxxx
            let (x0123, y01) = src[0].split_trits_raw(4);

            // 000yyy
            let (y234, _) = src[1].split_trits_raw(3);

            // 1Txxxx
            let double_start_trits = DOUBLE_START_PATTERN | x0123;
            dest[0] = Tryte::from_raw(double_start_trits);

            // Tyyyyy
            let continuation_trits = CONTINUATION_PATTERN | (y234 << (2 * Trit::BIT_SIZE)) | y01;
            dest[1] = Tryte::from_raw(continuation_trits);
        }

        // yyxxxx zzzyyy 0000zz -> 11xxxx Tyyyyy Tzzzzz
        3 => {
            // yyxxxx
            let (x0123, y01) = src[0].split_trits_raw(4);

            // zzzyyy
            let (y234, z012) = src[1].split_trits_raw(3);

            // 0000zz
            let (z34, _) = src[2].split_trits_raw(2);

            // 11xxxx
            let triple_start_trits = TRIPLE_START_PATTERN | x0123;
            dest[0] = Tryte::from_raw(triple_start_trits);

            // Tyyyyy
            let continuation1_trits = CONTINUATION_PATTERN | (y234 << (2 * Trit::BIT_SIZE)) | y01;
            dest[1] = Tryte::from_raw(continuation1_trits);

            // Tzzzzz
            let continuation2_trits = CONTINUATION_PATTERN | (z34 << (3 * Trit::BIT_SIZE)) | z012;
            dest[2] = Tryte::from_raw(continuation2_trits);
        }

        _ => unreachable!(),
    }

    Ok(&dest[..len])
}

pub fn decode_char(src: &[Tryte]) -> Result<(char, usize)> {
    let mut dest = [Tryte::ZERO; 3];

    let tryte0 = src[0];
    let trit5 = tryte0.trit(5);
    let trit4 = tryte0.trit(4);
    let (codepoint_offset, len) = match (trit5, trit4) {
        // 0xxxxx -> 0xxxxx
        (trit::_0, _) => {
            dest[0] = tryte0;
            Ok((SINGLE_OFFSET, 1))
        }

        // 1Txxxx Tyyyyy -> yyxxxx 000yyy
        (trit::_1, trit::_T) => {
            let tryte1 = src[1];
            if !tryte_is_continuation(tryte1) {
                return Err(invalid_encoding(&src[..2]));
            }

            // 1Txxxx
            let x0123 = tryte0.into_raw() & DOUBLE_START_BITMASK;

            // Tyyyyy
            let y01234 = tryte1.into_raw() & CONTINUATION_BITMASK;

            // yyxxxx
            let dest0_trits = (y01234 << (4 * Trit::BIT_SIZE) & tryte::BITMASK) | x0123;
            dest[0] = Tryte::from_raw(dest0_trits);

            // 000yyy
            let dest1_trits = y01234 >> (2 * Trit::BIT_SIZE);
            dest[1] = Tryte::from_raw(dest1_trits);

            Ok((DOUBLE_OFFSET, 2))
        }

        // 11xxxx Tyyyyy Tzzzzz -> yyxxxx zzzyyy 0000zz
        (trit::_1, trit::_1) => {
            let tryte1 = src[1];
            if !tryte_is_continuation(tryte1) {
                return Err(invalid_encoding(&src[..2]));
            }

            let tryte2 = src[2];
            if !tryte_is_continuation(tryte2) {
                return Err(invalid_encoding(&src[..3]));
            }

            // 11xxxx
            let x0123 = tryte0.into_raw() & TRIPLE_START_BITMASK;

            // Tyyyyy
            let y01234 = tryte1.into_raw() & CONTINUATION_BITMASK;

            // Tzzzzz
            let z01234 = tryte2.into_raw() & CONTINUATION_BITMASK;

            // yyxxxx
            let dest0_trits = (y01234 << (4 * Trit::BIT_SIZE) & tryte::BITMASK) | x0123;
            dest[0] = Tryte::from_raw(dest0_trits);

            // zzzyyy
            let dest1_trits =
                (z01234 << (3 * Trit::BIT_SIZE) & tryte::BITMASK) | y01234 >> (2 * Trit::BIT_SIZE);
            dest[1] = Tryte::from_raw(dest1_trits);

            // 0000zz
            let dest2_trits = z01234 >> (3 * Trit::BIT_SIZE);
            dest[2] = Tryte::from_raw(dest2_trits);

            Ok((TRIPLE_OFFSET, 3))
        }

        _ => Err(invalid_encoding(&src[..1])),
    }?;

    let value = TInt::from_trytes(dest);
    #[allow(clippy::cast_possible_truncation)]
    let shifted_codepoint = value.into_i64() as i32;
    let codepoint = unshift_codepoint(shifted_codepoint, codepoint_offset)?;
    let c = char::from_u32(codepoint).ok_or_else(|| invalid_encoding(src))?;
    Ok((c, len))
}

fn invalid_encoding(src: &[Tryte]) -> Error {
    Error::InvalidEncoding(src.to_vec())
}

#[allow(clippy::cast_possible_truncation, clippy::cast_possible_wrap)]
fn shift_codepoint(codepoint: u32, offset: isize) -> Result<i32> {
    let signed_codepoint = i32::try_from(codepoint)?;
    Ok(signed_codepoint.wrapping_sub(offset as i32))
}

#[allow(
    clippy::cast_possible_truncation,
    clippy::cast_possible_wrap,
    clippy::cast_sign_loss
)]
fn unshift_codepoint(shifted_codepoint: i32, offset: isize) -> Result<u32> {
    let signed_offset = i32::try_from(offset)?;
    let codepoint = u32::try_from(shifted_codepoint.wrapping_add(signed_offset))?;
    Ok(codepoint)
}

#[cfg(test)]
mod tests {
    use crate::text::{decode_string, encode_str};

    fn assert_roundtrip(s1: &str) {
        let trytes = encode_str(s1).unwrap();
        let s2 = decode_string(&trytes).unwrap();
        assert_eq!(s1, &s2[..]);
    }

    #[test]
    fn text_roundtrip_empty() {
        assert_roundtrip("");
    }

    #[test]
    fn text_roundtrip_fancy() {
        assert_roundtrip("⸘I like to éat 🍎 and 🍌 wheñ it is 100℉ oütside‽");
    }
}
