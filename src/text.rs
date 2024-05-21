use std::char;

use crate::{
    constants::{TRIT_BIT_LEN, WORD_LEN},
    core::Ternary,
    error::{Error, Result},
    trit::{self, _T},
    tryte::{self, Tryte},
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

pub fn encode_str(dest: &mut [Tryte], s: &str) -> Result<usize> {
    let mut i = 0;
    for c in s.chars() {
        let slice = &mut dest[i..];
        i += encode_char(slice, c)?;
    }

    Ok(i)
}

pub fn decode_string(src: &[Tryte]) -> Result<(String, usize)> {
    let mut s = String::new();
    let mut i = 0;
    let len = src.len();
    while i < len {
        let slice = &src[i..];
        let (c, count) = decode_char(slice)?;
        s.push(c);
        i += count;
    }

    Ok((s, i))
}

pub fn encode_char(dest: &mut [Tryte], c: char) -> Result<usize> {
    let codepoint = c as u32;
    let (len, codepoint_offset) = match codepoint as usize {
        SINGLE_MIN..=SINGLE_MAX => Ok((1, SINGLE_OFFSET)),
        DOUBLE_MIN..=DOUBLE_MAX => Ok((2, DOUBLE_OFFSET)),
        TRIPLE_MIN..=TRIPLE_MAX => Ok((3, TRIPLE_OFFSET)),
        _ => Err(Error::InvalidCharacter(c)),
    }?;

    let src = {
        let mut tmp = [tryte::ZERO; WORD_LEN];
        let shifted_codepoint = shift_codepoint(codepoint, codepoint_offset)?;
        tmp.read_i64(i64::from(shifted_codepoint))?;
        tmp
    };

    match len {
        1 => {
            // 0xxxxx
            dest[0] = src[0];
        }

        2 => {
            let src0 = src[0];
            let src1 = src[1];

            // yyxxxx
            let (x0123, y01) = src0.split_trits_raw(4);

            // 000yyy
            let (y234, _) = src1.split_trits_raw(3);

            // 1Txxxx
            let double_start_trits = DOUBLE_START_PATTERN | x0123;
            dest[0] = Tryte::from_raw(double_start_trits);

            // Tyyyyy
            let continuation_trits = CONTINUATION_PATTERN | (y234 << (2 * TRIT_BIT_LEN)) | y01;
            dest[1] = Tryte::from_raw(continuation_trits);
        }

        3 => {
            let src0 = src[0];
            let src1 = src[1];
            let src2 = src[2];

            // yyxxxx
            let (x0123, y01) = src0.split_trits_raw(4);

            // zzzyyy
            let (y234, z012) = src1.split_trits_raw(3);

            // 0000zz
            let (z34, _) = src2.split_trits_raw(2);

            // 11xxxx
            let triple_start_trits = TRIPLE_START_PATTERN | x0123;
            dest[0] = Tryte::from_raw(triple_start_trits);

            // Tyyyyy
            let continuation1_trits = CONTINUATION_PATTERN | (y234 << (2 * TRIT_BIT_LEN)) | y01;
            dest[1] = Tryte::from_raw(continuation1_trits);

            // Tzzzzz
            let continuation2_trits = CONTINUATION_PATTERN | (z34 << (3 * TRIT_BIT_LEN)) | z012;
            dest[2] = Tryte::from_raw(continuation2_trits);
        }

        _ => unreachable!(),
    }

    Ok(len)
}

pub fn decode_char(src: &[Tryte]) -> Result<(char, usize)> {
    let mut dest = [tryte::ZERO; 3];

    let tryte0 = src[0];
    let trit5 = tryte0.get_trit(5);
    let trit4 = tryte0.get_trit(4);
    let (codepoint_offset, len) = match (trit5, trit4) {
        (trit::_0, _) => {
            // 0xxxxx
            dest[0] = src[0];
            Ok((SINGLE_OFFSET, 1))
        }

        (trit::_1, trit::_T) => {
            let tryte1 = src[1];
            if !is_continuation(tryte1) {
                return Err(invalid_encoding(src));
            }

            // 1Txxxx
            let x0123 = tryte0.into_raw() & DOUBLE_START_BITMASK;

            // Tyyyyy
            let y01234 = tryte1.into_raw() & CONTINUATION_BITMASK;

            // yyxxxx
            let dest0_trits = x0123 | (y01234 << (4 * TRIT_BIT_LEN) & tryte::BITMASK);
            dest[0] = Tryte::from_raw(dest0_trits);

            // 000yyy
            let dest1_trits = y01234 >> (2 * TRIT_BIT_LEN);
            dest[1] = Tryte::from_raw(dest1_trits);
            Ok((DOUBLE_OFFSET, 2))
        }

        (trit::_1, trit::_1) => {
            let tryte1 = src[1];
            if !is_continuation(tryte1) {
                return Err(invalid_encoding(src));
            }

            let tryte2 = src[2];
            if !is_continuation(tryte2) {
                return Err(invalid_encoding(src));
            }

            // 11xxxx
            let x0123 = tryte0.into_raw() & TRIPLE_START_BITMASK;

            // Tyyyyy
            let y01234 = tryte1.into_raw() & CONTINUATION_BITMASK;

            // Tzzzzz
            let z01234 = tryte2.into_raw() & CONTINUATION_BITMASK;

            // yyxxxx
            let dest0_trits = (y01234 << (4 * TRIT_BIT_LEN) & tryte::BITMASK) | x0123;
            dest[0] = Tryte::from_raw(dest0_trits);

            // zzzyyy
            let dest1_trits =
                (z01234 << (3 * TRIT_BIT_LEN) & tryte::BITMASK) | y01234 >> (2 * TRIT_BIT_LEN);
            dest[1] = Tryte::from_raw(dest1_trits);

            // 0000zz
            let dest2_trits = z01234 >> (3 * TRIT_BIT_LEN);
            dest[2] = Tryte::from_raw(dest2_trits);

            Ok((TRIPLE_OFFSET, 3))
        }

        _ => Err(invalid_encoding(src)),
    }?;

    #[allow(clippy::cast_possible_truncation)]
    let shifted_codepoint = dest.as_i64() as i32;
    let codepoint = unshift_codepoint(shifted_codepoint, codepoint_offset)?;
    let c = char::from_u32(codepoint).ok_or_else(|| invalid_encoding(src))?;
    Ok((c, len))
}

pub fn is_continuation(tryte: Tryte) -> bool {
    tryte.get_trit(5) == _T
}

fn invalid_encoding(src: &[Tryte]) -> Error {
    let mut bytes = Vec::new();
    src.write_trits(&mut bytes).unwrap();
    let s = String::from_utf8_lossy(&bytes).into_owned();
    Error::InvalidEncoding(s)
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
    use std::iter::repeat;

    use crate::{
        text::{decode_string, encode_str},
        tryte,
    };

    fn assert_roundtrip(s1: &str) {
        let mut trytes = repeat(tryte::ZERO).take(s1.len()).collect::<Vec<_>>();
        let len = encode_str(&mut trytes, s1).unwrap();
        trytes.truncate(len);

        let (s2, _) = decode_string(&trytes).unwrap();
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
