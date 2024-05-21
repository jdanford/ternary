use crate::{
    error::{assert_length, Result},
    trit::{Trit, _0},
    tryte::Tryte,
    Ternary,
};

pub fn compare<T: Ternary + ?Sized>(lhs: &T, rhs: &T) -> Trit {
    let mut cmp_trit = _0;

    for i in (0..lhs.trit_len()).rev() {
        let a = lhs.get_trit(i);
        let b = rhs.get_trit(i);
        cmp_trit = a.tcmp(b);

        if cmp_trit != _0 {
            break;
        }
    }

    cmp_trit
}

pub fn negate<T: Ternary + ?Sized>(dest: &mut T, src: &T) {
    map_trytes(dest, src, Tryte::neg);
}

pub fn and<T: Ternary + ?Sized>(dest: &mut T, lhs: &T, rhs: &T) {
    zip_trits(dest, lhs, rhs, Trit::and);
}

pub fn or<T: Ternary + ?Sized>(dest: &mut T, lhs: &T, rhs: &T) {
    zip_trits(dest, lhs, rhs, Trit::or);
}

pub fn tcmp<T: Ternary + ?Sized>(dest: &mut T, lhs: &T, rhs: &T) {
    zip_trits(dest, lhs, rhs, Trit::tcmp);
}

pub fn tmul<T: Ternary + ?Sized>(dest: &mut T, lhs: &T, rhs: &T) {
    zip_trits(dest, lhs, rhs, Trit::mul);
}

#[allow(dead_code)]
fn read_trits<T: Ternary + ?Sized>(dest: &mut T, trits: &[Trit]) -> Result<()> {
    assert_length(trits.len(), dest.trit_len())?;

    for (i, &trit) in trits.iter().enumerate() {
        dest.set_trit(i, trit);
    }

    Ok(())
}

pub fn add<T: Ternary + ?Sized>(dest: &mut T, lhs: &T, rhs: &T, carry: Trit) -> Trit {
    let mut carry = carry;

    for i in 0..lhs.trit_len() {
        let a = lhs.get_trit(i);
        let b = rhs.get_trit(i);
        let (c, new_carry) = a.add_with_carry(b, carry);
        carry = new_carry;
        dest.set_trit(i, c);
    }

    carry
}

pub fn multiply<T: Ternary + ?Sized>(dest: &mut T, lhs: &T, rhs: &T) {
    let len = rhs.trit_len();
    for i in 0..len {
        let sign = rhs.get_trit(i);
        let carry = add_mul(dest, lhs, sign, i);
        dest.set_trit(i + len, carry);
    }
}

fn add_mul<T: Ternary + ?Sized>(dest: &mut T, src: &T, sign: Trit, offset: usize) -> Trit {
    let mut carry = _0;

    for i in 0..src.trit_len() {
        let a = dest.get_trit(i + offset);
        let b = src.get_trit(i);
        let (c, new_carry) = a.add_with_carry(b * sign, carry);
        carry = new_carry;
        dest.set_trit(i + offset, c);
    }

    carry
}

#[allow(clippy::cast_possible_wrap, clippy::cast_sign_loss)]
pub fn shift<T: Ternary + ?Sized>(dest: &mut T, src: &T, offset: isize) -> Result<()> {
    let src_len = src.trit_len();
    let dest_len = dest.trit_len();
    assert_length(dest_len, src_len * 3)?;

    let dest_offset = offset + src_len as isize;
    for i in 0..src_len {
        let j = i as isize + dest_offset;
        if 0 <= j && j < dest_len as isize {
            let trit = src.get_trit(i);
            dest.set_trit(j as usize, trit);
        }
    }

    Ok(())
}

fn zip_trits<T, F>(dest: &mut T, lhs: &T, rhs: &T, f: F)
where
    T: Ternary + ?Sized,
    F: Fn(Trit, Trit) -> Trit,
{
    for i in 0..lhs.trit_len() {
        let a = lhs.get_trit(i);
        let b = rhs.get_trit(i);
        let c = f(a, b);
        dest.set_trit(i, c);
    }
}

fn map_trytes<T, F>(dest: &mut T, lhs: &T, f: F)
where
    T: Ternary + ?Sized,
    F: Fn(Tryte) -> Tryte,
{
    for i in 0..lhs.tryte_len() {
        let tryte = lhs.get_tryte(i);
        dest.set_tryte(i, f(tryte));
    }
}

#[cfg(test)]
mod tests {
    use std::io::Cursor;

    use crate::{
        ops::{and, compare, multiply, negate, or, shift, tcmp, tmul},
        test_constants::*,
        trit::{_0, _1, _T},
        Result, Ternary, Tryte,
    };

    #[test]
    fn ternary_as_i64() {
        assert_eq!(WORD_MIN, TRYTE4_MIN.as_i64());
        assert_eq!(-1, TRYTE4_NEG1.as_i64());
        assert_eq!(0, TRYTE4_0.as_i64());
        assert_eq!(1, TRYTE4_1.as_i64());
        assert_eq!(WORD_MAX, TRYTE4_MAX.as_i64());
    }

    #[test]
    fn ternary_read_i64() {
        assert_eq!(&TRYTE4_MIN, &tryte4_from_int(WORD_MIN).unwrap()[..]);
        assert_eq!(&TRYTE4_NEG1, &tryte4_from_int(-1).unwrap()[..]);
        assert_eq!(&TRYTE4_0, &tryte4_from_int(0).unwrap()[..]);
        assert_eq!(&TRYTE4_1, &tryte4_from_int(1).unwrap()[..]);
        assert_eq!(&TRYTE4_MAX, &tryte4_from_int(WORD_MAX).unwrap()[..]);

        assert!(tryte4_from_int(i64::min_value()).is_err());
        assert!(tryte4_from_int(i64::max_value()).is_err());
    }

    fn tryte4_from_int(n: i64) -> Result<Vec<Tryte>> {
        try_with_cloned_trytes(&TRYTE4_0, |trytes| trytes.read_i64(n))
    }

    #[test]
    fn ternary_read_bytes() {
        assert_eq!(&TRYTE4_MIN, &tryte4_from_bytes(&BYTES_MIN).unwrap()[..]);
        assert_eq!(&TRYTE4_NEG1, &tryte4_from_bytes(&BYTES_NEG1).unwrap()[..]);
        assert_eq!(&TRYTE4_0, &tryte4_from_bytes(&BYTES_0).unwrap()[..]);
        assert_eq!(&TRYTE4_1, &tryte4_from_bytes(&BYTES_1).unwrap()[..]);
        assert_eq!(&TRYTE4_MAX, &tryte4_from_bytes(&BYTES_MAX).unwrap()[..]);
    }

    fn tryte4_from_bytes(bytes: &[u8]) -> Result<Vec<Tryte>> {
        try_with_cloned_trytes(&TRYTE4_0, |trytes| {
            trytes.read_bytes(&mut Cursor::new(bytes))
        })
    }

    #[test]
    fn ternary_write_bytes() {
        assert_eq!(&BYTES_MIN, &get_bytes(&TRYTE4_MIN[..])[..]);
        assert_eq!(&BYTES_NEG1, &get_bytes(&TRYTE4_NEG1[..])[..]);
        assert_eq!(&BYTES_0, &get_bytes(&TRYTE4_0[..])[..]);
        assert_eq!(&BYTES_1, &get_bytes(&TRYTE4_1[..])[..]);
        assert_eq!(&BYTES_MAX, &get_bytes(&TRYTE4_MAX[..])[..]);
    }

    fn get_bytes(trytes: &[Tryte]) -> Vec<u8> {
        let mut bytes = vec![];
        trytes.write_bytes(&mut bytes).unwrap();
        bytes
    }

    #[test]
    fn ternary_read_hytes() {
        assert_eq!(&TRYTE4_MIN, &tryte4_from_hyte_str("mmmmmmmm").unwrap()[..]);
        assert_eq!(&TRYTE4_NEG1, &tryte4_from_hyte_str("0000000a").unwrap()[..]);
        assert_eq!(&TRYTE4_0, &tryte4_from_hyte_str("00000000").unwrap()[..]);
        assert_eq!(&TRYTE4_1, &tryte4_from_hyte_str("0000000A").unwrap()[..]);
        assert_eq!(&TRYTE4_MAX, &tryte4_from_hyte_str("MMMMMMMM").unwrap()[..]);
    }

    fn tryte4_from_hyte_str(s: &str) -> Result<Vec<Tryte>> {
        try_with_cloned_trytes(&TRYTE4_0, |trytes| trytes.read_hytes(s))
    }

    #[test]
    fn ternary_display_hytes() {
        assert_eq!("mmmmmmmm", get_hyte_str(&TRYTE4_MIN[..]));
        assert_eq!("0000000a", get_hyte_str(&TRYTE4_NEG1[..]));
        assert_eq!("00000000", get_hyte_str(&TRYTE4_0[..]));
        assert_eq!("0000000A", get_hyte_str(&TRYTE4_1[..]));
        assert_eq!("MMMMMMMM", get_hyte_str(&TRYTE4_MAX[..]));
    }

    fn get_hyte_str(trytes: &[Tryte]) -> String {
        let mut bytes = Vec::new();
        trytes.write_hytes(&mut bytes).unwrap();
        String::from_utf8_lossy(&bytes).into_owned()
    }

    #[test]
    fn ternary_read_trits() {
        assert_eq!(
            &TRYTE4_MIN,
            &tryte4_from_trit_str("TTTTTTTTTTTTTTTTTTTTTTTT").unwrap()[..]
        );
        assert_eq!(
            &TRYTE4_NEG1,
            &tryte4_from_trit_str("00000000000000000000000T").unwrap()[..]
        );
        assert_eq!(
            &TRYTE4_0,
            &tryte4_from_trit_str("000000000000000000000000").unwrap()[..]
        );
        assert_eq!(
            &TRYTE4_1,
            &tryte4_from_trit_str("000000000000000000000001").unwrap()[..]
        );
        assert_eq!(
            &TRYTE4_MAX,
            &tryte4_from_trit_str("111111111111111111111111").unwrap()[..]
        );
    }

    fn tryte4_from_trit_str(s: &str) -> Result<Vec<Tryte>> {
        try_with_cloned_trytes(&TRYTE4_0, |trytes| trytes.read_trits(s))
    }

    #[test]
    fn ternary_display_trits() {
        assert_eq!("TTTTTTTTTTTTTTTTTTTTTTTT", get_trit_str(&TRYTE4_MIN[..]));
        assert_eq!("00000000000000000000000T", get_trit_str(&TRYTE4_NEG1[..]));
        assert_eq!("000000000000000000000000", get_trit_str(&TRYTE4_0[..]));
        assert_eq!("000000000000000000000001", get_trit_str(&TRYTE4_1[..]));
        assert_eq!("111111111111111111111111", get_trit_str(&TRYTE4_MAX[..]));
    }

    fn get_trit_str(trytes: &[Tryte]) -> String {
        let mut bytes = Vec::new();
        trytes.write_trits(&mut bytes).unwrap();
        String::from_utf8_lossy(&bytes).into_owned()
    }

    #[test]
    fn ternary_cmp() {
        assert_eq!(_0, compare(&TRYTE4_0[..], &TRYTE4_0[..]));
        assert_eq!(_T, compare(&TRYTE4_0[..], &TRYTE4_MAX[..]));
        assert_eq!(_1, compare(&TRYTE4_0[..], &TRYTE4_MIN[..]));
        assert_eq!(_1, compare(&TRYTE4_MAX[..], &TRYTE4_0[..]));
        assert_eq!(_1, compare(&TRYTE4_MAX[..], &TRYTE4_MIN[..]));
        assert_eq!(_0, compare(&TRYTE4_MAX[..], &TRYTE4_MAX[..]));
        assert_eq!(_T, compare(&TRYTE4_MIN[..], &TRYTE4_0[..]));
        assert_eq!(_T, compare(&TRYTE4_MIN[..], &TRYTE4_MAX[..]));
        assert_eq!(_0, compare(&TRYTE4_MIN[..], &TRYTE4_MIN[..]));
    }

    #[test]
    fn ternary_negate() {
        assert_eq!(&TRYTE4_MIN, &tryte4_negate(&TRYTE4_MAX)[..]);
        assert_eq!(&TRYTE4_NEG1, &tryte4_negate(&TRYTE4_1)[..]);
        assert_eq!(&TRYTE4_0, &tryte4_negate(&TRYTE4_0)[..]);
        assert_eq!(&TRYTE4_1, &tryte4_negate(&TRYTE4_NEG1)[..]);
        assert_eq!(&TRYTE4_MAX, &tryte4_negate(&TRYTE4_MIN)[..]);
    }

    fn tryte4_negate(trytes: &[Tryte]) -> Vec<Tryte> {
        with_cloned_trytes2(&TRYTE4_0, trytes, negate)
    }

    #[test]
    fn ternary_and() {
        assert_eq!(&TRYTE4_0, &tryte4_and(&TRYTE4_0, &TRYTE4_0)[..]);
        assert_eq!(&TRYTE4_0, &tryte4_and(&TRYTE4_0, &TRYTE4_MAX)[..]);
        assert_eq!(&TRYTE4_MIN, &tryte4_and(&TRYTE4_0, &TRYTE4_MIN)[..]);
        assert_eq!(&TRYTE4_0, &tryte4_and(&TRYTE4_MAX, &TRYTE4_0)[..]);
        assert_eq!(&TRYTE4_MAX, &tryte4_and(&TRYTE4_MAX, &TRYTE4_MAX)[..]);
        assert_eq!(&TRYTE4_MIN, &tryte4_and(&TRYTE4_MAX, &TRYTE4_MIN)[..]);
        assert_eq!(&TRYTE4_MIN, &tryte4_and(&TRYTE4_MIN, &TRYTE4_0)[..]);
        assert_eq!(&TRYTE4_MIN, &tryte4_and(&TRYTE4_MIN, &TRYTE4_MAX)[..]);
        assert_eq!(&TRYTE4_MIN, &tryte4_and(&TRYTE4_MIN, &TRYTE4_MIN)[..]);
    }

    fn tryte4_and(trytes1: &[Tryte], trytes2: &[Tryte]) -> Vec<Tryte> {
        with_cloned_trytes3(&TRYTE4_0, trytes1, trytes2, and)
    }

    #[test]
    fn ternary_or() {
        assert_eq!(&TRYTE4_0, &tryte4_or(&TRYTE4_0, &TRYTE4_0)[..]);
        assert_eq!(&TRYTE4_MAX, &tryte4_or(&TRYTE4_0, &TRYTE4_MAX)[..]);
        assert_eq!(&TRYTE4_0, &tryte4_or(&TRYTE4_0, &TRYTE4_MIN)[..]);
        assert_eq!(&TRYTE4_MAX, &tryte4_or(&TRYTE4_MAX, &TRYTE4_0)[..]);
        assert_eq!(&TRYTE4_MAX, &tryte4_or(&TRYTE4_MAX, &TRYTE4_MAX)[..]);
        assert_eq!(&TRYTE4_MAX, &tryte4_or(&TRYTE4_MAX, &TRYTE4_MIN)[..]);
        assert_eq!(&TRYTE4_0, &tryte4_or(&TRYTE4_MIN, &TRYTE4_0)[..]);
        assert_eq!(&TRYTE4_MAX, &tryte4_or(&TRYTE4_MIN, &TRYTE4_MAX)[..]);
        assert_eq!(&TRYTE4_MIN, &tryte4_or(&TRYTE4_MIN, &TRYTE4_MIN)[..]);
    }

    fn tryte4_or(trytes1: &[Tryte], trytes2: &[Tryte]) -> Vec<Tryte> {
        with_cloned_trytes3(&TRYTE4_0, trytes1, trytes2, or)
    }

    #[test]
    fn ternary_tcmp() {
        assert_eq!(&TRYTE4_MIN, &tryte4_tcmp(&TRYTE4_MIN, &TRYTE4_0)[..]);
        assert_eq!(&TRYTE4_MAX, &tryte4_tcmp(&TRYTE4_MAX, &TRYTE4_0)[..]);
        assert_eq!(&TRYTE4_NEG1, &tryte4_tcmp(&TRYTE4_NEG1, &TRYTE4_0)[..]);
        assert_eq!(&TRYTE4_0, &tryte4_tcmp(&TRYTE4_0, &TRYTE4_0)[..]);
        assert_eq!(&TRYTE4_1, &tryte4_tcmp(&TRYTE4_1, &TRYTE4_0)[..]);

        assert_eq!(&TRYTE4_MAX, &tryte4_tcmp(&TRYTE4_0, &TRYTE4_MIN)[..]);
        assert_eq!(&TRYTE4_MIN, &tryte4_tcmp(&TRYTE4_0, &TRYTE4_MAX)[..]);
        assert_eq!(&TRYTE4_1, &tryte4_tcmp(&TRYTE4_0, &TRYTE4_NEG1)[..]);
        assert_eq!(&TRYTE4_NEG1, &tryte4_tcmp(&TRYTE4_0, &TRYTE4_1)[..]);

        assert_eq!(&TRYTE4_0, &tryte4_tcmp(&TRYTE4_MIN, &TRYTE4_MIN)[..]);
        assert_eq!(&TRYTE4_0, &tryte4_tcmp(&TRYTE4_MAX, &TRYTE4_MAX)[..]);
        assert_eq!(&TRYTE4_0, &tryte4_tcmp(&TRYTE4_NEG1, &TRYTE4_NEG1)[..]);
        assert_eq!(&TRYTE4_0, &tryte4_tcmp(&TRYTE4_1, &TRYTE4_1)[..]);
    }

    fn tryte4_tcmp(trytes1: &[Tryte], trytes2: &[Tryte]) -> Vec<Tryte> {
        with_cloned_trytes3(&TRYTE4_0, trytes1, trytes2, tcmp)
    }

    #[test]
    fn ternary_tmul() {
        assert_eq!(&TRYTE4_0, &tryte4_tmul(&TRYTE4_MIN, &TRYTE4_0)[..]);
        assert_eq!(&TRYTE4_0, &tryte4_tmul(&TRYTE4_MAX, &TRYTE4_0)[..]);
        assert_eq!(&TRYTE4_0, &tryte4_tmul(&TRYTE4_NEG1, &TRYTE4_0)[..]);
        assert_eq!(&TRYTE4_0, &tryte4_tmul(&TRYTE4_0, &TRYTE4_0)[..]);
        assert_eq!(&TRYTE4_0, &tryte4_tmul(&TRYTE4_1, &TRYTE4_0)[..]);

        assert_eq!(&TRYTE4_MIN, &tryte4_tmul(&TRYTE4_MIN, &TRYTE4_MAX)[..]);
        assert_eq!(&TRYTE4_MAX, &tryte4_tmul(&TRYTE4_MAX, &TRYTE4_MAX)[..]);
        assert_eq!(&TRYTE4_NEG1, &tryte4_tmul(&TRYTE4_NEG1, &TRYTE4_MAX)[..]);
        assert_eq!(&TRYTE4_0, &tryte4_tmul(&TRYTE4_0, &TRYTE4_MAX)[..]);
        assert_eq!(&TRYTE4_1, &tryte4_tmul(&TRYTE4_1, &TRYTE4_MAX)[..]);

        assert_eq!(&TRYTE4_MAX, &tryte4_tmul(&TRYTE4_MIN, &TRYTE4_MIN)[..]);
        assert_eq!(&TRYTE4_MIN, &tryte4_tmul(&TRYTE4_MAX, &TRYTE4_MIN)[..]);
        assert_eq!(&TRYTE4_1, &tryte4_tmul(&TRYTE4_NEG1, &TRYTE4_MIN)[..]);
        assert_eq!(&TRYTE4_0, &tryte4_tmul(&TRYTE4_0, &TRYTE4_MIN)[..]);
        assert_eq!(&TRYTE4_NEG1, &tryte4_tmul(&TRYTE4_1, &TRYTE4_MIN)[..]);
    }

    fn tryte4_tmul(trytes1: &[Tryte], trytes2: &[Tryte]) -> Vec<Tryte> {
        with_cloned_trytes3(&TRYTE4_0, trytes1, trytes2, tmul)
    }

    #[test]
    fn ternary_multiply() {
        assert_eq!(&TRYTE4_0, &tryte4_mul(&TRYTE4_NEG4096, &TRYTE4_0)[..]);
        assert_eq!(&TRYTE4_0, &tryte4_mul(&TRYTE4_NEG1, &TRYTE4_0)[..]);
        assert_eq!(&TRYTE4_0, &tryte4_mul(&TRYTE4_0, &TRYTE4_0)[..]);
        assert_eq!(&TRYTE4_0, &tryte4_mul(&TRYTE4_1, &TRYTE4_0)[..]);
        assert_eq!(&TRYTE4_0, &tryte4_mul(&TRYTE4_4096, &TRYTE4_0)[..]);

        assert_eq!(&TRYTE4_0, &tryte4_mul(&TRYTE4_0, &TRYTE4_NEG4096)[..]);
        assert_eq!(&TRYTE4_0, &tryte4_mul(&TRYTE4_0, &TRYTE4_NEG1)[..]);
        assert_eq!(&TRYTE4_0, &tryte4_mul(&TRYTE4_0, &TRYTE4_1)[..]);
        assert_eq!(&TRYTE4_0, &tryte4_mul(&TRYTE4_0, &TRYTE4_4096)[..]);

        assert_eq!(&TRYTE4_NEG4096, &tryte4_mul(&TRYTE4_NEG4096, &TRYTE4_1)[..]);
        assert_eq!(&TRYTE4_NEG1, &tryte4_mul(&TRYTE4_NEG1, &TRYTE4_1)[..]);
        assert_eq!(&TRYTE4_1, &tryte4_mul(&TRYTE4_1, &TRYTE4_1)[..]);
        assert_eq!(&TRYTE4_4096, &tryte4_mul(&TRYTE4_4096, &TRYTE4_1)[..]);

        assert_eq!(&TRYTE4_NEG4096, &tryte4_mul(&TRYTE4_1, &TRYTE4_NEG4096)[..]);
        assert_eq!(&TRYTE4_NEG1, &tryte4_mul(&TRYTE4_1, &TRYTE4_NEG1)[..]);
        assert_eq!(&TRYTE4_4096, &tryte4_mul(&TRYTE4_1, &TRYTE4_4096)[..]);

        assert_eq!(&TRYTE4_4096, &tryte4_mul(&TRYTE4_NEG4096, &TRYTE4_NEG1)[..]);
        assert_eq!(&TRYTE4_1, &tryte4_mul(&TRYTE4_NEG1, &TRYTE4_NEG1)[..]);
        assert_eq!(&TRYTE4_NEG4096, &tryte4_mul(&TRYTE4_4096, &TRYTE4_NEG1)[..]);

        assert_eq!(&TRYTE4_4096, &tryte4_mul(&TRYTE4_NEG1, &TRYTE4_NEG4096)[..]);
        assert_eq!(&TRYTE4_NEG4096, &tryte4_mul(&TRYTE4_NEG1, &TRYTE4_4096)[..]);

        assert_eq!(&TRYTE4_64, &tryte4_mul(&TRYTE4_8, &TRYTE4_8)[..]);
        assert_eq!(&TRYTE4_64, &tryte4_mul(&TRYTE4_NEG8, &TRYTE4_NEG8)[..]);
        assert_eq!(&TRYTE4_NEG64, &tryte4_mul(&TRYTE4_8, &TRYTE4_NEG8)[..]);
        assert_eq!(&TRYTE4_NEG64, &tryte4_mul(&TRYTE4_NEG8, &TRYTE4_8)[..]);

        assert_eq!(&TRYTE4_81, &tryte4_mul(&TRYTE4_9, &TRYTE4_9)[..]);
        assert_eq!(&TRYTE4_81, &tryte4_mul(&TRYTE4_NEG9, &TRYTE4_NEG9)[..]);
        assert_eq!(&TRYTE4_NEG81, &tryte4_mul(&TRYTE4_9, &TRYTE4_NEG9)[..]);
        assert_eq!(&TRYTE4_NEG81, &tryte4_mul(&TRYTE4_NEG9, &TRYTE4_9)[..]);

        assert_eq!(&TRYTE4_4096, &tryte4_mul(&TRYTE4_8, &TRYTE4_512)[..]);
        assert_eq!(&TRYTE4_4096, &tryte4_mul(&TRYTE4_NEG8, &TRYTE4_NEG512)[..]);
        assert_eq!(&TRYTE4_NEG4096, &tryte4_mul(&TRYTE4_8, &TRYTE4_NEG512)[..]);
        assert_eq!(&TRYTE4_NEG4096, &tryte4_mul(&TRYTE4_NEG8, &TRYTE4_512)[..]);

        assert_eq!(&TRYTE4_4096, &tryte4_mul(&TRYTE4_512, &TRYTE4_8)[..]);
        assert_eq!(&TRYTE4_4096, &tryte4_mul(&TRYTE4_NEG512, &TRYTE4_NEG8)[..]);
        assert_eq!(&TRYTE4_NEG4096, &tryte4_mul(&TRYTE4_512, &TRYTE4_NEG8)[..]);
        assert_eq!(&TRYTE4_NEG4096, &tryte4_mul(&TRYTE4_NEG512, &TRYTE4_8)[..]);

        assert_eq!(&TRYTE4_4096, &tryte4_mul(&TRYTE4_16, &TRYTE4_256)[..]);
        assert_eq!(&TRYTE4_4096, &tryte4_mul(&TRYTE4_NEG16, &TRYTE4_NEG256)[..]);
        assert_eq!(&TRYTE4_NEG4096, &tryte4_mul(&TRYTE4_16, &TRYTE4_NEG256)[..]);
        assert_eq!(&TRYTE4_NEG4096, &tryte4_mul(&TRYTE4_NEG16, &TRYTE4_256)[..]);

        assert_eq!(&TRYTE4_4096, &tryte4_mul(&TRYTE4_256, &TRYTE4_16)[..]);
        assert_eq!(&TRYTE4_4096, &tryte4_mul(&TRYTE4_NEG256, &TRYTE4_NEG16)[..]);
        assert_eq!(&TRYTE4_NEG4096, &tryte4_mul(&TRYTE4_256, &TRYTE4_NEG16)[..]);
        assert_eq!(&TRYTE4_NEG4096, &tryte4_mul(&TRYTE4_NEG256, &TRYTE4_16)[..]);

        assert_eq!(&TRYTE4_4096, &tryte4_mul(&TRYTE4_64, &TRYTE4_64)[..]);
        assert_eq!(&TRYTE4_4096, &tryte4_mul(&TRYTE4_NEG64, &TRYTE4_NEG64)[..]);
        assert_eq!(&TRYTE4_NEG4096, &tryte4_mul(&TRYTE4_64, &TRYTE4_NEG64)[..]);
        assert_eq!(&TRYTE4_NEG4096, &tryte4_mul(&TRYTE4_NEG64, &TRYTE4_64)[..]);
    }

    fn tryte4_mul(trytes1: &[Tryte], trytes2: &[Tryte]) -> Vec<Tryte> {
        with_cloned_trytes3(&TRYTE8_0, trytes1, trytes2, multiply)[..4].to_vec()
    }

    #[test]
    #[allow(clippy::too_many_lines)]
    // TODO: use macro
    fn ternary_shift() {
        assert_eq!(
            tryte12_from_trit_str(
                "00000000000000000000000000000000000000000000000001T000110T001100T011000T",
            )
            .unwrap(),
            tryte4_shift("1T000110T001100T011000T1", -25).unwrap()
        );
        assert_eq!(
            tryte12_from_trit_str(
                "0000000000000000000000000000000000000000000000001T000110T001100T011000T1",
            )
            .unwrap(),
            tryte4_shift("1T000110T001100T011000T1", -24).unwrap()
        );
        assert_eq!(
            tryte12_from_trit_str(
                "000000000000000000000000000000000000000000000001T000110T001100T011000T10",
            )
            .unwrap(),
            tryte4_shift("1T000110T001100T011000T1", -23).unwrap()
        );
        assert_eq!(
            tryte12_from_trit_str(
                "00000000000000000000000000000000000000000000001T000110T001100T011000T100",
            )
            .unwrap(),
            tryte4_shift("1T000110T001100T011000T1", -22).unwrap()
        );
        assert_eq!(
            tryte12_from_trit_str(
                "0000000000000000000000000000000000000000000001T000110T001100T011000T1000",
            )
            .unwrap(),
            tryte4_shift("1T000110T001100T011000T1", -21).unwrap()
        );
        assert_eq!(
            tryte12_from_trit_str(
                "000000000000000000000000000000000000000000001T000110T001100T011000T10000",
            )
            .unwrap(),
            tryte4_shift("1T000110T001100T011000T1", -20).unwrap()
        );
        assert_eq!(
            tryte12_from_trit_str(
                "00000000000000000000000000000000000000000001T000110T001100T011000T100000",
            )
            .unwrap(),
            tryte4_shift("1T000110T001100T011000T1", -19).unwrap()
        );
        assert_eq!(
            tryte12_from_trit_str(
                "0000000000000000000000000000000000000000001T000110T001100T011000T1000000",
            )
            .unwrap(),
            tryte4_shift("1T000110T001100T011000T1", -18).unwrap()
        );
        assert_eq!(
            tryte12_from_trit_str(
                "000000000000000000000000000000000000000001T000110T001100T011000T10000000",
            )
            .unwrap(),
            tryte4_shift("1T000110T001100T011000T1", -17).unwrap()
        );
        assert_eq!(
            tryte12_from_trit_str(
                "00000000000000000000000000000000000000001T000110T001100T011000T100000000",
            )
            .unwrap(),
            tryte4_shift("1T000110T001100T011000T1", -16).unwrap()
        );
        assert_eq!(
            tryte12_from_trit_str(
                "0000000000000000000000000000000000000001T000110T001100T011000T1000000000",
            )
            .unwrap(),
            tryte4_shift("1T000110T001100T011000T1", -15).unwrap()
        );
        assert_eq!(
            tryte12_from_trit_str(
                "000000000000000000000000000000000000001T000110T001100T011000T10000000000",
            )
            .unwrap(),
            tryte4_shift("1T000110T001100T011000T1", -14).unwrap()
        );
        assert_eq!(
            tryte12_from_trit_str(
                "00000000000000000000000000000000000001T000110T001100T011000T100000000000",
            )
            .unwrap(),
            tryte4_shift("1T000110T001100T011000T1", -13).unwrap()
        );
        assert_eq!(
            tryte12_from_trit_str(
                "0000000000000000000000000000000000001T000110T001100T011000T1000000000000",
            )
            .unwrap(),
            tryte4_shift("1T000110T001100T011000T1", -12).unwrap()
        );
        assert_eq!(
            tryte12_from_trit_str(
                "000000000000000000000000000000000001T000110T001100T011000T10000000000000",
            )
            .unwrap(),
            tryte4_shift("1T000110T001100T011000T1", -11).unwrap()
        );

        assert_eq!(
            tryte12_from_trit_str(
                "00000000000000000000000000000000001T000110T001100T011000T100000000000000",
            )
            .unwrap(),
            tryte4_shift("1T000110T001100T011000T1", -10).unwrap()
        );
        assert_eq!(
            tryte12_from_trit_str(
                "0000000000000000000000000000000001T000110T001100T011000T1000000000000000",
            )
            .unwrap(),
            tryte4_shift("1T000110T001100T011000T1", -9).unwrap()
        );
        assert_eq!(
            tryte12_from_trit_str(
                "000000000000000000000000000000001T000110T001100T011000T10000000000000000",
            )
            .unwrap(),
            tryte4_shift("1T000110T001100T011000T1", -8).unwrap()
        );
        assert_eq!(
            tryte12_from_trit_str(
                "00000000000000000000000000000001T000110T001100T011000T100000000000000000",
            )
            .unwrap(),
            tryte4_shift("1T000110T001100T011000T1", -7).unwrap()
        );
        assert_eq!(
            tryte12_from_trit_str(
                "0000000000000000000000000000001T000110T001100T011000T1000000000000000000",
            )
            .unwrap(),
            tryte4_shift("1T000110T001100T011000T1", -6).unwrap()
        );
        assert_eq!(
            tryte12_from_trit_str(
                "000000000000000000000000000001T000110T001100T011000T10000000000000000000",
            )
            .unwrap(),
            tryte4_shift("1T000110T001100T011000T1", -5).unwrap()
        );
        assert_eq!(
            tryte12_from_trit_str(
                "00000000000000000000000000001T000110T001100T011000T100000000000000000000",
            )
            .unwrap(),
            tryte4_shift("1T000110T001100T011000T1", -4).unwrap()
        );
        assert_eq!(
            tryte12_from_trit_str(
                "0000000000000000000000000001T000110T001100T011000T1000000000000000000000",
            )
            .unwrap(),
            tryte4_shift("1T000110T001100T011000T1", -3).unwrap()
        );
        assert_eq!(
            tryte12_from_trit_str(
                "000000000000000000000000001T000110T001100T011000T10000000000000000000000",
            )
            .unwrap(),
            tryte4_shift("1T000110T001100T011000T1", -2).unwrap()
        );
        assert_eq!(
            tryte12_from_trit_str(
                "00000000000000000000000001T000110T001100T011000T100000000000000000000000",
            )
            .unwrap(),
            tryte4_shift("1T000110T001100T011000T1", -1).unwrap()
        );
        assert_eq!(
            tryte12_from_trit_str(
                "0000000000000000000000001T000110T001100T011000T1000000000000000000000000",
            )
            .unwrap(),
            tryte4_shift("1T000110T001100T011000T1", 0).unwrap()
        );
        assert_eq!(
            tryte12_from_trit_str(
                "000000000000000000000001T000110T001100T011000T10000000000000000000000000",
            )
            .unwrap(),
            tryte4_shift("1T000110T001100T011000T1", 1).unwrap()
        );
        assert_eq!(
            tryte12_from_trit_str(
                "00000000000000000000001T000110T001100T011000T100000000000000000000000000",
            )
            .unwrap(),
            tryte4_shift("1T000110T001100T011000T1", 2).unwrap()
        );
        assert_eq!(
            tryte12_from_trit_str(
                "0000000000000000000001T000110T001100T011000T1000000000000000000000000000",
            )
            .unwrap(),
            tryte4_shift("1T000110T001100T011000T1", 3).unwrap()
        );
        assert_eq!(
            tryte12_from_trit_str(
                "000000000000000000001T000110T001100T011000T10000000000000000000000000000",
            )
            .unwrap(),
            tryte4_shift("1T000110T001100T011000T1", 4).unwrap()
        );
        assert_eq!(
            tryte12_from_trit_str(
                "00000000000000000001T000110T001100T011000T100000000000000000000000000000",
            )
            .unwrap(),
            tryte4_shift("1T000110T001100T011000T1", 5).unwrap()
        );
        assert_eq!(
            tryte12_from_trit_str(
                "0000000000000000001T000110T001100T011000T1000000000000000000000000000000",
            )
            .unwrap(),
            tryte4_shift("1T000110T001100T011000T1", 6).unwrap()
        );
        assert_eq!(
            tryte12_from_trit_str(
                "000000000000000001T000110T001100T011000T10000000000000000000000000000000",
            )
            .unwrap(),
            tryte4_shift("1T000110T001100T011000T1", 7).unwrap()
        );
        assert_eq!(
            tryte12_from_trit_str(
                "00000000000000001T000110T001100T011000T100000000000000000000000000000000",
            )
            .unwrap(),
            tryte4_shift("1T000110T001100T011000T1", 8).unwrap()
        );
        assert_eq!(
            tryte12_from_trit_str(
                "0000000000000001T000110T001100T011000T1000000000000000000000000000000000",
            )
            .unwrap(),
            tryte4_shift("1T000110T001100T011000T1", 9).unwrap()
        );
        assert_eq!(
            tryte12_from_trit_str(
                "000000000000001T000110T001100T011000T10000000000000000000000000000000000",
            )
            .unwrap(),
            tryte4_shift("1T000110T001100T011000T1", 10).unwrap()
        );
        assert_eq!(
            tryte12_from_trit_str(
                "00000000000001T000110T001100T011000T100000000000000000000000000000000000",
            )
            .unwrap(),
            tryte4_shift("1T000110T001100T011000T1", 11).unwrap()
        );
        assert_eq!(
            tryte12_from_trit_str(
                "0000000000001T000110T001100T011000T1000000000000000000000000000000000000",
            )
            .unwrap(),
            tryte4_shift("1T000110T001100T011000T1", 12).unwrap()
        );
        assert_eq!(
            tryte12_from_trit_str(
                "000000000001T000110T001100T011000T10000000000000000000000000000000000000",
            )
            .unwrap(),
            tryte4_shift("1T000110T001100T011000T1", 13).unwrap()
        );
        assert_eq!(
            tryte12_from_trit_str(
                "00000000001T000110T001100T011000T100000000000000000000000000000000000000",
            )
            .unwrap(),
            tryte4_shift("1T000110T001100T011000T1", 14).unwrap()
        );
        assert_eq!(
            tryte12_from_trit_str(
                "0000000001T000110T001100T011000T1000000000000000000000000000000000000000",
            )
            .unwrap(),
            tryte4_shift("1T000110T001100T011000T1", 15).unwrap()
        );
        assert_eq!(
            tryte12_from_trit_str(
                "000000001T000110T001100T011000T10000000000000000000000000000000000000000",
            )
            .unwrap(),
            tryte4_shift("1T000110T001100T011000T1", 16).unwrap()
        );
        assert_eq!(
            tryte12_from_trit_str(
                "00000001T000110T001100T011000T100000000000000000000000000000000000000000",
            )
            .unwrap(),
            tryte4_shift("1T000110T001100T011000T1", 17).unwrap()
        );
        assert_eq!(
            tryte12_from_trit_str(
                "0000001T000110T001100T011000T1000000000000000000000000000000000000000000",
            )
            .unwrap(),
            tryte4_shift("1T000110T001100T011000T1", 18).unwrap()
        );
        assert_eq!(
            tryte12_from_trit_str(
                "000001T000110T001100T011000T10000000000000000000000000000000000000000000",
            )
            .unwrap(),
            tryte4_shift("1T000110T001100T011000T1", 19).unwrap()
        );
        assert_eq!(
            tryte12_from_trit_str(
                "00001T000110T001100T011000T100000000000000000000000000000000000000000000",
            )
            .unwrap(),
            tryte4_shift("1T000110T001100T011000T1", 20).unwrap()
        );
        assert_eq!(
            tryte12_from_trit_str(
                "0001T000110T001100T011000T1000000000000000000000000000000000000000000000",
            )
            .unwrap(),
            tryte4_shift("1T000110T001100T011000T1", 21).unwrap()
        );
        assert_eq!(
            tryte12_from_trit_str(
                "001T000110T001100T011000T10000000000000000000000000000000000000000000000",
            )
            .unwrap(),
            tryte4_shift("1T000110T001100T011000T1", 22).unwrap()
        );
        assert_eq!(
            tryte12_from_trit_str(
                "01T000110T001100T011000T100000000000000000000000000000000000000000000000",
            )
            .unwrap(),
            tryte4_shift("1T000110T001100T011000T1", 23).unwrap()
        );
        assert_eq!(
            tryte12_from_trit_str(
                "1T000110T001100T011000T1000000000000000000000000000000000000000000000000",
            )
            .unwrap(),
            tryte4_shift("1T000110T001100T011000T1", 24).unwrap()
        );
        assert_eq!(
            tryte12_from_trit_str(
                "T000110T001100T011000T10000000000000000000000000000000000000000000000000",
            )
            .unwrap(),
            tryte4_shift("1T000110T001100T011000T1", 25).unwrap()
        );
    }

    fn tryte4_shift(trit_str: &str, offset: isize) -> Result<Vec<Tryte>> {
        let trytes = tryte4_from_trit_str(trit_str)?;
        try_with_cloned_trytes2(&TRYTE12_0, &trytes[..], |dest, src| {
            shift(dest, src, offset)?;
            Ok(())
        })
    }

    fn tryte12_from_trit_str(s: &str) -> Result<Vec<Tryte>> {
        try_with_cloned_trytes(&TRYTE12_0, |trytes| trytes.read_trits(s))
    }

    fn clone_slice<T: Clone>(slice: &[T]) -> Vec<T> {
        let mut vec = Vec::new();
        vec.extend_from_slice(slice);
        vec
    }

    fn with_cloned_trytes2<F>(trytes1: &[Tryte], trytes2: &[Tryte], f: F) -> Vec<Tryte>
    where
        F: Fn(&mut [Tryte], &[Tryte]),
    {
        let mut trytes1 = clone_slice(trytes1);
        f(&mut trytes1[..], trytes2);
        trytes1
    }

    fn with_cloned_trytes3<F>(
        trytes1: &[Tryte],
        trytes2: &[Tryte],
        trytes3: &[Tryte],
        f: F,
    ) -> Vec<Tryte>
    where
        F: Fn(&mut [Tryte], &[Tryte], &[Tryte]),
    {
        let mut trytes1 = clone_slice(trytes1);
        f(&mut trytes1[..], trytes2, trytes3);
        trytes1
    }

    fn try_with_cloned_trytes<F>(trytes: &[Tryte], f: F) -> Result<Vec<Tryte>>
    where
        F: Fn(&mut [Tryte]) -> Result<()>,
    {
        let mut trytes = clone_slice(trytes);
        f(&mut trytes[..])?;
        Ok(trytes)
    }

    fn try_with_cloned_trytes2<F>(trytes1: &[Tryte], trytes2: &[Tryte], f: F) -> Result<Vec<Tryte>>
    where
        F: Fn(&mut [Tryte], &[Tryte]) -> Result<()>,
    {
        let mut trytes1 = clone_slice(trytes1);
        f(&mut trytes1[..], trytes2)?;
        Ok(trytes1)
    }
}
