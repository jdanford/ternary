use std::{
    cmp::Ordering,
    fmt::{self, Display},
    io, ops,
    str::FromStr,
};

use num_bigint::{BigInt, ToBigInt};
use num_traits::{CheckedAdd, CheckedMul, Signed};

use crate::{
    error::{Error, Result, assert_length_le},
    hyte::Hyte,
    trit::{_0, _1, _T, Trit},
    tryte::{self, Tryte},
};

#[allow(clippy::module_name_repetitions)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct TInt<const N: usize> {
    pub(crate) trytes: [Tryte; N],
}

pub type T6 = TInt<1>;
pub type T12 = TInt<2>;
pub type T24 = TInt<4>;
pub type T48 = TInt<8>;

const fn const_min_usize(a: usize, b: usize) -> usize {
    if a < b { a } else { b }
}

impl<const N: usize> TInt<N> {
    pub const SIZE: usize = N;
    pub const BYTE_SIZE: usize = Tryte::BYTE_SIZE * N;
    pub const TRIT_SIZE: usize = Tryte::TRIT_SIZE * N;

    pub const ZERO: Self = Self::from_trytes([Tryte::ZERO; N]);
    pub const MIN: Self = Self::from_trytes([Tryte::MIN; N]);
    pub const MAX: Self = Self::from_trytes([Tryte::MAX; N]);

    pub const RANGE_I64: i64 = Self::range();
    pub const MAX_I64: i64 = (Self::RANGE_I64 - 1) / 2;
    pub const MIN_I64: i64 = -Self::MAX_I64;

    pub const fn from_trytes(trytes: [Tryte; N]) -> Self {
        Self { trytes }
    }

    pub const fn into_trytes(self) -> [Tryte; N] {
        self.trytes
    }

    pub const fn from_trit(trit: Trit) -> Self {
        Self::ZERO.update_trit(0, trit)
    }

    pub fn from_hyte(hyte: Hyte) -> Self {
        let tryte = Tryte::from_hyte(hyte);
        Self::from_tryte(tryte)
    }

    pub fn from_tryte(tryte: Tryte) -> Self {
        let mut trytes = [Tryte::ZERO; N];
        trytes[0] = tryte;
        Self::from_trytes(trytes)
    }

    pub const fn shl_trytes(self, offset: usize) -> Self {
        let mut int = Self::ZERO;
        let mut i = 0;

        while i < Self::SIZE - offset {
            let j = i + offset;
            int.trytes[j] = self.trytes[i];
            i += 1;
        }

        int
    }

    pub const fn shr_trytes(self, offset: usize) -> Self {
        let mut int = Self::ZERO;
        let mut i = offset;

        while i < Self::SIZE {
            let j = i - offset;
            int.trytes[j] = self.trytes[i];
            i += 1;
        }

        int
    }

    fn shr_trits(self, offset: usize) -> Self {
        let n_lo = offset * Trit::BIT_SIZE;
        let n_hi = (Tryte::TRIT_SIZE - offset) * Trit::BIT_SIZE;
        let mask_hi = (tryte::BITMASK << n_hi) & tryte::BITMASK;

        let mut int = Self::ZERO;
        let size = Self::SIZE;
        let mut i = 0;

        while i < size - 1 {
            let bits_lo = self.trytes[i].into_raw();
            let bits_hi = self.trytes[i + 1].into_raw();
            let bits = (bits_lo >> n_lo) | ((bits_hi << n_hi) & mask_hi);
            int.trytes[i] = Tryte::from_raw(bits);
            i += 1;
        }

        let bits_lo = self.trytes[size - 1].into_raw();
        int.trytes[size - 1] = Tryte::from_raw(bits_lo >> n_lo);

        int
    }

    fn shl_trits(self, offset: usize) -> Self {
        let n_lo = (Tryte::TRIT_SIZE - offset) * Trit::BIT_SIZE;
        let n_hi = offset * Trit::BIT_SIZE;
        let mask_hi = (tryte::BITMASK << n_hi) & tryte::BITMASK;

        let mut int = Self::ZERO;
        let size = Self::SIZE;
        let mut i = size - 1;

        while i > 0 {
            let bits_lo = self.trytes[i - 1].into_raw();
            let bits_hi = self.trytes[i].into_raw();
            let bits = (bits_lo >> n_lo) | ((bits_hi << n_hi) & mask_hi);
            int.trytes[i] = Tryte::from_raw(bits);
            i -= 1;
        }

        let bits_hi = self.trytes[0].into_raw();
        int.trytes[0] = Tryte::from_raw((bits_hi << n_hi) & mask_hi);

        int
    }

    fn shr(self, offset: usize) -> Self {
        let (n_trytes, n_trits) = indices(offset);
        self.shr_trytes(n_trytes).shr_trits(n_trits)
    }

    fn shl(self, offset: usize) -> Self {
        let (n_trytes, n_trits) = indices(offset);
        self.shl_trytes(n_trytes).shl_trits(n_trits)
    }

    #[allow(clippy::cast_sign_loss)]
    pub fn shf(self, offset: isize) -> Self {
        match offset.signum() {
            1 => self.shl(offset as usize),
            -1 => self.shr(-offset as usize),
            _ => self,
        }
    }

    pub const fn resize<const M: usize>(self) -> TInt<M> {
        let size = const_min_usize(TInt::<M>::SIZE, TInt::<N>::SIZE);
        let mut int = TInt::<M>::ZERO;
        let mut i = 0;

        while i < size {
            int.trytes[i] = self.trytes[i];
            i += 1;
        }

        int
    }

    pub const fn range() -> i64 {
        let base = 3_i64;
        #[allow(clippy::cast_possible_truncation)]
        let exp = Self::TRIT_SIZE as u32;
        base.pow(exp)
    }

    pub fn max_bigint() -> BigInt {
        (Self::range_bigint() - 1) / 2
    }

    pub fn min_bigint() -> BigInt {
        -Self::max_bigint()
    }

    pub fn range_bigint() -> BigInt {
        #[allow(clippy::cast_possible_truncation)]
        BigInt::from(3).pow(Self::TRIT_SIZE as u32)
    }

    pub const fn trit(self, i: usize) -> Trit {
        let (tryte_index, trit_index) = indices(i);
        let tryte = self.trytes[tryte_index];
        tryte.trit(trit_index)
    }

    pub fn set_trit(&mut self, i: usize, trit: Trit) {
        let (tryte_index, trit_index) = indices(i);
        let tryte = self.trytes[tryte_index];
        self.trytes[tryte_index] = tryte.set_trit(trit_index, trit);
    }

    pub const fn update_trit(self, i: usize, trit: Trit) -> Self {
        let mut int = self;
        let (tryte_index, trit_index) = indices(i);
        let tryte = self.trytes[tryte_index];
        int.trytes[tryte_index] = tryte.set_trit(trit_index, trit);
        int
    }

    pub fn cmp_trit(self, rhs: Self) -> Trit {
        let mut cmp_trit = _0;

        for i in (0..Self::TRIT_SIZE).rev() {
            let a = self.trit(i);
            let b = rhs.trit(i);
            cmp_trit = a.tcmp(b);

            if cmp_trit != _0 {
                break;
            }
        }

        cmp_trit
    }

    pub fn try_from_int<
        I: Signed
            + PartialOrd
            + ops::AddAssign
            + ops::DivAssign
            + TryFrom<i8>
            + ToBigInt
            + Display
            + Copy,
    >(
        n: I,
    ) -> Result<Self> {
        let mut result = Self::ZERO;
        let big_n = n.to_bigint().unwrap();
        let min = Self::min_bigint();
        let max = Self::max_bigint();
        if !(min <= big_n && big_n <= max) {
            return Err(Error::IntegerOutOfBounds {
                min: format!("{min}"),
                max: format!("{max}"),
                value: format!("{n}"),
            });
        }

        let sign_trit = if n < I::zero() { _T } else { _1 };
        let mut n_pos = n.abs();

        for i in 0..Self::TRIT_SIZE {
            let rem_trit = match n_pos % I::try_from(3i8).map_err(|_| Error::TryFromInt)? {
                n if n == I::one() => _1,
                n if n == I::zero() => _0,
                _ => {
                    n_pos += I::one();
                    _T
                }
            };

            let trit = sign_trit * rem_trit;
            result.set_trit(i, trit);
            n_pos /= I::try_from(3i8).map_err(|_| Error::TryFromInt)?;
        }

        Ok(result)
    }

    pub fn into_i64(self) -> i64 {
        let mut n = 0;

        for i in (0..Self::SIZE).rev() {
            let tryte = self.trytes[i];
            n = n * T6::RANGE_I64 + i64::from(tryte.into_i16());
        }

        n
    }

    #[allow(clippy::cast_possible_truncation)]
    pub fn try_into_int<I: Signed + CheckedAdd + CheckedMul + From<i16>>(self) -> Result<I> {
        let mut n = I::zero();

        for i in (0..Self::SIZE).rev() {
            let tryte = self.trytes[i];
            n = n
                .checked_mul(&I::from(T6::RANGE_I64 as i16))
                .ok_or(Error::TryIntoInt)?
                .checked_add(&I::from(tryte.into_i16()))
                .ok_or(Error::TryIntoInt)?;
        }

        Ok(n)
    }

    pub fn tcmp(self, rhs: Self) -> Self {
        self.zip_trytes(rhs, Tryte::tcmp)
    }

    pub fn tmul(self, rhs: Self) -> Self {
        self.zip_trytes(rhs, Tryte::tmul)
    }

    pub fn add_with_carry(self, rhs: Self, carry: Trit) -> (Self, Trit) {
        let mut dest = Self::ZERO;
        let mut carry = carry;

        for i in 0..Self::TRIT_SIZE {
            let a = self.trit(i);
            let b = rhs.trit(i);
            let (c, new_carry) = a.add_with_carry(b, carry);
            carry = new_carry;
            dest.set_trit(i, c);
        }

        (dest, carry)
    }

    fn add_mul(&mut self, src: Self, sign: Trit, offset: usize) -> Trit {
        let mut carry = _0;

        for i in 0..(Self::TRIT_SIZE - offset) {
            let a = self.trit(i + offset);
            let b = src.trit(i);
            let (c, new_carry) = a.add_with_carry(b * sign, carry);
            carry = new_carry;
            self.set_trit(i + offset, c);
        }

        carry
    }

    fn sign_trit(self) -> Trit {
        for i in (0..Self::TRIT_SIZE).rev() {
            let trit = self.trit(i);
            if trit != _0 {
                return trit;
            }
        }

        _0
    }

    #[allow(dead_code)]
    fn abs(self) -> Self {
        if self.sign_trit() == _T { -self } else { self }
    }

    fn div_rem_pos_slow(self, d: Self) -> (Self, Self) {
        let n = self;

        let mut q = Self::ZERO;
        let mut r = n;

        while r >= d {
            q = q + Self::from_trit(_1);
            r = r - d;
        }

        (q, r)
    }

    pub fn div_rem_checked(self, d: Self) -> Option<(Self, Self)> {
        let n = self;
        let n_sign = n.sign_trit();
        let d_sign = d.sign_trit();

        match (n_sign, d_sign) {
            (_, trit::_0) => None,
            (trit::_0, _) => Some((Self::ZERO, Self::ZERO)),
            (trit::_1, trit::_1) => {
                let (q, r) = n.div_rem_pos_slow(d);
                Some((q, r))
            }
            (trit::_1, trit::_T) => {
                let (q, r) = n.div_rem_pos_slow(-d);
                Some((-q, r))
            }
            (trit::_T, trit::_1) => {
                let (q, r) = (-n).div_rem_pos_slow(d);
                if r == Self::ZERO {
                    Some((-q, Self::ZERO))
                } else {
                    Some((-q - Self::from_trit(_1), d - r))
                }
            }
            (trit::_T, trit::_T) => {
                let (q, r) = (-n).div_rem_pos_slow(-d);
                if r == Self::ZERO {
                    Some((-q, Self::ZERO))
                } else {
                    Some((-q - Self::from_trit(_1), d - r))
                }
            }
            (_, _) => unreachable!(),
        }
    }

    pub fn div_rem(self, divisor: Self) -> (Self, Self) {
        self.div_rem_checked(divisor).unwrap()
    }

    fn map_trytes<F>(self, f: F) -> Self
    where
        F: Fn(Tryte) -> Tryte,
    {
        let mut dest = self;
        for i in 0..Self::SIZE {
            dest.trytes[i] = f(self.trytes[i]);
        }

        dest
    }

    fn zip_trytes<F>(self, rhs: Self, f: F) -> Self
    where
        F: Fn(Tryte, Tryte) -> Tryte,
    {
        let mut dest = self;
        for i in 0..Self::SIZE {
            let a = self.trytes[i];
            let b = rhs.trytes[i];
            dest.trytes[i] = f(a, b);
        }

        dest
    }

    pub fn read_bytes<R: io::Read>(&mut self, reader: &mut R) -> Result<()> {
        let mut bytes = [0; Tryte::BYTE_SIZE];

        for i in 0..Self::SIZE {
            reader.read_exact(&mut bytes)?;
            let tryte = Tryte::try_from_bytes(bytes)?;
            self.trytes[i] = tryte;
        }

        Ok(())
    }

    pub fn write_bytes<W: io::Write>(&self, writer: &mut W) -> Result<()> {
        for i in 0..Self::SIZE {
            let tryte = self.trytes[i];
            writer.write_all(&tryte.into_bytes())?;
        }

        Ok(())
    }

    pub fn from_trit_str(s: &str) -> Result<Self> {
        assert_length_le(s.len(), Self::TRIT_SIZE)?;
        let mut int = Self::ZERO;

        for (i, c) in s.chars().rev().enumerate() {
            let trit = c.try_into()?;
            int.set_trit(i, trit);
        }

        Ok(int)
    }

    pub fn from_hyte_str(mut s: &str) -> Result<Self> {
        assert_length_le(s.len(), Self::TRIT_SIZE * 2)?;
        let mut int = Self::ZERO;

        for i in (0..Self::SIZE).rev() {
            let (substr, s_rest) = s.split_at(2);
            s = s_rest;
            let tryte = Tryte::from_hyte_str(substr)?;
            int.trytes[i] = tryte;
        }

        Ok(int)
    }

    fn fmt_trits<W: fmt::Write>(&self, writer: &mut W) -> fmt::Result {
        for i in (0..Self::TRIT_SIZE).rev() {
            let trit = self.trit(i);
            let c = char::from(trit);
            write!(writer, "{c}")?;
        }

        Ok(())
    }

    fn fmt_hytes<W: fmt::Write>(&self, writer: &mut W) -> fmt::Result {
        for i in (0..Self::SIZE).rev() {
            let tryte = self.trytes[i];
            tryte.fmt_hytes(writer)?;
        }

        Ok(())
    }

    pub fn display_trits(self) -> DisplayTrits<N> {
        DisplayTrits(self)
    }

    pub fn display_hytes(self) -> DisplayHytes<N> {
        DisplayHytes(self)
    }
}

impl T6 {
    pub fn into_tryte(self) -> Tryte {
        self.trytes[0]
    }
}

impl T6 {
    pub fn into_i16(self) -> i16 {
        self.trytes[0].into_i16()
    }
}

impl T12 {
    #[allow(clippy::cast_possible_truncation)]
    pub fn into_t4_t4_t4(self) -> (T6, T6, T6) {
        let [tryte_a, tryte_b] = self.into_trytes();
        let (a0123, a45) = tryte_a.split_trits_raw(4);
        let (b01, b2345) = tryte_b.split_trits_raw(2);

        let trit4_a = a0123;
        let trit4_b = b01 << (2 * Trit::BIT_SIZE) | a45;
        let trit4_c = b2345;

        let t6_a = T6::from_tryte(Tryte::from_raw(trit4_a));
        let t6_b = T6::from_tryte(Tryte::from_raw(trit4_b));
        let t6_c = T6::from_tryte(Tryte::from_raw(trit4_c));
        (t6_a, t6_b, t6_c)
    }
}

impl<const N: usize> FromStr for TInt<N> {
    type Err = Error;

    fn from_str(s: &str) -> Result<Self> {
        Self::from_trit_str(s)
    }
}

impl<const N: usize> fmt::Display for TInt<N> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.display_trits().fmt(f)
    }
}

pub struct DisplayTrits<const N: usize>(TInt<N>);

impl<const N: usize> fmt::Display for DisplayTrits<N> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.0.fmt_trits(f)
    }
}

pub struct DisplayHytes<const N: usize>(TInt<N>);

impl<const N: usize> fmt::Display for DisplayHytes<N> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.0.fmt_hytes(f)
    }
}

const fn indices(i: usize) -> (usize, usize) {
    let tryte_index = i / Tryte::TRIT_SIZE;
    let trit_index = i % Tryte::TRIT_SIZE;
    (tryte_index, trit_index)
}

impl<const N: usize> PartialOrd for TInt<N> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl<const N: usize> Ord for TInt<N> {
    fn cmp(&self, other: &Self) -> Ordering {
        self.cmp_trit(*other).into()
    }
}

impl<const N: usize> ops::Neg for TInt<N> {
    type Output = Self;

    fn neg(self) -> Self {
        self.map_trytes(Tryte::neg)
    }
}

impl<const N: usize> ops::BitAnd for TInt<N> {
    type Output = Self;

    fn bitand(self, rhs: Self) -> Self {
        self.zip_trytes(rhs, Tryte::and)
    }
}

impl<const N: usize> ops::BitOr for TInt<N> {
    type Output = Self;

    fn bitor(self, rhs: Self) -> Self {
        self.zip_trytes(rhs, Tryte::or)
    }
}

impl<const N: usize> ops::Add for TInt<N> {
    type Output = TInt<N>;

    fn add(self, rhs: Self) -> Self::Output {
        let (sum, _) = TInt::add_with_carry(self, rhs, _0);
        sum
    }
}

impl<const N: usize> ops::Sub for TInt<N> {
    type Output = TInt<N>;

    fn sub(self, rhs: Self) -> Self::Output {
        self + (-rhs)
    }
}

impl<const N: usize> ops::Mul for TInt<N> {
    type Output = TInt<N>;

    fn mul(self, rhs: Self) -> Self::Output {
        let mut dest = Self::ZERO;
        for i in 0..Self::TRIT_SIZE {
            let sign = rhs.trit(i);
            if sign != _0 {
                dest.add_mul(self, sign, i);
            }
        }

        dest
    }
}

impl<const N: usize> ops::Div for TInt<N> {
    type Output = TInt<N>;

    fn div(self, rhs: Self) -> Self::Output {
        if let Some((quotient, _)) = self.div_rem(rhs) {
            quotient
        } else {
            #[allow(unconditional_panic)]
            let _ = 1 / 0;
            unreachable!()
        }
    }
}

impl<const N: usize> ops::Rem for TInt<N> {
    type Output = TInt<N>;

    fn rem(self, rhs: Self) -> Self::Output {
        if let Some((_, rem)) = self.div_rem(rhs) {
            rem
        } else {
            #[allow(unconditional_panic)]
            let _ = 1 % 0;
            unreachable!()
        }
    }
}

impl<const N: usize> ops::Shl<usize> for TInt<N> {
    type Output = TInt<N>;

    fn shl(self, rhs: usize) -> Self::Output {
        self.shl(rhs)
    }
}

#[allow(clippy::cast_possible_wrap)]
impl<const N: usize> ops::Shr<usize> for TInt<N> {
    type Output = TInt<N>;

    fn shr(self, rhs: usize) -> Self::Output {
        self.shr(rhs)
    }
}

#[cfg(test)]
mod tests {
    use std::io::Cursor;

    use crate::{
        Result, T6, T24,
        test_constants::*,
        trit::{_0, _1, _T},
    };

    #[test]
    fn into_i64() {
        assert_eq!(T24::MIN_I64, T24_MIN.into_i64());
        assert_eq!(-1, T24_NEG1.into_i64());
        assert_eq!(0, T24_0.into_i64());
        assert_eq!(1, T24_1.into_i64());
        assert_eq!(T24::MAX_I64, T24_MAX.into_i64());
    }

    #[test]
    fn try_from_i64() {
        assert_eq!(T24_MIN, T24::try_from_int(T24::MIN_I64).unwrap());
        assert_eq!(T24_NEG1, T24::try_from_int(-1).unwrap());
        assert_eq!(T24_0, T24::try_from_int(0).unwrap());
        assert_eq!(T24_1, T24::try_from_int(1).unwrap());
        assert_eq!(T24_MAX, T24::try_from_int(T24::MAX_I64).unwrap());

        assert!(T24::try_from_int(i64::MIN).is_err());
        assert!(T24::try_from_int(T24::MIN_I64 - 1).is_err());
        assert!(T24::try_from_int(T24::MAX_I64 + 1).is_err());
        assert!(T24::try_from_int(i64::MAX).is_err());
    }

    #[test]
    fn cmp() {
        assert_eq!(_0, T24_0.cmp_trit(T24_0));
        assert_eq!(_T, T24_0.cmp_trit(T24_MAX));
        assert_eq!(_1, T24_0.cmp_trit(T24_MIN));
        assert_eq!(_1, T24_MAX.cmp_trit(T24_0));
        assert_eq!(_1, T24_MAX.cmp_trit(T24_MIN));
        assert_eq!(_0, T24_MAX.cmp_trit(T24_MAX));
        assert_eq!(_T, T24_MIN.cmp_trit(T24_0));
        assert_eq!(_T, T24_MIN.cmp_trit(T24_MAX));
        assert_eq!(_0, T24_MIN.cmp_trit(T24_MIN));
    }

    #[test]
    fn neg() {
        assert_eq!(T24_MIN, -T24_MAX);
        assert_eq!(T24_NEG1, -T24_1);
        assert_eq!(T24_0, -T24_0);
        assert_eq!(T24_1, -T24_NEG1);
        assert_eq!(T24_MAX, -T24_MIN);
    }

    #[test]
    fn and() {
        assert_eq!(T24_0, T24_0 & T24_0);
        assert_eq!(T24_0, T24_0 & T24_MAX);
        assert_eq!(T24_MIN, T24_0 & T24_MIN);
        assert_eq!(T24_0, T24_MAX & T24_0);
        assert_eq!(T24_MAX, T24_MAX & T24_MAX);
        assert_eq!(T24_MIN, T24_MAX & T24_MIN);
        assert_eq!(T24_MIN, T24_MIN & T24_0);
        assert_eq!(T24_MIN, T24_MIN & T24_MAX);
        assert_eq!(T24_MIN, T24_MIN & T24_MIN);
    }

    #[test]
    fn or() {
        assert_eq!(T24_0, T24_0 | T24_0);
        assert_eq!(T24_MAX, T24_0 | T24_MAX);
        assert_eq!(T24_0, T24_0 | T24_MIN);
        assert_eq!(T24_MAX, T24_MAX | T24_0);
        assert_eq!(T24_MAX, T24_MAX | T24_MAX);
        assert_eq!(T24_MAX, T24_MAX | T24_MIN);
        assert_eq!(T24_0, T24_MIN | T24_0);
        assert_eq!(T24_MAX, T24_MIN | T24_MAX);
        assert_eq!(T24_MIN, T24_MIN | T24_MIN);
    }

    #[test]
    fn tcmp() {
        assert_eq!(T24_MIN, T24_MIN.tcmp(T24_0));
        assert_eq!(T24_MAX, T24_MAX.tcmp(T24_0));
        assert_eq!(T24_NEG1, T24_NEG1.tcmp(T24_0));
        assert_eq!(T24_0, T24_0.tcmp(T24_0));
        assert_eq!(T24_1, T24_1.tcmp(T24_0));

        assert_eq!(T24_MAX, T24_0.tcmp(T24_MIN));
        assert_eq!(T24_MIN, T24_0.tcmp(T24_MAX));
        assert_eq!(T24_1, T24_0.tcmp(T24_NEG1));
        assert_eq!(T24_NEG1, T24_0.tcmp(T24_1));

        assert_eq!(T24_0, T24_MIN.tcmp(T24_MIN));
        assert_eq!(T24_0, T24_MAX.tcmp(T24_MAX));
        assert_eq!(T24_0, T24_NEG1.tcmp(T24_NEG1));
        assert_eq!(T24_0, T24_1.tcmp(T24_1));
    }

    #[test]
    fn tmul() {
        assert_eq!(T24_0, T24_MIN.tmul(T24_0));
        assert_eq!(T24_0, T24_MAX.tmul(T24_0));
        assert_eq!(T24_0, T24_NEG1.tmul(T24_0));
        assert_eq!(T24_0, T24_0.tmul(T24_0));
        assert_eq!(T24_0, T24_1.tmul(T24_0));

        assert_eq!(T24_MIN, T24_MIN.tmul(T24_MAX));
        assert_eq!(T24_MAX, T24_MAX.tmul(T24_MAX));
        assert_eq!(T24_NEG1, T24_NEG1.tmul(T24_MAX));
        assert_eq!(T24_0, T24_0.tmul(T24_MAX));
        assert_eq!(T24_1, T24_1.tmul(T24_MAX));

        assert_eq!(T24_MAX, T24_MIN.tmul(T24_MIN));
        assert_eq!(T24_MIN, T24_MAX.tmul(T24_MIN));
        assert_eq!(T24_1, T24_NEG1.tmul(T24_MIN));
        assert_eq!(T24_0, T24_0.tmul(T24_MIN));
        assert_eq!(T24_NEG1, T24_1.tmul(T24_MIN));
    }

    #[test]
    fn mul() {
        assert_eq!(T24_0, T24_NEG4096 * T24_0);
        assert_eq!(T24_0, T24_NEG1 * T24_0);
        assert_eq!(T24_0, T24_0 * T24_0);
        assert_eq!(T24_0, T24_1 * T24_0);
        assert_eq!(T24_0, T24_4096 * T24_0);

        assert_eq!(T24_0, T24_0 * T24_NEG4096);
        assert_eq!(T24_0, T24_0 * T24_NEG1);
        assert_eq!(T24_0, T24_0 * T24_1);
        assert_eq!(T24_0, T24_0 * T24_4096);

        assert_eq!(T24_NEG4096, T24_NEG4096 * T24_1);
        assert_eq!(T24_NEG1, T24_NEG1 * T24_1);
        assert_eq!(T24_1, T24_1 * T24_1);
        assert_eq!(T24_4096, T24_4096 * T24_1);

        assert_eq!(T24_NEG4096, T24_1 * T24_NEG4096);
        assert_eq!(T24_NEG1, T24_1 * T24_NEG1);
        assert_eq!(T24_4096, T24_1 * T24_4096);

        assert_eq!(T24_4096, T24_NEG4096 * T24_NEG1);
        assert_eq!(T24_1, T24_NEG1 * T24_NEG1);
        assert_eq!(T24_NEG4096, T24_4096 * T24_NEG1);

        assert_eq!(T24_4096, T24_NEG1 * T24_NEG4096);
        assert_eq!(T24_NEG4096, T24_NEG1 * T24_4096);

        assert_eq!(T24_64, T24_8 * T24_8);
        assert_eq!(T24_64, T24_NEG8 * T24_NEG8);
        assert_eq!(T24_NEG64, T24_8 * T24_NEG8);
        assert_eq!(T24_NEG64, T24_NEG8 * T24_8);

        assert_eq!(T24_81, T24_9 * T24_9);
        assert_eq!(T24_81, T24_NEG9 * T24_NEG9);
        assert_eq!(T24_NEG81, T24_9 * T24_NEG9);
        assert_eq!(T24_NEG81, T24_NEG9 * T24_9);

        assert_eq!(T24_4096, T24_8 * T24_512);
        assert_eq!(T24_4096, T24_NEG8 * T24_NEG512);
        assert_eq!(T24_NEG4096, T24_8 * T24_NEG512);
        assert_eq!(T24_NEG4096, T24_NEG8 * T24_512);

        assert_eq!(T24_4096, T24_512 * T24_8);
        assert_eq!(T24_4096, T24_NEG512 * T24_NEG8);
        assert_eq!(T24_NEG4096, T24_512 * T24_NEG8);
        assert_eq!(T24_NEG4096, T24_NEG512 * T24_8);

        assert_eq!(T24_4096, T24_16 * T24_256);
        assert_eq!(T24_4096, T24_NEG16 * T24_NEG256);
        assert_eq!(T24_NEG4096, T24_16 * T24_NEG256);
        assert_eq!(T24_NEG4096, T24_NEG16 * T24_256);

        assert_eq!(T24_4096, T24_256 * T24_16);
        assert_eq!(T24_4096, T24_NEG256 * T24_NEG16);
        assert_eq!(T24_NEG4096, T24_256 * T24_NEG16);
        assert_eq!(T24_NEG4096, T24_NEG256 * T24_16);

        assert_eq!(T24_4096, T24_64 * T24_64);
        assert_eq!(T24_4096, T24_NEG64 * T24_NEG64);
        assert_eq!(T24_NEG4096, T24_64 * T24_NEG64);
        assert_eq!(T24_NEG4096, T24_NEG64 * T24_64);
    }

    #[test]
    fn shift() {
        assert_shift("000000000000000000000000", "1T000110T001100T011000T1", -24);
        assert_shift("000000000000000000000001", "1T000110T001100T011000T1", -23);
        assert_shift("00000000000000000000001T", "1T000110T001100T011000T1", -22);
        assert_shift("0000000000000000000001T0", "1T000110T001100T011000T1", -21);
        assert_shift("000000000000000000001T00", "1T000110T001100T011000T1", -20);
        assert_shift("00000000000000000001T000", "1T000110T001100T011000T1", -19);
        assert_shift("0000000000000000001T0001", "1T000110T001100T011000T1", -18);
        assert_shift("000000000000000001T00011", "1T000110T001100T011000T1", -17);
        assert_shift("00000000000000001T000110", "1T000110T001100T011000T1", -16);
        assert_shift("0000000000000001T000110T", "1T000110T001100T011000T1", -15);
        assert_shift("000000000000001T000110T0", "1T000110T001100T011000T1", -14);
        assert_shift("00000000000001T000110T00", "1T000110T001100T011000T1", -13);
        assert_shift("0000000000001T000110T001", "1T000110T001100T011000T1", -12);
        assert_shift("000000000001T000110T0011", "1T000110T001100T011000T1", -11);
        assert_shift("00000000001T000110T00110", "1T000110T001100T011000T1", -10);
        assert_shift("0000000001T000110T001100", "1T000110T001100T011000T1", -9);
        assert_shift("000000001T000110T001100T", "1T000110T001100T011000T1", -8);
        assert_shift("00000001T000110T001100T0", "1T000110T001100T011000T1", -7);
        assert_shift("0000001T000110T001100T01", "1T000110T001100T011000T1", -6);
        assert_shift("000001T000110T001100T011", "1T000110T001100T011000T1", -5);
        assert_shift("00001T000110T001100T0110", "1T000110T001100T011000T1", -4);
        assert_shift("0001T000110T001100T01100", "1T000110T001100T011000T1", -3);
        assert_shift("001T000110T001100T011000", "1T000110T001100T011000T1", -2);
        assert_shift("01T000110T001100T011000T", "1T000110T001100T011000T1", -1);
        assert_shift("1T000110T001100T011000T1", "1T000110T001100T011000T1", 0);
        assert_shift("T000110T001100T011000T10", "1T000110T001100T011000T1", 1);
        assert_shift("000110T001100T011000T100", "1T000110T001100T011000T1", 2);
        assert_shift("00110T001100T011000T1000", "1T000110T001100T011000T1", 3);
        assert_shift("0110T001100T011000T10000", "1T000110T001100T011000T1", 4);
        assert_shift("110T001100T011000T100000", "1T000110T001100T011000T1", 5);
        assert_shift("10T001100T011000T1000000", "1T000110T001100T011000T1", 6);
        assert_shift("0T001100T011000T10000000", "1T000110T001100T011000T1", 7);
        assert_shift("T001100T011000T100000000", "1T000110T001100T011000T1", 8);
        assert_shift("001100T011000T1000000000", "1T000110T001100T011000T1", 9);
        assert_shift("01100T011000T10000000000", "1T000110T001100T011000T1", 10);
        assert_shift("1100T011000T100000000000", "1T000110T001100T011000T1", 11);
        assert_shift("100T011000T1000000000000", "1T000110T001100T011000T1", 12);
        assert_shift("00T011000T10000000000000", "1T000110T001100T011000T1", 13);
        assert_shift("0T011000T100000000000000", "1T000110T001100T011000T1", 14);
        assert_shift("T011000T1000000000000000", "1T000110T001100T011000T1", 15);
        assert_shift("011000T10000000000000000", "1T000110T001100T011000T1", 16);
        assert_shift("11000T100000000000000000", "1T000110T001100T011000T1", 17);
        assert_shift("1000T1000000000000000000", "1T000110T001100T011000T1", 18);
        assert_shift("000T10000000000000000000", "1T000110T001100T011000T1", 19);
        assert_shift("00T100000000000000000000", "1T000110T001100T011000T1", 20);
        assert_shift("0T1000000000000000000000", "1T000110T001100T011000T1", 21);
        assert_shift("T10000000000000000000000", "1T000110T001100T011000T1", 22);
        assert_shift("100000000000000000000000", "1T000110T001100T011000T1", 23);
        assert_shift("000000000000000000000000", "1T000110T001100T011000T1", 24);
    }

    fn assert_shift(output: &str, input: &str, i: isize) {
        assert_eq!(
            T24::from_trit_str(output).unwrap(),
            T24::from_trit_str(input).unwrap().shf(i)
        );
    }

    #[test]
    fn read_bytes() {
        assert_eq!(&T24_MIN, &t24_read_bytes(&BYTES_MIN).unwrap());
        assert_eq!(&T24_NEG1, &t24_read_bytes(&BYTES_NEG1).unwrap());
        assert_eq!(&T24_0, &t24_read_bytes(&BYTES_0).unwrap());
        assert_eq!(&T24_1, &t24_read_bytes(&BYTES_1).unwrap());
        assert_eq!(&T24_MAX, &t24_read_bytes(&BYTES_MAX).unwrap());
    }

    fn t24_read_bytes(bytes: &[u8]) -> Result<T24> {
        let mut int = T24::ZERO;
        int.read_bytes(&mut Cursor::new(bytes))?;
        Ok(int)
    }

    #[test]
    fn write_bytes() {
        assert_eq!(&BYTES_MIN, &t24_write_bytes(T24_MIN)[..]);
        assert_eq!(&BYTES_NEG1, &t24_write_bytes(T24_NEG1)[..]);
        assert_eq!(&BYTES_0, &t24_write_bytes(T24_0)[..]);
        assert_eq!(&BYTES_1, &t24_write_bytes(T24_1)[..]);
        assert_eq!(&BYTES_MAX, &t24_write_bytes(T24_MAX)[..]);
    }

    fn t24_write_bytes(int: T24) -> Vec<u8> {
        let mut bytes = vec![];
        int.write_bytes(&mut bytes).unwrap();
        bytes
    }

    #[test]
    fn from_hyte_str() {
        assert_eq!(T24_MIN, T24::from_hyte_str("mmmmmmmm").unwrap());
        assert_eq!(T24_NEG1, T24::from_hyte_str("0000000a").unwrap());
        assert_eq!(T24_0, T24::from_hyte_str("00000000").unwrap());
        assert_eq!(T24_1, T24::from_hyte_str("0000000A").unwrap());
        assert_eq!(T24_MAX, T24::from_hyte_str("MMMMMMMM").unwrap());
    }

    #[test]
    fn display_hytes() {
        assert_eq!("mmmmmmmm", format!("{}", T24_MIN.display_hytes()));
        assert_eq!("0000000a", format!("{}", T24_NEG1.display_hytes()));
        assert_eq!("00000000", format!("{}", T24_0.display_hytes()));
        assert_eq!("0000000A", format!("{}", T24_1.display_hytes()));
        assert_eq!("MMMMMMMM", format!("{}", T24_MAX.display_hytes()));
    }

    #[test]
    fn from_trit_str() {
        assert_eq!(
            T24_MIN,
            T24::from_trit_str("TTTTTTTTTTTTTTTTTTTTTTTT").unwrap()
        );
        assert_eq!(T24_NEG1, T24::from_trit_str("00000000000000000T").unwrap());
        assert_eq!(T24_0, T24::from_trit_str("000000000000000000").unwrap());
        assert_eq!(T24_1, T24::from_trit_str("000000000000000001").unwrap());
        assert_eq!(
            T24_MAX,
            T24::from_trit_str("111111111111111111111111").unwrap()
        );
    }

    #[test]
    fn display_trits() {
        assert_eq!(
            "TTTTTTTTTTTTTTTTTTTTTTTT",
            format!("{}", T24_MIN.display_trits())
        );
        assert_eq!(
            "00000000000000000000000T",
            format!("{}", T24_NEG1.display_trits())
        );
        assert_eq!(
            "000000000000000000000000",
            format!("{}", T24_0.display_trits())
        );
        assert_eq!(
            "000000000000000000000001",
            format!("{}", T24_1.display_trits())
        );
        assert_eq!(
            "111111111111111111111111",
            format!("{}", T24_MAX.display_trits())
        );
    }

    #[test]
    fn div_rem() {
        assert_eq!((t6(0), t6(0)), t6(0).div_rem(t6(-364)));
        assert_eq!((t6(0), t6(0)), t6(0).div_rem(t6(-1)));
        assert_eq!((t6(0), t6(0)), t6(0).div_rem(t6(1)));
        assert_eq!((t6(0), t6(0)), t6(0).div_rem(t6(364)));

        assert_eq!((t6(-1), t6(0)), t6(-7).div_rem(t6(7)));
        assert_eq!((t6(-1), t6(1)), t6(-6).div_rem(t6(7)));
        assert_eq!((t6(-1), t6(2)), t6(-5).div_rem(t6(7)));
        assert_eq!((t6(-1), t6(3)), t6(-4).div_rem(t6(7)));
        assert_eq!((t6(-1), t6(4)), t6(-3).div_rem(t6(7)));
        assert_eq!((t6(-1), t6(5)), t6(-2).div_rem(t6(7)));
        assert_eq!((t6(-1), t6(6)), t6(-1).div_rem(t6(7)));
        assert_eq!((t6(0), t6(0)), t6(0).div_rem(t6(7)));
        assert_eq!((t6(0), t6(1)), t6(1).div_rem(t6(7)));
        assert_eq!((t6(0), t6(2)), t6(2).div_rem(t6(7)));
        assert_eq!((t6(0), t6(3)), t6(3).div_rem(t6(7)));
        assert_eq!((t6(0), t6(4)), t6(4).div_rem(t6(7)));
        assert_eq!((t6(0), t6(5)), t6(5).div_rem(t6(7)));
        assert_eq!((t6(0), t6(6)), t6(6).div_rem(t6(7)));
        assert_eq!((t6(1), t6(0)), t6(7).div_rem(t6(7)));

        assert!(t6(0).div_rem_checked(t6(0)).is_none());
    }

    fn t6(n: i16) -> T6 {
        T6::try_from_int(n).unwrap()
    }
}
