use std::io::Write;

use byteorder::{ReadBytesExt, WriteBytesExt};

use crate::{
    error::{assert_length, Error, Result},
    trit::{Trit, _0, _1, _T},
    tryte::{self, Tryte},
};

pub trait Ternary {
    fn tryte_len(&self) -> usize;
    fn get_tryte(&self, i: usize) -> Tryte;
    fn set_tryte(&mut self, i: usize, tryte: Tryte);

    fn trit_len(&self) -> usize {
        self.tryte_len() * tryte::TRIT_LEN
    }

    fn get_trit(&self, i: usize) -> Trit {
        let (tryte_index, trit_index) = indices(i);
        let tryte = self.get_tryte(tryte_index);
        tryte.get_trit(trit_index)
    }

    fn set_trit(&mut self, i: usize, trit: Trit) {
        let (tryte_index, trit_index) = indices(i);
        let tryte = self.get_tryte(tryte_index);
        let updated_tryte = tryte.set_trit(trit_index, trit);
        self.set_tryte(tryte_index, updated_tryte);
    }

    fn range(&self) -> i64 {
        let base = 3_i64;
        #[allow(clippy::cast_possible_truncation)]
        let exp = self.trit_len() as u32;
        base.pow(exp)
    }

    fn min_value(&self) -> i64 {
        -(self.range() - 1) / 2
    }

    fn max_value(&self) -> i64 {
        (self.range() - 1) / 2
    }

    fn clear(&mut self) {
        for i in 0..self.tryte_len() {
            self.set_tryte(i, tryte::ZERO);
        }
    }

    fn read_bytes<R: ReadBytesExt>(&mut self, reader: &mut R) -> Result<()> {
        for i in 0..self.tryte_len() {
            let tryte = Tryte::from_bytes(reader)?;
            self.set_tryte(i, tryte);
        }

        Ok(())
    }

    fn write_bytes<W: WriteBytesExt>(&self, writer: &mut W) -> Result<()> {
        for i in 0..self.tryte_len() {
            let tryte = self.get_tryte(i);
            tryte.write_bytes(writer)?;
        }

        Ok(())
    }

    fn as_i64(&self) -> i64 {
        let mut n = 0;

        for i in (0..self.trit_len()).rev() {
            let trit = self.get_trit(i);
            let t = i8::from(trit);
            n = n * 3 + i64::from(t);
        }

        n
    }

    fn read_i64(&mut self, n: i64) -> Result<()> {
        let min = self.min_value();
        let max = self.max_value();
        if !(min <= n && n <= max) {
            return Err(Error::IntegerOutOfBounds { min, max, value: n });
        }

        let sign_trit = if n < 0 { _T } else { _1 };
        let mut n_pos = n.abs();

        for i in 0..self.trit_len() {
            let rem_trit = match n_pos % 3 {
                1 => _1,
                0 => _0,
                _ => {
                    n_pos += 1;
                    _T
                }
            };

            let trit = sign_trit * rem_trit;
            self.set_trit(i, trit);
            n_pos /= 3;
        }

        Ok(())
    }

    fn read_hytes(&mut self, mut s: &str) -> Result<()> {
        assert_length(s.len(), self.tryte_len() * 2)?;

        for i in (0..self.tryte_len()).rev() {
            let (substr, s_rest) = s.split_at(2);
            s = s_rest;
            let tryte = Tryte::from_hyte_str(substr)?;
            self.set_tryte(i, tryte);
        }

        Ok(())
    }

    fn write_hytes<W: Write>(&self, writer: &mut W) -> Result<()> {
        for i in (0..self.tryte_len()).rev() {
            let tryte = self.get_tryte(i);
            tryte.write_hytes(writer)?;
        }

        Ok(())
    }

    fn read_trits(&mut self, s: &str) -> Result<()> {
        assert_length(s.len(), self.trit_len())?;

        for (i, c) in s.chars().rev().enumerate() {
            let trit = c.try_into()?;
            self.set_trit(i, trit);
        }

        Ok(())
    }

    fn write_trits<W: Write>(&self, writer: &mut W) -> Result<()> {
        for i in (0..self.trit_len()).rev() {
            let trit = self.get_trit(i);
            let c = char::from(trit);
            write!(writer, "{c}")?;
        }

        Ok(())
    }
}

impl Ternary for [Tryte] {
    fn tryte_len(&self) -> usize {
        self.len()
    }

    fn get_tryte(&self, i: usize) -> Tryte {
        self[i]
    }

    fn set_tryte(&mut self, i: usize, tryte: Tryte) {
        self[i] = tryte;
    }
}

impl<const N: usize> Ternary for [Tryte; N] {
    fn tryte_len(&self) -> usize {
        self.len()
    }

    fn get_tryte(&self, i: usize) -> Tryte {
        self[i]
    }

    fn set_tryte(&mut self, i: usize, tryte: Tryte) {
        self[i] = tryte;
    }
}

impl Ternary for Vec<Tryte> {
    fn tryte_len(&self) -> usize {
        self.len()
    }

    fn get_tryte(&self, i: usize) -> Tryte {
        self[i]
    }

    fn set_tryte(&mut self, i: usize, tryte: Tryte) {
        self[i] = tryte;
    }
}

const fn indices(i: usize) -> (usize, usize) {
    let tryte_index = i / tryte::TRIT_LEN;
    let trit_index = i % tryte::TRIT_LEN;
    (tryte_index, trit_index)
}
