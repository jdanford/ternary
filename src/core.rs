use std::convert::TryFrom;
use std::io::Write;

use byteorder::{ReadBytesExt, WriteBytesExt};

use crate::error::{Error, Result};
use crate::trit;
use crate::trit::Trit;
use crate::tryte;
use crate::tryte::Tryte;

pub trait Ternary {
    fn trit_len(&self) -> usize;
    fn tryte_len(&self) -> usize;
    fn get_trit(&self, i: usize) -> Trit;
    fn set_trit(&mut self, i: usize, trit: Trit);
    fn get_tryte(&self, i: usize) -> Tryte;
    fn set_tryte(&mut self, i: usize, tryte: Tryte);

    fn range(&self) -> i64 {
        let base = 3_i64;
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
        let mut n = 0_i64;

        for i in (0..self.trit_len()).rev() {
            let trit = self.get_trit(i);
            let t: i8 = trit.into();
            n = n * 3 + i64::from(t);
        }

        n
    }

    fn read_i64(&mut self, n: i64) -> Result<()> {
        if n < self.min_value() || self.max_value() < n {
            return Err(Error::IntegerOutOfBounds(
                self.min_value(),
                self.max_value(),
                n,
            ));
        }

        let sign_trit = if n < 0 { trit::NEG } else { trit::POS };
        let mut n_pos = n.abs();

        for i in 0..self.trit_len() {
            let rem_trit = match n_pos % 3 {
                1 => trit::POS,
                0 => trit::ZERO,
                _ => {
                    n_pos += 1;
                    trit::NEG
                }
            };

            let trit = sign_trit * rem_trit;
            self.set_trit(i, trit);
            n_pos /= 3;
        }

        Ok(())
    }

    fn read_hytes(&mut self, mut s: &str) -> Result<()> {
        let len = self.tryte_len() * 2;
        if s.len() != len {
            return Err(Error::InvalidLength(len, s.len()));
        }

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
            tryte.write_hytes(writer).map_err(|_| Error::FormatError)?;
        }

        Ok(())
    }

    fn read_trits(&mut self, s: &str) -> Result<()> {
        if s.len() != self.trit_len() {
            return Err(Error::InvalidLength(self.trit_len(), s.len()));
        }

        for (i, c) in s.chars().rev().enumerate() {
            let trit = Trit::try_from(c)?;
            self.set_trit(i, trit);
        }

        Ok(())
    }

    fn write_trits<W: Write>(&self, writer: &mut W) -> Result<()> {
        for i in (0..self.trit_len()).rev() {
            let trit = self.get_trit(i);
            let c: char = trit.into();
            write!(writer, "{c}").map_err(|_| Error::FormatError)?;
        }

        Ok(())
    }
}
