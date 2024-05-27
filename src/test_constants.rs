#![allow(dead_code)]

use crate::{
    trit::{_0, _1, _T},
    Trit, Tryte, T24,
};

const fn tryte(t5: Trit, t4: Trit, t3: Trit, t2: Trit, t1: Trit, t0: Trit) -> Tryte {
    Tryte::from_trits([t0, t1, t2, t3, t4, t5])
}

pub const TRYTE_MIN: Tryte = tryte(_T, _T, _T, _T, _T, _T);
pub const TRYTE_NEG278: Tryte = tryte(_T, _0, _T, _T, _0, _1);
pub const TRYTE_NEG256: Tryte = tryte(_T, _0, _0, _T, _T, _T);
pub const TRYTE_NEG217: Tryte = tryte(_T, _0, _1, _0, _0, _T);
pub const TRYTE_NEG81: Tryte = tryte(_0, _T, _0, _0, _0, _0);
pub const TRYTE_NEG64: Tryte = tryte(_0, _T, _1, _T, _0, _T);
pub const TRYTE_NEG16: Tryte = tryte(_0, _0, _T, _1, _1, _T);
pub const TRYTE_NEG9: Tryte = tryte(_0, _0, _0, _T, _0, _0);
pub const TRYTE_NEG8: Tryte = tryte(_0, _0, _0, _T, _0, _1);
pub const TRYTE_NEG6: Tryte = tryte(_0, _0, _0, _T, _1, _0);
pub const TRYTE_NEG1: Tryte = tryte(_0, _0, _0, _0, _0, _T);
pub const TRYTE_0: Tryte = tryte(_0, _0, _0, _0, _0, _0);
pub const TRYTE_1: Tryte = tryte(_0, _0, _0, _0, _0, _1);
pub const TRYTE_6: Tryte = tryte(_0, _0, _0, _1, _T, _0);
pub const TRYTE_8: Tryte = tryte(_0, _0, _0, _1, _0, _T);
pub const TRYTE_9: Tryte = tryte(_0, _0, _0, _1, _0, _0);
pub const TRYTE_16: Tryte = tryte(_0, _0, _1, _T, _T, _1);
pub const TRYTE_64: Tryte = tryte(_0, _1, _T, _1, _0, _1);
pub const TRYTE_81: Tryte = tryte(_0, _1, _0, _0, _0, _0);
pub const TRYTE_217: Tryte = tryte(_1, _0, _T, _0, _0, _1);
pub const TRYTE_256: Tryte = tryte(_1, _0, _0, _1, _1, _1);
pub const TRYTE_278: Tryte = tryte(_1, _0, _1, _1, _0, _T);
pub const TRYTE_MAX: Tryte = tryte(_1, _1, _1, _1, _1, _1);

const fn t24(trytes: [Tryte; T24::SIZE]) -> T24 {
    T24::from_trytes(trytes)
}

pub const T24_MIN: T24 = t24([TRYTE_MIN; 4]);
pub const T24_NEG4096: T24 = t24([TRYTE_278, TRYTE_NEG6, TRYTE_0, TRYTE_0]);
pub const T24_NEG512: T24 = t24([TRYTE_217, TRYTE_NEG1, TRYTE_0, TRYTE_0]);
pub const T24_NEG256: T24 = t24([TRYTE_NEG256, TRYTE_0, TRYTE_0, TRYTE_0]);
pub const T24_NEG81: T24 = t24([TRYTE_NEG81, TRYTE_0, TRYTE_0, TRYTE_0]);
pub const T24_NEG64: T24 = t24([TRYTE_NEG64, TRYTE_0, TRYTE_0, TRYTE_0]);
pub const T24_NEG16: T24 = t24([TRYTE_NEG16, TRYTE_0, TRYTE_0, TRYTE_0]);
pub const T24_NEG9: T24 = t24([TRYTE_NEG9, TRYTE_0, TRYTE_0, TRYTE_0]);
pub const T24_NEG8: T24 = t24([TRYTE_NEG8, TRYTE_0, TRYTE_0, TRYTE_0]);
pub const T24_NEG1: T24 = t24([TRYTE_NEG1, TRYTE_0, TRYTE_0, TRYTE_0]);
pub const T24_0: T24 = t24([TRYTE_0, TRYTE_0, TRYTE_0, TRYTE_0]);
pub const T24_1: T24 = t24([TRYTE_1, TRYTE_0, TRYTE_0, TRYTE_0]);
pub const T24_8: T24 = t24([TRYTE_8, TRYTE_0, TRYTE_0, TRYTE_0]);
pub const T24_9: T24 = t24([TRYTE_9, TRYTE_0, TRYTE_0, TRYTE_0]);
pub const T24_16: T24 = t24([TRYTE_16, TRYTE_0, TRYTE_0, TRYTE_0]);
pub const T24_64: T24 = t24([TRYTE_64, TRYTE_0, TRYTE_0, TRYTE_0]);
pub const T24_81: T24 = t24([TRYTE_81, TRYTE_0, TRYTE_0, TRYTE_0]);
pub const T24_256: T24 = t24([TRYTE_256, TRYTE_0, TRYTE_0, TRYTE_0]);
pub const T24_512: T24 = t24([TRYTE_NEG217, TRYTE_1, TRYTE_0, TRYTE_0]);
pub const T24_4096: T24 = t24([TRYTE_NEG278, TRYTE_6, TRYTE_0, TRYTE_0]);
pub const T24_MAX: T24 = t24([TRYTE_MAX; 4]);

pub const BYTES_MIN: [u8; 8] = [
    0b11_11_11_11,
    0b00_00_11_11,
    0b11_11_11_11,
    0b00_00_11_11,
    0b11_11_11_11,
    0b00_00_11_11,
    0b11_11_11_11,
    0b00_00_11_11,
];

pub const BYTES_NEG1: [u8; 8] = [
    0b00_00_00_11,
    0b00_00_00_00,
    0b00_00_00_00,
    0b00_00_00_00,
    0b00_00_00_00,
    0b00_00_00_00,
    0b00_00_00_00,
    0b00_00_00_00,
];

pub const BYTES_0: [u8; 8] = [
    0b00_00_00_00,
    0b00_00_00_00,
    0b00_00_00_00,
    0b00_00_00_00,
    0b00_00_00_00,
    0b00_00_00_00,
    0b00_00_00_00,
    0b00_00_00_00,
];

pub const BYTES_1: [u8; 8] = [
    0b00_00_00_01,
    0b00_00_00_00,
    0b00_00_00_00,
    0b00_00_00_00,
    0b00_00_00_00,
    0b00_00_00_00,
    0b00_00_00_00,
    0b00_00_00_00,
];

pub const BYTES_MAX: [u8; 8] = [
    0b01_01_01_01,
    0b00_00_01_01,
    0b01_01_01_01,
    0b00_00_01_01,
    0b01_01_01_01,
    0b00_00_01_01,
    0b01_01_01_01,
    0b00_00_01_01,
];
