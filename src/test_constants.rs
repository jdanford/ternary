use crate::{
    trit::{_0, _1, _T},
    Tryte,
};

pub const TRYTE_MIN: Tryte = Tryte::from_trits(_T, _T, _T, _T, _T, _T);
pub const TRYTE_NEG317: Tryte = Tryte::from_trits(_T, _1, _0, _1, _T, _1);
pub const TRYTE_NEG278: Tryte = Tryte::from_trits(_T, _0, _T, _T, _0, _1);
pub const TRYTE_NEG256: Tryte = Tryte::from_trits(_T, _0, _0, _T, _T, _T);
pub const TRYTE_NEG217: Tryte = Tryte::from_trits(_T, _0, _1, _0, _0, _T);
pub const TRYTE_NEG167: Tryte = Tryte::from_trits(_T, _1, _0, _T, _1, _1);
pub const TRYTE_NEG89: Tryte = Tryte::from_trits(_0, _T, _0, _T, _0, _1);
pub const TRYTE_NEG81: Tryte = Tryte::from_trits(_0, _T, _0, _0, _0, _0);
pub const TRYTE_NEG64: Tryte = Tryte::from_trits(_0, _T, _1, _T, _0, _T);
pub const TRYTE_NEG16: Tryte = Tryte::from_trits(_0, _0, _T, _1, _1, _T);
pub const TRYTE_NEG9: Tryte = Tryte::from_trits(_0, _0, _0, _T, _0, _0);
pub const TRYTE_NEG8: Tryte = Tryte::from_trits(_0, _0, _0, _T, _0, _1);
pub const TRYTE_NEG6: Tryte = Tryte::from_trits(_0, _0, _0, _T, _1, _0);
pub const TRYTE_NEG3: Tryte = Tryte::from_trits(_0, _0, _0, _0, _T, _0);
pub const TRYTE_NEG1: Tryte = Tryte::from_trits(_0, _0, _0, _0, _0, _T);
pub const TRYTE_0: Tryte = Tryte::from_trits(_0, _0, _0, _0, _0, _0);
pub const TRYTE_1: Tryte = Tryte::from_trits(_0, _0, _0, _0, _0, _1);
pub const TRYTE_3: Tryte = Tryte::from_trits(_0, _0, _0, _0, _1, _0);
pub const TRYTE_6: Tryte = Tryte::from_trits(_0, _0, _0, _1, _T, _0);
pub const TRYTE_8: Tryte = Tryte::from_trits(_0, _0, _0, _1, _0, _T);
pub const TRYTE_9: Tryte = Tryte::from_trits(_0, _0, _0, _1, _0, _0);
pub const TRYTE_16: Tryte = Tryte::from_trits(_0, _0, _1, _T, _T, _1);
pub const TRYTE_64: Tryte = Tryte::from_trits(_0, _1, _T, _1, _0, _1);
pub const TRYTE_81: Tryte = Tryte::from_trits(_0, _1, _0, _0, _0, _0);
pub const TRYTE_89: Tryte = Tryte::from_trits(_0, _1, _0, _1, _0, _T);
pub const TRYTE_167: Tryte = Tryte::from_trits(_1, _T, _0, _1, _T, _T);
pub const TRYTE_217: Tryte = Tryte::from_trits(_1, _0, _T, _0, _0, _1);
pub const TRYTE_256: Tryte = Tryte::from_trits(_1, _0, _0, _1, _1, _1);
pub const TRYTE_278: Tryte = Tryte::from_trits(_1, _0, _1, _1, _0, _T);
pub const TRYTE_317: Tryte = Tryte::from_trits(_1, _1, _0, _T, _1, _T);
pub const TRYTE_MAX: Tryte = Tryte::from_trits(_1, _1, _1, _1, _1, _1);

pub const TRYTE4_MIN: [Tryte; 4] = [TRYTE_MIN; 4];
pub const TRYTE4_NEG1073741824: [Tryte; 4] = [TRYTE_89, TRYTE_NEG317, TRYTE_167, TRYTE_NEG3];
pub const TRYTE4_NEG4096: [Tryte; 4] = [TRYTE_278, TRYTE_NEG6, TRYTE_0, TRYTE_0];
pub const TRYTE4_NEG512: [Tryte; 4] = [TRYTE_217, TRYTE_NEG1, TRYTE_0, TRYTE_0];
pub const TRYTE4_NEG256: [Tryte; 4] = [TRYTE_NEG256, TRYTE_0, TRYTE_0, TRYTE_0];
pub const TRYTE4_NEG81: [Tryte; 4] = [TRYTE_NEG81, TRYTE_0, TRYTE_0, TRYTE_0];
pub const TRYTE4_NEG64: [Tryte; 4] = [TRYTE_NEG64, TRYTE_0, TRYTE_0, TRYTE_0];
pub const TRYTE4_NEG16: [Tryte; 4] = [TRYTE_NEG16, TRYTE_0, TRYTE_0, TRYTE_0];
pub const TRYTE4_NEG9: [Tryte; 4] = [TRYTE_NEG9, TRYTE_0, TRYTE_0, TRYTE_0];
pub const TRYTE4_NEG8: [Tryte; 4] = [TRYTE_NEG8, TRYTE_0, TRYTE_0, TRYTE_0];
pub const TRYTE4_NEG1: [Tryte; 4] = [TRYTE_NEG1, TRYTE_0, TRYTE_0, TRYTE_0];
pub const TRYTE4_0: [Tryte; 4] = [TRYTE_0, TRYTE_0, TRYTE_0, TRYTE_0];
pub const TRYTE4_1: [Tryte; 4] = [TRYTE_1, TRYTE_0, TRYTE_0, TRYTE_0];
pub const TRYTE4_8: [Tryte; 4] = [TRYTE_8, TRYTE_0, TRYTE_0, TRYTE_0];
pub const TRYTE4_9: [Tryte; 4] = [TRYTE_9, TRYTE_0, TRYTE_0, TRYTE_0];
pub const TRYTE4_16: [Tryte; 4] = [TRYTE_16, TRYTE_0, TRYTE_0, TRYTE_0];
pub const TRYTE4_64: [Tryte; 4] = [TRYTE_64, TRYTE_0, TRYTE_0, TRYTE_0];
pub const TRYTE4_81: [Tryte; 4] = [TRYTE_81, TRYTE_0, TRYTE_0, TRYTE_0];
pub const TRYTE4_256: [Tryte; 4] = [TRYTE_256, TRYTE_0, TRYTE_0, TRYTE_0];
pub const TRYTE4_512: [Tryte; 4] = [TRYTE_NEG217, TRYTE_1, TRYTE_0, TRYTE_0];
pub const TRYTE4_4096: [Tryte; 4] = [TRYTE_NEG278, TRYTE_6, TRYTE_0, TRYTE_0];
pub const TRYTE4_1073741824: [Tryte; 4] = [TRYTE_NEG89, TRYTE_317, TRYTE_NEG167, TRYTE_3];
pub const TRYTE4_MAX: [Tryte; 4] = [TRYTE_MAX; 4];

pub const TRYTE8_0: [Tryte; 8] = [TRYTE_0; 8];

pub const TRYTE12_0: [Tryte; 12] = [TRYTE_0; 12];

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

pub const WORD_MIN: i64 = -141_214_768_240;
pub const WORD_MAX: i64 = 141_214_768_240;
