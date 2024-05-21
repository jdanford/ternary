use crate::{
    trit::{index2, index3, index4, _0, _1, _INVALID, _T},
    Trit,
};

const TRIT2_TABLE_SIZE: usize = 16;
const TRIT3_TABLE_SIZE: usize = 64;
const TRIT4_TABLE_SIZE: usize = 256;

pub const TRIT2_TO_AND: [Trit; TRIT2_TABLE_SIZE] = {
    let mut table = [_INVALID; TRIT2_TABLE_SIZE];

    table[index2(_0, _0)] = _0;
    table[index2(_0, _1)] = _0;
    table[index2(_0, _T)] = _T;
    table[index2(_1, _0)] = _0;
    table[index2(_1, _1)] = _1;
    table[index2(_1, _T)] = _T;
    table[index2(_T, _0)] = _T;
    table[index2(_T, _1)] = _T;
    table[index2(_T, _T)] = _T;

    table
};

pub const TRIT2_TO_CMP: [Trit; TRIT2_TABLE_SIZE] = {
    let mut table = [_INVALID; TRIT2_TABLE_SIZE];

    table[index2(_0, _0)] = _0;
    table[index2(_0, _1)] = _T;
    table[index2(_0, _T)] = _1;
    table[index2(_1, _0)] = _1;
    table[index2(_1, _1)] = _0;
    table[index2(_1, _T)] = _1;
    table[index2(_T, _0)] = _T;
    table[index2(_T, _1)] = _T;
    table[index2(_T, _T)] = _0;

    table
};

pub const TRIT2_TO_OR: [Trit; TRIT2_TABLE_SIZE] = {
    let mut table = [_INVALID; TRIT2_TABLE_SIZE];

    table[index2(_0, _0)] = _0;
    table[index2(_0, _1)] = _1;
    table[index2(_0, _T)] = _0;
    table[index2(_1, _0)] = _1;
    table[index2(_1, _1)] = _1;
    table[index2(_1, _T)] = _1;
    table[index2(_T, _0)] = _0;
    table[index2(_T, _1)] = _1;
    table[index2(_T, _T)] = _T;

    table
};

pub const TRIT2_TO_PRODUCT: [Trit; TRIT2_TABLE_SIZE] = {
    let mut table = [_INVALID; TRIT2_TABLE_SIZE];

    table[index2(_0, _0)] = _0;
    table[index2(_0, _1)] = _0;
    table[index2(_0, _T)] = _0;
    table[index2(_1, _0)] = _0;
    table[index2(_1, _1)] = _1;
    table[index2(_1, _T)] = _T;
    table[index2(_T, _0)] = _0;
    table[index2(_T, _1)] = _T;
    table[index2(_T, _T)] = _1;

    table
};

pub const TRIT3_TO_SUM_AND_CARRY: [(Trit, Trit); TRIT3_TABLE_SIZE] = {
    let mut table = [(_INVALID, _INVALID); TRIT3_TABLE_SIZE];

    table[index3(_0, _0, _0)] = (_0, _0);
    table[index3(_0, _0, _1)] = (_1, _0);
    table[index3(_0, _0, _T)] = (_T, _0);
    table[index3(_0, _1, _0)] = (_1, _0);
    table[index3(_0, _1, _1)] = (_T, _1);
    table[index3(_0, _1, _T)] = (_0, _0);
    table[index3(_0, _T, _0)] = (_T, _0);
    table[index3(_0, _T, _1)] = (_0, _0);
    table[index3(_0, _T, _T)] = (_1, _T);
    table[index3(_1, _0, _0)] = (_1, _0);
    table[index3(_1, _0, _1)] = (_T, _1);
    table[index3(_1, _0, _T)] = (_0, _0);
    table[index3(_1, _1, _0)] = (_T, _1);
    table[index3(_1, _1, _1)] = (_0, _1);
    table[index3(_1, _1, _T)] = (_1, _0);
    table[index3(_1, _T, _0)] = (_0, _0);
    table[index3(_1, _T, _1)] = (_1, _0);
    table[index3(_1, _T, _T)] = (_T, _0);
    table[index3(_T, _0, _0)] = (_T, _0);
    table[index3(_T, _0, _1)] = (_0, _0);
    table[index3(_T, _0, _T)] = (_1, _T);
    table[index3(_T, _1, _0)] = (_0, _0);
    table[index3(_T, _1, _1)] = (_1, _0);
    table[index3(_T, _1, _T)] = (_T, _0);
    table[index3(_T, _T, _0)] = (_1, _T);
    table[index3(_T, _T, _1)] = (_T, _0);
    table[index3(_T, _T, _T)] = (_0, _T);

    table
};

pub const TRIT4_TO_I8: [i8; TRIT4_TABLE_SIZE] = {
    let mut table = [i8::MAX; TRIT4_TABLE_SIZE];

    table[index4(_T, _T, _0, _1)] = -35;
    table[index4(_T, _T, _1, _T)] = -34;
    table[index4(_T, _T, _1, _0)] = -33;
    table[index4(_T, _T, _1, _1)] = -32;
    table[index4(_T, _0, _T, _T)] = -31;
    table[index4(_T, _0, _T, _0)] = -30;
    table[index4(_T, _0, _T, _1)] = -29;
    table[index4(_T, _0, _0, _T)] = -28;
    table[index4(_T, _0, _0, _0)] = -27;
    table[index4(_T, _0, _0, _1)] = -26;
    table[index4(_T, _0, _1, _T)] = -25;
    table[index4(_T, _0, _1, _0)] = -24;
    table[index4(_T, _0, _1, _1)] = -23;
    table[index4(_T, _1, _T, _T)] = -22;
    table[index4(_T, _1, _T, _0)] = -21;
    table[index4(_T, _1, _T, _1)] = -20;
    table[index4(_T, _1, _0, _T)] = -19;
    table[index4(_T, _1, _0, _0)] = -18;
    table[index4(_T, _1, _0, _1)] = -17;
    table[index4(_T, _1, _1, _T)] = -16;
    table[index4(_T, _1, _1, _0)] = -15;
    table[index4(_T, _1, _1, _1)] = -14;
    table[index4(_0, _T, _T, _T)] = -13;
    table[index4(_0, _T, _T, _0)] = -12;
    table[index4(_0, _T, _T, _1)] = -11;
    table[index4(_0, _T, _0, _T)] = -10;
    table[index4(_0, _T, _0, _0)] = -9;
    table[index4(_0, _T, _0, _1)] = -8;
    table[index4(_0, _T, _1, _T)] = -7;
    table[index4(_0, _T, _1, _0)] = -6;
    table[index4(_0, _T, _1, _1)] = -5;
    table[index4(_0, _0, _T, _T)] = -4;
    table[index4(_0, _0, _T, _0)] = -3;
    table[index4(_0, _0, _T, _1)] = -2;
    table[index4(_0, _0, _0, _T)] = -1;
    table[index4(_0, _0, _0, _0)] = 0;
    table[index4(_0, _0, _0, _1)] = 1;
    table[index4(_0, _0, _1, _T)] = 2;
    table[index4(_0, _0, _1, _0)] = 3;
    table[index4(_0, _0, _1, _1)] = 4;
    table[index4(_0, _1, _T, _T)] = 5;
    table[index4(_0, _1, _T, _0)] = 6;
    table[index4(_0, _1, _T, _1)] = 7;
    table[index4(_0, _1, _0, _T)] = 8;
    table[index4(_0, _1, _0, _0)] = 9;
    table[index4(_0, _1, _0, _1)] = 10;
    table[index4(_0, _1, _1, _T)] = 11;
    table[index4(_0, _1, _1, _0)] = 12;
    table[index4(_0, _1, _1, _1)] = 13;
    table[index4(_1, _T, _T, _T)] = 14;
    table[index4(_1, _T, _T, _0)] = 15;
    table[index4(_1, _T, _T, _1)] = 16;
    table[index4(_1, _T, _0, _T)] = 17;
    table[index4(_1, _T, _0, _0)] = 18;
    table[index4(_1, _T, _0, _1)] = 19;
    table[index4(_1, _T, _1, _T)] = 20;
    table[index4(_1, _T, _1, _0)] = 21;
    table[index4(_1, _T, _1, _1)] = 22;
    table[index4(_1, _0, _T, _T)] = 23;
    table[index4(_1, _0, _T, _0)] = 24;
    table[index4(_1, _0, _T, _1)] = 25;
    table[index4(_1, _0, _0, _T)] = 26;
    table[index4(_1, _0, _0, _0)] = 27;
    table[index4(_1, _0, _0, _1)] = 28;
    table[index4(_1, _0, _1, _T)] = 29;
    table[index4(_1, _0, _1, _0)] = 30;
    table[index4(_1, _0, _1, _1)] = 31;
    table[index4(_1, _1, _T, _T)] = 32;
    table[index4(_1, _1, _T, _0)] = 33;
    table[index4(_1, _1, _T, _1)] = 34;
    table[index4(_1, _1, _0, _T)] = 35;

    table
};
