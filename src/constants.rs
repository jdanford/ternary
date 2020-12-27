pub const TRIT_BIT_LEN: usize = 2;

pub const HYTE_BIT_LEN: usize = 6;

pub const TRYTE_LEN: usize = 1;
pub const TRYTE_TRIT_LEN: usize = 6;
pub const TRYTE_BIT_LEN: usize = TRYTE_TRIT_LEN * TRIT_BIT_LEN;

pub const HALF_LEN: usize = 2;
pub const HALF_TRIT_LEN: usize = HALF_LEN * TRYTE_TRIT_LEN;
pub const HALF_BIT_LEN: usize = HALF_TRIT_LEN * TRIT_BIT_LEN;

pub const WORD_LEN: usize = 4;
pub const WORD_TRIT_LEN: usize = WORD_LEN * TRYTE_TRIT_LEN;
pub const WORD_BIT_LEN: usize = WORD_TRIT_LEN * TRIT_BIT_LEN;
