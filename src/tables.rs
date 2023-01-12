pub const TRIT2_TO_AND: [u16; 16] = {
    let mut table = [u16::MAX; 16];

    table[0b00_00] = 0b00;
    table[0b00_01] = 0b00;
    table[0b00_11] = 0b11;
    table[0b01_00] = 0b00;
    table[0b01_01] = 0b01;
    table[0b01_11] = 0b11;
    table[0b11_00] = 0b11;
    table[0b11_01] = 0b11;
    table[0b11_11] = 0b11;

    table
};

pub const TRIT2_TO_CMP: [u16; 16] = {
    let mut table = [u16::MAX; 16];

    table[0b00_00] = 0b00;
    table[0b00_01] = 0b11;
    table[0b00_11] = 0b01;
    table[0b01_00] = 0b01;
    table[0b01_01] = 0b00;
    table[0b01_11] = 0b01;
    table[0b11_00] = 0b11;
    table[0b11_01] = 0b11;
    table[0b11_11] = 0b00;

    table
};

pub const TRIT2_TO_OR: [u16; 16] = {
    let mut table = [u16::MAX; 16];

    table[0b00_00] = 0b00;
    table[0b00_01] = 0b01;
    table[0b00_11] = 0b00;
    table[0b01_00] = 0b01;
    table[0b01_01] = 0b01;
    table[0b01_11] = 0b01;
    table[0b11_00] = 0b00;
    table[0b11_01] = 0b01;
    table[0b11_11] = 0b11;

    table
};

pub const TRIT2_TO_PRODUCT: [u16; 16] = {
    let mut table = [u16::MAX; 16];

    table[0b00_00] = 0b00;
    table[0b00_01] = 0b00;
    table[0b00_11] = 0b00;
    table[0b01_00] = 0b00;
    table[0b01_01] = 0b01;
    table[0b01_11] = 0b11;
    table[0b11_00] = 0b00;
    table[0b11_01] = 0b11;
    table[0b11_11] = 0b01;

    table
};

pub const TRIT3_TO_SUM_AND_CARRY: [(u16, u16); 64] = {
    let mut table = [(u16::MAX, u16::MAX); 64];

    table[0b00_00_00] = (0b00, 0b00);
    table[0b00_00_01] = (0b01, 0b00);
    table[0b00_00_11] = (0b11, 0b00);
    table[0b00_01_00] = (0b01, 0b00);
    table[0b00_01_01] = (0b11, 0b01);
    table[0b00_01_11] = (0b00, 0b00);
    table[0b00_11_00] = (0b11, 0b00);
    table[0b00_11_01] = (0b00, 0b00);
    table[0b00_11_11] = (0b01, 0b11);
    table[0b01_00_00] = (0b01, 0b00);
    table[0b01_00_01] = (0b11, 0b01);
    table[0b01_00_11] = (0b00, 0b00);
    table[0b01_01_00] = (0b11, 0b01);
    table[0b01_01_01] = (0b00, 0b01);
    table[0b01_01_11] = (0b01, 0b00);
    table[0b01_11_00] = (0b00, 0b00);
    table[0b01_11_01] = (0b01, 0b00);
    table[0b01_11_11] = (0b11, 0b00);
    table[0b11_00_00] = (0b11, 0b00);
    table[0b11_00_01] = (0b00, 0b00);
    table[0b11_00_11] = (0b01, 0b11);
    table[0b11_01_00] = (0b00, 0b00);
    table[0b11_01_01] = (0b01, 0b00);
    table[0b11_01_11] = (0b11, 0b00);
    table[0b11_11_00] = (0b01, 0b11);
    table[0b11_11_01] = (0b11, 0b00);
    table[0b11_11_11] = (0b00, 0b11);

    table
};
