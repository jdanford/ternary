# ternary

Arithmetic, logical, and textual operations for balanced ternary data.

From [Wikipedia](https://en.wikipedia.org/wiki/Balanced_ternary):

> Balanced ternary is a ternary numeral system (i.e. base 3 with three digits) that uses a balanced
> signed-digit representation of the integers in which the digits have the values −1, 0, and 1. This stands
> in contrast to the standard (unbalanced) ternary system, in which digits have values 0, 1 and 2. The balanced
> ternary system can represent all integers without using a separate minus sign; the value of the leading
> non-zero digit of a number has the sign of the number itself.

## Trits

A trit (ternary digit) is one of { -1, 0, 1 }, written here as { T, 0, 1 }. T serves as a visual
approximation of a 1 with a bar over it, i.e. the negation of 1.
A trit can also represent the values { false, unknown, true } for use in [three-valued (Kleene)
logic](https://en.wikipedia.org/wiki/Three-valued_logic#Kleene_and_Priest_logics), or the values { less,
equal, greater } for use in comparisons.

This library represents a trit as two bits using the following mapping:

| Binary | Ternary   |
| ------ | --------- |
| 00     | 0         |
| 01     | 1         |
| 10     | _invalid_ |
| 11     | T         |

A trit holds log<sub>2</sub>3 ≈ 1.58 bits of information.

## Trytes

A tryte is a group of 6 trits, representing the range [-364, +364].

This library represents a tryte as an unsigned 16-bit integer, packing its 6 trits into the lower 12 bits and
leaving the highest 4 bits as 0.

A tryte holds log<sub>2</sub>(3<sup>6</sup>) ≈ 9.51 bits of information.

## Integers

Due to the nature of the balanced ternary system, there is no need for separate signed/unsigned integer
types. While this library performs all of its multi-tryte operations in little-endian fashion on tryte
sequences of any size, the following types are standardized:

| Type       | Size |                Range                 |
| ---------- | ---: | :----------------------------------: |
| Tryte      |    6 |             [-364, +364]             |
| Half(word) |   12 |         [-265,720, +265,720]         |
| Word       |   24 | [-141,214,768,240, +141,214,768,240] |

## Hytes

A byte can be written as two hexadecimal characters representing four bits each. Analogously, a tryte can be
written as two hytes (i.e. half trytes) representing three trits each, using the following mapping:

| Hyte | Ternary | Decimal |
| ---- | ------- | ------: |
| m    | TTT     |     -13 |
| l    | TT0     |     -12 |
| k    | TT1     |     -11 |
| j    | T0T     |     -10 |
| i    | T00     |      -9 |
| h    | T01     |      -8 |
| g    | T1T     |      -7 |
| f    | T10     |      -6 |
| e    | T11     |      -5 |
| d    | 0TT     |      -4 |
| c    | 0T0     |      -3 |
| b    | 0T1     |      -2 |
| a    | 00T     |      -1 |
| 0    | 000     |       0 |
| A    | 001     |       1 |
| B    | 01T     |       2 |
| C    | 010     |       3 |
| D    | 011     |       4 |
| E    | 1TT     |       5 |
| F    | 1T0     |       6 |
| G    | 1T1     |       7 |
| H    | 10T     |       8 |
| I    | 100     |       9 |
| J    | 101     |      10 |
| K    | 11T     |      11 |
| L    | 110     |      12 |
| M    | 111     |      13 |

## UTF-6T

This library implements Unicode text handling using UTF-6T, a ternary adaptation of UTF-8. Code points are
encoded in one, two, or three trytes using the following patterns:

| Code point type | Trytes               |
| --------------- | -------------------- |
| Single          | 0xxxxx               |
| Double          | 1Txxxx Txxxxx        |
| Triple          | 11xxxx Txxxxx Txxxxx |
