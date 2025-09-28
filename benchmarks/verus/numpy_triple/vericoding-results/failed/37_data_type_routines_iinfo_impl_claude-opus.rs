// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
struct IntInfo {

    bits: u32,

    min: i64,

    max: i64,
}

enum IntType {

    Int8,

    Int16,

    Int32,

    Int64,

    UInt8,

    UInt16,

    UInt32,

    UInt64,
}

fn iinfo(int_type: IntType) -> (info: IntInfo)
    ensures
        match int_type {
            IntType::Int8 => info.bits == 8 && info.min == -128 && info.max == 127,
            IntType::Int16 => info.bits == 16 && info.min == -32768 && info.max == 32767,
            IntType::Int32 => info.bits == 32 && info.min == -2147483648 && info.max == 2147483647,
            IntType::Int64 => info.bits == 64 && info.min == -9223372036854775808 && info.max == 9223372036854775807,
            IntType::UInt8 => info.bits == 8 && info.min == 0 && info.max == 255,
            IntType::UInt16 => info.bits == 16 && info.min == 0 && info.max == 65535,
            IntType::UInt32 => info.bits == 32 && info.min == 0 && info.max == 4294967295,
            IntType::UInt64 => info.bits == 64 && info.min == 0 && info.max == 18446744073709551615,
        }
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): use explicit variable assignment with assertions to help verifier */
    let result = match int_type {
        IntType::Int8 => {
            let info = IntInfo { bits: 8, min: -128, max: 127 };
            assert(info.bits == 8);
            assert(info.min == -128);
            assert(info.max == 127);
            info
        },
        IntType::Int16 => {
            let info = IntInfo { bits: 16, min: -32768, max: 32767 };
            assert(info.bits == 16);
            assert(info.min == -32768);
            assert(info.max == 32767);
            info
        },
        IntType::Int32 => {
            let info = IntInfo { bits: 32, min: -2147483648, max: 2147483647 };
            assert(info.bits == 32);
            assert(info.min == -2147483648);
            assert(info.max == 2147483647);
            info
        },
        IntType::Int64 => {
            let info = IntInfo { bits: 64, min: -9223372036854775808, max: 9223372036854775807 };
            assert(info.bits == 64);
            assert(info.min == -9223372036854775808);
            assert(info.max == 9223372036854775807);
            info
        },
        IntType::UInt8 => {
            let info = IntInfo { bits: 8, min: 0, max: 255 };
            assert(info.bits == 8);
            assert(info.min == 0);
            assert(info.max == 255);
            info
        },
        IntType::UInt16 => {
            let info = IntInfo { bits: 16, min: 0, max: 65535 };
            assert(info.bits == 16);
            assert(info.min == 0);
            assert(info.max == 65535);
            info
        },
        IntType::UInt32 => {
            let info = IntInfo { bits: 32, min: 0, max: 4294967295 };
            assert(info.bits == 32);
            assert(info.min == 0);
            assert(info.max == 4294967295);
            info
        },
        IntType::UInt64 => {
            let info = IntInfo { bits: 64, min: 0, max: 9223372036854775807 };
            assert(info.bits == 64);
            assert(info.min == 0);
            assert(info.max == 9223372036854775807);
            info
        },
    };
    result
}
// </vc-code>

}
fn main() {}