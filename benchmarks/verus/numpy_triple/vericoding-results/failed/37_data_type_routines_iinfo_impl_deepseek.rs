// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Use correct literal syntax for large unsigned values */
fn iinfo_match_int8() -> (info: IntInfo)
    ensures
        info.bits == 8,
        info.min == -128,
        info.max == 127,
{
    IntInfo { bits: 8, min: -128, max: 127 }
}

fn iinfo_match_int16() -> (info: IntInfo)
    ensures
        info.bits == 16,
        info.min == -32768,
        info.max == 32767,
{
    IntInfo { bits: 16, min: -32768, max: 32767 }
}

fn iinfo_match_int32() -> (info: IntInfo)
    ensures
        info.bits == 32,
        info.min == -2147483648,
        info.max == 2147483647,
{
    IntInfo { bits: 32, min: -2147483648, max: 2147483647 }
}

fn iinfo_match_int64() -> (info: IntInfo)
    ensures
        info.bits == 64,
        info.min == -9223372036854775808,
        info.max == 9223372036854775807,
{
    IntInfo { bits: 64, min: -9223372036854775808, max: 9223372036854775807 }
}

fn iinfo_match_uint8() -> (info: IntInfo)
    ensures
        info.bits == 8,
        info.min == 0,
        info.max == 255,
{
    IntInfo { bits: 8, min: 0, max: 255 }
}

fn iinfo_match_uint16() -> (info: IntInfo)
    ensures
        info.bits == 16,
        info.min == 0,
        info.max == 65535,
{
    IntInfo { bits: 16, min: 0, max: 65535 }
}

fn iinfo_match_uint32() -> (info: IntInfo)
    ensures
        info.bits == 32,
        info.min == 0,
        info.max == 4294967295,
{
    IntInfo { bits: 32, min: 0, max: 4294967295 }
}

fn iinfo_match_uint64() -> (info: IntInfo)
    ensures
        info.bits == 64,
        info.min == 0,
        info.max == 18446744073709551615u64 as i64,
{
    IntInfo { bits: 64, min: 0, max: 18446744073709551615u64 as i64 }
}
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
    /* code modified by LLM (iteration 5): Updated to use corrected helper functions */
    match int_type {
        IntType::Int8 => iinfo_match_int8(),
        IntType::Int16 => iinfo_match_int16(),
        IntType::Int32 => iinfo_match_int32(),
        IntType::Int64 => iinfo_match_int64(),
        IntType::UInt8 => iinfo_match_uint8(),
        IntType::UInt16 => iinfo_match_uint16(),
        IntType::UInt32 => iinfo_match_uint32(),
        IntType::UInt64 => iinfo_match_uint64(),
    }
}
// </vc-code>

}
fn main() {}