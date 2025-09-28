// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): added postcondition capturing field equality to aid verification */
fn mk_info(bits: u32, min: i64, max: i64) -> IntegerInfo
    ensures
        result.bits == bits,
        result.min == min,
        result.max == max,
{
    IntegerInfo { bits, min, max }
}
// </vc-helpers>

// <vc-spec>
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum IntegerType {
    Int8,
    Int16, 
    Int32,
    Int64,
    UInt8,
    UInt16,
    UInt32,
    UInt64,
}

pub struct IntegerInfo {
    pub bits: u32,
    pub min: i64,
    pub max: i64,
}

fn iinfo(int_type: IntegerType) -> (result: IntegerInfo)
    ensures match int_type {
        IntegerType::Int8 => 
            result.bits == 8 && result.min == -128 && result.max == 127,
        IntegerType::Int16 => 
            result.bits == 16 && result.min == -32768 && result.max == 32767,
        IntegerType::Int32 => 
            result.bits == 32 && result.min == -2147483648 && result.max == 2147483647,
        IntegerType::Int64 => 
            result.bits == 64 && result.min == -9223372036854775808 && result.max == 9223372036854775807,
        IntegerType::UInt8 => 
            result.bits == 8 && result.min == 0 && result.max == 255,
        IntegerType::UInt16 => 
            result.bits == 16 && result.min == 0 && result.max == 65535,
        IntegerType::UInt32 => 
            result.bits == 32 && result.min == 0 && result.max == 4294967295,
        IntegerType::UInt64 => 
            result.bits == 64 && result.min == 0 && result.max == 18446744073709551615,
    }
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): set exact constants for all integer types, including UInt64 max */
    match int_type {
        IntegerType::Int8 => mk_info(8, -128, 127),
        IntegerType::Int16 => mk_info(16, -32768, 32767),
        IntegerType::Int32 => mk_info(32, -2147483647 - 1, 2147483647),
        IntegerType::Int64 => mk_info(64, -9223372036854775807 - 1, 9223372036854775807),
        IntegerType::UInt8 => mk_info(8, 0, 255),
        IntegerType::UInt16 => mk_info(16, 0, 65535),
        IntegerType::UInt32 => mk_info(32, 0, 4294967295),
        IntegerType::UInt64 => mk_info(64, 0, 18446744073709551615),
    }
}
// </vc-code>

}
fn main() {}