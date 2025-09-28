// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed UInt64 max value to avoid truncation warning */
proof fn integer_type_info(int_type: IntegerType) -> (info: IntegerInfo)
    ensures
        int_type == IntegerType::Int8 ==> info.bits == 8 && info.min == -128 && info.max == 127,
        int_type == IntegerType::Int16 ==> info.bits == 16 && info.min == -32768 && info.max == 32767,
        int_type == IntegerType::Int32 ==> info.bits == 32 && info.min == -2147483648 && info.max == 2147483647,
        int_type == IntegerType::Int64 ==> info.bits == 64 && info.min == -9223372036854775808 && info.max == 9223372036854775807,
        int_type == IntegerType::UInt8 ==> info.bits == 8 && info.min == 0 && info.max == 255,
        int_type == IntegerType::UInt16 ==> info.bits == 16 && info.min == 0 && info.max == 65535,
        int_type == IntegerType::UInt32 ==> info.bits == 32 && info.min == 0 && info.max == 4294967295,
        int_type == IntegerType::UInt64 ==> info.bits == 64 && info.min == 0 && info.max == 18446744073709551615,
{
    match int_type {
        IntegerType::Int8 => IntegerInfo {bits: 8, min: -128i64, max: 127i64},
        IntegerType::Int16 => IntegerInfo {bits: 16, min: -32768i64, max: 32767i64},
        IntegerType::Int32 => IntegerInfo {bits: 32, min: -2147483648i64, max: 2147483647i64},
        IntegerType::Int64 => IntegerInfo {bits: 64, min: -9223372036854775808i64, max: 9223372036854775807i64},
        IntegerType::UInt8 => IntegerInfo {bits: 8, min: 0i64, max: 255i64},
        IntegerType::UInt16 => IntegerInfo {bits: 16, min: 0i64, max: 65535i64},
        IntegerType::UInt32 => IntegerInfo {bits: 32, min: 0i64, max: 4294967295i64},
        IntegerType::UInt64 => IntegerInfo {bits: 64, min: 0i64, max: 18446744073709551615},
    }
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
/* code modified by LLM (iteration 5): Use helper function to ensure verified implementation */
{
    let result = integer_type_info(int_type);
    result
}
// </vc-code>

}
fn main() {}