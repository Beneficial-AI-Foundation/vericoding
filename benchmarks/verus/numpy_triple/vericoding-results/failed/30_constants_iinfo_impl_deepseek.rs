// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Added helpers for safe arithmetic and validation */
proof fn safe_arithmetic_uint64() 
    ensures 0x7FFFFFFFFFFFFFFF as i64 + 1 == 0x8000000000000000 as i64
{
}

proof fn validate_int64_min() 
    ensures -9223372036854775808 == 0x8000000000000000 as i64
{
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
    /* code modified by LLM (iteration 5): Added proof blocks and safe arithmetic for UInt64 case */
    match int_type {
        IntegerType::Int8 => IntegerInfo { bits: 8, min: -128, max: 127 },
        IntegerType::Int16 => IntegerInfo { bits: 16, min: -32768, max: 32767 },
        IntegerType::Int32 => IntegerInfo { bits: 32, min: -2147483648, max: 2147483647 },
        IntegerType::Int64 => {
            proof {
                validate_int64_min();
            }
            IntegerInfo { bits: 64, min: 0x8000000000000000 as i64, max: 9223372036854775807 }
        },
        IntegerType::UInt8 => IntegerInfo { bits: 8, min: 0, max: 255 },
        IntegerType::UInt16 => IntegerInfo { bits: 16, min: 0, max: 65535 },
        IntegerType::UInt32 => IntegerInfo { bits: 32, min: 0, max: 4294967295 },
        IntegerType::UInt64 => {
            proof {
                safe_arithmetic_uint64();
            }
            IntegerInfo { bits: 64, min: 0, max: 0x8000000000000000 as i64 }
        },
    }
}
// </vc-code>

}
fn main() {}