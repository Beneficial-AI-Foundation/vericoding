// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): simple constructor with ensures for all fields */
fn mk_info(bits: u32, min: i64, max: i64) -> (result: IntegerInfo)
    ensures
        result.bits == bits,
        result.min == min,
        result.max == max
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
    /* code modified by LLM (iteration 5): implemented all IntegerType cases using mk_info with precise constants */
    match int_type {
        IntegerType::Int8 => {
            mk_info(8u32, -128i64, 127i64)
        }
        IntegerType::Int16 => {
            mk_info(16u32, -32768i64, 32767i64)
        }
        IntegerType::Int32 => {
            let min32: i64 = -2147483647i64 - 1i64;
            mk_info(32u32, min32, 2147483647i64)
        }
        IntegerType::Int64 => {
            let min64: i64 = -9223372036854775807i64 - 1i64;
            mk_info(64u32, min64, 9223372036854775807i64)
        }
        IntegerType::UInt8 => {
            mk_info(8u32, 0i64, 255i64)
        }
        IntegerType::UInt16 => {
            mk_info(16u32, 0i64, 65535i64)
        }
        IntegerType::UInt32 => {
            mk_info(32u32, 0i64, 4294967295i64)
        }
        IntegerType::UInt64 => {
            mk_info(64u32, 0i64, 18446744073709551615)
        }
    }
}
// </vc-code>

}
fn main() {}