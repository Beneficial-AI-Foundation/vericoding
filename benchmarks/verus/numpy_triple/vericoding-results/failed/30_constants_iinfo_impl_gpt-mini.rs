// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): make pow2 take an int and return i64; use casts for u32->int */
spec fn pow2(n: int) -> i64 decreases n {
    if n == 0 { 1i64 } else { 2i64 * pow2(n - 1) }
}

spec fn signed_min(bits: u32) -> i64 {
    -pow2((bits as int) - 1)
}

spec fn signed_max(bits: u32) -> i64 {
    pow2((bits as int) - 1) - 1i64
}

spec fn unsigned_min(bits: u32) -> i64 {
    0i64
}

spec fn unsigned_max(bits: u32) -> i64 {
    pow2(bits as int) - 1i64
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
    /* code modified by LLM (iteration 5): construct IntegerInfo using helpers with casts */
    match int_type {
        IntegerType::Int8 => IntegerInfo { bits: 8u32, min: signed_min(8u32), max: signed_max(8u32) },
        IntegerType::Int16 => IntegerInfo { bits: 16u32, min: signed_min(16u32), max: signed_max(16u32) },
        IntegerType::Int32 => IntegerInfo { bits: 32u32, min: signed_min(32u32), max: signed_max(32u32) },
        IntegerType::Int64 => IntegerInfo { bits: 64u32, min: signed_min(64u32), max: signed_max(64u32) },
        IntegerType::UInt8 => IntegerInfo { bits: 8u32, min: unsigned_min(8u32), max: unsigned_max(8u32) },
        IntegerType::UInt16 => IntegerInfo { bits: 16u32, min: unsigned_min(16u32), max: unsigned_max(16u32) },
        IntegerType::UInt32 => IntegerInfo { bits: 32u32, min: unsigned_min(32u32), max: unsigned_max(32u32) },
        IntegerType::UInt64 => IntegerInfo { bits: 64u32, min: unsigned_min(64u32), max: unsigned_max(64u32) },
    }
}
// </vc-code>

}
fn main() {}