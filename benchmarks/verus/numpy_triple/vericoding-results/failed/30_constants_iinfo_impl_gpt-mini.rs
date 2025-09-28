// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): returns bit width for integer type */
fn bits_of(t: IntegerType) -> u32
    ensures
        match t {
            IntegerType::Int8 => result == 8,
            IntegerType::Int16 => result == 16,
            IntegerType::Int32 => result == 32,
            IntegerType::Int64 => result == 64,
            IntegerType::UInt8 => result == 8,
            IntegerType::UInt16 => result == 16,
            IntegerType::UInt32 => result == 32,
            IntegerType::UInt64 => result == 64,
        },
{
    match t {
        IntegerType::Int8 => 8,
        IntegerType::Int16 => 16,
        IntegerType::Int32 => 32,
        IntegerType::Int64 => 64,
        IntegerType::UInt8 => 8,
        IntegerType::UInt16 => 16,
        IntegerType::UInt32 => 32,
        IntegerType::UInt64 => 64,
    }
}

/* helper modified by LLM (iteration 5): returns minimum value for integer type */
fn min_of(t: IntegerType) -> i64
    ensures
        match t {
            IntegerType::Int8 => result == -128,
            IntegerType::Int16 => result == -32768,
            IntegerType::Int32 => result == -2147483648,
            IntegerType::Int64 => result == -9223372036854775808,
            IntegerType::UInt8 => result == 0,
            IntegerType::UInt16 => result == 0,
            IntegerType::UInt32 => result == 0,
            IntegerType::UInt64 => result == 0,
        },
{
    match t {
        IntegerType::Int8 => -128,
        IntegerType::Int16 => -32768,
        IntegerType::Int32 => -2147483648,
        IntegerType::Int64 => -9223372036854775808,
        IntegerType::UInt8 => 0,
        IntegerType::UInt16 => 0,
        IntegerType::UInt32 => 0,
        IntegerType::UInt64 => 0,
    }
}

/* helper modified by LLM (iteration 5): returns maximum value for integer type */
fn max_of(t: IntegerType) -> i64
    ensures
        match t {
            IntegerType::Int8 => result == 127,
            IntegerType::Int16 => result == 32767,
            IntegerType::Int32 => result == 2147483647,
            IntegerType::Int64 => result == 9223372036854775807,
            IntegerType::UInt8 => result == 255,
            IntegerType::UInt16 => result == 65535,
            IntegerType::UInt32 => result == 4294967295,
            IntegerType::UInt64 => result == 18446744073709551615,
        },
{
    match t {
        IntegerType::Int8 => 127,
        IntegerType::Int16 => 32767,
        IntegerType::Int32 => 2147483647,
        IntegerType::Int64 => 9223372036854775807,
        IntegerType::UInt8 => 255,
        IntegerType::UInt16 => 65535,
        IntegerType::UInt32 => 4294967295,
        IntegerType::UInt64 => 18446744073709551615,
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
{
    /* code modified by LLM (iteration 5): construct IntegerInfo using helpers */
    IntegerInfo {
        bits: bits_of(int_type),
        min: min_of(int_type),
        max: max_of(int_type),
    }
}

// </vc-code>

}
fn main() {}