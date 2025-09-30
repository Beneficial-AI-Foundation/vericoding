// <vc-preamble>
use vstd::prelude::*;

verus! {

/* Structure representing floating-point type information */
pub struct FloatInfo {
    pub eps: u32,              // Machine epsilon (represented as u32)
    pub epsneg: u32,           // Negative machine epsilon  
    pub max: u32,              // Maximum representable value
    pub min: i32,              // Minimum representable value (typically -max)
    pub tiny: u32,             // Smallest positive normal number
    pub smallest_subnormal: u32, // Smallest positive subnormal number
    pub maxexp: i32,           // Maximum exponent
    pub minexp: i32,           // Minimum exponent
    pub negep: i32,            // Negative epsilon exponent
    pub nexp: u32,             // Number of bits in exponent
    pub nmant: u32,            // Number of bits in mantissa
    pub precision: u32,        // Approximate decimal precision
}
// </vc-preamble>

// <vc-helpers>
proof fn lemma_one_lt_two()
    ensures
        1 < 2,
{
}

// </vc-helpers>

// <vc-spec>
fn numpy_finfo() -> (info: FloatInfo)
    ensures
        /* Machine epsilon is positive */
        info.eps > 0,
        /* Negative epsilon is positive */
        info.epsneg > 0,
        /* Max is positive and finite */
        info.max > 0,
        /* Min is negative max (for symmetric representation) */
        info.min == -(info.max as i32),
        /* Tiny (smallest normal) is positive */
        info.tiny > 0,
        /* Smallest subnormal is positive and less than tiny */
        info.smallest_subnormal > 0,
        info.smallest_subnormal < info.tiny,
        /* Exponent relationships */
        info.maxexp > 0,
        info.minexp < 0,
        info.negep < 0,
        /* Bit counts are positive */
        info.nexp > 0,
        info.nmant > 0,
        /* Precision is at least 1 */
        info.precision >= 1,
        /* Relationship between mantissa bits and precision */
        info.precision <= info.nmant
// </vc-spec>
// <vc-code>
{
    let max_val: u32 = 100u32;
    let info = FloatInfo {
        eps: 1u32,
        epsneg: 1u32,
        max: max_val,
        min: -(max_val as i32),
        tiny: 2u32,
        smallest_subnormal: 1u32,
        maxexp: 10,
        minexp: -10,
        negep: -1,
        nexp: 8u32,
        nmant: 24u32,
        precision: 6u32,
    };
    info
}
// </vc-code>


}
fn main() {}