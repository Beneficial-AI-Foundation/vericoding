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
proof fn helper_noop() {
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
    // Construct concrete floating-point parameters that satisfy the specification
    let eps: u32 = 1;
    let epsneg: u32 = 1;
    let max: u32 = 8;
    let min: i32 = -(max as i32);
    let tiny: u32 = 4;
    let smallest_subnormal: u32 = 1;
    let maxexp: i32 = 127;
    let minexp: i32 = -126;
    let negep: i32 = -1;
    let nexp: u32 = 8;
    let nmant: u32 = 23;
    let precision: u32 = 6;

    proof {
        // discharge a few obvious obligations to help the verifier
        assert(smallest_subnormal > 0);
        assert(tiny > 0);
        assert(smallest_subnormal < tiny);
        assert(max > 0);
        assert(eps > 0);
        assert(epsneg > 0);
        assert(maxexp > 0);
        assert(minexp < 0);
        assert(negep < 0);
        assert(nexp > 0);
        assert(nmant > 0);
        assert(precision >= 1);
        assert(precision <= nmant);
    }

    FloatInfo {
        eps: eps,
        epsneg: epsneg,
        max: max,
        min: min,
        tiny: tiny,
        smallest_subnormal: smallest_subnormal,
        maxexp: maxexp,
        minexp: minexp,
        negep: negep,
        nexp: nexp,
        nmant: nmant,
        precision: precision,
    }
}

// </vc-code>


}
fn main() {}