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
    // Assuming f64 characteristics for numpy.finfo(np.float64)
    // These values are derived from IEEE 754 double-precision floating-point format.
    // Most `u32` fields represent the raw bit patterns that would correspond to these float values.

    // Machine epsilon: 2**-52. Represented as its bit pattern.
    let eps: u32 = 0x3cb00000; // Corresponds to 2.220446049250313e-16 (f64)

    // Negative machine epsilon: -2**-52.
    let epsneg: u32 = 0xbcb00000; // Corresponds to -2.220446049250313e-16 (f64)

    // Maximum representable value: (2 - 2**-52) * 2**1023. Represented as its bit pattern.
    let max: u32 = 0x7fefffff; // Corresponds to 1.7976931348623157e+308 (f64)

    // Minimum representable value (typically -max for symmetric representation).
    // This is -max in terms of conceptual value, not bit pattern.
    let min: i32 = -(max as i32); // Using i32 to match the FloatInfo struct field

    // Smallest positive normal number: 2**-1022. Represented as its bit pattern.
    let tiny: u32 = 0x00100000; // Corresponds to 2.2250738585072014e-308 (f64)

    // Smallest positive subnormal number: 2**-1074. Represented as its bit pattern.
    let smallest_subnormal: u32 = 0x00000001; // Corresponds to 4.9406564584124654e-324 (f64)

    // Maximum exponent: 1023 (for double precision)
    let maxexp: i32 = 1023;

    // Minimum exponent: -1022 (for double precision).
    // This refers to the exponent of the smallest normal number (2^-1022).
    let minexp: i32 = -1022;

    // Negative epsilon exponent: The exponent of machine epsilon (2^-52).
    let negep: i32 = -52;

    // Number of bits in exponent: 11 for double precision
    let nexp: u32 = 11;

    // Number of bits in mantissa (including implicit 1): 53 for double precision
    let nmant: u32 = 53;

    // Approximate decimal precision: log10(2**53) approx 15.95
    let precision: u32 = 15;

    FloatInfo {
        eps,
        epsneg,
        max,
        min,
        tiny,
        smallest_subnormal,
        maxexp,
        minexp,
        negep,
        nexp,
        nmant,
        precision,
    }
}
// </vc-code>


}
fn main() {}