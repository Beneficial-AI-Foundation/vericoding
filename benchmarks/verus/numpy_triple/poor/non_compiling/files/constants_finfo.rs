/* Machine limits for floating point types.

Returns a structure containing information about the numerical properties 
and limits of floating-point types, including epsilon, maximum/minimum 
values, and precision details according to IEEE 754 standard. */

use vstd::prelude::*;

verus! {
/* Structure representing floating-point type information */
pub struct FloatInfo {
    eps: f64,              // Machine epsilon
    epsneg: f64,           // Negative machine epsilon  
    max: f64,              // Maximum representable value
    min: f64,              // Minimum representable value (typically -max)
    tiny: f64,             // Smallest positive normal number
    smallest_subnormal: f64, // Smallest positive subnormal number
    maxexp: i32,           // Maximum exponent
    minexp: i32,           // Minimum exponent
    negep: i32,            // Negative epsilon exponent
    nexp: u32,             // Number of bits in exponent
    nmant: u32,            // Number of bits in mantissa
    precision: u32,        // Approximate decimal precision
}
fn numpy_finfo() -> (info: FloatInfo)
    ensures
        info.eps > 0.0,
        info.epsneg > 0.0,
        1.0f64 + info.eps > 1.0,
        1.0f64 - info.epsneg < 1.0,
        info.max > 0.0,
        info.min == -info.max,
        info.tiny > 0.0,
        info.smallest_subnormal > 0.0,
        info.smallest_subnormal < info.tiny,
        info.maxexp > 0,
        info.minexp < 0,
        info.negep < 0,
        info.nexp > 0,
        info.nmant > 0,
        info.precision >= 1,
        info.precision <= info.nmant
{
    // impl-start
    assume(false);
    FloatInfo {
        eps: 0.0,
        epsneg: 0.0,
        max: 0.0,
        min: 0.0,
        tiny: 0.0,
        smallest_subnormal: 0.0,
        maxexp: 0,
        minexp: 0,
        negep: 0,
        nexp: 0,
        nmant: 0,
        precision: 1,
    }
    // impl-end
}
}
fn main() {}