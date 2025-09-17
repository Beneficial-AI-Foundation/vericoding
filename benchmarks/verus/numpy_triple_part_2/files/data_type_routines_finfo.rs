// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
/* Structure representing floating point type information returned by numpy.finfo */
struct FloatInfo {
    /* The number of bits occupied by the type */
    bits: nat,
    /* The smallest representable positive number such that 1.0 + eps != 1.0 */
    eps: int,
    /* The largest representable number */
    max: int,
    /* The smallest representable number, typically -max */
    min: int,
    /* The approximate number of decimal digits to which this kind of float is precise */
    precision: nat,
    /* The approximate decimal resolution of this type */
    resolution: int,
    /* The smallest positive floating point number with 1 as leading bit in the mantissa */
    smallest_normal: int,
    /* The smallest positive floating point number with 0 as leading bit in the mantissa */
    smallest_subnormal: int,
}

fn numpy_finfo() -> (info: FloatInfo)
    ensures
        /* Basic sanity checks */
        info.bits > 0,
        info.precision > 0,
        /* eps is positive and small */
        info.eps > 0,
        info.eps < 1,
        /* max is positive, min is negative */
        info.max > 0,
        info.min < 0,
        /* min is typically -max for symmetric floating point types */
        info.min == -info.max,
        /* resolution is positive */
        info.resolution > 0,
        /* smallest_normal is positive and smaller than 1 */
        info.smallest_normal > 0,
        info.smallest_normal < 1,
        /* smallest_subnormal is positive and smaller than smallest_normal */
        info.smallest_subnormal > 0,
        info.smallest_subnormal <= info.smallest_normal,
        /* eps represents the machine epsilon property */
        info.eps == info.resolution,
        /* The number of bits should be reasonable (32 or 64 for common float types) */
        info.bits == 32 || info.bits == 64,
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    unreached()
    // impl-end
}
// </vc-code>


}
fn main() {}