/* Machine limits for floating point types.
    
Returns machine limits for the Float type.
This provides information about the precision and range of Float values. */

use vstd::prelude::*;

verus! {
struct FloatInfo {
    bits: usize,
    eps: f64,
    max: f64,
    min: f64,
    precision: usize,
    resolution: f64,
    smallest_normal: f64,
    smallest_subnormal: f64,
}

fn numpy_finfo() -> (info: FloatInfo)
    ensures
        info.bits > 0,
        info.precision > 0,
        info.eps > 0.0,
        info.eps < 1.0,
        info.max > 0.0,
        info.min < 0.0,
        info.min == -info.max,
        info.resolution > 0.0,
        info.smallest_normal > 0.0,
        info.smallest_normal < 1.0,
        info.smallest_subnormal > 0.0,
        info.smallest_subnormal <= info.smallest_normal,
        info.eps == info.resolution,
        info.bits == 32 || info.bits == 64,
{
    // impl-start
    assume(false);
    FloatInfo {
        bits: 0,
        eps: 0.0,
        max: 0.0,
        min: 0.0,
        precision: 0,
        resolution: 0.0,
        smallest_normal: 0.0,
        smallest_subnormal: 0.0,
    }
    // impl-end
}
}
fn main() {}