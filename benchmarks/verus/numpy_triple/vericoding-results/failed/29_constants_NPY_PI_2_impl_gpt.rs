// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn approx_pi_over_2_i32() -> (r: i32)
    ensures
        1000 < r < 2000,
{
    1571
}
// </vc-helpers>

// <vc-spec>
fn npy_pi_2() -> (result: i32)
    ensures
        /* π/2 is approximately 1.5708... represented as fixed point */
        1570 < result < 1571,
        /* Basic sanity check: π/2 is between 1 and 2 */
        1000 < result < 2000,
        /* 2*(π/2) should be approximately π (3.14159...) */
        3141 < 2 * (result as int) < 3142,
        /* (π/2)/2 = π/4 is approximately 0.7854... */
        785 < (result as int) / 2 < 786,
        /* 3*(π/2) = 3π/2 is approximately 4.7124... (270 degrees) */
        4712 < 3 * (result as int) < 4713,
        /* 4*(π/2) = 2π is approximately 6.2832... (full circle) */
        6283 < 4 * (result as int) < 6284,
// </vc-spec>
// <vc-code>
{
    let result = approx_pi_over_2_i32();
    result
}
// </vc-code>


}
fn main() {}