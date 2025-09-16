// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): Adding helper for arithmetic check */
proof fn u64_multiplication_fits_u128_div_2(a: u64, h: u64)
    requires
        a > 0,
        h > 0,
        a * h / 2 <= u64::MAX,
    ensures
        (a as u128 * h as u128) / 2 <= u64::MAX as u128,
{

}
// </vc-helpers>

// <vc-spec>
fn triangle_area(a: u64, h: u64) -> (area: u64)

    requires
        a > 0,
        h > 0,
        a * h / 2 <= u64::MAX
        ,

    ensures
        area == a * h / 2,
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): Fix compilation issue by correctly implementing the function body. */
{
    let result: u64;
    proof {
        u64_multiplication_fits_u128_div_2(a, h);
    }
    result = (a as u128 * h as u128 / 2) as u64;
    result
}
// </vc-code>

}
fn main() {}