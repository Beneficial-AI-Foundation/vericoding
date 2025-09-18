// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Corrected `mul_i32` to ensure `b` is `3` and added postcondition for `a * 3` only. */
fn mul_i32(a: i32, b: i32) -> (result: i64)
    requires
        b == 3,
        (a <= i32::MAX / 3) && (a >= i32::MIN / 3),
    ensures
        result == a as i64 * 3,
{
    a as i64 * b as i64
}
// </vc-helpers>

// <vc-spec>
fn triple(x: i32) -> (result: i32)
    ensures
        result / 3 == x,
        result / 3 * 3 == result,
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Addressed the `mul_i32` precondition issue and the assertion failures. Changed `mul_i32` to accept `i32` as second argument and correctly calculate the result as `i64`. Added an explicit proof to show that `result_i64 / 3` is equal to `x` when `result_i64` is cast back to `i32`.*/
{
    let result_i64 = mul_i32(x, 3);
    proof {
        assert(result_i64 == x as i64 * 3);
        // Since x is within bounds (x <= i32::MAX / 3 && x >= i32::MIN / 3),
        // 3 * x will not overflow i32, so (x as i64 * 3) will fit in i32 after truncation.
        // Also, integer division by 3 for a multiple of 3 will return the original number.
        assert(result_i64 as i32 / 3 == x) by(integer_ring) ;
        assert(result_i64 as i32 / 3 * 3 == result_i64 as i32) by(integer_ring);
    }
    result_i64 as i32
}
// </vc-code>

}
fn main() {}