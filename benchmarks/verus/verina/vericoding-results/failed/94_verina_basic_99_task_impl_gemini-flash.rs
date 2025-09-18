// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Adding a helper function to ensure `x * 3` does not overflow and returns the product. */
fn checked_mul_3_i32(x: i32) -> (result: i32)
    requires
        x <= 715827882,
        x >= -715827882,
    ensures
        result == x * 3,
{
    x * 3
}
// </vc-helpers>

// <vc-spec>
fn triple(x: i32) -> (result: i32)
    ensures
        result / 3 == x,
        result / 3 * 3 == result,
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Use a helper function for multiplication to avoid `checked_mul` and ensure no overflow. */
{
    let result = checked_mul_3_i32(x);
    assert(result == x * 3);
    result
}
// </vc-code>

}
fn main() {}